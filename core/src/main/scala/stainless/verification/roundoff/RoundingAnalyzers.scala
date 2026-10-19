/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification
package roundoff

import trees._
import java.io.File
import java.nio.file.Files
import java.util.concurrent.TimeUnit
import scala.jdk.CollectionConverters._
import scala.util.Try
import scala.collection.mutable

/** One straight-line expression to analyse, written in the analyzer's input language. */
case class RoundingQuery(name: String, precision: FPPrecision, source: String)

/** Writes a straight-line expression in one analyzer's input language.
  *
  * It refuses what the analyzer cannot express while the function is decomposed, before any
  * time is spent on Ibex.
  */
trait RoundingSourceEmitter {
  def emit(name: String, label: String, expr: Expr, spec: InputSpec)(using Symbols)
    : Either[String, String]
}

/** A tool that bounds the rounding error of straight-line expressions. */
trait RoundingAnalyzer {
  val name: String

  /** Writes a query the way this tool reads it. */
  val emitter: RoundingSourceEmitter

  /** Answers every query in one batch: an absolute error bound, or why there is none. */
  def analyze(queries: Seq[RoundingQuery]): Map[String, Either[String, BigDecimal]]
}

object RoundingAnalyzer {

  /** Every query answered with what the tool reported for it, or with `why` for all of them
    * when the run as a whole failed.
    */
  def answers(tool: String, queries: Seq[RoundingQuery],
              reported: Either[String, Map[String, Either[String, BigDecimal]]])
    : Map[String, Either[String, BigDecimal]] =
    queries.map { q =>
      q.name -> reported.flatMap(_.getOrElse(q.name, Left(s"$tool reported nothing for this function")))
    }.toMap
}

/** The name an input goes by in an analyzer's input language, unique across the program. */
private[roundoff] def symbol(id: Identifier): String = s"v_${id.globalId}"

/** `Right` for round-to-nearest-ties-to-even, the one mode the analyzers support. */
private[roundoff] def roundsToNearestEven(mode: Expr, toolNote: String): Either[String, Unit] =
  mode match {
    case RoundNearestTiesToEven => Right(())
    case other => Left(s"unsupported rounding mode (${roundingModeName(other)}); $toolNote")
  }

private def roundingModeName(e: Expr): String = e match {
  case RoundTowardZero => "toward zero"
  case RoundTowardPositive => "toward positive"
  case RoundTowardNegative => "toward negative"
  case RoundNearestTiesToAway => "nearest, ties to away"
  case _ => "unknown"
}

/** Finds and runs the external tools: Daisy, FPTaylor and the fuzzer. */
private[roundoff] object ExternalTool {

  /** What a finished run printed, standard output and standard error together. */
  case class Finished(exitCode: Int, output: String)

  /** The executable, as given or as found on `PATH`. */
  def find(configured: String): Option[File] = {
    val direct = new File(configured)
    if (direct.isFile && direct.canExecute) Some(direct.getAbsoluteFile)
    else if (configured.contains(File.separator)) None
    else Option(System.getenv("PATH")).flatMap { path =>
      path.split(File.pathSeparatorChar).iterator
        .map(dir => new File(dir, configured))
        .find(f => f.isFile && f.canExecute)
        .map(_.getAbsoluteFile)
    }
  }

  def notFound(tool: String, configured: String, option: String): String =
    s"$tool executable '$configured' not found; set --$option=<path> or put it on your PATH"

  /** Runs `command` in `directory` with nothing on its standard input.
    *
    * The output goes to a file rather than a pipe, because reading a pipe to its end blocks
    * for as long as the run takes and would leave `timeout` nothing to do.
    *
    * @param tool        the name used in messages
    * @param timeout     seconds after which the run is killed, and what to suggest then
    */
  def run(tool: String, command: Seq[String], directory: File, reporter: inox.Reporter,
          environment: Map[String, String] = Map.empty,
          timeout: Option[(Double, String)] = None): Either[String, Finished] = {
    reporter.debug(s"Invoking ${command.mkString(" ")}")(using DebugSectionVerification)

    val transcript = File.createTempFile("stainless-", ".out")
    try {
      val builder = new ProcessBuilder(command.asJava)
      builder.directory(directory)
      environment.foreach { case (name, value) => builder.environment().put(name, value) }
      builder.redirectErrorStream(true)
      builder.redirectOutput(transcript)

      val process = builder.start()
      process.getOutputStream.close()

      val finished = timeout match {
        case Some((seconds, _)) => process.waitFor((seconds * 1000).toLong, TimeUnit.MILLISECONDS)
        case None => process.waitFor(); true
      }

      if (!finished) {
        process.destroyForcibly()
        val (seconds, hint) = timeout.get
        Left(s"$tool did not finish within $seconds seconds; $hint")
      } else
        Right(Finished(process.exitValue(),
                       new String(Files.readAllBytes(transcript.toPath), "UTF-8")))
    } catch {
      case e: java.io.IOException => Left(s"could not run $tool: ${e.getMessage}")
      case e: InterruptedException =>
        Thread.currentThread().interrupt()
        Left(s"interrupted while waiting for $tool")
    } finally transcript.delete()
  }
}

/** Drives Daisy as an external process, sending FPCore and reading back a CSV. */
class DaisyRunner(ctx: inox.Context, settings: RoundoffSettings) extends RoundingAnalyzer {

  val name = "daisy"

  val emitter = FPCoreEmitter

  def analyze(queries: Seq[RoundingQuery]): Map[String, Either[String, BigDecimal]] =
    ExternalTool.find(settings.daisy) match {
      case None =>
        val why = ExternalTool.notFound("Daisy", settings.daisy, "daisy")
        RoundingAnalyzer.answers("Daisy", queries, Left(why))

      case Some(executable) =>
        // --precision is global to an invocation, so each precision is its own batch.
        queries.groupBy(_.precision).flatMap { case (precision, batch) =>
          RoundingAnalyzer.answers("Daisy", batch, invoke(executable, precision, batch))
        }
    }

  /** One Daisy run: a row per function, or why the run as a whole produced nothing. */
  private def invoke(executable: File, precision: FPPrecision, batch: Seq[RoundingQuery])
    : Either[String, Map[String, Either[String, BigDecimal]]] = {

    // Daisy's working directory, where its `lib/` and `output/` live.
    val directory = executable.getParentFile

    // Daisy writes into output/ without creating it, and appends if the file is already
    // there, so each run gets a fresh name in a directory we make ourselves.
    val stamp = java.util.UUID.randomUUID().toString.take(12)
    val source = File.createTempFile(s"stainless-$stamp-", ".fpcore")
    val csvName = s"stainless-$stamp.csv"
    val outputDir = new File(directory, "output")
    val csv = new File(outputDir, csvName)

    try {
      outputDir.mkdirs()
      Files.write(source.toPath, batch.map(_.source).mkString("\n").getBytes("UTF-8"))

      val command = Seq(
        executable.getAbsolutePath,
        "--treesitter",
        s"--precision=${precision.daisyName}",
        s"--results-csv=$csvName",
        "--no-stdout-print",
        source.getAbsolutePath
      )

      ExternalTool.run("Daisy", command, directory, ctx.reporter).flatMap { run =>
        // Daisy exits non-zero when any function failed, yet still reports the others, so
        // the results file and not the exit code says whether the run produced anything.
        if (csv.isFile) Right(parseCsv(Files.readAllLines(csv.toPath).asScala.toSeq))
        else Left(s"Daisy exited with code ${run.exitCode}" +
                  firstError(run.output).map(": " + _).getOrElse(""))
      }
    } finally {
      source.delete()
      csv.delete()
    }
  }

  /** The most informative line of a failed run. */
  private def firstError(output: String): Option[String] =
    output.linesIterator
      .map(stripAnsi)
      .find(l => l.contains("Fatal") || l.contains("Exception"))
      .map(_.trim)
      .filter(_.nonEmpty)

  private def stripAnsi(s: String): String = s.replaceAll("\\[[;\\d]*m", "")

  /** Reads rows of `name; abs error; rel error; range; time; failure`.
    *
    * The failure column comes last in every mode Daisy writes, and is absent altogether
    * in a version that gives up on the whole run rather than reporting one function.
    */
  private def parseCsv(lines: Seq[String]): Map[String, Either[String, BigDecimal]] =
    lines.flatMap { line =>
      val fields = line.split(";", -1).map(_.trim)
      val failure = if (fields.length >= 6) fields.last else ""

      if (fields.length < 2 || fields.head == "Function name") None
      else if (failure.nonEmpty) Some(fields.head -> Left(failure))
      else Some(fields.head -> Try(BigDecimal(fields(1))).toOption
        .toRight("Daisy reported no absolute error for this function"))
    }.toMap
}

/** Writes a floating-point expression as an FPCore definition. */
object FPCoreEmitter extends RoundingSourceEmitter {

  /** Writes `expr` as a self-contained FPCore definition called `name`. */
  def emit(name: String, label: String, expr: Expr, spec: InputSpec)(using Symbols)
    : Either[String, String] = {

    for {
      // Checked here because Daisy silently drops a function whose inputs are not all bounded.
      inputs <- spec.rangedInputs(expr)
      precondition <- bounds(inputs, spec)
      body <- convert(expr, inputs.map(_.id).toSet)
    } yield
      s"""|(FPCore $name (${inputs.map(v => symbol(v.id)).mkString(" ")})
          | :name "$label"
          | :pre (and ${precondition.mkString(" ")})
          | $body)
          |""".stripMargin
  }

  /** The precondition Daisy is given: what every input is known to lie between. */
  private def bounds(inputs: Seq[Variable], spec: InputSpec): Either[String, Seq[String]] =
    traverse(inputs) { v =>
      val (low, high) = spec.ranges(v.id)
      for {
        l <- Fraction.toFPCore(low)
        h <- Fraction.toFPCore(high)
      } yield s"(<= $l ${symbol(v.id)}) (<= ${symbol(v.id)} $h)"
    }

  private def convert(e: Expr, inScope: Set[Identifier]): Either[String, String] = {
    def binary(op: String, l: Expr, r: Expr): Either[String, String] =
      convert(l, inScope).flatMap(a => convert(r, inScope).map(b => s"($op $a $b)"))

    def rounded(op: String, mode: Expr, args: Expr*): Either[String, String] =
      roundsToNearestEven(mode, "Daisy assumes round-to-nearest-ties-to-even")
        .flatMap(_ => nary(op, args))

    def nary(op: String, args: Seq[Expr]): Either[String, String] =
      traverse(args)(convert(_, inScope)).map(as => s"($op ${as.mkString(" ")})")

    e match {
      case v: Variable =>
        if (inScope(v.id)) Right(symbol(v.id)) else Left(s"unbound variable '${v.id.name}'")

      case FPLit(d) => Fraction.toFPCore(d)

      case FPAdd(mode, l, r) => rounded("+", mode, l, r)
      case FPSub(mode, l, r) => rounded("-", mode, l, r)
      case FPMul(mode, l, r) => rounded("*", mode, l, r)
      case FPDiv(mode, l, r) => rounded("/", mode, l, r)
      case FPFMA(mode, a, b, c) => rounded("fma", mode, a, b, c)
      case FPUMinus(a) => convert(a, inScope).map(s => s"(- $s)")
      case TranscendentalFunctionCall(f, args) => nary(f.symbol, args)

      case Let(vd, value, body) =>
        convert(value, inScope).flatMap { v =>
          convert(body, inScope + vd.id).map(b => s"(let ([${symbol(vd.id)} $v]) $b)")
        }

      case IfExpr(condition, thenBranch, elseBranch) =>
        nary("if", Seq(condition, thenBranch, elseBranch))

      case FPLessThan(l, r)      => binary("<", l, r)
      case FPLessEquals(l, r)    => binary("<=", l, r)
      case FPGreaterThan(l, r)   => binary(">", l, r)
      case FPGreaterEquals(l, r) => binary(">=", l, r)
      case FPEquals(l, r)        => binary("==", l, r)

      case And(parts) => nary("and", parts)
      case Or(parts) => nary("or", parts)
      case Not(a) => convert(a, inScope).map(s => s"(not $s)")
      case BooleanLiteral(b) => Right(if (b) "TRUE" else "FALSE")

      case other => Left(s"no FPCore equivalent for ${other.getClass.getSimpleName}")
    }
  }
}

/** Runs FPTaylor on all queries at once, one task per query, and reads its summary.
  *
  * Tasks are independent, so each leaf keeps its own input ranges, and a task FPTaylor cannot
  * evaluate only fails that query.
  */
class FPTaylorRunner(ctx: inox.Context, settings: RoundoffSettings) extends RoundingAnalyzer {
  val name = "fptaylor"

  val emitter = FPTaylorEmitter

  def analyze(queries: Seq[RoundingQuery]): Map[String, Either[String, BigDecimal]] =
    ExternalTool.find(settings.fptaylor) match {
      case None =>
        val why = ExternalTool.notFound("FPTaylor", settings.fptaylor, "fptaylor")
        RoundingAnalyzer.answers("FPTaylor", queries, Left(why))

      case Some(executable) =>
        if (queries.isEmpty) Map.empty
        else RoundingAnalyzer.answers("FPTaylor", queries, invoke(executable, queries))
    }

  /** One FPTaylor run: a bound per task, or why the run as a whole produced nothing. */
  private def invoke(executable: File, queries: Seq[RoundingQuery])
    : Either[String, Map[String, Either[String, BigDecimal]]] = {

    // FPTaylor's own directory, where `default.cfg` and the optimizer's sources live. It is
    // both the working directory and `FPTAYLOR_BASE`, because the branch-and-bound optimizer
    // compiles each objective against sources under its own installation.
    val directory = executable.getParentFile

    val source = File.createTempFile("stainless-", ".fptaylor")
    // FPTaylor compiles each objective under its temporary directory and writes a log beside
    // it, both named after the input file, so two runs sharing one installation would write
    // over each other. Each run gets its own scratch directory.
    val scratch = Files.createTempDirectory("stainless-fptaylor-").toFile

    try {
      Files.write(source.toPath, queries.map(_.source).mkString("\n").getBytes("UTF-8"))

      val command = Seq(
        executable.getAbsolutePath,
        "--abs-error", "true",
        "--rel-error", "false",
        "--find-bounds", "false",
        "--print-hex-floats", "false",
        "--print-precision", "17",
        "--opt", settings.fptaylorOptimizer,
        "--opt-timeout", settings.fptaylorOptTimeout.toString,
        "--tmp-base-dir", new File(scratch, "tmp").getAbsolutePath,
        "--log-base-dir", new File(scratch, "log").getAbsolutePath,
        "--verbosity", "1",
        source.getAbsolutePath
      )

      ExternalTool.run("FPTaylor", command, directory, ctx.reporter,
                       environment = Map("FPTAYLOR_BASE" -> directory.getAbsolutePath),
                       timeout = Some((settings.fptaylorTimeout, "raise --fptaylor-timeout")))
        .flatMap { run =>
          val rows = parseSummary(run.output)
          // Nothing parsed means the whole run failed, so every query gets the run's error.
          if (rows.isEmpty) Left("FPTaylor reported no results" +
            firstError(run.output).map(": " + _).getOrElse(""))
          else Right(rows)
        }
    } finally {
      source.delete()
      remove(scratch)
    }
  }

  /** Deletes a scratch directory and whatever the run left in it. */
  private def remove(file: File): Unit = {
    Option(file.listFiles).foreach(_.foreach(remove))
    file.delete()
  }

  /** The most informative line of a failed run. */
  private def firstError(output: String): Option[String] =
    output.linesIterator
      .find(_.startsWith("**ERROR**"))
      .map(_.stripPrefix("**ERROR**:").trim)
      .filter(_.nonEmpty)

  /** Reads the summary: a `Problem: name` line, then the bounds for that task. A task that
    * failed has a `Problem` line but no bound.
    */
  private def parseSummary(output: String): Map[String, Either[String, BigDecimal]] = {
    val problem = "Problem: (.+)".r
    val absolute = raw"Absolute error \([^)]*\): *([0-9eE.+-]+).*".r

    val (rows, _) = output.linesIterator.map(_.trim).foldLeft(
      (Map.empty[String, Either[String, BigDecimal]], Option.empty[String])) {
      case ((found, _), problem(task)) =>
        (found + (task -> Left("FPTaylor computed no bound for this function")), Some(task))

      case ((found, Some(task)), absolute(value)) =>
        val bound = Try(BigDecimal(value)).toOption
          .toRight("FPTaylor printed an absolute error this reader could not parse")
        // Several bounds may be printed for one task; the tightest of them is still sound.
        val kept = (found.get(task).flatMap(_.toOption), bound.toOption) match {
          case (Some(had), Some(now)) => Right(had min now)
          case _ => bound
        }
        (found + (task -> kept), Some(task))

      case (state, _) => state
    }

    rows
  }
}

/** Writes a floating-point expression as an FPTaylor task.
  *
  * Each task is self-contained, so two leaves can use different ranges for the same input.
  *
  * Inputs are declared `real` rather than `float64`, so that FPTaylor answers the same question
  * as Daisy: an input is an exact real, rounded on entry. The two tools then agree to the digit
  * on `x * x` over `[1, 2]`; they differ only in how tightly they bound the error.
  */
object FPTaylorEmitter extends RoundingSourceEmitter {

  /** Functions the portable `simple_interval` build of FPTaylor cannot evaluate.
    *
    * The `INTERVAL` library that supports them needs x87 assembly and does not build on arm64.
    * Refusing them here gives a clear reason instead of a missing result.
    */
  private val unevaluable: Set[TranscendentalFunction] = {
    import TranscendentalFunction._
    Set(Sin, Cos, Tan, Asin, Acos, Atan)
  }

  def emit(name: String, label: String, expr: Expr, spec: InputSpec)(using Symbols)
    : Either[String, String] = {

    val definitions = mutable.ListBuffer.empty[(String, String)]
    val rounding = spec.precision.fptaylorRounding

    for {
      inputs <- spec.rangedInputs(expr)
      variables <- traverse(inputs)(declaration(_, spec))
      body <- convert(expr, inputs.map(_.id).toSet, definitions)
    } yield {
      val defined =
        if (definitions.isEmpty) ""
        else definitions.map { case (n, v) => s"  $n $rounding= $v;\n" }
          .mkString("\nDefinitions\n", "", "")

      s"""|{
          |// $label
          |Variables
          |${variables.map("  " + _ + ";").mkString("\n")}
          |$defined
          |Expressions
          |  $name $rounding= $body;
          |}
          |""".stripMargin
    }
  }

  /** An input declared with its range, as an exact rational interval. */
  private def declaration(v: Variable, spec: InputSpec): Either[String, String] = {
    val (low, high) = spec.ranges(v.id)
    for {
      l <- Fraction.toFPCore(low)
      h <- Fraction.toFPCore(high)
    } yield s"real ${symbol(v.id)} in [$l, $h]"
  }

  /** `e` in FPTaylor syntax. Each `let` binding is added to `definitions`, which is how
    * FPTaylor shares a subexpression; naming it adds no rounding.
    */
  private def convert(e: Expr, inScope: Set[Identifier],
                      definitions: mutable.ListBuffer[(String, String)])
    : Either[String, String] = {

    def binary(op: String, l: Expr, r: Expr): Either[String, String] =
      convert(l, inScope, definitions).flatMap(a =>
        convert(r, inScope, definitions).map(b => s"($a $op $b)"))

    /** The rounding operator applies to the whole task, so an operation only has to be
      * round-to-nearest, which is what `rnd32` and `rnd64` mean.
      */
    def rounded(mode: Expr)(build: => Either[String, String]): Either[String, String] =
      roundsToNearestEven(mode, "FPTaylor's rnd32 and rnd64 are round-to-nearest-ties-to-even")
        .flatMap(_ => build)

    e match {
      case v: Variable =>
        if (inScope(v.id)) Right(symbol(v.id)) else Left(s"unbound variable '${v.id.name}'")

      case FPLit(d) => Fraction.toFPCore(d).map(r => s"($r)")

      case FPAdd(mode, l, r) => rounded(mode)(binary("+", l, r))
      case FPSub(mode, l, r) => rounded(mode)(binary("-", l, r))
      case FPMul(mode, l, r) => rounded(mode)(binary("*", l, r))
      case FPDiv(mode, l, r) => rounded(mode)(binary("/", l, r))

      // FPTaylor reads `fma(a, b, c)` as the real `a * b + c` rounded once, as Stainless does.
      case FPFMA(mode, a, b, c) => rounded(mode)(
        traverse(Seq(a, b, c))(convert(_, inScope, definitions))
          .map(as => s"fma(${as.mkString(", ")})"))

      case FPUMinus(a) => convert(a, inScope, definitions).map(s => s"(-$s)")

      case TranscendentalFunctionCall(f, _) if unevaluable(f) =>
        Left(s"'${f.symbol}' is not implemented by the interval library this FPTaylor is " +
             "built against; rebuild it against INTERVAL to bound it")

      case TranscendentalFunctionCall(TranscendentalFunction.Pow, _) =>
        Left("FPTaylor has no power operation; write the exponent out as multiplications")

      case TranscendentalFunctionCall(f, args) =>
        traverse(args)(convert(_, inScope, definitions))
          .map(as => s"${f.symbol}(${as.mkString(", ")})")

      case Let(vd, value, body) =>
        convert(value, inScope, definitions).flatMap { v =>
          definitions += (symbol(vd.id) -> v)
          convert(body, inScope + vd.id, definitions)
        }

      case other => Left(s"no FPTaylor equivalent for ${other.getClass.getSimpleName}")
    }
  }
}
