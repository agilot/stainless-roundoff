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

/* The external tools that bound the rounding error of straight-line code
 */

/** Straight-line expression to analyse. */
case class RoundingQuery(name: String, precision: FPPrecision, source: String)

/** Writes a straight-line expression in analyzers' input language.
  */
trait RoundingSourceEmitter {
  def emit(name: String, label: String, expr: Expr, spec: InputSpec)(using Symbols)
    : Either[String, String]

  /** The name an input goes by in the analyzer's input language, unique across the program. */
  protected def symbol(id: Identifier): String = s"v_${id.globalId}"
}

/** Types of errors */
enum AnalyzerFailure {
  case MayOverflow(reported: String)
  case Failed(why: String)
}

trait RoundingAnalyzer {
  val name: String
  val emitter: RoundingSourceEmitter
  def analyze(queries: Seq[RoundingQuery], seconds: Double): Map[String, Either[AnalyzerFailure, BigDecimal]]
}

object RoundingAnalyzer {

  /** What the tool reported for each query.
    */
  def answerPerQuery(tool: String, queries: Seq[RoundingQuery],
                     reported: Either[String, Map[String, Either[AnalyzerFailure, BigDecimal]]])
    : Map[String, Either[AnalyzerFailure, BigDecimal]] =
    queries.map { q =>
      q.name -> reported.left.map(AnalyzerFailure.Failed(_)).flatMap(
        _.getOrElse(q.name, Left(AnalyzerFailure.Failed(s"$tool reported nothing for this function"))))
    }.toMap
}

/** Finds and runs the external tools: Daisy, FPTaylor and the fuzzer. */
private[roundoff] object ExternalTool {

  case class ProcessResult(exitCode: Int, output: String)

  /** The executable, as given or as found on `PATH`. */
  def findExecutable(configured: String): Option[File] = {
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

  def notFoundMessage(tool: String, configured: String, option: String): String =
    s"$tool executable '$configured' not found; set --$option=<path> or put it on your PATH"

  /** Runs `command` in `directory`  */
  def run(tool: String, command: Seq[String], directory: File, reporter: inox.Reporter,
          environment: Map[String, String] = Map.empty,
          timeout: Option[Double] = None): Either[String, ProcessResult] = {
    reporter.debug(s"Invoking ${command.mkString(" ")}")(using DebugSectionVerification)

    val outputFile = File.createTempFile("stainless-", ".out")
    try {
      val builder = new ProcessBuilder(command.asJava)
      builder.directory(directory)
      environment.foreach { case (name, value) => builder.environment().put(name, value) }
      builder.redirectErrorStream(true)
      builder.redirectOutput(outputFile)

      val process = builder.start()
      process.getOutputStream.close()

      val finished = timeout match {
        case Some(seconds) => process.waitFor((seconds.max(0.0) * 1000).toLong, TimeUnit.MILLISECONDS)
        case None => process.waitFor(); true
      }

      if (!finished) {
        // A launcher script that does not `exec` leaves the tool running as its child, so the
        // children are stopped first, while they still belong to it.
        process.descendants().forEach(child => { child.destroyForcibly(); () })
        process.destroyForcibly()
        throw new OutOfTime(
          f"$tool did not finish within the ${timeout.get}%.3fs left")
      } else
        Right(ProcessResult(process.exitValue(),
                            new String(Files.readAllBytes(outputFile.toPath), "UTF-8")))
    } catch {
      case e: java.io.IOException => Left(s"could not run $tool: ${e.getMessage}")
      case e: InterruptedException =>
        Thread.currentThread().interrupt()
        Left(s"interrupted while waiting for $tool")
    } finally outputFile.delete()
  }
}

/** Sends FPCore to Daisy and reads back a CSV. */
class DaisyRunner(ctx: inox.Context, settings: RoundoffSettings) extends RoundingAnalyzer {

  val name = "daisy"

  val emitter = FPCoreEmitter

  def analyze(queries: Seq[RoundingQuery], seconds: Double): Map[String, Either[AnalyzerFailure, BigDecimal]] =
    ExternalTool.findExecutable(settings.daisy) match {
      case None =>
        val why = ExternalTool.notFoundMessage("Daisy", settings.daisy, "daisy")
        RoundingAnalyzer.answerPerQuery("Daisy", queries, Left(why))

      case Some(executable) =>
        val time = new TimeLimit(seconds)
        // --precision is global to an invocation, so each precision is its own batch.
        queries.groupBy(_.precision).flatMap { case (precision, batch) =>
          RoundingAnalyzer.answerPerQuery("Daisy", batch,
                                          runDaisy(executable, precision, batch, time.secondsLeft))
        }
    }

  /** One Daisy run: a row per function */
  private def runDaisy(executable: File, precision: FPPrecision, batch: Seq[RoundingQuery],
                       seconds: Double): Either[String, Map[String, Either[AnalyzerFailure, BigDecimal]]] = {

    // Daisy's working directory, where its `lib/` and `output/` live.
    val directory = executable.getParentFile

    // Daisy writes into output/ without creating it, and appends to a file that is already
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

      ExternalTool.run("Daisy", command, directory, ctx.reporter, timeout = Some(seconds)).flatMap { run =>
        // Daisy exits non-zero when any function failed, yet still reports the others, so the
        // results file, not the exit code, says whether the run produced anything.
        if (csv.isFile) Right(DaisyRunner.parseCsv(Files.readAllLines(csv.toPath).asScala.toSeq))
        else Left(s"Daisy exited with code ${run.exitCode}" +
                  mostInformativeLine(run.output).map(": " + _).getOrElse(""))
      }
    } finally {
      source.delete()
      csv.delete()
    }
  }

  /** The most informative line of a failed run. */
  private def mostInformativeLine(output: String): Option[String] =
    output.linesIterator
      .map(stripAnsi)
      .find(l => l.contains("Fatal") || l.contains("Exception"))
      .map(_.trim)
      .filter(_.nonEmpty)

  private def stripAnsi(s: String): String = s.replaceAll("\u001b\\[[;\\d]*m", "")
}

object DaisyRunner {

  /** Reads rows of `name; abs error; rel error; range; time; failure`. The failure column comes
    * last in every mode Daisy writes, and is absent in a version that gives up on the whole run
    * rather than on one function.
    */
  private[roundoff] def parseCsv(lines: Seq[String]): Map[String, Either[AnalyzerFailure, BigDecimal]] =
    lines.flatMap { line =>
      val fields = line.split(";", -1).map(_.trim)
      val failureColumn = if (fields.length >= 6) fields.last else ""

      if (fields.length < 2 || fields.head == "Function name") None
      else if (failureColumn.nonEmpty) Some(fields.head -> Left(classifiedFailure(failureColumn)))
      else Some(fields.head -> Try(BigDecimal(fields(1))).toOption
        .toRight(AnalyzerFailure.Failed("Daisy reported no absolute error for this function")))
    }.toMap
  
  private def classifiedFailure(message: String): AnalyzerFailure =
    if (message.startsWith("OverflowException") ||
        message.contains("cannot convert +infinity") || message.contains("cannot convert -infinity"))
      AnalyzerFailure.MayOverflow(message)
    else AnalyzerFailure.Failed(message)
}

/** Writes a floating-point expression as a self-contained FPCore definition. */
object FPCoreEmitter extends RoundingSourceEmitter {

  def emit(name: String, label: String, expr: Expr, spec: InputSpec)(using Symbols)
    : Either[String, String] = {

    for {
      // Checked here because Daisy silently drops a function whose inputs are not all bounded.
      inputs <- spec.rangedInputs(expr)
      precondition <- rangeConditions(inputs, spec)
      body <- toFPCore(expr, inputs.map(_.id).toSet)
    } yield
      s"""|(FPCore $name (${inputs.map(parameterDeclaration).mkString(" ")})
          | :name "$label"
          | :pre (and ${precondition.mkString(" ")})
          | $body)
          |""".stripMargin
  }

  /** An integer input is marked, so that Daisy does not round it. */
  private def parameterDeclaration(v: Variable): String =
    if (isIntegral(v)) s"(! :precision integer ${symbol(v.id)})" else symbol(v.id)

  /** `e`, an integer, in FPCore integer arithmetic, without the marking. */
  private def integerToFPCore(e: Expr): Either[String, String] = {
    def prefixOperation(op: String, args: Expr*) =
      traverse(args)(integerToFPCore).map(as => s"($op ${as.mkString(" ")})")
    e match {
      case Int32Literal(n) => Right(n.toString)
      case Int64Literal(n) => Right(n.toString)
      case BVWideningCast(inner, _) => integerToFPCore(inner)
      case v: Variable => Right(symbol(v.id))
      case Plus(l, r) => prefixOperation("+", l, r)
      case Minus(l, r) => prefixOperation("-", l, r)
      case Times(l, r) => prefixOperation("*", l, r)
      case UMinus(a) => prefixOperation("-", a)
      case Let(vd, value, body) =>
        for (v <- integerToFPCore(value); b <- integerToFPCore(body))
        yield s"(let ([${symbol(vd.id)} $v]) $b)"
      case other => Left(s"no FPCore integer equivalent for '$other'")
    }
  }

  /** The range of every input, as Daisy's precondition. */
  private def rangeConditions(inputs: Seq[Variable], spec: InputSpec): Either[String, Seq[String]] =
    traverse(inputs) { v =>
      val (low, high) = spec.ranges(v.id)
      for {
        l <- Fraction.toFPCore(low)
        h <- Fraction.toFPCore(high)
      } yield s"(<= $l ${symbol(v.id)}) (<= ${symbol(v.id)} $h)"
    }

  /** `e`, a straight-line leaf or a side of a guard, in FPCore. */
  private def toFPCore(e: Expr, inScope: Set[Identifier]): Either[String, String] = {
    def prefixOperation(op: String, args: Seq[Expr]): Either[String, String] =
      traverse(args)(toFPCore(_, inScope)).map(as => s"($op ${as.mkString(" ")})")

    e match {
      // Daisy reads integers as reals.
      case FPCast(_, _, _, inner) if isIntegral(inner) => toFPCore(inner, inScope)
      case _ if isIntegral(e) =>
        exprOps.variablesOf(e).find(v => !inScope(v.id))
          .map(v => Left(s"unbound variable '${v.id.name}'"))
          .getOrElse(integerToFPCore(e).map(i => s"(! :precision integer $i)"))

      case v: Variable =>
        if (inScope(v.id)) Right(symbol(v.id)) else Left(s"unbound variable '${v.id.name}'")

      case FPLit(d) => Fraction.toFPCore(d)

      // The preprocessor only lets round-to-nearest-ties-to-even through, which Daisy assumes.
      case FPAdd(_, l, r) => prefixOperation("+", Seq(l, r))
      case FPSub(_, l, r) => prefixOperation("-", Seq(l, r))
      case FPMul(_, l, r) => prefixOperation("*", Seq(l, r))
      case FPDiv(_, l, r) => prefixOperation("/", Seq(l, r))
      case FPFMA(_, a, b, c) => prefixOperation("fma", Seq(a, b, c))
      case FPUMinus(a) => toFPCore(a, inScope).map(s => s"(- $s)")
      case TranscendentalFunctionCall(f, args) => prefixOperation(f.symbol, args)

      case Let(vd, value, body) =>
        toFPCore(value, inScope).flatMap { v =>
          toFPCore(body, inScope + vd.id).map(b => s"(let ([${symbol(vd.id)} $v]) $b)")
        }

      case other => Left(s"no FPCore equivalent for '$other'")
    }
  }
}

/** Runs FPTaylor on all queries at once, one task per query, and reads its summary. Tasks are
  * independent, so each leaf keeps its own input ranges, and a task FPTaylor cannot evaluate
  * only fails that query.
  */
class FPTaylorRunner(ctx: inox.Context, settings: RoundoffSettings) extends RoundingAnalyzer {
  val name = "fptaylor"

  val emitter = FPTaylorEmitter

  def analyze(queries: Seq[RoundingQuery], seconds: Double): Map[String, Either[AnalyzerFailure, BigDecimal]] =
    ExternalTool.findExecutable(settings.fptaylor) match {
      case None =>
        val why = ExternalTool.notFoundMessage("FPTaylor", settings.fptaylor, "fptaylor")
        RoundingAnalyzer.answerPerQuery("FPTaylor", queries, Left(why))

      case Some(executable) =>
        RoundingAnalyzer.answerPerQuery("FPTaylor", queries, runFPTaylor(executable, queries, seconds))
    }

  /** One FPTaylor run: a bound per task, or why the run as a whole produced nothing. */
  private def runFPTaylor(executable: File, queries: Seq[RoundingQuery], seconds: Double)
    : Either[String, Map[String, Either[AnalyzerFailure, BigDecimal]]] = {

    // FPTaylor's own directory, where `default.cfg` and the optimizer's sources live. It is
    // both the working directory and `FPTAYLOR_BASE`, because the branch-and-bound optimizer
    // compiles each objective against sources under its own installation.
    val directory = executable.getParentFile

    val source = File.createTempFile("stainless-", ".fptaylor")
    // FPTaylor names its temporary files and its log after the input file, so two runs sharing
    // one installation would write over each other: each run gets its own directory.
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
                       timeout = Some(seconds))
        .flatMap(run => FPTaylorRunner.parseOutput(run.output))
    } finally {
      source.delete()
      deleteRecursively(scratch)
    }
  }

  private def deleteRecursively(file: File): Unit = {
    Option(file.listFiles).foreach(_.foreach(deleteRecursively))
    file.delete()
  }
}

object FPTaylorRunner {

  /** A bound per task, or why the run as a whole produced nothing. A task without a bound
    * gets the error FPTaylor printed while processing it, such as a square root of a range
    * that reaches below zero.
    */
  private[roundoff] def parseOutput(output: String)
    : Either[String, Map[String, Either[AnalyzerFailure, BigDecimal]]] = {

    val bounds = boundsByTask(output)
    val errors = errorMessagesByTask(output)
    val errorOfTask = errors.collect { case (Some(task), message) => task -> message }
      .distinctBy(_._1).toMap

    if (bounds.isEmpty)
      Left("FPTaylor reported no results" + errors.headOption.map((_, m) => s": $m").getOrElse(""))
    else Right(bounds.map { (task, bound) =>
      task -> bound.left.map(why => AnalyzerFailure.Failed(errorOfTask.getOrElse(task, why)))
    })
  }

  /** Each `**ERROR**` message, with the task FPTaylor was processing when it printed it. Some
    * messages start on the line after the marker; a potential exception then ends that line
    * with ` at:`, and the whole expression follows.
    */
  private def errorMessagesByTask(output: String): Seq[(Option[String], String)] = {
    val processingLine = "Processing: (.+)".r
    val errorMarker = "**ERROR**"
    val lines = output.linesIterator.map(_.trim).toIndexedSeq

    val (messages, _) = lines.zipWithIndex.foldLeft(
      (Seq.empty[(Option[String], String)], Option.empty[String])) {
      case ((found, _), (processingLine(task), _)) => (found, Some(task))

      case ((found, task), (line, i)) if line.startsWith(errorMarker) =>
        val message = Some(line.stripPrefix(errorMarker).stripPrefix(":").trim).filter(_.nonEmpty)
          .orElse(lines.lift(i + 1).filter(_.nonEmpty))
          .map(_.stripSuffix(" at:"))
        (found ++ message.map(task -> _), task)

      case (state, _) => state
    }

    messages
  }

  /** Reads the summary: a `Problem: name` line, then the bounds for that task. A task that
    * failed has a `Problem` line but no bound.
    */
  private def boundsByTask(output: String): Map[String, Either[String, BigDecimal]] = {
    val problemLine = "Problem: (.+)".r
    val absoluteErrorLine = raw"Absolute error \([^)]*\): *([0-9eE.+-]+).*".r

    val (bounds, _) = output.linesIterator.map(_.trim).foldLeft(
      (Map.empty[String, Either[String, BigDecimal]], Option.empty[String])) {
      case ((found, _), problemLine(task)) =>
        (found + (task -> Left("FPTaylor computed no bound for this function")), Some(task))

      case ((found, Some(task)), absoluteErrorLine(value)) =>
        val bound = Try(BigDecimal(value)).toOption
          .toRight("FPTaylor printed an absolute error this reader could not parse")
        // Several bounds may be printed for one task; the tightest is still sound.
        val tightest = (found.get(task).flatMap(_.toOption), bound.toOption) match {
          case (Some(had), Some(now)) => Right(had min now)
          case _ => bound
        }
        (found + (task -> tightest), Some(task))

      case (state, _) => state
    }

    bounds
  }
}

/** Writes a floating-point expression as a self-contained FPTaylor task, so that two leaves can
  * use different ranges for the same input. Inputs are exact reals, rounded on entry.
  */
object FPTaylorEmitter extends RoundingSourceEmitter {

  /** Functions the portable `simple_interval` build of FPTaylor cannot evaluate: the `INTERVAL`
    * library that supports them needs x87 assembly and does not build on arm64.
    */
  private val unsupportedByIntervalLibrary: Set[TranscendentalFunction] = {
    import TranscendentalFunction._
    Set(Sin, Cos, Tan, Asin, Acos, Atan)
  }

  def emit(name: String, label: String, expr: Expr, spec: InputSpec)(using Symbols)
    : Either[String, String] = {

    val definitions = mutable.ListBuffer.empty[(String, String)]
    val roundingOperator = spec.precision.fptaylorRounding

    for {
      inputs <- spec.rangedInputs(expr)
      declarations <- traverse(inputs)(variableDeclaration(_, spec))
      body <- toFPTaylor(expr, inputs.map(_.id).toSet, definitions)
    } yield {
      val definitionsSection =
        if (definitions.isEmpty) ""
        else definitions.map { case (n, v) => s"  $n $roundingOperator= $v;\n" }
          .mkString("\nDefinitions\n", "", "")

      s"""|{
          |// $label
          |Variables
          |${declarations.map("  " + _ + ";").mkString("\n")}
          |$definitionsSection
          |Expressions
          |  $name $roundingOperator= $body;
          |}
          |""".stripMargin
    }
  }

  /** An input declared with its range, as an exact rational interval. */
  private def variableDeclaration(v: Variable, spec: InputSpec): Either[String, String] = {
    val (low, high) = spec.ranges(v.id)
    for {
      l <- Fraction.toFPCore(low)
      h <- Fraction.toFPCore(high)
    } yield s"real ${symbol(v.id)} in [$l, $h]"
  }

  /** `e` in FPTaylor syntax. Each `let` binding is added to `definitions`, which is how FPTaylor
    * shares a subexpression; naming it adds no rounding.
    */
  private def toFPTaylor(e: Expr, inScope: Set[Identifier],
                         definitions: mutable.ListBuffer[(String, String)])
    : Either[String, String] = {

    def infixOperation(op: String, l: Expr, r: Expr): Either[String, String] =
      toFPTaylor(l, inScope, definitions).flatMap(a =>
        toFPTaylor(r, inScope, definitions).map(b => s"($a $op $b)"))

    val noIntegersMessage =
      "FPTaylor reads no integers other than constants; --roundoff-analyzer=daisy handles them"

    e match {
      case _ if isIntegral(e) => Left(noIntegersMessage)

      case v: Variable =>
        if (inScope(v.id)) Right(symbol(v.id)) else Left(s"unbound variable '${v.id.name}'")

      // Also an integer constant converted exactly, such as the `2` of `x * 2`.
      case FPLit(d) => Fraction.toFPCore(d).map(r => s"($r)")
      case FPCast(_, _, _, inner) if isIntegral(inner) => Left(noIntegersMessage)

      // The preprocessor only lets round-to-nearest-ties-to-even through, which is what the
      // task's `rnd32` and `rnd64` mean.
      case FPAdd(_, l, r) => infixOperation("+", l, r)
      case FPSub(_, l, r) => infixOperation("-", l, r)
      case FPMul(_, l, r) => infixOperation("*", l, r)
      case FPDiv(_, l, r) => infixOperation("/", l, r)

      // FPTaylor reads `fma(a, b, c)` as the real `a * b + c` rounded once, as Stainless does.
      case FPFMA(_, a, b, c) =>
        traverse(Seq(a, b, c))(toFPTaylor(_, inScope, definitions))
          .map(as => s"fma(${as.mkString(", ")})")

      case FPUMinus(a) => toFPTaylor(a, inScope, definitions).map(s => s"(-$s)")

      case TranscendentalFunctionCall(f, _) if unsupportedByIntervalLibrary(f) =>
        Left(s"'${f.symbol}' is not implemented by the interval library this FPTaylor is " +
             "built against; rebuild it against INTERVAL to bound it")

      case TranscendentalFunctionCall(TranscendentalFunction.Pow, _) =>
        Left("FPTaylor has no power operation; write the exponent out as multiplications")

      case TranscendentalFunctionCall(f, args) =>
        traverse(args)(toFPTaylor(_, inScope, definitions))
          .map(as => s"${f.symbol}(${as.mkString(", ")})")

      // Substituted, so that its conversion reads as a literal.
      case Let(vd, constant @ (Int32Literal(_) | Int64Literal(_)), body) =>
        toFPTaylor(exprOps.replaceFromSymbols(Map(vd -> constant), body), inScope, definitions)

      case Let(vd, value, body) =>
        toFPTaylor(value, inScope, definitions).flatMap { v =>
          definitions += (symbol(vd.id) -> v)
          toFPTaylor(body, inScope + vd.id, definitions)
        }

      case other => Left(s"no FPTaylor equivalent for '$other'")
    }
  }
}
