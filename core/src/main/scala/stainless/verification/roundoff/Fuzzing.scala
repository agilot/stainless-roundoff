/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification
package roundoff

import trees._
import java.io.File
import scala.util.Try

/** Runs the fuzzer, which searches for large errors and so gives a lower bound on the
  * worst-case roundoff error.
  */
class FuzzRunner(ctx: inox.Context, settings: RoundoffSettings) {
  val name = "gavdos"

  val enabled: Boolean = settings.fuzzingEnabled

  /** Runs the fuzzer on a configuration and returns the largest error it found for each
    * function, or why it found none.
    */
  def run(conf: File): Either[String, Map[String, BigDecimal]] =
    ExternalTool.find(settings.fuzzer) match {
      case None => Left(ExternalTool.notFound("fuzzer", settings.fuzzer, "fuzz"))

      case Some(executable) =>
        val command = Seq(executable.getAbsolutePath, conf.getAbsolutePath)
        ExternalTool.run("the fuzzer", command, conf.getAbsoluteFile.getParentFile, ctx.reporter)
          .flatMap { run =>
            val observed = parse(run.output)
            // A run that found nothing has failed at something.
            if (observed.nonEmpty) Right(observed)
            else Left(s"the fuzzer exited with code ${run.exitCode} and reported no error" +
              lastLine(run.output).map(l => s": $l").getOrElse(""))
          }
    }

  /** The heading the fuzzer prints above each function's configurations. */
  private val heading = """(\S+): (?:divergences|rounding error)\s*$""".r.unanchored

  /** What one configuration's widest disagreement was reported as. */
  private val observation = """max abs error\s+(\S+)""".r.unanchored

  /** The widest error reported under each function, across all of its configurations.
    */
  def parse(output: String): Map[String, BigDecimal] =
    output.linesIterator.foldLeft((Option.empty[String], Map.empty[String, BigDecimal])) {
      case ((_, found), heading(function)) => (Some(function), found)

      case ((Some(function), found), observation(value)) =>
        val widest = Try(BigDecimal(value)).toOption.map { error =>
          function -> found.get(function).map(_ max error).getOrElse(error)
        }
        (Some(function), found ++ widest)

      case (state, _) => state
    }._2

  private def lastLine(output: String): Option[String] =
    output.linesIterator.map(_.trim).filter(_.nonEmpty).toSeq.lastOption
}

/** One function handed to the fuzzer, with its parameters and their ranges. */
case class FuzzSubject(name: String, parameters: Seq[String], domain: Seq[(Double, Double)])

/** Writes the fuzzer configuration: each function's input domain and the regions Ibex found. */
object FuzzConfEmitter {

  /** How many inputs the fuzzer tries in each configuration. */
  private val samples = 10000

  /** How far a certified box is widened before it is searched. */
  private val widening = 1000

  def emit(subjects: Seq[(FuzzSubject, Seq[Witness])]): String = {
    val entries = subjects.flatMap { case (subject, witnesses) => configurations(subject, witnesses) }
    val column = entries.map(_._1.length).maxOption.getOrElse(0)

    val settings = Seq(s"n = $samples", s"widen = $widening")
    val body = entries.map { case (key, value) => s"${key.padTo(column, ' ')} = $value" }

    (settings ++ Seq("") ++ body).mkString("", "\n", "\n")
  }

  private def configurations(subject: FuzzSubject, witnesses: Seq[Witness])
  : Seq[(String, String)] = {
    val domain = (s"${subject.name}.rounding.domain",
      subject.domain.map { case (low, high) => s"[$low, $high]" }.mkString(", "))

    // A divergence without a box has no region to search, so it is left out.
    val divergences = witnesses.collect {
      case w if w.box.isDefined =>
        (s"${subject.name}.divergence.${nameOf(w)}", box(w.box.get, subject.parameters))
    }

    domain +: divergences
  }

  private def nameOf(w: Witness): String = {
    val objective = w.maximizing.map(if (_) "max" else "min").getOrElse("any")
    s"g${w.site.guard}_u${w.site.untaken}_t${w.site.taken}_$objective"
  }

  /** One interval per parameter, in declaration order. A missing bound is written `*`, which
    * the fuzzer replaces by the bound of the domain.
    */
  private def box(bounds: Box, parameters: Seq[String]): String =
    parameters.map { parameter =>
      bounds.get(parameter) match {
        case Some((low, high)) => s"[${end(low)}, ${end(high)}]"
        case None => "[*, *]"
      }
    }.mkString(", ")

  private def end(d: Option[BigDecimal]): String = d.map(_.toString).getOrElse("*")
}

/** Writes a preprocessed function as a Scala program for the fuzzer.
  *
  * It prints the body the analysis used (calls inlined, conditionals moved to the top), not the
  * source, so that the fuzzer and the analysis look at the same computation.
  */
object FuzzProgramEmitter {

  /** The program for `fd`, called `name`, or why none could be written.
    *
    * @param values      the flattened parameters, which the program takes
    * @param assumptions the precondition and the invariants, over those parameters
    */
  def emit(fd: FunDef, name: String, spec: InputSpec, body: Expr,
           values: Seq[ValDef], assumptions: Expr)(using Symbols): Either[String, String] = {

    val precondition = Option(assumptions).filterNot(_ == BooleanLiteral(true))

    val doublesThroughout = (fd.returnType +: values.map(_.tpe))
      .forall(tpe => FPPrecision.fromType(tpe).contains(FPPrecision.Binary64))

    // The first reason the fuzzer cannot be given this function, where there is one.
    val refused =
      Option.when(spec.precision != FPPrecision.Binary64)(
          "the fuzzer runs subject programs in double precision")
        .orElse(Option.when(!doublesThroughout)("the fuzzer passes and returns doubles only"))
        .orElse(unsupported(body))
        .orElse(precondition.flatMap(unsupported))

    refused.toLeft {
      val parameters = values.map(show).mkString(", ")
      val block = withLiteralCasts(precondition.map(Require(_, body)).getOrElse(body))

      s"""|@fuzz
          |def $name($parameters): ${show(fd.returnType)} = {
          |${indented(show(block))}
          |}
          |""".stripMargin
    }
  }

  /** `e` with each exact integer-to-double cast replaced by a double literal.
    *
    * `x <= 10` for a `Double` `x` arrives as `x <= 10.toDouble`. The fuzzer's plugin turns
    * `Double` values and literals into high-precision numbers but leaves the cast a `Double`,
    * so the program would not compile (`required: shadow.MPFR`). A literal is converted.
    */
  private def withLiteralCasts(e: Expr)(using Symbols): Expr = exprOps.postMap {
    case ToDouble(IntLit(n)) if n.abs <= BigInt(2).pow(53) => Some(Float64Literal(n.toDouble))
    case _ => None
  }(e)

  /** What the fuzzer's high-precision build cannot handle: its plugin does not convert calls,
    * so a call would receive a high-precision number where it expects a `Double`.
    */
  private def unsupported(e: Expr)(using Symbols): Option[String] =
    exprOps.collect[String] {
      case TranscendentalFunctionCall(f, _) => Set(s"'${f.symbol}'")
      case FPFMA(_, _, _, _) => Set("a fused multiply-add")
      case _ => Set.empty
    }(e).headOption.map(_ + " has no counterpart in the fuzzer's MPFR build")

  private def indented(block: String): String =
    block.linesIterator.map(line => if (line.isEmpty) line else "  " + line).mkString("\n")

  private def show(tree: Tree): String = {
    val opts = PrinterOptions()
    val ctx = PrinterContext(tree, Nil, opts.baseIndent, opts)
    FuzzPrinter.pp(tree)(using ctx)
    ctx.sb.toString
  }

  /** The Scala printer, with a unique name for every binding. Inlining can put two bindings
    * with the same name in one block, which Scala rejects as a redefinition.
    */
  private object FuzzPrinter extends ast.ScalaPrinter {
    val trees: stainless.trees.type = stainless.trees
    import trees._

    override def ppBody(tree: Tree)(using ctx: PrinterContext): Unit = tree match {
      case v: Variable => p"${scalaName(v.id)}"
      case vd: ValDef => p"${scalaName(vd.id)}: ${vd.tpe}"

      // The tree printer writes floating-point equality as `===`, which is not Scala.
      case FPEquals(lhs, rhs) => optP { p"$lhs == $rhs" }

      case _ => super.ppBody(tree)
    }

    private def scalaName(id: Identifier): String = {
      val letters = id.name.map(c => if (c.isLetterOrDigit || c == '_') c else '_')
      val start = if (letters.headOption.exists(c => c.isLetter || c == '_')) letters else s"v$letters"
      s"${start}_${id.id}"
    }
  }
}

/** Hands the `@fuzz` functions to the fuzzer and reads back a lower bound for each.
  *
  * @param functions       the `@roundoff` functions, in declaration order
  * @param decompositionOf the decomposition of a function's whole result
  * @param witnesses       the divergence regions Ibex found, read once the search is over
  */
private[roundoff] final class FuzzDriver(
  ctx: inox.Context,
  settings: RoundoffSettings,
  fuzzer: FuzzRunner,
  functions: Seq[FunDef],
  decompositionOf: FunDef => Either[String, RoundoffErrorDecomposition],
  witnesses: () => Seq[Witness],
  timers: inox.utils.TimerStorage
)(using symbols: Symbols) {

  import ctx.reporter

  private given PrinterOptions = PrinterOptions.fromSymbols(symbols, ctx)

  /** Runs the fuzzer over every subject, once. */
  def run(): Unit = { val _ = result }

  /** The error the fuzzer found for `fd`, if it was run on it. */
  def lowerBound(fd: FunDef): Option[BigDecimal] =
    if (!fuzzer.enabled || subjects.isEmpty) None
    else
      result.flatMap(_.get(fd.id.name).toRight("the fuzzer reported nothing for it")) match {
        case Right(error) => Some(error)
        case Left(why) =>
          reporter.warning(fd.getPos, s"No fuzzed error for ${fd.id.asString}: $why")
          None
      }

  /** Writes the subject programs and the fuzzer configuration beside `base`, if there are any
    * subjects. The fuzzer finds its program from the configuration's name, so both share it.
    */
  def writeInputs(base: java.io.File): Unit =
    if (subjects.nonEmpty) { val _ = writeSubjects(base) }

  /** The `@fuzz` functions, each with the program the fuzzer runs for it. */
  private lazy val subjects: Seq[(FuzzSubject, String)] =
    functions.filter(_.flags.contains(Fuzz)).foldLeft(Seq.empty[(FuzzSubject, String)]) {
      (written, fd) =>
        subjectOf(fd, written.map(_._1.name)) match {
          case Right(subject) => written :+ subject
          case Left(why) =>
            reporter.warning(fd.getPos, s"No fuzzer program for ${fd.id.asString}: $why")
            written
        }
    }

  private def subjectOf(fd: FunDef, taken: Seq[String]): Either[String, (FuzzSubject, String)] = {
    val name = fd.id.name

    if (taken.contains(name))
      Left(s"another annotated function is called '$name', and a witness names only " +
           "the function it belongs to, so the two cannot be told apart")
    else if (AccessPath.isCompound(fd.returnType))
      Left("the fuzzer returns one double, and this function's result holds several " +
           "numbers; the analysis answers about each of them but the fuzzer is not " +
           "asked about any")
    else
      for {
        parts <- decompositionOf(fd)
        values = parts.flattening.parameters
        domain <- domainOf(parts)
        source <- FuzzProgramEmitter.emit(fd, name, parts.spec, parts.body, values,
                                          InputRanges.assumptions(fd, parts.flattening))
      } yield (FuzzSubject(name, values.map(_.id.name), domain), source)
  }

  /** What the precondition says each input lies between, in the order they are declared. */
  private def domainOf(parts: RoundoffErrorDecomposition): Either[String, Seq[(Double, Double)]] =
    traverse(parts.flattening.parameters)(p => parts.spec.ranges.get(p.id).toRight(
      s"no range in the precondition for '${p.id.name}'"))

  private lazy val result: Either[String, Map[String, BigDecimal]] =
    if (!fuzzer.enabled || subjects.isEmpty) Left("the fuzzer was not run")
    else
      scala.util.Try(
        timers.fuzzing.run(fuzzer.run(writeSubjects(settings.witnessFile.getOrElse(scratch))))
      ) match {
        case scala.util.Success(errors) => errors
        case scala.util.Failure(e) => Left(s"the fuzzer could not be run: ${e.getMessage}")
      }

  /** Writes the program and the configuration, and returns the configuration. */
  private def writeSubjects(base: java.io.File): java.io.File = {
    val found = witnesses().groupBy(_.function)
    val conf = sibling(base, "conf")

    write(sibling(base, "scala"), subjects.map(_._2).mkString("\n"))
    write(conf, FuzzConfEmitter.emit(subjects.map {
      case (subject, _) => subject -> found.getOrElse(subject.name, Seq.empty)
    }))
    conf
  }

  /** Where the fuzzer's input goes when no witness file was asked for. */
  private lazy val scratch: java.io.File = {
    val directory = java.nio.file.Files.createTempDirectory("stainless-roundoff").toFile
    directory.deleteOnExit()
    new java.io.File(directory, "roundoff.json")
  }

  private def sibling(file: java.io.File, extension: String): java.io.File = {
    val name = file.getName
    val base = name.lastIndexOf('.') match { case -1 => name; case dot => name.take(dot) }
    new java.io.File(file.getParentFile, s"$base.$extension")
  }

  private def write(file: java.io.File, content: String): Unit = {
    val out = new java.io.FileWriter(file)
    try out.write(content) finally out.close()
  }
}
