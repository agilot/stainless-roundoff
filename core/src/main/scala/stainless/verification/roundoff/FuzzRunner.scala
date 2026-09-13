/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification
package roundoff

import trees._
import java.io.File
import scala.jdk.CollectionConverters._
import scala.util.Try

/** Drives a fuzzer as an external process to compute a lower bound for the worst-case
 * roundoff error.
  */
class FuzzRunner(ctx: inox.Context) {
  import ctx.reporter

  val name = "gavdos"

  private val configured = ctx.options.findOptionOrDefault(optFuzz)

  val enabled: Boolean = configured.nonEmpty

  private lazy val executable: Option[File] = findExecutable(configured)

  /** Runs the fuzzer of each function using a given configuration path and outputs the result
   * of the fuzzer for each function or an error.
   */
  def run(conf: File): Either[String, Map[String, BigDecimal]] =
    executable match {
      case None =>
        Left(s"fuzzer executable '$configured' not found; " +
          "set --fuzz=<path> or put it on your PATH")

      case Some(exe) =>
        val cmd = List(exe.getAbsolutePath, conf.getAbsolutePath)
        reporter.debug(s"Invoking ${cmd.mkString(" ")}")(using DebugSectionVerification)

        try {
          val pb = new ProcessBuilder(cmd.asJava)
          pb.directory(conf.getAbsoluteFile.getParentFile)
          pb.redirectErrorStream(true)

          val proc = pb.start()
          proc.getOutputStream.close()
          val output = new String(proc.getInputStream.readAllBytes(), "UTF-8")
          val exit = proc.waitFor()

          val observed = parse(output)
          // A run that found nothing has failed at something.
          if (observed.nonEmpty) Right(observed)
          else Left(s"the fuzzer exited with code $exit and reported no error" +
            lastLine(output).fold("")(l => s": $l"))
        } catch {
          case e: java.io.IOException => Left(s"could not run the fuzzer: ${e.getMessage}")
          case e: InterruptedException =>
            Thread.currentThread().interrupt()
            Left("interrupted while waiting for the fuzzer")
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
          function -> found.get(function).fold(error)(_ max error)
        }
        (Some(function), found ++ widest)

      case (state, _) => state
    }._2

  private def lastLine(output: String): Option[String] =
    output.linesIterator.map(_.trim).filter(_.nonEmpty).toSeq.lastOption
}

/** One function handed to the fuzzer, with its parameters and their ranges */
case class FuzzSubject(name: String, parameters: Seq[String], domain: Seq[(Double, Double)])

/** Writes the intervals output by the static analysis as a configuration the fuzzer can search. */
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

    // Only a bounded divergence carries a box, and only the merged scheme is read back for
    // now, so anything else is left out rather than named without a region to search.
    val divergences = witnesses.collect {
      case w if w.scheme == DiscontinuityMode.Merged && w.box.isDefined =>
        (s"${subject.name}.divergence.${nameOf(w)}", box(w.box.get, subject.parameters))
    }

    domain +: divergences
  }

  private def nameOf(w: Witness): String = {
    val objective = w.maximizing.map(if (_) "max" else "min").getOrElse("any")
    val taken = w.against.map(against => s"_t$against").getOrElse("")
    s"g${w.region}_u${w.other}${taken}_$objective"
  }

  /** One interval per parameter, in declaration order.
   *
   * A parameter the query never narrowed, and an end it left open, are written `*`, which
   * the fuzzer reads as the matching end of the domain.
   */
  private def box(bounds: Box, parameters: Seq[String]): String =
    parameters.map { parameter =>
      bounds.get(parameter) match {
        case Some((low, high)) => s"[${end(low)}, ${end(high)}]"
        case None => "[*, *]"
      }
    }.mkString(", ")

  private def end(d: Option[BigDecimal]): String = d.fold("*")(_.toString)
}

/** Writes a preprocessed function as a subject program for the fuzzer.
 *
 * What is printed is the body the analysis measured, not the one that was written: calls
 * are already inlined and conditionals already lifted. That keeps the two sides looking at
 * the same computation, at the cost of a program that reads nothing like its source.
 */
object FuzzProgramEmitter {

  /** The subject program for `fd`, called `name`, or why none could be written. */
  /** @param values      what the function takes once its fields are values of their own, which is
   *                     the signature the subject program is written with
   * @param assumptions  the precondition and the invariants together, over those same values
   */
  def emit(fd: FunDef, name: String, spec: InputSpec, body: Expr,
           values: Seq[ValDef], assumptions: Expr)(using Symbols): Either[String, String] = {

    val precondition = Option(assumptions).filterNot(_ == BooleanLiteral(true))

    for {
      _ <- Either.cond(spec.precision == FPPrecision.Binary64, (),
        "the fuzzer runs subject programs in double precision")
      _ <- (fd.returnType +: values.map(_.tpe))
        .find(tpe => !FPPrecision.fromType(tpe).contains(FPPrecision.Binary64))
        .map(_ => "the fuzzer passes and returns doubles only")
        .toLeft(())
      _ <- (unsupported(body) orElse precondition.flatMap(unsupported)).toLeft(())
    } yield {
      val parameters = values.map(show).mkString(", ")
      val block = written(precondition.fold(body)(Require(_, body)))

      s"""|@fuzz
          |def $name($parameters): ${show(fd.returnType)} = {
          |${indented(show(block))}
          |}
          |""".stripMargin
    }
  }

  /** The program as the fuzzer's plugin has to read it.
   *
   * An integer written among floating-point operands — `x <= 10` for a `Double` `x` — reaches
   * here as a cast, which the tree printer shows as `10.toDouble`. The plugin promotes the
   * `Double` type and its literals to an arbitrary-precision one and leaves everything else
   * alone, so a cast from an integer stays a `Double` while what it is compared against does
   * not, and the program fails to compile with `required: shadow.MPFR`. Written as the literal
   * it stands for, it is promoted with the rest.
   *
   * Only a cast that names its value exactly is folded, which is the same test the input
   * ranges are read under, so the program and the box it is fuzzed over agree.
   */
  private def written(e: Expr)(using Symbols): Expr = exprOps.postMap {
    case ToDouble(IntLit(n)) if n.abs <= BigInt(2).pow(53) => Some(Float64Literal(n.toDouble))
    case _ => None
  }(e)

  /** What the fuzzer could not build the high-precision half of the program from.
   *
   * Its plugin promotes literals and the `Double` type, and leaves calls alone, so a call
   * that survives here would be handed an `MPFRFloat` by a signature that takes a double.
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

  /** The Scala printer, with bindings named apart.
   *
   * Inlining puts several bindings of the same source name in one block, which Scala reads
   * as a redefinition rather than the shadowing the tree means, so each one is printed
   * under the name the identifier is unique by.
   */
  private object FuzzPrinter extends ast.ScalaPrinter {
    val trees: stainless.trees.type = stainless.trees
    import trees._

    override def ppBody(tree: Tree)(using ctx: PrinterContext): Unit = tree match {
      case v: Variable => p"${scalaName(v.id)}"
      case vd: ValDef => p"${scalaName(vd.id)}: ${vd.tpe}"

      // The tree printer writes floating-point equality as `===`, which tells it apart from
      // structural equality when a tree is being read by a person. What is written here is
      // compiled as Scala, where two doubles are compared with `==` and `===` is not an
      // operator at all.
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

