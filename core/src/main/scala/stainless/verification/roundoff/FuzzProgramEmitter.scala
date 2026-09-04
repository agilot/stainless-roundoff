/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification
package roundoff

import trees._

/** Writes a preprocessed function as a subject program for the fuzzer.
  *
  * What is printed is the body the analysis measured, not the one that was written: calls
  * are already inlined and conditionals already lifted. That keeps the two sides looking at
  * the same computation, at the cost of a program that reads nothing like its source.
  */
object FuzzProgramEmitter {

  /** The subject program for `fd`, called `name`, or why none could be written. */
  def emit(fd: FunDef, name: String, spec: InputSpec, body: Expr)(using Symbols)
    : Either[String, String] = {

    val precondition = fd.precondition.map(Preprocessor.stripAnnotations)

    for {
      _ <- Either.cond(spec.precision == FPPrecision.Binary64, (),
             "the fuzzer runs subject programs in double precision")
      _ <- (fd.returnType +: fd.params.map(_.tpe))
             .find(tpe => !FPPrecision.fromType(tpe).contains(FPPrecision.Binary64))
             .map(_ => "the fuzzer passes and returns doubles only")
             .toLeft(())
      _ <- (unsupported(body) orElse precondition.flatMap(unsupported)).toLeft(())
    } yield {
      val parameters = fd.params.map(show).mkString(", ")
      val block = precondition.fold(body)(Require(_, body))

      s"""|@fuzz
          |def $name($parameters): ${show(fd.returnType)} = {
          |${indented(show(block))}
          |}
          |""".stripMargin
    }
  }

  /** What the fuzzer could not build the high-precision half of the program from.
    *
    * Its plugin promotes literals and the `Double` type, and leaves calls alone, so a call
    * that survives here would be handed an `MPFRFloat` by a signature that takes a double.
    */
  private def unsupported(e: Expr)(using Symbols): Option[String] =
    exprOps.collect[String] {
      case MathCall(f, _) => Set(s"'${f.symbol}'")
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
      case _ => super.ppBody(tree)
    }

    private def scalaName(id: Identifier): String = {
      val letters = id.name.map(c => if (c.isLetterOrDigit || c == '_') c else '_')
      val start = if (letters.headOption.exists(c => c.isLetter || c == '_')) letters else s"v$letters"
      s"${start}_${id.id}"
    }
  }
}
