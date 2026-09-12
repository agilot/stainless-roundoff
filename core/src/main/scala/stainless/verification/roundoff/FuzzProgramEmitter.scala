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
