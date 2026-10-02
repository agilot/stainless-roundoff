/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification
package roundoff

import trees._

import scala.collection.mutable

/** Writes a floating-point expression as an FPTaylor task.
  *
  * A task is self-contained and shares nothing with the others in the same file, which is what
  * lets a leaf be asked about over the narrowed ranges of the path that reaches it while
  * another leaf is asked about the same input over different ones.
  *
  * Inputs are declared `real` rather than `float64` so that the question matches the one Daisy
  * answers: an input holds an exact real and is rounded on entry. The two agree to the digit
  * on `x * x` over `[1, 2]` once FPTaylor's improved rounding model is turned off, so the
  * difference between the tools is how tightly they bound the same quantity, not which
  * quantity they bound.
  */
object FPTaylorEmitter extends RoundingSourceEmitter {

  /** What the portable `simple_interval` build of FPTaylor cannot evaluate.
    *
    * `simple_interval/interval.ml` raises `Not implemented` for these, and the bundled
    * `INTERVAL` library that does implement them needs x87 assembly to set the rounding mode,
    * so it does not build on arm64. Refusing them here turns what would be a silent missing
    * result into a reason the report can print.
    */
  private val unevaluable: Set[TranscendentalFunction] = {
    import TranscendentalFunction._
    Set(Sin, Cos, Tan, Asin, Acos, Atan)
  }

  def emit(name: String, label: String, expr: Expr, spec: InputSpec)(using Symbols)
    : Either[String, String] = {

    val inputs = exprOps.variablesOf(expr).toSeq.sortBy(_.id.globalId)
    val unbounded = inputs.find(v => !spec.ranges.contains(v.id))

    if (inputs.isEmpty)
      Left("no floating-point inputs to bound")
    else if (unbounded.isDefined)
      Left(s"no range in the precondition for '${unbounded.get.id.name}'; " +
           "add bounds of the form 'lo <= x && x <= hi'")
    else {
      val definitions = mutable.ListBuffer.empty[(String, String)]
      val rounding = spec.precision.fptaylorRounding

      traverse(inputs)(declaration(_, spec)).flatMap { variables =>
        convert(expr, inputs.map(_.id).toSet, definitions).map { body =>
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
    }
  }

  /** What an input is known to lie between, as an exact rational interval. */
  private def declaration(v: Variable, spec: InputSpec): Either[String, String] = {
    val (low, high) = spec.ranges(v.id)
    Fraction.toFPCore(low).flatMap { l =>
      Fraction.toFPCore(high).map(h => s"real ${symbol(v.id)} in [$l, $h]")
    }
  }

  /** A binding becomes a definition of its own rather than a nested expression, which is how
    * FPTaylor shares a subexpression; it charges no rounding for the name itself.
    */
  private def convert(e: Expr, inScope: Set[Identifier],
                      definitions: mutable.ListBuffer[(String, String)])
    : Either[String, String] = {

    def binary(op: String, l: Expr, r: Expr): Either[String, String] =
      convert(l, inScope, definitions).flatMap(a =>
        convert(r, inScope, definitions).map(b => s"($a $op $b)"))

    /** The rounding operator is applied to the whole task, so an operation only has to say
      * that it rounds to nearest, which is the one mode that `rnd32`/`rnd64` stand for.
      */
    def rounded(mode: Expr)(build: => Either[String, String]): Either[String, String] =
      mode match {
        case RoundNearestTiesToEven => build
        case other => Left(s"unsupported rounding mode (${roundingModeName(other)}); " +
          "FPTaylor's rnd32 and rnd64 are round-to-nearest-ties-to-even")
      }

    e match {
      case v: Variable =>
        if (inScope(v.id)) Right(symbol(v.id)) else Left(s"unbound variable '${v.id.name}'")

      case FPLit(d) => Fraction.toFPCore(d).map(r => s"($r)")

      case FPAdd(mode, l, r) => rounded(mode)(binary("+", l, r))
      case FPSub(mode, l, r) => rounded(mode)(binary("-", l, r))
      case FPMul(mode, l, r) => rounded(mode)(binary("*", l, r))
      case FPDiv(mode, l, r) => rounded(mode)(binary("/", l, r))

      // FPTaylor reads `fma(a, b, c)` as the real `a * b + c`, so under the task's rounding
      // operator it rounds once, which is the operation Stainless means.
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

  private def roundingModeName(e: Expr): String = e match {
    case RoundTowardZero => "toward zero"
    case RoundTowardPositive => "toward positive"
    case RoundTowardNegative => "toward negative"
    case RoundNearestTiesToAway => "nearest, ties to away"
    case _ => "unknown"
  }
}
