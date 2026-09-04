/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification
package roundoff

import trees._

/** A function both Daisy and Ibex know, named by the symbol the two of them spell it with. */
private[roundoff] enum MathFunction(val symbol: String, val arity: Int) {
  case Sqrt extends MathFunction("sqrt", 1)
  case Exp extends MathFunction("exp", 1)
  case Log extends MathFunction("log", 1)
  case Sin extends MathFunction("sin", 1)
  case Cos extends MathFunction("cos", 1)
  case Tan extends MathFunction("tan", 1)
  case Asin extends MathFunction("asin", 1)
  case Acos extends MathFunction("acos", 1)
  case Atan extends MathFunction("atan", 1)
  case Pow extends MathFunction("pow", 2)
}

private[roundoff] object MathFunction {

  /** Where the library defines each one, `sqrt` apart, which the frontend turns into a node. */
  private val library: Map[String, MathFunction] =
    values.filter(_ != Sqrt).map(f => s"stainless.math.${f.symbol}" -> f).toMap

  def of(name: String): Option[MathFunction] = library.get(name)
}

/** A call the analysis reads as the exact function the program approximates.
  *
  * The library implements these in Scala over floats, and reading one as its exact
  * counterpart assumes that implementation is as accurate as Daisy's model of it.
  */
private[roundoff] object MathCall {
  def unapply(e: Expr): Option[(MathFunction, Seq[Expr])] = e match {
    case Sqrt(RoundNearestTiesToEven, a) => Some((MathFunction.Sqrt, Seq(a)))

    case FunctionInvocation(id, _, args) =>
      MathFunction.of(id.fullName).filter(_.arity == args.size).map(_ -> args)

    case _ => None
  }
}
