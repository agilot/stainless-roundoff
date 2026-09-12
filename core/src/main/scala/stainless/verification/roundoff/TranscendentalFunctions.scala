/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification
package roundoff

import trees._

private[roundoff] enum TranscendentalFunction(val symbol: String, val arity: Int) {
  case Sqrt extends TranscendentalFunction("sqrt", 1)
  case Exp extends TranscendentalFunction("exp", 1)
  case Log extends TranscendentalFunction("log", 1)
  case Sin extends TranscendentalFunction("sin", 1)
  case Cos extends TranscendentalFunction("cos", 1)
  case Tan extends TranscendentalFunction("tan", 1)
  case Asin extends TranscendentalFunction("asin", 1)
  case Acos extends TranscendentalFunction("acos", 1)
  case Atan extends TranscendentalFunction("atan", 1)
  case Pow extends TranscendentalFunction("pow", 2)
}

private[roundoff] object TranscendentalFunction {
  val pathToFunction: Map[String, TranscendentalFunction] =
    values.filter(_ != Sqrt).map(f => s"stainless.math.${f.symbol}" -> f).toMap
}

private[roundoff] object TranscendentalFunctionCall {
  def unapply(e: Expr): Option[(TranscendentalFunction, Seq[Expr])] = e match {
    case Sqrt(RoundNearestTiesToEven, a) => Some((TranscendentalFunction.Sqrt, Seq(a)))
    case FunctionInvocation(id, _, args) =>
      TranscendentalFunction.pathToFunction.get(id.fullName).filter(_.arity == args.size).map(_ -> args)
    case _ => None
  }
}
