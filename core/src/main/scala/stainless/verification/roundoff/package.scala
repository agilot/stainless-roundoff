/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification
package roundoff

import trees.*

import scala.annotation.tailrec



/** Rounds upwards, so that a rounded bound is still a bound, to the default `BigDecimal`
  * width, so that later arithmetic does not round it again.
  */
private[roundoff] val reportedPrecision =
  new java.math.MathContext(34, java.math.RoundingMode.CEILING)

private def round(e: BigDecimal, towards: java.math.RoundingMode): String =
    e.round(new java.math.MathContext(4, towards)).toString

/** Floating-point numbers and the integers [[isIntegerType]] accepts. */
private[roundoff] def isNumberType(tpe: Type): Boolean = tpe match {
  case FPType(_, _) => true
  case other => isIntegerType(other)
}

private[roundoff] def isIntegerType(tpe: Type): Boolean = tpe match {
  case Int32Type() | Int64Type() => true
  case _ => false
}

/** Whether `e`, computes an integer. Integer arithmetic is
  * exact, since Stainless checks that it does not overflow.
  */
@tailrec
private[roundoff] def isIntegral(e: Expr): Boolean = e match {
  case Int32Literal(_) | Int64Literal(_) => true
  case v: Variable => isIntegerType(v.tpe)
  case _: Plus | _: Minus | _: Times | _: UMinus | _: BVWideningCast => true
  case Let(_, _, body) => isIntegral(body)
  case _ => false
}

/** `f` applied to every element, or the first error. */
private[roundoff] def traverse[A, B](as: Seq[A])(f: A => Either[String, B])
  : Either[String, Seq[B]] =
  as.foldLeft[Either[String, Seq[B]]](Right(Seq.empty)) {
    case (done, a) => done.flatMap(built => f(a).map(built :+ _))
  }

/** `body` under the `bindings`, the first one outermost. */
private[roundoff] def withLets(bindings: Seq[(ValDef, Expr)], body: Expr): Expr =
  bindings.foldRight(body) { case ((vd, value), rest) => Let(vd, value, rest) }

/** `e` with its `let` bindings substituted. */
private[roundoff] def withoutLets(e: Expr): Expr = e match {
  case Let(vd, value, body) =>
    withoutLets(exprOps.replaceFromSymbols(Map(vd -> withoutLets(value)), body))
  case other => other
}

/** `e` without the `let` bindings nothing reads. */
private[roundoff] def withoutUnusedLets(e: Expr): Expr = exprOps.postMap {
  case Let(vd, _, body) if !exprOps.variablesOf(body).exists(_.id == vd.id) => Some(body)
  case _ => None
}(e)

/** The value of `e` if it is a floating-point constant, looking through its bindings. */
private[roundoff] def constantOf(e: Expr, known: Map[Identifier, Expr] = Map.empty): Option[Double] =
  e match {
    case FPLit(d) => Some(d)
    case v: Variable => known.get(v.id).flatMap(constantOf(_, known))
    case Let(vd, value, body) => constantOf(body, known + (vd.id -> value))
    case _ => None
  }

/** What `e` computes in floating point if it has no inputs, such as NaN for `0.0 / 0.0`. */
private[roundoff] def valueWithoutInputs(e: Expr, precision: FPPrecision): Option[Double] =
  constantOf(e).orElse(
    if (exprOps.variablesOf(e).nonEmpty) None
    else ConstantEvaluator.evaluate(e, Map.empty, precision).toOption.map(_.rounded))

/** The invariant of the class `obj` is built from, if it has one, about `obj`. */
private[roundoff] def invariantOf(obj: Expr)(using Symbols): Option[Expr] = obj.getType match {
  case adt: ADTType =>
    adt.getSort.invariant.flatMap { inv =>
      exprOps.withoutSpecs(inv.fullBody).map(inv.withParamSubst(Seq(obj), _))
    }
  case _ => None
}

/** A number of seconds, counted from when it is created.
  *
  * Kept as elapsed time rather than as an end point, which an infinite budget would overflow.
  */
private[roundoff] final class TimeLimit(seconds: Double) {
  private val start: Long = System.nanoTime()
  private val limit: Long = (seconds.max(0.0) * 1e9).toLong

  def secondsLeft: Double = ((limit - (System.nanoTime() - start)) / 1e9).max(0.0)

  /** Throws [[OutOfTime]] once the time is up. */
  def check(): Unit =
    if (System.nanoTime() - start > limit)
      throw new OutOfTime(s"reading took longer than the ${seconds}s budget")
}

private[roundoff] object TimeLimit {
  val never: TimeLimit = new TimeLimit(Double.PositiveInfinity)
}

private[roundoff] final class OutOfTime(message: String) extends Exception(message)

/** An integer literal of any width, possibly negated. */
private[roundoff] object IntLit {
  def unapply(e: Expr): Option[BigInt] = e match {
    case Int8Literal(n) => Some(BigInt(n))
    case Int16Literal(n) => Some(BigInt(n))
    case Int32Literal(n) => Some(BigInt(n))
    case Int64Literal(n) => Some(BigInt(n))
    case IntegerLiteral(n) => Some(n)
    case UMinus(IntLit(n)) => Some(-n)
    // An `Int` constant compared with or added to a `Long` is widened first.
    case BVWideningCast(IntLit(n), _) => Some(n)
    case _ => None
  }
}

/** A floating-point constant, including an integer converted exactly and a negated literal. */
private[roundoff] object FPLit {
  def unapply(e: Expr): Option[Double] = e match {
    case Float64Literal(d) => Some(d)
    case Float32Literal(f) => Some(f.toDouble)
    case FPCast(_, significand, _, IntLit(n)) if n.abs <= BigInt(2).pow(significand) =>
      Some(n.toDouble)
    case FPUMinus(FPLit(d)) => Some(-d)
    case Assert(_, _, FPLit(d)) => Some(d)
    case Annotated(FPLit(d), _) => Some(d)
    case _ => None
  }
}

/** An exact fraction in lowest terms, with the sign carried by the numerator. */
private[roundoff] final case class Rational(num: BigInt, den: BigInt) extends Ordered[Rational] {
  def +(o: Rational): Rational = Rational.of(num * o.den + o.num * den, den * o.den)
  def -(o: Rational): Rational = this + -o
  def *(o: Rational): Rational = Rational.of(num * o.num, den * o.den)
  def /(o: Rational): Rational = Rational.of(num * o.den, den * o.num)
  def unary_- : Rational = Rational(-num, den)
  def pow(n: Int): Rational = Rational(num.pow(n), den.pow(n))
  def abs: Rational = if (num < 0) -this else this
  def compare(o: Rational): Int = (num * o.den).compare(o.num * den)
  def isZero: Boolean = num == 0

  /** Rounded up to the precision bounds are reported at. */
  def toBigDecimal: BigDecimal =
    new BigDecimal(BigDecimal(num).bigDecimal.divide(BigDecimal(den).bigDecimal, reportedPrecision),
                   reportedPrecision)
}

private[roundoff] object Rational {
  val zero: Rational = Rational(0, 1)
  val one: Rational = Rational(1, 1)

  def of(n: BigInt, d: BigInt): Rational = {
    require(d != 0)
    val sign = if (d < 0) BigInt(-1) else BigInt(1)
    val g = n.gcd(d)
    Rational(sign * (n / g), sign * (d / g))
  }
}

/** The exact fraction a double stands for. */
private[roundoff] object Fraction {

  def apply(d: Double): Either[String, Rational] =
    if (d.isNaN || d.isInfinite) Left(s"non-finite literal ($d)")
    else if (d == 0.0) Right(Rational.zero)
    else {
      val bits = java.lang.Double.doubleToLongBits(d)
      val biasedExponent = ((bits >> 52) & 0x7ff).toInt
      val storedMantissa = bits & 0xfffffffffffffL

      // A subnormal has no implicit leading bit and uses the smallest exponent.
      val (mantissa, exponent) =
        if (biasedExponent == 0) (BigInt(storedMantissa), -1074)
        else (BigInt(storedMantissa | 0x10000000000000L), biasedExponent - 1075)

      val signed = if (d < 0) -mantissa else mantissa

      if (exponent >= 0) Right(Rational(signed * BigInt(2).pow(exponent), BigInt(1)))
      else {
        // Cancel the powers of two both sides share, so the fraction is in lowest terms.
        val shared = signed.abs.lowestSetBit min -exponent
        Right(Rational(signed >> shared, BigInt(2).pow(-exponent - shared)))
      }
    }

  def toExpr(d: Double): inox.trees.Expr = apply(d) match {
    case Right(r) => inox.trees.FractionLiteral(r.num, r.den)
    case Left(why) => throw new IllegalArgumentException(why)
  }

  /** Written `n` or `n/d`, as FPCore and FPTaylor read it. */
  def toFPCore(d: Double): Either[String, String] =
    Fraction(d).map(r => if (r.den == 1) r.num.toString else s"${r.num}/${r.den}")
}

/** The `stainless.math` functions the analysis understands, and `sqrt`. */
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

/** A call to a [[TranscendentalFunction]] with the right number of arguments. */
private[roundoff] object TranscendentalFunctionCall {
  def unapply(e: Expr): Option[(TranscendentalFunction, Seq[Expr])] = e match {
    case Sqrt(RoundNearestTiesToEven, a) => Some((TranscendentalFunction.Sqrt, Seq(a)))
    case FunctionInvocation(id, _, args) =>
      TranscendentalFunction.pathToFunction.get(id.fullName).filter(_.arity == args.size).map(_ -> args)
    case _ => None
  }
}
