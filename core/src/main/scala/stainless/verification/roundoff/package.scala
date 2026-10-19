/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification
package roundoff

import trees._

/** `--debug=roundoff`: the settings, and per function the shape of its branches and how
  * the time was spent.
  */
object DebugSectionRoundoff extends inox.DebugSection("roundoff")

/** `n` followed by `thing`, in the plural unless `n` is one. */
private[roundoff] def counted(n: Int, thing: String, plural: String = ""): String =
  s"$n ${if (n == 1) thing else if (plural.nonEmpty) plural else thing + "s"}"

/** How a bound is rounded when it has too many digits: upwards, so it stays an upper bound,
  * and to the default `BigDecimal` width, so later arithmetic does not round it again.
  */
private[roundoff] val reportedPrecision =
  new java.math.MathContext(34, java.math.RoundingMode.CEILING)

/** `f` applied to every element, or the first error. */
private[roundoff] def traverse[A, B](as: Seq[A])(f: A => Either[String, B])
  : Either[String, Seq[B]] =
  as.foldLeft[Either[String, Seq[B]]](Right(Seq.empty)) {
    case (done, a) => done.flatMap(built => f(a).map(built :+ _))
  }

/** A number of seconds shared by a known number of queries.
  *
  * Each query may use the time left divided by the queries left, so time one query does not
  * use goes to the queries after it.
  */
private[roundoff] final class TimeBudget(seconds: Double, queries: Int) {

  private val deadline: Long = System.nanoTime() + (seconds.max(0.0) * 1e9).toLong
  private var pending: Int = queries

  /** Seconds left before the deadline. */
  def left: Double = ((deadline - System.nanoTime()) / 1e9).max(0.0)

  /** Seconds the next query may use. */
  def nextShare: Double = left / pending.max(1)

  /** Records that one query was asked, whatever time it used. */
  def markAsked(): Unit = pending -= 1

  /** The next query's share, recorded as asked. */
  def takeShare(): Double = {
    val share = nextShare
    markAsked()
    share
  }
}

/** An integer literal of any width, possibly negated. */
private[roundoff] object IntLit {
  def unapply(e: Expr): Option[BigInt] = e match {
    case Int8Literal(n) => Some(BigInt(n))
    case Int16Literal(n) => Some(BigInt(n))
    case Int32Literal(n) => Some(BigInt(n))
    case Int64Literal(n) => Some(BigInt(n))
    case IntegerLiteral(n) => Some(n)
    case UMinus(IntLit(n)) => Some(-n)
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
private[roundoff] final case class Rational(num: BigInt, den: BigInt) {
  def +(o: Rational): Rational = Rational.of(num * o.den + o.num * den, den * o.den)
  def -(o: Rational): Rational = this + -o
  def *(o: Rational): Rational = Rational.of(num * o.num, den * o.den)
  def /(o: Rational): Rational = Rational.of(num * o.den, den * o.num)
  def unary_- : Rational = Rational(-num, den)
  def abs: Rational = if (num < 0) -this else this
  def isZero: Boolean = num == 0
  def isOne: Boolean = num == 1 && den == 1

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

/** Exact fractions of doubles. */
private[roundoff] object Fraction {

  /** The exact fraction a double stands for. */
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
        // Cancel what both sides share, so the fraction is in lowest terms.
        val shared = signed.abs.lowestSetBit min -exponent
        Right(Rational(signed >> shared, BigInt(2).pow(-exponent - shared)))
      }
    }

  /** The same as [[apply]], but as an Inox literal. */
  def toExpr(d: Double): inox.trees.Expr = apply(d) match {
    case Right(r) => inox.trees.FractionLiteral(r.num, r.den)
    case Left(why) => throw new IllegalArgumentException(why)
  }

  /** The same as [[apply]], written as `n` or `n/d` for FPCore and FPTaylor. */
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
