/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification
package roundoff

import trees._

/** Works out how far a value with no inputs left in it falls from what it is worth exactly.
  *
  * Such a value is ordinary once calls are inlined: a helper returning a constant in one of
  * its branches meets another one in the same leaf. The analyzer is given one query per
  * leaf and needs at least one bounded input to answer, so this error is worked out rather
  * than asked for.
  *
  * Folding the value into the literal it evaluates to would not do instead, because both
  * sides of the analysis read a literal as exactly the double it names. The rounding of the
  * operations between the literals would be dropped along with them.
  */
private[roundoff] object ConstantEvaluator {

  def error(e: Expr, precision: FPPrecision): Either[String, BigDecimal] =
    for {
      value <- evaluate(e, Map.empty, precision)
      _ <- Either.cond(!value.rounded.isNaN && !value.rounded.isInfinite, (),
             s"a value with no inputs is not finite (${value.rounded})")
      landed <- Exact.ofDouble(value.rounded)
    } yield decimal((landed - value.exact).abs)

  /** What the program computes, beside what the same expression is worth exactly. */
  private case class Value(rounded: Double, exact: Exact)

  private def evaluate(e: Expr, bound: Map[Identifier, Value], precision: FPPrecision)
    : Either[String, Value] = {

    /** Single precision is computed in `Float` rather than rounded from a `Double` result,
      * which would round it twice and can land on the wrong value.
      */
    def binary(single: (Float, Float) => Float,
               double: (Double, Double) => Double,
               exact: (Exact, Exact) => Either[String, Exact])
              (l: Expr, r: Expr): Either[String, Value] =
      for {
        a <- evaluate(l, bound, precision)
        b <- evaluate(r, bound, precision)
        combined <- exact(a.exact, b.exact)
      } yield Value(precision match {
        case FPPrecision.Binary32 => single(a.rounded.toFloat, b.rounded.toFloat).toDouble
        case FPPrecision.Binary64 => double(a.rounded, b.rounded)
      }, combined)

    e match {
      // Ahead of the arithmetic, since a literal reaches here wrapped in a sign flip or a
      // cast as readily as on its own.
      case FPLit(d) => Exact.ofDouble(d).map(Value(d, _))

      case FPAdd(_, l, r) => binary(_ + _, _ + _, (a, b) => Right(a + b))(l, r)
      case FPSub(_, l, r) => binary(_ - _, _ - _, (a, b) => Right(a - b))(l, r)
      case FPMul(_, l, r) => binary(_ * _, _ * _, (a, b) => Right(a * b))(l, r)
      case FPDiv(_, l, r) => binary(_ / _, _ / _, (a, b) => a / b)(l, r)

      case FPUMinus(a) => evaluate(a, bound, precision).map(v => Value(-v.rounded, -v.exact))

      case FPFMA(_, a, b, c) =>
        for {
          x <- evaluate(a, bound, precision)
          y <- evaluate(b, bound, precision)
          z <- evaluate(c, bound, precision)
        } yield Value(precision match {
          case FPPrecision.Binary32 =>
            Math.fma(x.rounded.toFloat, y.rounded.toFloat, z.rounded.toFloat).toDouble
          case FPPrecision.Binary64 => Math.fma(x.rounded, y.rounded, z.rounded)
        }, x.exact * y.exact + z.exact)

      case Let(vd, value, body) =>
        evaluate(value, bound, precision)
          .flatMap(v => evaluate(body, bound + (vd.id -> v), precision))

      case v: Variable =>
        bound.get(v.id).toRight(s"'${v.id.name}' is not bound in a value with no inputs")

      // The exact side is a fraction, and none of these is one.
      case MathCall(f, _) =>
        Left(s"a value with no inputs calls '${f.symbol}', which is not a fraction")

      case other =>
        Left(s"${other.getClass.getSimpleName} cannot be evaluated without inputs")
    }
  }

  private def decimal(value: Exact): BigDecimal =
    new BigDecimal(BigDecimal(value.numerator).bigDecimal.divide(
      BigDecimal(value.denominator).bigDecimal, reportedPrecision), reportedPrecision)

  /** A fraction in lowest terms, with the sign carried by the numerator. */
  private case class Exact(numerator: BigInt, denominator: BigInt) {

    def +(other: Exact): Exact =
      Exact.of(numerator * other.denominator + other.numerator * denominator,
               denominator * other.denominator)

    def -(other: Exact): Exact = this + -other

    def *(other: Exact): Exact =
      Exact.of(numerator * other.numerator, denominator * other.denominator)

    def /(other: Exact): Either[String, Exact] =
      if (other.numerator == 0) Left("a value with no inputs divides by zero")
      else Right(Exact.of(numerator * other.denominator, denominator * other.numerator))

    def unary_- : Exact = Exact(-numerator, denominator)

    def abs: Exact = if (numerator < 0) -this else this
  }

  private object Exact {

    def of(numerator: BigInt, denominator: BigInt): Exact = {
      val shared = numerator.gcd(denominator)
      val divisor = if (shared == 0) BigInt(1) else shared
      val sign = if (denominator < 0) BigInt(-1) else BigInt(1)
      Exact(sign * numerator / divisor, sign * denominator / divisor)
    }

    /** Seeded the same way the rest of the analysis reads a literal. */
    def ofDouble(d: Double): Either[String, Exact] =
      Fraction.ofDouble(d).map { case (numerator, denominator) => Exact(numerator, denominator) }
  }
}
