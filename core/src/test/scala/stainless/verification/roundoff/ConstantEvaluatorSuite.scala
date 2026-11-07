/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification
package roundoff

import org.scalatest.funsuite.AnyFunSuite
import stainless.trees._

/** Covers values with no inputs, which are evaluated both in floating point and exactly. */
class ConstantEvaluatorSuite extends AnyFunSuite {

  private val rm = RoundNearestTiesToEven

  private def toDouble(e: Expr): Expr = FPCast(11, 53, rm, e)

  private def error(e: Expr): Either[String, BigDecimal] =
    ConstantEvaluator.roundingError(e, FPPrecision.Binary64)

  test("a division that rounds has the error of that rounding") {
    val third = FPDiv(rm, Float64Literal(1.0), Float64Literal(3.0))
    assert(error(third).exists(e => e > 0 && e < BigDecimal("1e-16")))
  }

  test("an integer computed from literals and converted to Double is exact") {
    val sum = Plus(Int64Literal(1), Int64Literal(1))
    assert(error(FPAdd(rm, toDouble(sum), Float64Literal(0.5))) == Right(BigDecimal(0)))
  }

  test("an integer bound to a name, as an inlined `val n = l.count` is, is read through it") {
    val n = ValDef.fresh("n", Int64Type())
    val weights = Let(n, Int64Literal(1), FPAdd(rm, toDouble(n.toVariable), toDouble(n.toVariable)))
    assert(error(weights) == Right(BigDecimal(0)))
    assert(ConstantEvaluator.evaluate(weights, Map.empty, FPPrecision.Binary64).map(_.rounded) ==
             Right(2.0))
  }

  test("a division by zero has no exact value, and floating point makes it NaN or an infinity") {
    val zero = Float64Literal(0.0)
    val undefined = ConstantEvaluator.evaluate(FPDiv(rm, zero, zero), Map.empty, FPPrecision.Binary64)
    assert(undefined.exists(v => v.rounded.isNaN && v.exact.isEmpty))
    assert(valueWithoutInputs(FPDiv(rm, zero, zero), FPPrecision.Binary64).exists(_.isNaN))
    assert(valueWithoutInputs(FPDiv(rm, Float64Literal(1.0), zero), FPPrecision.Binary64)
             .contains(Double.PositiveInfinity))
  }

  test("an integer above 2^24 rounds when converted to Float, and that is its error") {
    val large = Plus(Int32Literal(1 << 24), Int32Literal(1))
    assert(ConstantEvaluator.roundingError(FPCast(8, 24, rm, large), FPPrecision.Binary32) ==
             Right(BigDecimal(1)))
  }

  test("an integer above 2^53 rounds when converted to Double, and that is its error") {
    val large = Plus(Int64Literal(1L << 53), Int64Literal(1))
    assert(error(toDouble(large)) == Right(BigDecimal(1)))
  }
}