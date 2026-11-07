/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification
package roundoff

import org.scalatest.funsuite.AnyFunSuite

/** Covers how Daisy's results file is read: a bound, an overflow, or another failure. */
class DaisyCsvSuite extends AnyFunSuite {

  private val answers = DaisyRunner.parseCsv(Seq(
    "Function name; Absolute error; Relative error; Real range; Time; Failure",
    "bounded;5.7e-14;;[0, 1];81;",
    "exponential;;;;;ArithmeticException: cannot convert +infinity to a fraction",
    "product;;;;;OverflowException: Potential overflow detected. Error bound cannot be computed.",
    "quotient;;;;;DivisionByZeroException: trying to divide by interval containing 0"))

  private def kindOf(name: String): String = answers(name) match {
    case Right(_) => "bound"
    case Left(AnalyzerFailure.MayOverflow(_)) => "overflow"
    case Left(AnalyzerFailure.Failed(_)) => "failure"
  }

  test("a bound is read as a bound") {
    assert(answers("bounded") == Right(BigDecimal("5.7e-14")))
  }

  test("both ways Daisy reports an overflow are read as one, and nothing else is") {
    assert(Seq("exponential", "product", "quotient").map(kindOf) ==
             Seq("overflow", "overflow", "failure"))
  }
}
