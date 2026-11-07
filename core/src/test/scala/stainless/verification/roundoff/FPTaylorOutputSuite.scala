/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification
package roundoff

import org.scalatest.funsuite.AnyFunSuite

/** Covers how FPTaylor's output is read: a bound, or the error it printed for a task. */
class FPTaylorOutputSuite extends AnyFunSuite {

  /** FPTaylor 0.9.4 on `smartRoot` from `fpbench/`, with the expressions shortened. */
  private val smartRoot =
    """|FPTaylor, version 0.9.4+dev
       |Loading: /tmp/stainless-1.fptaylor
       |Processing: f_26_leaf0
       |**ERROR**:
       |Potential exception detected: Sqrt of negative number at:
       |sqrt(rnd64((rnd64(v_28) - rnd64(v_25))))
       |Processing: f_26_guard0_rhs
       |Building Taylor forms...
       |exact total: 3.441691e-15 (low = 3.441691e-15, subopt = 0.0%)
       |-------------------------------------------------------------------------------
       |Problem: f_26_leaf0
       |
       |Bounds (without rounding): [-inf, +inf]
       |
       |Elapsed time: 0.00
       |-------------------------------------------------------------------------------
       |Problem: f_26_guard0_rhs
       |
       |Bounds (without rounding): [-inf, +inf]
       |
       |Absolute error (exact): 3.4416913763379857e-15
       |
       |Elapsed time: 0.01
       |""".stripMargin

  private val answers = FPTaylorRunner.parseOutput(smartRoot).toOption.get

  test("a bound is read as a bound") {
    assert(answers("f_26_guard0_rhs") == Right(BigDecimal("3.4416913763379857e-15")))
  }

  test("a task without a bound gets the error FPTaylor printed for it, without the expression") {
    assert(answers("f_26_leaf0") ==
             Left(AnalyzerFailure.Failed("Potential exception detected: Sqrt of negative number")))
  }

  test("a run with no results gives its first error") {
    val failed = FPTaylorRunner.parseOutput("**ERROR**: Not implemented\n")
    assert(failed == Left("FPTaylor reported no results: Not implemented"))
  }
}
