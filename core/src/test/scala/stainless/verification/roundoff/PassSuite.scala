/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification
package roundoff

import org.scalatest.funsuite.AnyFunSuite

/** Covers how queries share a pass's time, and when they may go over it. */
class PassSuite extends AnyFunSuite {

  test("while its own time lasts, a pass shares it, not its limit") {
    val share = new SharedQueryTime(4, 2, limit = new TimeLimit(100)).secondsForNextQuery()
    assert(share > 1.9 && share <= 2.0)
  }

  test("once its own time is used up, a pass shares what is left of its limit") {
    val pass = new SharedQueryTime(0, 2, limit = new TimeLimit(10))
    val share = pass.secondsForNextQuery()
    assert(share > 4.9 && share <= 5.0)
    assert(pass.limit.secondsLeft > 0)
  }

  test("a pass with no further limit runs out with its own time") {
    val pass = new SharedQueryTime(0, 2)
    assertThrows[OutOfTime](pass.secondsForNextQuery())
    assert(pass.limit.secondsLeft == 0)
  }
}
