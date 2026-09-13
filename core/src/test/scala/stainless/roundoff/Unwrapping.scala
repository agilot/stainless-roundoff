/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package roundoff

import org.scalatest.Assertions

/** Reads what a phase of the analysis returned, failing the test with its reason instead. */
trait Unwrapping { self: Assertions =>

  extension [A](outcome: Either[String, A])
    def orFail: A = outcome match {
      case Right(value) => value
      case Left(why) => fail(why)
    }
}
