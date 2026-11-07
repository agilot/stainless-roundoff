// SPDX-License-Identifier: MIT
// Copyright 2021 FPBench Project Contributors
// From FPBench rosa.fpcore (Darulova and Kuncak, POPL 2014)
// squareRoot3Invalid for Stainless

import stainless.lang
import stainless.annotation.*
import stainless.math.sqrt

object SquareRoot3Invalid {

  @roundoff
  def squareRoot3Invalid(x: Double): Double = {
    require(0 <= x && x <= 10)
    if (x < 1e-4)
      1 + 0.5 * x
    else
      sqrt(1 + x)
  }

}