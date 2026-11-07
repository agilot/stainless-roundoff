// SPDX-License-Identifier: MIT
// Copyright 2021 FPBench Project Contributors
// From FPBench rosa.fpcore (Darulova and Kuncak, POPL 2014)
// triangleSorted for Stainless

import stainless.lang
import stainless.annotation.*
import stainless.math.sqrt

object TriangleSorted {

  @roundoff
  def triangleSorted(a: Double, b: Double, c: Double): Double = {
    require(1 <= a && a <= 9 && 1 <= b && b <= 9 && 1 <= c && c <= 9 &&
      a + b > c + 1e-6 && a + c > b + 1e-6 && b + c > a + 1e-6 &&
      a < c && b < c)
    if (a < b)
      sqrt((c + (b + a)) * (a - (c - b)) * (a + (c - b)) * (c + (b - a))) / 4.0
    else
      sqrt((c + (a + b)) * (b - (c - a)) * (b + (c - a)) * (c + (a - b))) / 4.0
  }

}