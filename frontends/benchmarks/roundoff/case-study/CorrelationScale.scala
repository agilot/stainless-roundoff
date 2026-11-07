/*
Copyright 2012 Twitter, Inc.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
 */

package com.twitter.algebird

import stainless.annotation.*

/**
 * A class to calculate covariance and the first two central moments of a sequence of pairs of Doubles, from
 * which the pearson correlation coeifficient can be calculated.
 *
 * m{i}x denotes the ith central moment of the first projection of the pair. m{i}y denotes the ith central
 * moment of the second projection of the pair. c2 the covariance equivalent of the second central moment,
 * i.e. c2 = Sum_(x,y) (x - m1x)*(y - m1y).
 */
case class Correlation(c2: Double, m2x: Double, m2y: Double, m1x: Double, m1y: Double, m0: Double) {
  @roundoff
  def scale(z: Double): Correlation =
    require(1 <= m0 && m0 <= 1e6)
    require(0 <= m1x && m1x <= 1e3)
    require(0 <= m1y && m1y <= 1e3)
    require(0 <= m2x && m2x <= 2.5e11)
    require(0 <= m2y && m2y <= 2.5e11)
    require(-2.5e11 <= c2 && c2 <= 2.5e11)
    require(0 <= z && z <= 1)
    if (z == 0)
      CorrelationMonoid.zero
    else
      Correlation(c2 = z * c2, m2x = z * m2x, m2y = z * m2y, m1x = m1x, m1y = m1y, m0 = z * m0)
}

object CorrelationMonoid {
  val zero: Correlation = Correlation(0, 0, 0, 0, 0, 0)
}