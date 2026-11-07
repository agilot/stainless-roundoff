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
import stainless.math


object CorrelationDistributivityLhs {
  import CorrelationMonoid.plus

  @roundoff
  def lhs(a: Correlation, b: Correlation, z: Double): Correlation = {
    require(1 <= a.m0 && a.m0 <= 100 && 0 <= a.m1x && a.m1x <= 1e3 && 0 <= a.m1y && a.m1y <= 1e3)
    require(0 <= a.m2x && a.m2x <= 2.5e11 && 0 <= a.m2y && a.m2y <= 2.5e11 && -2.5e11 <= a.c2 && a.c2 <= 2.5e11)
    require(1 <= b.m0 && b.m0 <= 100 && 0 <= b.m1x && b.m1x <= 1e3 && 0 <= b.m1y && b.m1y <= 1e3)
    require(0 <= b.m2x && b.m2x <= 2.5e11 && 0 <= b.m2y && b.m2y <= 2.5e11 && -2.5e11 <= b.c2 && b.c2 <= 2.5e11)
    require(0.5 <= z && z <= 1)
    plus(a, b).scale(z)
  }
}

/**
 * A class to calculate covariance and the first two central moments of a sequence of pairs of Doubles, from
 * which the pearson correlation coeifficient can be calculated.
 *
 * m{i}x denotes the ith central moment of the first projection of the pair. m{i}y denotes the ith central
 * moment of the second projection of the pair. c2 the covariance equivalent of the second central moment,
 * i.e. c2 = Sum_(x,y) (x - m1x)*(y - m1y).
 */
case class Correlation(c2: Double, m2x: Double, m2y: Double, m1x: Double, m1y: Double, m0: Double) {
  def totalWeight: Double = m0

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

  /**
   * The algorithm for combining the correlation calculations from two partitions of pairs of numbers. Comes
   * from Pébay, Philippe (2008), "Formulas for Robust, One-Pass Parallel Computation of Covariances and
   * Arbitrary-Order Statistical Moments", Technical Report SAND2008-6212, Sandia National Laboratories
   * https://prod-ng.sandia.gov/techlib-noauth/access-control.cgi/2008/086212.pdf
   *
   * Extending this to weights can be found in Schubert, Erich; Gertz, Michael (9 July 2018). Numerically
   * stable parallel computation of (co-)variance. ACM. p. 10. doi:10.1145/3221269.3223036. ISBN
   * 9781450365055. http://dl.acm.org/citation.cfm?id=3221269.3223036
   * https://dl.acm.org/doi/10.1145/3221269.3223036
   */
  def plus(a: Correlation, b: Correlation): Correlation = {
    require(1 <= a.m0 && a.m0 <= 1e6)
    require(0 <= a.m1x && a.m1x <= 1e3)
    require(0 <= a.m1y && a.m1y <= 1e3)
    require(0 <= a.m2x && a.m2x <= 2.5e11)
    require(0 <= a.m2y && a.m2y <= 2.5e11)
    require(-2.5e11 <= a.c2 && a.c2 <= 2.5e11)
    require(1 <= b.m0 && b.m0 <= 1e6)
    require(0 <= b.m1x && b.m1x <= 1e3)
    require(0 <= b.m1y && b.m1y <= 1e3)
    require(0 <= b.m2x && b.m2x <= 2.5e11)
    require(0 <= b.m2y && b.m2y <= 2.5e11)
    require(-2.5e11 <= b.c2 && b.c2 <= 2.5e11)
    val count = a.totalWeight + b.totalWeight
    if (count == 0.0)
      CorrelationMonoid.zero
    else {
      val prodSumRatio = a.totalWeight * b.totalWeight / count

      val m1x = Moments.getCombinedMeanDoubleSorted(a.totalWeight, a.m1x, b.totalWeight, b.m1x)
      val m1y = Moments.getCombinedMeanDoubleSorted(a.totalWeight, a.m1y, b.totalWeight, b.m1y)
      val deltaX = b.m1x - a.m1x
      val deltaY = b.m1y - a.m1y

      val m2x = a.m2x + b.m2x + math.pow(deltaX, 2) * prodSumRatio
      val m2y =
        a.m2y + b.m2y + math.pow(deltaY, 2) * prodSumRatio

      val c2 = a.c2 + b.c2 + deltaX * deltaY * prodSumRatio

      Correlation(c2 = c2, m2x = m2x, m2y = m2y, m1x = m1x, m1y = m1y, m0 = count)
    }
  }

  val zero: Correlation = Correlation(0, 0, 0, 0, 0, 0)
}

object Moments {

  private[this] val STABILITY_CONSTANT = 0.1

  // Note from the authors: this is our own addition to avoid recursion
  def getCombinedMeanDoubleSorted(weightN: Double, an: Double, weightK: Double, ak: Double): Double = {
    require(1 <= weightN && weightN <= 1e6)
    require(1 <= weightK && weightK <= 1e6)
    require(0 <= an && an <= 1e3)
    require(0 <= ak && ak <= 1e3)
    if (weightN < weightK) getCombinedMeanDouble(weightK, ak, weightN, an)
    else getCombinedMeanDouble(weightN, an, weightK, ak)
  }

  /**
   * Given two streams of doubles (weightN, an) and (weightK, ak) of form (weighted count, mean), calculates
   * the mean of the combined stream.
   *
   * Uses a more stable online algorithm which should be suitable for large numbers of records similar to:
   * http://en.wikipedia.org/wiki/Algorithms_for_calculating_variance#Parallel_algorithm
   *
   * This differs from the implementation in MomentsGroup.scala only in that here, the counts are weighted,
   * and are thus doubles instead of longs
   */
  def getCombinedMeanDouble(weightN: Double, an: Double, weightK: Double, ak: Double): Double =
    require(weightN >= weightK)
    require(1 <= weightN && weightN <= 1e6)
    require(1 <= weightK && weightK <= 1e6)
    require(0 <= an && an <= 1e3)
    require(0 <= ak && ak <= 1e3)
    (weightN + weightK) match {
      case 0.0 => 0.0
      case newCount if newCount == weightN => an
      case newCount =>
        val scaling = weightK / newCount
        // a_n + (a_k - a_n)*(k/(n+k)) is only stable if n is not approximately k
        if (scaling < STABILITY_CONSTANT) an + (ak - an) * scaling
        else (weightN * an + weightK * ak) / newCount
    }
}