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
 * A class to calculate the first five central moments over a sequence of Doubles. Given the first five
 * central moments, we can then calculate metrics like skewness and kurtosis.
 *
 * m{i} denotes the ith central moment.
 *
 * This code manually inlines code to make it look like a case class. This is done because we changed the
 * count from a Long to a Double to enable the scale method, which allows exponential decays of moments, but
 * we didn't want to break backwards binary compatibility.
 */
sealed class Moments(val m0D: Double, val m1: Double, val m2: Double, val m3: Double, val m4: Double)
  extends Product
    with Serializable {

  def m0: Long = m0D.toLong

  def count: Long = m0

  def mean: Double = m1

  override def canEqual(that: Any): Boolean =
    that.isInstanceOf[Moments]

  override def productArity: Int = 5

  override def productElement(idx: Int): Any =
    idx match {
      case 0 => count
      case 1 => m1
      case 2 => m2
      case 3 => m3
      case 4 => m4
    }
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

object MomentsMonoid {

  /**
   * When combining averages, if the counts sizes are too close we should use a different algorithm. This
   * constant defines how close the ratio of the smaller to the total count can be:
   */
  private val STABILITY_CONSTANT = 0.1

  val zero: Moments = new Moments(0.0, 0.0, 0.0, 0.0, 0.0)

  // Combines the moment calculations from two streams.
  // See http://en.wikipedia.org/wiki/Algorithms_for_calculating_variance#Higher-order_statistics
  // for more information on the formulas used to update the moments.
  @roundoff
  def plus(a: Moments, b: Moments): Moments = {
    require(1 <= a.m0D && a.m0D <= 1e6)
    require(0 <= a.m1 && a.m1 <= 1000)
    require(0 <= a.m2 && a.m2 <= 2.5e11)
    require(-1e14 <= a.m3 && a.m3 <= 1e14)
    require(0 <= a.m4 && a.m4 <= 1e17)
    require(1 <= b.m0D && b.m0D <= 1e6)
    require(0 <= b.m1 && b.m1 <= 1000)
    require(0 <= b.m2 && b.m2 <= 2.5e11)
    require(-1e14 <= b.m3 && b.m3 <= 1e14)
    require(0 <= b.m4 && b.m4 <= 1e17)
    val countCombined = a.m0D + b.m0D
    if (countCombined == 0.0) zero
    else {
      val delta = b.mean - a.mean
      val delta_n = delta / countCombined
      val delta_n2 = delta_n * delta_n
      val delta_n3 = delta_n2 * delta_n
      val ln_sq = a.m0D * a.m0D
      val rn_sq = b.m0D * b.m0D

      val meanCombined = Moments.getCombinedMeanDoubleSorted(a.m0D, a.mean, b.m0D, b.mean)

      val m2 = a.m2 + b.m2 + delta * delta_n * a.m0D * b.m0D

      val m3 = a.m3 + b.m3 +
        delta * delta_n2 * a.m0D * b.m0D * (a.m0D - b.m0D) +
        3 * delta_n * (a.m0D * b.m2 - b.m0D * a.m2)

      val m4 = a.m4 + b.m4 +
        delta * delta_n3 * a.m0D * b.m0D * (ln_sq - a.m0D * b.m0D + rn_sq) +
        6 * delta_n2 * (ln_sq * b.m2 + rn_sq * a.m2) +
        4 * delta_n * (a.m0D * b.m3 - b.m0D * a.m3)

      new Moments(countCombined, meanCombined, m2, m3, m4)
    }
  }
}
