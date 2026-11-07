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


object AveragedAssociativity4Rhs {
  import AveragedGroup.plus

  @roundoff
  def rhs(c1: Long, x1: Double, c2: Long, x2: Double,
          c3: Long, x3: Double, c4: Long, x4: Double): AveragedValue = {
    require(1 <= c1 && c1 <= 100 && 0 <= x1 && x1 <= 1e3)
    require(1 <= c2 && c2 <= 100 && 0 <= x2 && x2 <= 1e3)
    require(1 <= c3 && c3 <= 100 && 0 <= x3 && x3 <= 1e3)
    require(1 <= c4 && c4 <= 100 && 0 <= x4 && x4 <= 1e3)
    plus(plus(plus(AveragedValue(c1, x1), AveragedValue(c2, x2)), AveragedValue(c3, x3)), AveragedValue(c4, x4))
  }
}

/**
 * Tracks the count and mean value of Doubles in a data stream.
 *
 * Adding two instances of [[AveragedValue]] with [[+]] is equivalent to taking an average of the two streams,
 * with each stream weighted by its count.
 *
 * The mean calculation uses a numerically stable online algorithm suitable for large numbers of records,
 * similar to Chan et. al.'s
 * [[http://en.wikipedia.org/wiki/Algorithms_for_calculating_variance#Parallel_algorithm parallel variance algorithm on Wikipedia]].
 * As long as your count doesn't overflow a Long, the mean calculation won't overflow.
 *
 * @see
 *   [[Moments.getCombinedMeanDouble]] for implementation of [[+]]
 * @param count
 *   the number of aggregated items
 * @param value
 *   the average value of all aggregated items
 */
case class AveragedValue(count: Long, value: Double)

/**
 * [[Group]] implementation for [[AveragedValue]].
 *
 * @define T
 *   `AveragedValue`
 */
object AveragedGroup {
  /**
   * combine two AveragedValue instances
   */
  def plus(l: AveragedValue, r: AveragedValue): AveragedValue = {
    require(0 <= l.value && l.value <= 1e3)
    require(0 <= r.value && r.value <= 1e3)
    require(1 <= l.count && l.count <= 1000000L)
    require(1 <= r.count && r.count <= 1000000L)
    val n = l.count
    val k = r.count
    val newAve = Moments.getCombinedMeanDoubleSorted(n.toDouble, l.value, k.toDouble, r.value)
    AveragedValue(n + k, newAve)
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