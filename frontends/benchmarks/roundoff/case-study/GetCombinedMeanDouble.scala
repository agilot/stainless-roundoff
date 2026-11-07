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

object Moments {

  private[this] val STABILITY_CONSTANT = 0.1

  // Note from the authors: this is our own addition to avoid recursion
  @roundoff
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
