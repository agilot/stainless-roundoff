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

  /**
   * Scale all the moments by a constant. This allows you to use Moments with exponential decay
   */
  @roundoff
  def scale(z: Double): Moments =
    require(0 <= z && z <= 1)
    require(1 <= m0D && m0D <= 1e6)
    require(0 <= m1 && m1 <= 1000)
    require(0 <= m2 && m2 <= 2.5e11)
    require(-1e14 <= m3 && m3 <= 1e14)
    require(0 <= m4 && m4 <= 1e17)
    if (z == 0) {
      // Note from the authors: remove implicit value
      MomentsMonoid.zero
    } else
      new Moments(m0D = z * m0D, m1 = m1, m2 = z * m2, m3 = z * m3, m4 = z * m4)
}

// Note from the authors: port to Scala 3
object MomentsMonoid {
  val zero: Moments = new Moments(0.0, 0.0, 0.0, 0.0, 0.0)
}
