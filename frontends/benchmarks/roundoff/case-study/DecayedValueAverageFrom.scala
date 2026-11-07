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

// Represents a decayed value that is decayed of the form:
// \sum_i e^{-(t_i - t)} v_i
// 2^{-(t/th)} = exp(ln(2)(-t/th)) = exp(-t * (ln(2)/th))
// So time is measured in units of (half-life/ln(2)), so.
// t in seconds, 1 day half life means: t => t * ln(2)/(86400.0)

object DecayedValue {

  // Note from the authors: changed bounded polymorphism V :< Numeric to Double
  def build(value: Double, time: Double, halfLife: Double): DecayedValue = {
    DecayedValue(value, time * math.log(2.0) / halfLife)
  }

  val zero: DecayedValue = DecayedValue(0.0, Double.NegativeInfinity)

  def scale(newv: DecayedValue, oldv: DecayedValue, eps: Double): DecayedValue = {
    val newValue = newv.value +
      math.exp(oldv.scaledTime - newv.scaledTime) * oldv.value
    if (math.abs(newValue) > eps) {
      DecayedValue(newValue, newv.scaledTime)
    } else {
      zero
    }
  }
}

case class DecayedValue(value: Double, scaledTime: Double) {

  /*
   * Moving average assuming the signal started at zero a fixed point in the past.
   * This normalizes by the integral of exp(-t(ln(2))/halflife) from 0 to (endTime - startTime).
   */
  @roundoff
  def averageFrom(halfLife: Double, startTime: Double, endTime: Double): Double =
    require(60 <= halfLife && halfLife <= 3600)
    require(0 <= startTime && startTime <= 86400)
    require(0 <= endTime && endTime <= 86400)
    require(0 <= scaledTime && scaledTime <= 1000)
    require(0 <= value && value <= 1e9)
    if (endTime > startTime) {
      val asOfEndTime =
        DecayedValue.scale(DecayedValue.build(0, endTime, halfLife), this, 0.0)
      val timeDelta = startTime - endTime
      val normalization = halfLife * (1 - math.pow(2, timeDelta / halfLife)) / math
        .log(2)
      asOfEndTime.value / normalization
    } else {
      0.0
    }
}