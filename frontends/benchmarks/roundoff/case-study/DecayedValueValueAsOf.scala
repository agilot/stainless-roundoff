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

case class DecayedValueMonoid(eps: Double) {
  val zero: DecayedValue = DecayedValue(0.0, Double.NegativeInfinity)

  def plus(left: DecayedValue, right: DecayedValue): DecayedValue =
    if (left.scaledTime < right.scaledTime) {
      // left is older:
      DecayedValue.scale(right, left, eps)
    } else {
      // right is older
      DecayedValue.scale(left, right, eps)
    }

  @roundoff
  // Returns value if timestamp is less than value's timestamp
  def valueAsOf(value: DecayedValue, halfLife: Double, timestamp: Double): Double =
    require(0 <= value.value && value.value <= 1e9)
    require(0 <= value.scaledTime && value.scaledTime <= 1000)
    require(60 <= halfLife && halfLife <= 3600)
    require(0 <= timestamp && timestamp <= 86400)
    require(0 <= eps && eps <= 1e-9)
    plus(DecayedValue.build(0, timestamp, halfLife), value).value
}

case class DecayedValue(value: Double, scaledTime: Double)