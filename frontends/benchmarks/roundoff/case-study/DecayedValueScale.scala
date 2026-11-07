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
  val zero: DecayedValue = DecayedValue(0.0, Double.NegativeInfinity)

  @roundoff
  def scale(newv: DecayedValue, oldv: DecayedValue, eps: Double): DecayedValue = {
    require(0 <= newv.value && newv.value <= 1e9)
    require(0 <= oldv.value && oldv.value <= 1e9)
    require(0 <= newv.scaledTime && newv.scaledTime <= 1000)
    require(0 <= oldv.scaledTime && oldv.scaledTime <= 1000)
    require(newv.scaledTime >= oldv.scaledTime)
    require(0 <= eps && eps <= 1e-9)
    val newValue = newv.value +
      math.exp(oldv.scaledTime - newv.scaledTime) * oldv.value
    if (math.abs(newValue) > eps) {
      DecayedValue(newValue, newv.scaledTime)
    } else {
      zero
    }
  }
}


case class DecayedValue(value: Double, scaledTime: Double)