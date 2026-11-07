// Circular.easeInOut adapted from outr/youi (MIT License)
// Source: https://github.com/outr/youi/blob/6c81b1262569cdaba4e81681362d909022fe3a8e/ui/shared/src/main/scala/io/youi/easing/Easing.scala#L131
package io.youi.easing

import stainless.math
import stainless.annotation.*

object Circular {
  @roundoff
  def easeInOut(time: Double, start: Double, change: Double, duration: Double): Double = {
    require(0.0 <= time && time <= 1.0)
    require(0.0 <= start && start <= 0.0)
    require(1.0 <= change && change <= 1.0)
    require(1.0 <= duration && duration <= 1.0)
    val t = time / (duration / 2)
    if (t < 1) {
      -change / 2.0 * (math.sqrt(1.0 - t * t) - 1.0) + start
    } else {
      val t2 = t - 2.0
      change / 2.0 * (math.sqrt(1.0 - t2 * t2) + 1.0) + start
    }
  }
}
