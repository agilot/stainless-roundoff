// AnimateBy.update adapted from outr/youi (MIT License)
// Source: https://github.com/outr/youi/blob/6c81b1262569cdaba4e81681362d909022fe3a8e/ui/shared/src/main/scala/io/youi/task/AnimateBy.scala#L7
package io.youi.task

import stainless.annotation.*

sealed trait Conclusion

object Conclusion {
  case object Continue extends Conclusion
  case object Finished extends Conclusion
}

case class AnimateBy(stepBy: Double,
                     get: Double,
                     destination: Double) {
  @roundoff
  def update(delta: Double, reset: Boolean): (Conclusion, Double) = {
    require(0.0 <= stepBy && stepBy <= 1000.0)
    require(-10000.0 <= get && get <= 10000.0)
    require(-10000.0 <= destination && destination <= 10000.0)
    require(0.0 <= delta && delta <= 1.0)
    val current = get
    val end = destination
    val step = delta * stepBy
    if (current < end) {
      val value = current + step
      if (value > end) {
        (Conclusion.Finished, end)
      } else {
        (Conclusion.Continue, value)
      }
    } else {
      val value = current - step
      if (value < end) {
        (Conclusion.Finished, end)
      } else {
        (Conclusion.Continue, value)
      }
    }
  }
}
