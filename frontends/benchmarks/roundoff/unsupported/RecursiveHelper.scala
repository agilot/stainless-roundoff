import stainless.annotation.*
import stainless.lang.*

object RecursiveHelper {

  private def halve(value: Double, steps: BigInt): Double = {
    require(steps >= 0)
    decreases(steps)
    if (steps <= 0) value else halve(value * 0.5, steps - 1)
  }

  /** Inlining a recursive callee reaches no finite body, so the obligation is reported as
    * unsupported with the function named.
    */
  @roundoff
  def attenuate(signal: Double): Double = {
    require(1.0 <= signal && signal <= 100.0)

    halve(signal, 4)
  }
}
