import stainless.annotation.*

object JumpTooLarge {

  /** The rounding here is nothing, but misreading the guard moves the result by the whole
    * step, so the bound has to account for the discontinuity rather than the rounding.
    */
  @roundoff(1e-10)
  def step(x: Double, threshold: Double): Double = {
    require(0.0 <= x && x <= 10.0)
    require(1.0 <= threshold && threshold <= 5.0)

    val load = x * 1.5

    if (load < threshold) 0.0 else 100.0
  }
}
