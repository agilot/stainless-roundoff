import stainless.annotation.*

object SoftThreshold {

  /** A helper that branches on its own. Inlining puts its guard into the caller's path
    * enumeration, so the caller ends up with four paths where it has no branch of its own.
    */
  private def shrink(value: Double, amount: Double): Double =
    if (value * value < amount) value * 0.1 else value - amount

  @roundoff
  def denoise(a: Double, b: Double, amount: Double): Double = {
    require(0.1 <= a && a <= 10.0)
    require(0.1 <= b && b <= 10.0)
    require(0.5 <= amount && amount <= 2.0)

    shrink(a, amount) + shrink(b, amount)
  }
}
