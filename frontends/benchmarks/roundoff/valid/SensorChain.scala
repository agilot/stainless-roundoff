import stainless.annotation.*

object SensorChain {

  private def toVolts(raw: Double): Double = raw * 3.3 / 4096.0
  private def toCelsius(volts: Double): Double = (volts - 0.5) * 100.0
  private def calibrated(raw: Double, offset: Double): Double = toCelsius(toVolts(raw)) + offset

  /** A helper calling a helper calling a helper, so inlining has to recurse into a body it
    * has already substituted.
    */
  @roundoff
  def reading(raw: Double, offset: Double): Double = {
    require(0.0 <= raw && raw <= 4095.0)
    require(-2.0 <= offset && offset <= 2.0)

    calibrated(raw, offset)
  }
}
