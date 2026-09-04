import stainless.annotation.*

object MissingRange {

  /** `drift` is bounded on one side only, and a half-open range is no more usable than a
    * missing one, so the checker names the input that needs bounds.
    */
  @roundoff
  def corrected(reading: Double, drift: Double): Double = {
    require(0.0 <= reading && reading <= 100.0)
    require(0.0 <= drift)

    reading - drift
  }
}
