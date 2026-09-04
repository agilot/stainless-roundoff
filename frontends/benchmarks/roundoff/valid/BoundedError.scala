import stainless.annotation.*

object BoundedError {

  /** The annotation carries a bound, and the obligation holds because the inferred error
    * comes in under it.
    */
  @roundoff(1e-12)
  def mix(a: Double, b: Double, weight: Double): Double = {
    require(-10.0 <= a && a <= 10.0)
    require(-10.0 <= b && b <= 10.0)
    require(0.0 <= weight && weight <= 1.0)

    a * weight + b * (1.0 - weight)
  }
}
