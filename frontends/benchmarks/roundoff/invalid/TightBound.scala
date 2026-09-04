import stainless.annotation.*

object TightBound {

  /** The bound is smaller than a single rounding of this expression, so the obligation
    * fails and the checker reports the error it inferred against the bound asked for.
    */
  @roundoff(1e-18)
  def mix(a: Double, b: Double, weight: Double): Double = {
    require(-10.0 <= a && a <= 10.0)
    require(-10.0 <= b && b <= 10.0)
    require(0.0 <= weight && weight <= 1.0)

    a * weight + b * (1.0 - weight)
  }
}
