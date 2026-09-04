import stainless.annotation.*

object SinglePrecision {

  /** The same shape in single precision, which the rest of the suite never asks about.
    *
    * A float rounds about eight decimal digits earlier than a double, so the bound here should
    * come out around 1e-7 where its double counterpart lands near 1e-16. It is also the only
    * benchmark that sends the analyzer a batch at a precision other than `Float64`, since that
    * setting is fixed for one invocation and each precision is therefore its own batch.
    */
  @roundoff
  def mix(a: Float, b: Float, weight: Float): Float = {
    require(0.0f <= a && a <= 100.0f)
    require(0.0f <= b && b <= 100.0f)
    require(0.0f <= weight && weight <= 1.0f)

    a * weight + b * (1.0f - weight)
  }
}
