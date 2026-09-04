import stainless.lang.*

object FloatSpecComparisons {
  // `x` cannot be NaN under this precondition: if it were, `x >= 0.0` would be
  // false and the call would be rejected. So the precondition itself must not
  // give rise to a "Comparison with NaN" check.
  def requireOnly(x: Double): Double = {
    require(x >= 0.0d)
    x
  }

  // The precondition is still strong enough to discharge the NaN checks
  // of the (non-specification) body.
  def requireThenBody(x: Double): Boolean = {
    require(0.0d <= x && x <= 1.0d)
    x < 0.5d
  }

  def ensuringOnly(x: Float): Float = {
    require(x.isFinite)
    x
  }.ensuring(res => res == x)

  def assertOnly(x: Float, y: Float): Unit = {
    require(x == 1.0f && y == 2.0f)
    assert(x < y)
  }
}