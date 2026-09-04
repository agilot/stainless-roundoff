import stainless.annotation.*

object EqualityGuard {

  /** An equality guard marks no region two paths can be compared over, since the set where
    * it holds has no width for the solver to search.
    */
  @roundoff
  def select(x: Double, y: Double): Double = {
    require(1.0 <= x && x <= 10.0)
    require(1.0 <= y && y <= 10.0)

    if (x * y == 4.0) x + y else x - y
  }
}
