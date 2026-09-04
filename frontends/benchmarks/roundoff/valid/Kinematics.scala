import stainless.annotation.*

object Kinematics {

  /** Displacement under constant acceleration, with no branch to take. */
  @roundoff
  def displacement(v0: Double, a: Double, t: Double): Double = {
    require(0.0 <= v0 && v0 <= 50.0)
    require(-10.0 <= a && a <= 10.0)
    require(0.0 <= t && t <= 20.0)

    v0 * t + 0.5 * a * t * t
  }
}
