import stainless.annotation.*

object ComputedGuard {

  /** Both sides of the guard are computed, so the width of the band where the two programs
    * can disagree is the sum of two analyzer results rather than one.
    */
  @roundoff
  def crossover(x: Double, y: Double, z: Double): Double = {
    require(0.5 <= x && x <= 4.0)
    require(0.5 <= y && y <= 4.0)
    require(0.5 <= z && z <= 4.0)

    if (x * y + z < y * z + x) x * x + y
    else y * y + z
  }
}
