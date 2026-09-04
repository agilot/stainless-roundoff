import stainless.annotation.*

object Interpolate {

  /** Smoothstep between two edges.
    *
    * A guard built from `&&` is the nesting it stands for, and the path enumeration writes
    * it out that way so every path condition stays a conjunction the solver can take.
    */
  @roundoff
  def smoothstep(x: Double, low: Double, high: Double): Double = {
    require(0.0 <= x && x <= 100.0)
    require(10.0 <= low && low <= 30.0)
    require(60.0 <= high && high <= 90.0)

    val position = (x - low) / (high - low)

    if (0.0 < position && position < 1.0) position * position * (3.0 - 2.0 * position)
    else if (position <= 0.0) 0.0
    else 1.0
  }
}
