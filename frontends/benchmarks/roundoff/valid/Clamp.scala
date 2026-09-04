import stainless.annotation.*
import stainless.math.{abs, max, min}

object Clamp {

  /** `abs`, `min` and `max` are conditionals in disguise, and the analysis unfolds them
    * into the branches they stand for before enumerating paths.
    */
  @roundoff
  def limitedError(measured: Double, expected: Double, tolerance: Double): Double = {
    require(-100.0 <= measured && measured <= 100.0)
    require(-100.0 <= expected && expected <= 100.0)
    require(0.1 <= tolerance && tolerance <= 5.0)

    val error = abs(measured - expected)
    min(max(error, tolerance), 10.0 * tolerance)
  }
}
