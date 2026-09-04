import stainless.annotation.*

object Saturate {

  /** A reading clamped before it is scaled, which is what a sensor front end does.
    *
    * The guard holds `reading` under 100 on the branch that computes anything, so that leaf
    * never runs on the rest of the range. Told only the precondition, the analyzer bounds
    * `reading * gain` over the whole of `[0, 1000000]` and answers about a result near 1.1e6;
    * told the guard as well, it answers about a result near 110, and the bound falls by about
    * four orders of magnitude.
    *
    * The guard compares an input against a literal, so under `--roundoff-exact-inputs=true` both
    * sides round exactly and no divergence can start there. The bound is rounding alone, which
    * is what makes this the case where narrowing a leaf's ranges is visible in the answer rather
    * than fifteen orders below it.
    */
  @roundoff
  def clampedGain(reading: Double, gain: Double): Double = {
    require(0.0 <= reading && reading <= 1000000.0)
    require(0.9 <= gain && gain <= 1.1)

    if (reading > 100.0) 110.0 else reading * gain
  }
}
