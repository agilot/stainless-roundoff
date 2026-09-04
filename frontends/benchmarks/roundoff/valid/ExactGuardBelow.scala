import stainless.annotation.*

object ExactGuardBelow {

  /** Under `--roundoff-exact-inputs=true` a guard comparing an input against a literal
    * rounds exactly, so both programs read it the same way and no divergence can start
    * there. That is a reason to drop a divergence only when it is the guard being crossed.
    *
    * Here the crossing is at the outer guard, whose two sides are computed and so carry
    * error. The exactly-rounded `mode` guard sits *below* it on both sides, where the
    * rounded run simply takes it for real. Treating that as a reason to refuse the
    * divergence discards every crossing of the outer guard in both directions, and the
    * function is then reported as rounding alone: about 5e-15 in place of 34.
    */
  @roundoff
  def tariff(usage: Double, allowance: Double, mode: Double): Double = {
    require(1.0 <= usage && usage <= 20.0)
    require(1.0 <= allowance && allowance <= 20.0)
    require(0.0 <= mode && mode <= 1.0)

    if (usage * 1.5 < allowance * 1.5) {
      if (mode < 0.5) usage * 0.10 else usage * 0.12
    } else {
      if (mode < 0.5) usage * 0.40 + 12.0 else usage * 0.55 + 25.0
    }
  }
}
