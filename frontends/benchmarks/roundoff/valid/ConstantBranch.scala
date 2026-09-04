import stainless.annotation.*

object ConstantBranch {

  private def floorAt(value: Double, limit: Double): Double =
    if (value * value < limit) 0.0 else value - limit

  /** Both calls can take their first branch at once, and that path's leaf is `0.0 + 0.0`:
    * arithmetic with no input left in it.
    *
    * The analyzer is given one query per leaf and needs at least one bounded input to
    * answer, so such a leaf is worked out directly instead of being sent. Here it happens
    * to be exact, and the reported error comes from the other three paths.
    *
    * Inlining is what makes this ordinary: a helper returning a constant in one branch is
    * everyday code, and the two literals only meet once the calls are substituted.
    */
  @roundoff
  def denoise(a: Double, b: Double, limit: Double): Double = {
    require(0.1 <= a && a <= 10.0)
    require(0.1 <= b && b <= 10.0)
    require(0.5 <= limit && limit <= 2.0)

    floorAt(a, limit) + floorAt(b, limit)
  }
}
