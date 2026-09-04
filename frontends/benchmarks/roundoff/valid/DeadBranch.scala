import stainless.annotation.*

object DeadBranch {

  /** A branch the precondition already decides.
    *
    * The else leaf overflows on every input the precondition allows, so an analyzer asked
    * about it answers with an enormous error, and the worst rounding of the function is the
    * maximum over its leaves. Bounding a leaf no input reaches therefore does not merely cost
    * a query: it decides the answer. Asking whether a branch is taken before enumerating it
    * is what keeps `x * 0.1 + 0.2` the leaf the bound comes from.
    *
    * The obligation that the result is finite still holds, since the result is always the
    * then leaf, and establishing that is the same reasoning that refuses the else one.
    */
  @roundoff(1e-13)
  def scale(x: Double): Double = {
    require(0.0 <= x && x <= 1.0)

    if (x < 2.0) x * 0.1 + 0.2 else x * 1e300 * 1e300
  }

  /** A whole subtree the precondition decides, which is where asking pays.
    *
    * `10.0 < x` is refused under `x <= 1.0`, and the guard on `rate` sits below it, so one
    * question sets aside both of the leaves under it. Asking per leaf instead would ask about
    * the inner guard twice over and settle for the same answer.
    *
    * Under `--debug=solver` the questions arrive in preorder, and none of them mentions
    * `rate`: that is the subtree being cut rather than each of its leaves being refused.
    */
  @roundoff(1e-13)
  def tier(x: Double, rate: Double): Double = {
    require(0.0 <= x && x <= 1.0)
    require(0.5 <= rate && rate <= 2.0)

    if (x > 10.0) {
      if (rate < 1.0) x * 1e300 * 1e300 else x * rate * 1e300
    } else {
      x * rate + 0.5
    }
  }
}
