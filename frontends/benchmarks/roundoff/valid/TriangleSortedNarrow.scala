import stainless.annotation.*
import stainless.math.sqrt

object TriangleSortedNarrow {

  /** The area of a triangle by Heron's formula, over sides narrow enough that every factor
    * under the root is positive on the box alone: `a + b` is at least ten where `c` is at
    * most nine. `unsupported/TriangleSorted` is the same formula over `[1, 9]`, where only
    * the inequalities keep the product positive and the analyzer cannot read them.
    *
    * The two branches compute the same real number — the factors are the same four, in a
    * different order — so what a misread guard costs is rounding rather than a step. Under
    * `--roundoff-exact-inputs=false` the guard `a < b` becomes crossable and the bound is
    * the width of the result rather than its last digits, because the two branches are not
    * recognised as equal.
    */
  @roundoff
  def triangleSorted(a: Double, b: Double, c: Double): Double = {
    require(5.0 <= a && a <= 8.0 && 5.0 <= b && b <= 8.0 && 5.0 <= c && c <= 9.0 &&
      a + b > c + 1e-6 && a + c > b + 1e-6 && b + c > a + 1e-6 &&
      a < c && b < c)
    if (a < b)
      sqrt((c + (b + a)) * (a - (c - b)) * (a + (c - b)) * (c + (b - a))) / 4.0
    else
      sqrt((c + (a + b)) * (b - (c - a)) * (b + (c - a)) * (c + (a - b))) / 4.0
  }
}
