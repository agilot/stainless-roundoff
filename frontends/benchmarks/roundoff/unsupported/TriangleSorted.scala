import stainless.annotation.*
import stainless.math.sqrt

object TriangleSorted {

  /** Heron's formula is real only because the three sides make a triangle, and that is what
    * the three inequalities say. They relate three inputs, so unlike `SmartRoot` there is no
    * bound on any one input to write instead: over the box alone `a - (c - b)` runs from
    * `1 - 9 + 1` to `9 - 1 + 9`, the product under the root can be negative, and the analyzer
    * is asked for the square root of an interval that straddles zero.
    *
    * A box narrow enough to make every factor positive on its own is a different problem
    * rather than a restatement of this one; `valid/TriangleSortedNarrow` is that problem.
    */
  @roundoff
  def triangleSorted(a: Double, b: Double, c: Double): Double = {
    require(1.0 <= a && a <= 9.0 && 1.0 <= b && b <= 9.0 && 1.0 <= c && c <= 9.0 &&
      a + b > c + 1e-6 && a + c > b + 1e-6 && b + c > a + 1e-6 &&
      a < c && b < c)
    if (a < b)
      sqrt((c + (b + a)) * (a - (c - b)) * (a + (c - b)) * (c + (b - a))) / 4.0
    else
      sqrt((c + (a + b)) * (b - (c - a)) * (b + (c - a)) * (c + (a - b))) / 4.0
  }
}
