import stainless.annotation.*

object EqualityGuard {

  /** An equality between two inputs, which is decided exactly.
    *
    * Neither side rounds, so the band a divergence would live in has no width and the rounded
    * run takes the branch the exact one does. The figure here is the rounding of `(a + b) / 2`
    * and nothing else, which is the right answer and not a coincidence: an equality is only
    * ever misread where one of its sides was computed.
    */
  @roundoff
  def average(a: Double, b: Double): Double = {
    require(1.0 <= a && a <= 2.0 && 1.0 <= b && b <= 2.0)
    if (a == b) a else (a + b) / 2.0
  }

  /** An equality whose left side is computed, so it can be read the wrong way.
    *
    * Where `a * b` and `c` are within the error of the product, a run may answer `c` where the
    * exact one answers the product, or the other way about. The two branches agree on the
    * boundary, so the divergence is the width of that band rather than a jump — and the
    * objective is the guard's own difference, so it is read off rather than searched for.
    */
  @roundoff
  def matched(a: Double, b: Double, c: Double): Double = {
    require(1.0 <= a && a <= 2.0 && 1.0 <= b && b <= 2.0 && 1.0 <= c && c <= 4.0)
    if (a * b == c) c else a * b
  }

  /** The same guard the other way up, which is the same two regions with the branches swapped. */
  @roundoff
  def unmatched(a: Double, b: Double, c: Double): Double = {
    require(1.0 <= a && a <= 2.0 && 1.0 <= b && b <= 2.0 && 1.0 <= c && c <= 4.0)
    if (a * b != c) a * b else c
  }

  /** An equality whose branches disagree on it, so the divergence is a jump and not a width.
    *
    * `x + y` against `x - y` is `2y` apart wherever the product lands on 4, so the figure is a
    * jump rather than anything near an ulp. It comes out at 8 and not at 20, because the guard
    * itself caps `y`: with `x` at least 1 and the product 4, `y` cannot pass 4. This is the case
    * an equality guard is usually written for — a value singled out and handled apart — and the
    * one where reading the guard the wrong way costs the most.
    */
  @roundoff
  def select(x: Double, y: Double): Double = {
    require(1.0 <= x && x <= 10.0)
    require(1.0 <= y && y <= 10.0)

    if (x * y == 4.0) x + y else x - y
  }
}
