import stainless.annotation.*
import stainless.math.sqrt

object SmartRoot {

  /** The discriminant is positive exactly where the precondition says it is, but the range
    * reader only takes a bound from a comparison between an input and a literal, and
    * `3.5 * 3.5 - 3.0 * c * 4.0 > 0.1` is a comparison between a computed value and one.
    * So `c` keeps the range `[-2, 2]` it is given directly, `discr` comes out as
    * `[-11.75, 36.25]`, and the analyzer is asked for the square root of an interval that
    * straddles zero.
    *
    * What the precondition means is `c < 1.0125`. Writing that as well is not enough: it has
    * to replace `c <= 2.0` rather than join it, since two bounds on one side of one input are
    * intersected and `c <= 2.0` is the one the constraint is about. `valid/SmartRootBounded`
    * is the same function with that substitution made.
    */
  @roundoff
  def smartRoot(c: Double): Double = {
    require(-2.0 <= c && c <= 2.0 && 3.5 * 3.5 - 3.0 * c * 4.0 > 0.1)
    val a: Double = 3.0
    val b: Double = 3.5
    val discr = b * b - a * c * 4.0
    if (b * b - a * c > 10.0) {
      if (b > 0.0) c * 2.0 / (-b - sqrt(discr))
      else if (b < 0.0) (-b + sqrt(discr)) / (a * 2.0)
      else (-b + sqrt(discr)) / (a * 2.0)
    } else {
      (-b + sqrt(discr)) / (a * 2.0)
    }
  }
}
