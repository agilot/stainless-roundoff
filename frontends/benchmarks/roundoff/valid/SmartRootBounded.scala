import stainless.annotation.*
import stainless.math.sqrt

object SmartRootBounded {

  /** The root of a quadratic, taken through whichever expression is stable for the sign of
    * `b`, which here is a constant so only one of the three branches is ever run.
    *
    * `c <= 1.0125` replaces the `c <= 2.0` of `unsupported/SmartRoot`, and says the same
    * thing as the discriminant constraint beside it, which admits exactly `c < 1.0125`. It
    * has to replace that bound rather than join it, because bounds on one side of one input
    * are intersected and the loosest is the one that would otherwise be kept.
    */
  @roundoff
  def smartRoot(c: Double): Double = {
    require(-2.0 <= c && c <= 1.0125 && 3.5 * 3.5 - 3.0 * c * 4.0 > 0.1)
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
