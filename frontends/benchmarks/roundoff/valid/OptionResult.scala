import stainless.annotation.*
import stainless.lang.*

object OptionResult {

  /** A ratio that is only given when the divisor is large enough.
    *
    * The guard compares an input with a literal. With exact inputs both runs read it the same
    * way and always end in the same case; with rounded inputs they can disagree just around
    * `y = 0.5`. The error of `Some.v` is about the one path that returns `Some`.
    */
  @roundoff
  def safeRatio(x: Double, y: Double): Option[Double] = {
    require(0.0 <= x && x <= 10.0 && 0.0 <= y && y <= 10.0)
    if (y > 0.5) Some(x / y) else None[Double]()
  }

  /** The next level of a tank, or nothing when it overflows.
    *
    * The overflow test is on a computed value, so the two runs can end in different cases
    * near `next = 100`. Between the two `Some` leaves, the jump at `next < 10` is tiny, since
    * both sides equal 10 there; the `None` leaf is not part of that error.
    */
  @roundoff
  def tank(level: Double, inflow: Double): Option[Double] = {
    require(0.0 <= level && level <= 100.0 && -5.0 <= inflow && inflow <= 5.0)
    val next = level + inflow * 0.1
    if (next > 100.0) None[Double]()
    else if (next < 10.0) Some(10.0)
    else Some(next)
  }
}
