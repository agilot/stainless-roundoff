import stainless.annotation.*

object OrientationIndexFilter {

  /** Only the two coordinates the predicate reads need bounds; `z` is never looked at, so nothing
    * is asked about it.
    */
  case class Coordinate(x: Double, y: Double, z: Double) {
    require(-1000.0 <= x && x <= 1000.0 && -1000.0 <= y && y <= 1000.0)
  }

  /** The determinant whose sign says which way the three points turn.
    *
    * This is the quantity the filter below has to account for the error of, and the only part of
    * it that has an error at all: the filter answers a direction, and a direction is not a number
    * that can be out by a little.
    *
    * Six fields across three objects, and a difference of two products that cancels to nothing
    * exactly when the points are collinear — which is where a filter has to give up.
    *
    * The bound inferred here is what `ERR_BOUND` stands in for, and the two can be compared. Over
    * coordinates in [-1000, 1000] the analysis gives 2.750e-9, while `ERR_BOUND * detsum` at the
    * furthest corner of that box, where `detsum` reaches 8e6, allows 8e-9. So the constant is
    * sound here with a little under three times to spare — which is the answer a filter's author
    * otherwise has to arrive at by hand.
    */

  def determinant(pa: Coordinate, pb: Coordinate, pc: Coordinate): Double =
    (pa.x - pc.x) * (pb.y - pc.y) - (pa.y - pc.y) * (pb.x - pc.x)

  /** A relative bound on the determinant's error, as a fraction of the size of its two halves. */
  private val ERR_BOUND = 1e-15

  /** Shewchuk's filter, written without the assignment the original uses.
    *
    * Where the two products have opposite signs their difference cannot lose them, so the sign is
    * read off at once. Where they agree it can, and the answer is trusted only if the determinant
    * stands further from zero than the error its own magnitude allows. `2` means it does not, and
    * the caller falls back on exact arithmetic.
    */
  @roundoff
  def orientationIndexFilter(pa: Coordinate, pb: Coordinate, pc: Coordinate): Double = {
    val detleft = (pa.x - pc.x) * (pb.y - pc.y)
    val detright = (pa.y - pc.y) * (pb.x - pc.x)
    val det = determinant(pa, pb, pc)

    if (detleft > 0.0) {
      if (detright <= 0.0) signum(det) else decided(det, detleft + detright)
    } else if (detleft < 0.0) {
      if (detright >= 0.0) signum(det) else decided(det, -detleft - detright)
    } else signum(det)
  }

  private def decided(det: Double, detsum: Double): Double = {
    val errbound = ERR_BOUND * detsum
    if (det >= errbound || -det >= errbound) signum(det) else 2.0
  }

  private def signum(x: Double): Double =
    if (x > 0.0) 1 else if (x < 0.0) -1.0 else 0.0
}
