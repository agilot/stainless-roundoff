import stainless.annotation.*

object ObjectHelper {

  case class Point(x: Double, y: Double) {
    require(1.0 <= x && x <= 10.0 && 1.0 <= y && y <= 10.0)
  }

  private def norm(p: Point): Double = p.x * p.x + p.y * p.y

  /** A helper taking the object, called twice.
    *
    * Inlining binds a callee's argument rather than substituting it, so the body of `norm` reads
    * its own name for the point it was handed. Both readings have to come back to the point the
    * caller passed: were `p.x` inside the helper a different value from `a.x` outside it, the
    * analysis would be free to believe the two can differ, and the bound would be wrong rather
    * than merely loose.
    */
  @roundoff
  @fuzz
  def spread(a: Point, b: Point): Double = norm(a) - norm(b)
}
