import stainless.annotation.*

object TupleHelper {

  private def polar(x: Double, y: Double): (Double, Double) = (x * x + y * y, y / x)

  /** A tuple-returning callee inlines to a constructor read back by a selector, which the
    * analysis has no floating-point meaning for. Handling tuples properly is separate work.
    */
  @roundoff
  def radius(x: Double, y: Double): Double = {
    require(1.0 <= x && x <= 10.0)
    require(1.0 <= y && y <= 10.0)

    polar(x, y)._1
  }
}
