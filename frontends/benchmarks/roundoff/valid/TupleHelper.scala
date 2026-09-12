import stainless.annotation.*

object TupleHelper {

  private def polar(x: Double, y: Double): (Double, Double) = (x * x + y * y, y / x)

  /** A tuple-returning callee inlines to a constructor read back by a selector.
    *
    * The selector is pushed down the bindings and the branches until it meets the constructor,
    * and what is left is the field's own computation — the same fold that projects a result
    * onto one of its numbers, here with the projection written in the source.
    */
  @roundoff
  def radius(x: Double, y: Double): Double = {
    require(1.0 <= x && x <= 10.0)
    require(1.0 <= y && y <= 10.0)

    polar(x, y)._1
  }
}
