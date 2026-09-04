import stainless.annotation.*
import stainless.math.sqrt

object Normalise {

  private def component(v: Double, norm: Double): Double = v / norm

  /** The same helper is called twice with different arguments, so inlining has to bind
    * each call's parameters separately rather than sharing one name.
    */
  @roundoff
  def unitVector(x: Double, y: Double): Double = {
    require(1.0 <= x && x <= 10.0)
    require(1.0 <= y && y <= 10.0)

    val norm = sqrt(x * x + y * y)
    component(x, norm) + component(y, norm)
  }
}
