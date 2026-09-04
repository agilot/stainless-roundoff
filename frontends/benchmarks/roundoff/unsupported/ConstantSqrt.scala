import stainless.annotation.*
import stainless.math.sqrt

object ConstantSqrt {

  private def diagonal(side: Double): Double = sqrt(side * side + side * side)

  /** A value with no inputs left in it is worked out as a fraction, and a square root is
    * not one. The leaf `sqrt(2.0 * 2.0 + 2.0 * 2.0)` is therefore refused by name rather
    * than answered, which is what the analysis did with every such leaf before.
    *
    * Bounding it would mean evaluating the root to high precision with the rounding
    * directed outwards, which is a larger and more delicate piece of work than the
    * arithmetic case and is not done here.
    */
  @roundoff
  def clearance(width: Double, standard: Double): Double = {
    require(1.0 <= width && width <= 10.0)
    require(0.0 <= standard && standard <= 1.0)

    if (standard < 0.5) diagonal(2.0) else width
  }
}
