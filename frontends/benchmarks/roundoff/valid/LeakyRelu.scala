import stainless.annotation.*

object LeakyRelu {

  /** One guard whose two branches meet at the boundary, so crossing it moves the result by
    * almost nothing and the reported error is dominated by rounding.
    *
    * The guard compares a computed value against a literal. Were it a bare input instead,
    * both sides would round exactly under `--roundoff-exact-inputs=true`, the two programs
    * could never read it differently, and there would be no divergence to bound at all.
    */
  @roundoff
  def activate(x: Double, bias: Double, slope: Double): Double = {
    require(-10.0 <= x && x <= 10.0)
    require(-1.0 <= bias && bias <= 1.0)
    require(0.001 <= slope && slope <= 0.1)

    val excitation = x - bias

    if (excitation < 0.0) slope * excitation else excitation
  }
}
