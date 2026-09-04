import stainless.annotation.*

object Piecewise {

  /** A tariff charged in bands, each band computing rather than returning a constant.
    *
    * `GearRatio` has this shape but answers with a literal in every band and branches on a
    * computed value; here each band does arithmetic and the thresholds are read off the input,
    * so every leaf is bounded over its own band rather than over the whole range.
    *
    * The band that reaches furthest is the last one, and nothing caps it, so the widest leaf is
    * the same either way and the reported figure does not move. What narrowing changes is every
    * other leaf, which is worth having the moment one of them becomes the widest.
    */
  @roundoff
  def charge(units: Double, rate: Double): Double = {
    require(0.0 <= units && units <= 5000.0)
    require(0.05 <= rate && rate <= 0.35)

    if (units < 100.0) units * rate
    else if (units < 500.0) 100.0 * rate + (units - 100.0) * rate * 0.9
    else 100.0 * rate + 400.0 * rate * 0.9 + (units - 500.0) * rate * 0.8
  }
}
