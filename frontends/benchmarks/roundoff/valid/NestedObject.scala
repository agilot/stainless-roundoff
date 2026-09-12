import stainless.annotation.*

object NestedObject {

  case class Calibration(offset: Double) {
    require(-1.0 <= offset && offset <= 1.0)
  }

  case class Sensor(raw: Double, cal: Calibration) {
    require(0.0 <= raw && raw <= 100.0)
  }

  /** A field of a field, so the reading is reached through two objects rather than one.
    *
    * Each object promises something about itself and neither knows the other, so the range for
    * `cal.offset` can only come from `Calibration`. Both are asked, along the path actually read.
    *
    * The guard compares a field against a literal, which is the shape that narrows a leaf's
    * ranges, so a leaf below it is bounded over the band it runs on rather than the whole of it.
    */
  @roundoff
  def reading(s: Sensor): Double =
    if (s.raw < 10.0) s.raw * 0.5 + s.cal.offset
    else s.raw + s.cal.offset
}
