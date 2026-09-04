import stainless.annotation.*

object Deadband {

  /** One guard whose branches genuinely disagree at the boundary, so misreading it moves
    * the result by the whole threshold.
    */
  @roundoff
  def suppress(reading: Double, baseline: Double, threshold: Double): Double = {
    require(0.0 <= reading && reading <= 5.0)
    require(0.0 <= baseline && baseline <= 1.0)
    require(0.5 <= threshold && threshold <= 1.5)

    val deviation = reading - baseline

    if (deviation < threshold) 0.0 else deviation
  }
}
