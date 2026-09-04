import stainless.annotation.*

object SharedIntermediate {

  /** One binding is read by the guard and by both branches, so every path has to carry it
    * back into the expression the analyzer is given.
    */
  @roundoff
  def power(voltage: Double, current: Double, limit: Double): Double = {
    require(200.0 <= voltage && voltage <= 250.0)
    require(0.1 <= current && current <= 16.0)
    require(1000.0 <= limit && limit <= 3000.0)

    val apparent = voltage * current

    if (apparent < limit) apparent * 0.95
    else limit * 0.95 + (apparent - limit) * 0.5
  }
}
