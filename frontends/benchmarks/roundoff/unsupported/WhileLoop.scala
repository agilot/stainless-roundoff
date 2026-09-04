import stainless.annotation.*
import stainless.lang.*

object WhileLoop {

  /** A `while` loop is lifted into a recursive function before verification runs, so it
    * reaches the analysis as a recursive call and is refused as one. Bounding a loop needs
    * either a trip count or the analyzer's own loop support.
    */
  @roundoff
  def decay(start: Double): Double = {
    require(1.0 <= start && start <= 100.0)

    var value = start
    while (value > 1.0) {
      decreases(value)
      value = value / 2.0
    }
    value
  }
}
