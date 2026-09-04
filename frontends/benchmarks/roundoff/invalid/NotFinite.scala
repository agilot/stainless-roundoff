import stainless.annotation.*
import stainless.math.sqrt

object NotFinite {

  /** A root of a value that can be negative, so the result can be NaN.
    *
    * A roundoff bound says how far a result sits from the exact one, which says nothing at
    * all about a result that is not a number. The finiteness obligation is what reports that,
    * and it reports it with the input that does it.
    *
    * The bound itself is a separate obligation and the two are checked side by side, so the
    * roundoff row still says whatever the analysis made of the function: here the analyzer is
    * asked about `sqrt` over a range reaching below zero, and answers nothing useful.
    */
  @roundoff(1e-13)
  def magnitude(x: Double): Double = {
    require(-1.0 <= x && x <= 1.0)

    sqrt(x)
  }

  /** A product that overflows over part of its box, so the result can be an infinity.
    *
    * Every input here is finite and so is every intermediate value; it is the one
    * multiplication that leaves the range doubles can hold.
    */
  @roundoff(1e-13)
  def amplify(x: Double, gain: Double): Double = {
    require(1e150 <= x && x <= 1e200)
    require(1e150 <= gain && gain <= 1e200)

    x * gain
  }
}
