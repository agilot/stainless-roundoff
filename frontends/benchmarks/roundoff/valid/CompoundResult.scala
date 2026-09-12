import stainless.annotation.*

object CompoundResult {

  case class Reading(value: Double, confidence: Double)

  /** A result of two numbers, each answered about on its own.
    *
    * Both are computed by the same branches, so the guards, the questions asked about which of
    * them a run takes, and the errors of their operands are worked out once for the function;
    * only the leaves are read a field at a time.
    *
    * The two answers differ in kind, which is why one figure for the pair would say nothing.
    * `value` is the same expression either side of the guard, so crossing it costs nothing and
    * what is left is the rounding of a sum. `confidence` steps from a half to one, and a run
    * that reads `strength < 4.0` the wrong way returns the wrong one of those, so its figure is
    * the whole of that step.
    */
  @roundoff
  def reading(x: Double, y: Double): Reading = {
    require(1.0 <= x && x <= 4.0)
    require(1.0 <= y && y <= 4.0)

    val strength = x * y
    if (strength < 4.0) Reading(x + y, 0.5) else Reading(x + y, 1.0)
  }

  /** The same result written as a tuple, whose fields are `_1` and `_2`. */
  @roundoff
  def pair(x: Double, y: Double): (Double, Double) = {
    require(1.0 <= x && x <= 4.0)
    require(1.0 <= y && y <= 4.0)

    val strength = x * y
    if (strength < 4.0) (x + y, 0.5) else (x + y, 1.0)
  }

  case class Span(low: Reading, high: Double)

  /** Taking apart goes as deep as the type does, so the fields here are `low.value`,
    * `low.confidence` and `high`. A field that is not a number — the flag — is passed over
    * rather than refused, since nothing about it is a roundoff error.
    */
  case class Tagged(reading: Reading, flag: Boolean)

  @roundoff
  def span(x: Double, y: Double): Span = {
    require(1.0 <= x && x <= 4.0)
    require(1.0 <= y && y <= 4.0)

    Span(Reading(x * y, x / y), x - y)
  }

  @roundoff
  def tagged(x: Double, y: Double): Tagged = {
    require(1.0 <= x && x <= 4.0)
    require(1.0 <= y && y <= 4.0)

    Tagged(Reading(x * y, x + y), x <= y)
  }
}
