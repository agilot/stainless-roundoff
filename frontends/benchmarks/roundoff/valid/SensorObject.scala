import stainless.annotation.*

object SensorObject {

  /** The ranges are stated once, by the class, rather than at every function that takes one. */
  case class Sensor(reading: Double, gain: Double) {
    require(0.0 <= reading && reading <= 100.0 && 0.5 <= gain && gain <= 2.0)
  }

  /** A field of a parameter carries what a parameter carries, so it is read as one.
    *
    * The invariant is where the ranges come from: a function handed a `Sensor` is entitled to
    * what the class promises about it, and by the time the analysis runs that promise is not in
    * the function's own precondition but on the type.
    *
    * `scaled` below computes the same thing over the same ranges, written the other way. The two
    * bounds have to agree, and that agreement is the whole claim of reading fields as values.
    */
  @roundoff
  def scale(s: Sensor): Double = s.reading * s.gain

  @roundoff
  def scaled(reading: Double, gain: Double): Double = {
    require(0.0 <= reading && reading <= 100.0)
    require(0.5 <= gain && gain <= 2.0)

    reading * gain
  }
}
