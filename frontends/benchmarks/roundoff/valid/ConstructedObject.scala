import stainless.annotation.*

object ConstructedObject {

  case class Pair(first: Double, second: Double)

  private def split(v: Double): Pair = Pair(v * 0.5, v * 0.25)

  /** An object built inside the body and read back, the case-class counterpart of
    * `TupleHelper.scala`.
    *
    * Nothing has to bound the object: a field read off something the body built is followed to
    * whatever the constructor was given, so what is measured is `v * 0.5` and the `Pair` is
    * never a value the analysis has to hold a range for.
    */
  @roundoff
  def half(v: Double): Double = {
    require(1.0 <= v && v <= 10.0)

    split(v).first
  }
}
