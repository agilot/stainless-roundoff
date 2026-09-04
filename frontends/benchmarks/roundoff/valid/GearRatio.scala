import stainless.annotation.*

object GearRatio {

  /** A chain of five nested guards, which is the shape where every region holds one leaf
    * on each side and the two discontinuity schemes send the same queries.
    */
  @roundoff
  def ratio(speed: Double, load: Double): Double = {
    require(0.0 <= speed && speed <= 60.0)
    require(0.5 <= load && load <= 2.0)

    val demand = speed * load

    if (demand < 10.0) 3.545
    else if (demand < 25.0) 2.048
    else if (demand < 45.0) 1.386
    else if (demand < 70.0) 1.000
    else if (demand < 95.0) 0.815
    else 0.673
  }
}
