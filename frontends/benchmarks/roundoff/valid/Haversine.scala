import stainless.annotation.*
import stainless.math.{asin, cos, sin, sqrt}

object Haversine {

  /** Great-circle distance in kilometres.
    *
    * The analysis reads `sin`, `cos`, `asin` and `sqrt` as the exact functions the library
    * approximates, rather than inlining their implementations.
    *
    * The two points are kept in separate quadrants so that both half-differences stay
    * positive. Straddling zero would let the interval for `sin(h) * sin(h)` reach below it,
    * and the analyzer would then refuse the square root.
    *
    * Its finiteness obligation is reported invalid, and that is a limit of the library rather
    * than of this function. `sin` promises a result in `[-1, 1]` and no identity beyond that,
    * so `chord` may be as large as 2 as far as a solver can tell, and `asin` of a root above
    * one is NaN by its own postcondition. The haversine identity that keeps `chord` below one
    * is nowhere in the specifications.
    */
  @roundoff
  def distance(lat1: Double, lon1: Double, lat2: Double, lon2: Double): Double = {
    require(0.1 <= lat1 && lat1 <= 0.5)
    require(0.1 <= lon1 && lon1 <= 0.5)
    require(0.7 <= lat2 && lat2 <= 1.1)
    require(0.7 <= lon2 && lon2 <= 1.1)

    val halfLat = (lat2 - lat1) / 2.0
    val halfLon = (lon2 - lon1) / 2.0
    val chord = sin(halfLat) * sin(halfLat) +
                cos(lat1) * cos(lat2) * sin(halfLon) * sin(halfLon)

    12742.0 * asin(sqrt(chord))
  }
}
