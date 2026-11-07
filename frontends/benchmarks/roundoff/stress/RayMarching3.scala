import stainless.annotation.*
import stainless.math.*

object RayMarching3 {

  val Epsilon = 0.0001

  // Unit cube centered at the origin
  def box(x: Double, y: Double, z: Double): Double =
    max(max(abs(x), abs(y)), abs(z)) - 1.0

  // A cube in a room: cube centered at z = 3, back wall at z = 4, side wall at x = 1.5
  def sceneSDF(x: Double, y: Double, z: Double): Double =
    min(min(box(x, y, z - 3.0), 4.0 - z), 1.5 - x)

  @roundoff
  def march2(ex: Double, ey: Double, ez: Double,
             dx: Double, dy: Double, dz: Double,
             start: Double, end: Double): Double =
    require(-1 <= ex && ex <= 1 && -1 <= ey && ey <= 1 && 1.0 <= ez && ez <= 1.5)
    require(-0.3 <= dx && dx <= 0.3 && -0.3 <= dy && dy <= 0.3 && 0.9 <= dz && dz <= 1)
    require(0 <= start && start <= 0.5 && 10 <= end && end <= 20)
    val depth0 = start
    val dist0 = sceneSDF(ex + depth0 * dx, ey + depth0 * dy, ez + depth0 * dz)
    if dist0 < Epsilon then depth0
    else
      val depth1 = depth0 + dist0
      if depth1 >= end then end
      else
        val dist1 = sceneSDF(ex + depth1 * dx, ey + depth1 * dy, ez + depth1 * dz)
        if dist1 < Epsilon then depth1
        else
          val depth2 = depth1 + dist1
          if depth2 >= end then end
          else
            val dist2 = sceneSDF(ex + depth2 * dx, ey + depth2 * dy, ez + depth2 * dz)
            if dist2 < Epsilon then depth2 else end
}