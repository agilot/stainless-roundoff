
import stainless.annotation.roundoff

object BouncingBall2 {

  def pos(y: Double, v: Double): Double =
    val a = y + 0.1 * v
    if a < 0 then -a else a

  def vel(y: Double, v: Double): Double =
    val a = y + 0.1 * v
    val w = v - 0.1 * 9.81
    if a < 0 then -0.8 * w else w

  @roundoff
  def ball(y0: Double, v0: Double): Double =
    require(0.0 <= y0 && y0 <= 2.0)
    require(-10.0 <= v0 && v0 <= 10.0)
    val y1 = pos(y0, v0);
    val v1 = vel(y0, v0)
    val y2 = pos(y1, v1);
    val v2 = vel(y1, v1)
    pos(y2, v2)
}
