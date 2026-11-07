import stainless.annotation.*
import stainless.math.*

object Rover {

  def hardTanh(x: Double): Double =
    if (x < -1.0) -1.0 else if (x > 1.0) 1.0 else x

  def net(x1: Double, x2: Double): Double = {
    val h1 = hardTanh(-3.26 * x1 + 3.24 * x2 - 1.09)
    val h2 = hardTanh(-3.30 * x1 + 0.01 * x2 + 0.64)
    val g1 = hardTanh(3.18 * h1 - 2.08 * h2 - 0.10)
    val g2 = hardTanh(3.29 * h1 - 2.19 * h2 + 0.10)
    -1.55 * g1 - 1.45 * g2 - 1.00
  }

  @roundoff @fuzz def rover(d: Double, v: Double): Double = {
    require(5.0 <= d && d <= 15.0 && 0.0 <= v && v <= 10.0)
    val a = net(d / 10.0 - 1.0, v / 5.0 - 1.0) // proposed acceleration
    val v1 = v + 0.1 * a                        // speed after one step
    val d1 = d - 0.1 * v1                       // distance after one step
    if (v1 * v1 < 8.0 * (d1 - 1.0)) a           // can still stop in time
    else -4.0                                   // full braking
  }
}

