import stainless.annotation.*
import stainless.math
import stainless.math.*

object StepResponseArea4 {

  val Tol = 0.001

  def err(t: Double): Double =
    math.exp(-0.6 * t) * (math.cos(3.0 * t) + 0.2 * math.sin(3.0 * t))

  def mid(a: Double, b: Double): Double = 0.5 * (a + b)

  def gap(a: Double, b: Double): Double = math.abs(err(mid(a, b)) - mid(err(a), err(b)))

  def area0(a: Double, b: Double): Double = (b - a) * mid(err(a), err(b))

  def area1(a: Double, b: Double, tol: Double): Double =
    if (gap(a, b) < tol) area0(a, b)
    else area0(a, mid(a, b)) + area0(mid(a, b), b)

  def area2(a: Double, b: Double, tol: Double): Double =
    if (gap(a, b) < tol) area0(a, b)
    else area1(a, mid(a, b), tol / 2) + area1(mid(a, b), b, tol / 2)

  def area3(a: Double, b: Double, tol: Double): Double =
    if (gap(a, b) < tol) area0(a, b)
    else area2(a, mid(a, b), tol / 2) + area2(mid(a, b), b, tol / 2)

  def area4(a: Double, b: Double, tol: Double): Double =
    if (gap(a, b) < tol) area0(a, b)
    else area3(a, mid(a, b), tol / 2) + area3(mid(a, b), b, tol / 2)

  @roundoff
  def area(a: Double, b: Double): Double = {
    require(0 <= a && a <= 1 && 1 <= b && b <= 2)
    area4(a, b, Tol)
  }
}