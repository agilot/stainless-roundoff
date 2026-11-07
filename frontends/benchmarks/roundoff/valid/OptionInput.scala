import stainless.annotation.*
import stainless.lang.*

sealed trait Shape
case class Circle(r: Double) extends Shape
case class Square(side: Double) extends Shape
case class Rect(w: Double, h: Double) extends Shape

object OptionInput {

  @roundoff
  def scaled(o: Option[Double], x: Double): Double = {
    require(0 <= x && x <= 1)
    require(o match { case Some(v) => 0 <= v && v <= 1; case None() => true })
    o match {
      case Some(v) => if (v * x < 0.5) v * x else 0.5
      case None() => x
    }
  }

  @roundoff
  def ratio(a: Option[Double], b: Option[Double]): Double = {
    require(a.isEmpty || (1 <= a.get && a.get <= 2))
    require(b.isEmpty || (1 <= b.get && b.get <= 2))
    (a, b) match {
      case (Some(u), Some(v)) => u / v
      case (Some(u), None()) => u
      case (None(), Some(v)) => 1 / v
      case (None(), None()) => 1.0
    }
  }

  @roundoff
  def area(s: Shape): Double = {
    require(s match {
      case Circle(r) => 0 <= r && r <= 10
      case Square(a) => 0 <= a && a <= 10
      case Rect(w, h) => 0 <= w && w <= 10 && 0 <= h && h <= 10
    })
    s match {
      case Circle(r) => 3.14159 * r * r
      case Square(a) => a * a
      case Rect(w, h) => w * h
    }
  }
}
