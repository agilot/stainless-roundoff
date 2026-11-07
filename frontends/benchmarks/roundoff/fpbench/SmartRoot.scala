import stainless.annotation.*
import stainless.math.sqrt

object SmartRoot {

  @roundoff
  def smartRoot(c: Double): Double = {
    require(-2.0 <= c && c <= 2.0 && 3.5 * 3.5 - 3 * c * 4.0 > 0.1)
    val a = 3.0
    val b = 3.5
    val discr = b * b - a * c * 4.0
    if (b * b - a * c > 10) {
      if (b > 0) c * 2 / (-b - sqrt(discr))
      else if (b < 0) (-b + sqrt(discr)) / (a * 2)
      else (-b + sqrt(discr)) / (a * 2)
    } else {
      (-b + sqrt(discr)) / (a * 2)
    }
  }

}