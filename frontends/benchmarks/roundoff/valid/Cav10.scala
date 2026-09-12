import stainless.annotation.*

object Cav10 {
  @roundoff
  def cav10(x: Double): Double = {
    require(0 < x && x < 10)
    if (x*x - x >= 0)
      x/10
    else
      x*x + 2
  }
}