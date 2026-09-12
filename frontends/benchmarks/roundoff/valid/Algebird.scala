import stainless.annotation.*

case class Moments(val m0D: Double, val m1: Double, val m2: Double, val m3: Double, val m4: Double) {
  require(1 <= m0D && m0D <= 50)
  require(-50 <= m1 && m1 <= 50)
  require(-50 <= m2 && m2 <= 50)
  require(-50 <= m3 && m3 <= 50)
  require(-50 <= m4 && m4 <= 50)
  def mean: Double = m1

  @roundoff
  def +(b: Double): Moments = {
    require(-50 <= b && b <= 50)

    val n = m0D + 1
    val delta = b - mean
    val delta_n = delta / n
    val delta_n2 = delta_n * delta_n
    val term1 = delta * delta_n * m0D

    val meanCombined = Moments.getCombinedMeanDouble(m0D, mean, 1.0, b)
    val m2combined = m2 + term1
    val m3combined = m3 + term1 * delta_n * (n - 2) - 3 * delta_n * m2
    val m4combined = m4 + term1 * delta_n2 * (n * n - 3 * n + 3) +
      6 * delta_n2 * m2 - 4 * delta_n * m3

    new Moments(n, meanCombined, m2combined, m3combined, m4combined)
  }
}


object Moments {

  def getCombinedMeanDouble(weightN: Double, an: Double, weightK: Double, ak: Double): Double = {
    require(1.0 <= weightN && weightN <= 10)
    require(1.0 <= weightK && weightK <= 10)
    require(-50 <= an && an <= 50)
    require(-50 <= ak && ak <= 50)
    require(weightN >= weightK)
    val newCount = weightN + weightK
    if newCount == 0 then 0.0
    else if newCount == weightN then an
    else
      val STABILITY_CONSTANT = 0.1
      val scaling = weightK / newCount
      assert(scaling <= 1)
      // a_n + (a_k - a_n)*(k/(n+k)) is only stable if n is not approximately k
      if (scaling < STABILITY_CONSTANT) an + (ak - an) * scaling
      else (weightN * an + weightK * ak) / newCount
  }
}