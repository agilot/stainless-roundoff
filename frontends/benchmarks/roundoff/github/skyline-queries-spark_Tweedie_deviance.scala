// Tweedie.deviance adapted from Lukas-Grasmann/skyline-queries-spark (Apache License 2.0)
// Source: https://github.com/Lukas-Grasmann/skyline-queries-spark/blob/25a2f0773db0108b0bcc8f7756daf7f308da09f6/mllib/src/main/scala/org/apache/spark/ml/regression/GeneralizedLinearRegression.scala#L648
package org.apache.spark.ml.regression

import stainless.math
import stainless.annotation.*

object GeneralizedLinearRegression {

  private[regression] class Tweedie(val variancePower: Double) {

    private def yp(y: Double, mu: Double, p: Double): Double = {
      require(-1.0 <= p && p <= 1.0)
      if (p == 0) {
        math.log(y / mu)
      } else {
        (math.pow(y, p) - math.pow(mu, p)) / p
      }
    }

    @roundoff
    def deviance(y: Double, mu: Double, weight: Double): Double = {
      require(1.0 <= variancePower && variancePower < 2.0)
      require(0.0 <= y && y <= 1000.0)
      require(1e-16 <= mu && mu <= 1000.0)
      require(0.0 <= weight && weight <= 100.0)
      // Force y >= delta for Poisson or compound Poisson
      val y1 = if (variancePower >= 1.0 && variancePower < 2.0) {
        math.max(y, Tweedie.delta)
      } else {
        y
      }
      2.0 * weight *
        (y * yp(y1, mu, 1.0 - variancePower) - yp(y, mu, 2.0 - variancePower))
    }
  }

  private[regression] object Tweedie{

    /** Constant used in initialization and deviance to avoid numerical issues. */
    val delta: Double = 0.1
  }
}
