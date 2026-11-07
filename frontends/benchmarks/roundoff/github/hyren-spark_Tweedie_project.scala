// Tweedie.project adapted from mickyuan/hyren-spark (Apache License 2.0)
// Source: https://github.com/mickyuan/hyren-spark/blob/360b986473c0ec6cb7a3eb4466f78f66e75c881b/mllib/src/main/scala/org/apache/spark/ml/regression/GeneralizedLinearRegression.scala#L656

package org.apache.spark.ml.regression

import stainless.annotation.*
import stainless.lang.*

object GeneralizedLinearRegression {

  val epsilon: Double = 1E-16

  class Tweedie(val variancePower: Double) {

    @roundoff
    def project(mu: Double): Double = {
      require(-1000.0 <= mu && mu <= 1000.0)
      if (mu < epsilon) {
        epsilon
      } else if (mu.isInfinity) {
        Double.MaxValue
      } else {
        mu
      }
    }
  }
}
