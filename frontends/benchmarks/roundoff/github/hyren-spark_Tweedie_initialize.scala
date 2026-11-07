// Tweedie.initialize adapted from mickyuan/hyren-spark (Apache License 2.0)
// Source: https://github.com/mickyuan/hyren-spark/blob/360b986473c0ec6cb7a3eb4466f78f66e75c881b/mllib/src/main/scala/org/apache/spark/ml/regression/GeneralizedLinearRegression.scala#L612
package org.apache.spark.ml.regression

import stainless.annotation.*

object GeneralizedLinearRegression {

  class Tweedie(val variancePower: Double) {

    @roundoff
    def initialize(y: Double, weight: Double): Double = {
      require(1.0 <= variancePower && variancePower < 2.0)
      require(0.0 <= y && y <= 1000.0)
      if (variancePower >= 1.0 && variancePower < 2.0) {
        assert(y >= 0.0)
      } else if (variancePower >= 2.0) {
        assert(y > 0.0)
      }
      if (y == 0) Tweedie.delta else y
    }
  }

  object Tweedie {

    val delta: Double = 0.1
  }
}
