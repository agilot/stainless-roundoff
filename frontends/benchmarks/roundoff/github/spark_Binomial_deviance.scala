// Binomial.deviance adapted from MrLight0809/spark (Apache License 2.0)
// Source: https://github.com/MrLight0809/spark/blob/0863ff039b1f579e40e6cd5f6dc48af582d4c1c4/mllib/src/main/scala/org/apache/spark/ml/regression/GeneralizedLinearRegression.scala#L743
// Calls GeneralizedLinearRegression.ylogy: https://github.com/MrLight0809/spark/blob/0863ff039b1f579e40e6cd5f6dc48af582d4c1c4/mllib/src/main/scala/org/apache/spark/ml/regression/GeneralizedLinearRegression.scala#L482
package org.apache.spark.ml.regression

import stainless.math
import stainless.annotation.*

object GeneralizedLinearRegression {

  def ylogy(y: Double, mu: Double): Double = {
    if (y == 0) 0.0 else y * math.log(y / mu)
  }

  object Binomial {

    @roundoff
    def deviance(y: Double, mu: Double, weight: Double): Double = {
      require(0.0 <= y && y <= 1.0)
      require(1e-16 <= mu && mu <= 0.9999999999999999)
      require(0.0 <= weight && weight <= 100.0)
      2.0 * weight * (ylogy(y, mu) + ylogy(1.0 - y, 1.0 - mu))
    }
  }
}
