// PRPoint.recall adapted from sameersingh/scalaplot (BSD 2-Clause "Simplified" License)
// Source: https://github.com/sameersingh/scalaplot/blob/438a61e5b0b7276f869f73d36230fa5ac4c5897a/src/main/scala/org/sameersingh/scalaplot/metrics/PrecRecallCurve.scala#L30
package org.sameersingh.scalaplot.metrics

import stainless.annotation.*

case class PRPoint(thresh: Double, tp: Int, tn: Int, fp: Int, fn: Int) {
  def recallNumerator: Double = tp

  def recallDenominator: Double = tp + fn

  @roundoff
  def recall: Double = {
    require(0 <= tp && tp <= 1000000)
    require(0 <= fn && fn <= 1000000)
    if (recallDenominator == 0.0) {
      1.0
    } else {
      recallNumerator / recallDenominator
    }
  }
}
