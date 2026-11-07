// PRPoint.f1 adapted from sameersingh/scalaplot (BSD 2-Clause "Simplified" License)
// Source: https://github.com/sameersingh/scalaplot/blob/438a61e5b0b7276f869f73d36230fa5ac4c5897a/src/main/scala/org/sameersingh/scalaplot/metrics/PrecRecallCurve.scala#L38
// Calls PRPoint.recall: https://github.com/sameersingh/scalaplot/blob/438a61e5b0b7276f869f73d36230fa5ac4c5897a/src/main/scala/org/sameersingh/scalaplot/metrics/PrecRecallCurve.scala#L30
package org.sameersingh.scalaplot.metrics

import stainless.annotation.*

case class PRPoint(thresh: Double, tp: Int, tn: Int, fp: Int, fn: Int) {
  def precNumerator: Double = tp

  def precDenominator: Double = tp + fp

  def recallNumerator: Double = tp

  def recallDenominator: Double = tp + fn

  def precision: Double = {
    require(0 <= tp && tp <= 1000000)
    require(0 <= fp && fp <= 1000000)
    if (precDenominator == 0.0) {
      1.0
    } else {
      precNumerator / precDenominator
    }
  }

  def recall: Double = {
    require(0 <= tp && tp <= 1000000)
    require(0 <= fn && fn <= 1000000)
    if (recallDenominator == 0.0) {
      1.0
    } else {
      recallNumerator / recallDenominator
    }
  }

  @roundoff
  def f1: Double = {
    require(0 <= tp && tp <= 1000000)
    require(0 <= fp && fp <= 1000000)
    require(0 <= fn && fn <= 1000000)
    val r: Double = recall
    val p: Double = precision
    if (p + r == 0.0) 0.0
    else (2 * p * r) / (p + r)
  }
}
