// FullRunningAverage.removeDatum, adapted from BenchCouncil/BigDataBench_V5.0_BigData_ComponentBenchmark (Apache License 2.0)
// Source: https://github.com/BenchCouncil/BigDataBench_V5.0_BigData_ComponentBenchmark/blob/ac82abce9653af8152fe3dbd34f3da829d9148d5/Hadoop/apache-mahout-0.10.2-compile/math-scala/src/main/scala/org/apache/mahout/classifier/stats/ClassifierStats.scala#L298
package org.apache.mahout.classifier.stats

import stainless.annotation.*
import stainless.lang.*

class FullRunningAverage(private val count: Int = 0,
                         private val average: Double = Double.NaN) {

  @roundoff
  def removeDatum(datum: Double): Option[FullRunningAverage] = {
    require(0 <= count && count <= 1000000)
    require(-1000.0 <= average && average <= 1000.0)
    require(-1000.0 <= datum && datum <= 1000.0)
    if (count == 0) {
      None()
    }
    else {
      val updatedCount = count - 1
      val updatedAverage =
        if (updatedCount == 0) {
          Double.NaN
        }
        else {
          average * (updatedCount + 1) / updatedCount - datum / updatedCount
        }
      Some(new FullRunningAverage(updatedCount, updatedAverage))
    }
  }
}
