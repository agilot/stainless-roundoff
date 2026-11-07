// RandomForest.samplesFractionForFindSplits adapted from Lukas-Grasmann/skyline-queries-spark (Apache License 2.0)
// Source: https://github.com/Lukas-Grasmann/skyline-queries-spark/blob/25a2f0773db0108b0bcc8f7756daf7f308da09f6/mllib/src/main/scala/org/apache/spark/ml/tree/impl/RandomForest.scala#L1327
package org.apache.spark.ml.tree.impl

import stainless.math
import stainless.annotation.*

class DecisionTreeMetadata(
    val numExamples: Long,
    val maxBins: Int)

object RandomForest {

  @roundoff
  private def samplesFractionForFindSplits(
      metadata: DecisionTreeMetadata): Double = {
    require(2 <= metadata.maxBins && metadata.maxBins <= 10000)
    require(1L <= metadata.numExamples && metadata.numExamples <= 10000000000L)
    // Calculate the number of samples for approximate quantile calculation.
    val requiredSamples = math.max(metadata.maxBins * metadata.maxBins, 10000)
    if (requiredSamples < metadata.numExamples) {
      requiredSamples.toDouble / metadata.numExamples
    } else {
      1.0
    }
  }
}
