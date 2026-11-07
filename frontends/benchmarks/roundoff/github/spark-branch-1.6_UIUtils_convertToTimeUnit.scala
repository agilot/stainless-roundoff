// UIUtils.convertToTimeUnit adapted from lmd1993/spark-branch-1.6 (Apache License 2.0)
// Source: https://github.com/lmd1993/spark-branch-1.6/blob/b1a9c32c82e5154b3296348edefca8a3b782371d/streaming/src/main/scala/org/apache/spark/streaming/ui/UIUtils.scala#L71

package org.apache.spark.streaming.ui

import stainless.annotation.*

enum TimeUnit {
  case NANOSECONDS, MICROSECONDS, MILLISECONDS, SECONDS, MINUTES, HOURS, DAYS
}

object UIUtils {

  @roundoff
  def convertToTimeUnit(milliseconds: Long, unit: TimeUnit): Double = {
    require(0L <= milliseconds && milliseconds <= 86400000L)
    unit match {
      case TimeUnit.NANOSECONDS => milliseconds * 1000 * 1000
      case TimeUnit.MICROSECONDS => milliseconds * 1000
      case TimeUnit.MILLISECONDS => milliseconds
      case TimeUnit.SECONDS => milliseconds / 1000.0
      case TimeUnit.MINUTES => milliseconds / 1000.0 / 60.0
      case TimeUnit.HOURS => milliseconds / 1000.0 / 60.0 / 60.0
      case TimeUnit.DAYS => milliseconds / 1000.0 / 60.0 / 60.0 / 24.0
    }
  }
}
