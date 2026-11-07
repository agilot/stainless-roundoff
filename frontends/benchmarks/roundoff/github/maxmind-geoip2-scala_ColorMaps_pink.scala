// ColorMaps.pink adapted from Sanoma-CDA/maxmind-geoip2-scala (Apache License 2.0)
// Source: https://github.com/Sanoma-CDA/maxmind-geoip2-scala/blob/b117e8bfab1bc71b38a9673586e18e200561157f/src/main/scala/com/sanoma/cda/geo/ColorMaps.scala#L110
// Calls ColorMaps.hot: https://github.com/Sanoma-CDA/maxmind-geoip2-scala/blob/b117e8bfab1bc71b38a9673586e18e200561157f/src/main/scala/com/sanoma/cda/geo/ColorMaps.scala#L77

package com.sanoma.cda.geo

import stainless.math
import stainless.annotation.*

object ColorMaps {

  def hot(x: Double): (Double, Double, Double) = {
    require(0.0 <= x && x <= 1.0)
    if (x <= 3.0 / 8.0) {
      val low = 0.0
      val high = 3.0 / 8.0
      ((x - low) / (high - low), 0.0, 0.0)
    }
    else if (x <= 6.0 / 8.0) {
      val low = 3.0 / 8.0
      val high = 6.0 / 8.0
      (1.0, (x - low) / (high - low), 0.0)
    }
    else {
      val low = 6.0 / 8.0
      val high = 1.0
      (1.0, 1.0, (x - low) / (high - low))
    }
  }

  @roundoff
  def pink(x: Double): (Double, Double, Double) = {
    require(0.0 <= x && x <= 1.0)
    import math.sqrt
    val rgbhot = hot(x)
    (sqrt(2.0 * x + rgbhot._1 / 3.0),
      sqrt(2.0 * x + rgbhot._2 / 3.0),
      sqrt(2.0 * x + rgbhot._3 / 3.0))
  }
}
