// FloatIsReal.logLogistic adapted from ctongfei/nexus (MIT License)
// Source: https://github.com/ctongfei/nexus/blob/a9998d346036ec521f494f447001105cae21cdbc/tensor/src/main/scala/nexus/instances/float32.scala#L50
package nexus.instances

import stainless.math
import stainless.annotation.*

object FloatIsReal {
  type R = Float

  @roundoff
  def logLogistic(x: R) = {  // numeric stability
    require(-50.0f <= x && x <= 50.0f)
    if (x >= 0f) -math.log1p(math.exp(-x)).toFloat
    else x - math.log1p(math.exp(x)).toFloat
  }
}
