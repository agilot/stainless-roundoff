import stainless.annotation.*
import stainless.lang.*
import stainless.math.*

//@roundoff
//def square(x: Double) = {
//  require(-10 <= x && x <= 10)
//  x * x
//}
//
//@roundoff
//def squareCursed(x: Double) = {
//  require(1 <= x && x <= 10)
//  stainless.math.sqrt(x * x * x * x)
//}

//@roundoff
//def smooth_l1_loss (input: Double, target: Double, beta: Double) = {
//  require(-20 < input && input < 20)
//  require(-5 < target && target < 5)
//  require(0.05 <= beta && beta < 1)
//  require(input > target)
//  val n = input - target
//  if n < beta then   0.5 * n * n / beta  else    n - 0.5 * beta
//}//.ensuring(_ >= 0)

//@roundoff
//def classify(x1: Double, x2: Double, x3: Double, x4: Double): Double = {
//  require(1.0 < x1 && x1 < 4.0 && 1.0 < x2 && x2 < 4.0 &&
//    0.5 < x3 && x3 < 2.0 && 2.0 < x4 && x4 < 5.0)
//
//  if (x1*x1 + x2*x2 < 10.0) {
//    if (x1*x2*x3 < 6.0)
//      (x1*x2 + x3*x4) / (x1 + x2)
//    else
//      x1*x1*x3 - x2/x4
//  } else {
//    if (x3*x4*x4 - x1*x2 > 2.0)
//      (x1 + x2*x3) / (x4*x4)
//    else
//      (x2*x2*x2) / (x1 + x3*x4)
//  }
//}

type Real = Double

//@roundoff
//def bridge(x1: Real, x2: Real, x3: Real, x4: Real): Real = {
//    require(0.5 < x1 && x1 < 3.0 &&
//      0.5 < x2 && x2 < 3.0 &&
//      1.0 < x3 && x3 < 4.0 &&
//      1.0 < x4 && x4 < 4.0)
//
//    val s   = x1 + x2
//    val d   = x1 - x2
//    val w   = x3*x4 + x3/x4
//    val den = w*w + x3*x3 + 1.0
//    val q   = 2.0*(x1*x1 + x2*x2)
//
//    val gain = (x3*x3*x4 - x1*x2*x4 + 2.0*x3) / den
//
//    if (x1*x2 < 0.75)
//      (4.0*x1*x2) * gain / q
//    else
//      (s*s - d*d) * gain / q
//  }

//@roundoff
//def whileTest(x: Double) = {
//  var y = x
//  var res = 0.0
//  while (y > 1.0) {
//    res = res * 2.0
//    y /= 2
//  }
//  res
//}

def square(x: Double): Double = x * x

//@roundoff
//def bridge(x1: Double, x2: Double, x3: Double, x4: Double): Double = {
//  require(0.5 < x1 && x1 < 3.0 &&
//    0.5 < x2 && x2 < 3.0 &&
//    1.0 < x3 && x3 < 4.0 &&
//    1.0 < x4 && x4 < 4.0)
//
//  val s   = x1 + x2
//  val d   = x1 - x2
//  val w   = x3*x4 + x3/x4
//  val den = w*w + x3*x3 + 1.0
//
//  val gain = (x3*x3*x4 - x1*x2*x4 + 2.0*x3) / den
//
//  if (x1*x2 < 0.75)
//    (4.0*x1*x2) * gain / (s*s + d*d)
//  else
//    (s*s - d*d) * gain / (s*s + d*d)
//}

//@roundoff
//def limiter(x1: Double, x2: Double, x3: Double, x4: Double): Double = {
//  require(0.0 < x1 && x1 < 2.0 &&
//    0.0 < x2 && x2 < 2.0 &&
//    0.0 < x3 && x3 < 2.0 &&
//    0.0 < x4 && x4 < 2.0)
//
//  val t = x1*x2 + x3*x4
//
//  if (t < 1.0) t
//  else {
//    if (t < 2.0) 1.0 + (t - 1.0)/2.0
//    else {
//      if (t < 3.0) 1.5 + (t - 2.0)/4.0
//      else {
//        if (t < 4.0) 1.75 + (t - 3.0)/8.0
//        else {
//          if (t < 5.0) 1.875 + (t - 4.0)/16.0
//          else         1.9375 + (t - 5.0)/32.0
//        }
//      }
//    }
//  }
//}

//def EPSILON = {
//  var eps = 1.0
//  (while ((1.0 + (eps / 2.0)) != 1.0) {
//    decreases(eps)
//    eps /= 2.0
//  }).invariant(0.0 < eps && eps <= 1.0)
//  eps
//}

@roundoff
def cav10(x: Double) = {
  require(0 < x && x < 10)
  if square(x) - x >= 0  then
    x / 10
  else
    square(x) + 2
}.ensuring(res => 0 <= res && res <= 3)
//
//@roundoff
//def nestedCond(x: Double, y: Double) = {
//  require(-10 < x && x < 10)
//  require(-10 < y && y < 10)
//  abs(x) + abs(y)
//}.ensuring(res => 0 <= res && res <= 20)
//
//@roundoff
//def absorption(big: Double) = {
//  require(1e16 < big && big < 1e17)
//  if big + 1.0 - big > 0.0 then big else -big
//}


//@roundoff
//def cosTest(x: Double): Double = {
//  require(0.5 < x && x < 6)
//  if (x * x >= 1)
//    x * x * x
//  else
//    -x + 2
//}

//@roundoff
//def randomTest(x: Double, y: Double): Double = {
//  require(1 < x && x < 6 && 0.5 < y && y < 6)
//  if (x * x <= y / x)
//    x * x * x - y
//  else
//    y * y * x
//}

//@roundoff
//def jetApproxGoodFitWithError(x: Double, y: Double): Double = {
//  require(-5<=x && x<=5)
//  require(-5<=y && y<=5)
//  if (y < x) {
//    -0.317581 + 0.0563331*x + 0.0966019*x*x + 0.0132828*y +
//      0.0372319*x*y + 0.00204579*y*y
//  } else {
//    -0.330458 + 0.0478931*x + 0.154893*x*x + 0.0185116*y -
//      0.0153842*x*y - 0.00204579*y*y
//  }
//}

//@roundoff
//def fastSquaredDistance(x1: Double, x2: Double, y1: Double, y2: Double): Double = {
//  require(10.00001 <= x1 && x1 <= 10.001)
//  require(0.5     <= x2 && x2 <= 0.500000001)
//  require(0.5     <= y1 && y1 <= 0.500000001)
//  require(10.0    <= y2 && y2 <= 10.000000001)
//
//  val norm1 = sqrt(x1 * x1 + x2 * x2)
//  val norm2 = sqrt(y1 * y1 + y2 * y2)
//
//  val sumSquaredNorm = norm1 * norm1 + norm2 * norm2
//  val normDiff = norm1 - norm2
//
//  val precisionBound1 =
//    2.0 * 2.220446049250313e-16 * sumSquaredNorm /
//      (normDiff * normDiff + 2.220446049250313e-16)
//
//  if (precisionBound1 < 1e-6) {
//    sumSquaredNorm - 2.0 * (x1 * y1 + x2 * y2)
//  } else {
//    val dotValue = x1 * y1 + x2 * y2
//    val diff = sumSquaredNorm - 2.0 * dotValue
//    val sqDist = if (diff > 0.0) diff else 0.0
//    val absDot = if (dotValue >= 0.0) dotValue else -dotValue
//    val precisionBound2 =
//      2.220446049250313e-16 * (sumSquaredNorm + 2.0 * absDot) /
//        (sqDist + 2.220446049250313e-16)
//    if (precisionBound2 > 1e-6) {
//      (x1 - y1) * (x1 - y1) + (x2 - y2) * (x2 - y2)
//    } else {
//      sqDist
//    }
//  }
//}