// FloatParam.jValueDecode adapted from MrLight0809/spark (Apache License 2.0)
// Source: https://github.com/MrLight0809/spark/blob/0863ff039b1f579e40e6cd5f6dc48af582d4c1c4/mllib/src/main/scala/org/apache/spark/ml/param/params.scala#L459
// Uses JValue (json4s 3.6.6, Apache License 2.0) : https://github.com/json4s/json4s/blob/4472f92fba948c68d4d582ed4d9640dc268832e1/ast/src/main/scala/org/json4s/JsonAST.scala#L35
// Uses JString (json4s 3.6.6, Apache License 2.0) : https://github.com/json4s/json4s/blob/4472f92fba948c68d4d582ed4d9640dc268832e1/ast/src/main/scala/org/json4s/JsonAST.scala#L121
// Uses JDouble (json4s 3.6.6, Apache License 2.0) : https://github.com/json4s/json4s/blob/4472f92fba948c68d4d582ed4d9640dc268832e1/ast/src/main/scala/org/json4s/JsonAST.scala#L126
package org.apache.spark.ml.param {

  import org.json4s.JsonAST._
  import stainless.annotation.*
  import stainless.lang.*

  object FloatParam {

    /** Decodes a param value from JValue. */
    @roundoff
    def jValueDecode(jValue: JValue): Option[Float] = {
      require(jValue match {
        case JDouble(x) => -3.4028234663852886e38 <= x && x <= 3.4028234663852886e38
        case _ => true
      })
      jValue match {
        case JString("NaN") =>
          Some(Float.NaN)
        case JString("-Inf") =>
          Some(Float.NegativeInfinity)
        case JString("Inf") =>
          Some(Float.PositiveInfinity)
        case JDouble(x) =>
          Some(x.toFloat)
        case _ =>
          None()
      }
    }
  }
}

// json4s 3.6.6, ast/src/main/scala/org/json4s/JsonAST.scala (Apache License 2.0)
package org.json4s {

  object JsonAST {

    sealed abstract class JValue

    case class JString(s: String) extends JValue

    case class JDouble(num: Double) extends JValue
  }
}
