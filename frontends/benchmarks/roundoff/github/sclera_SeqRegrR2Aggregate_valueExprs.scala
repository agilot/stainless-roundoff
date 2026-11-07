// SeqRegrR2Aggregate.valueExprs adapted from scleradb/sclera (Apache License 2.0)
// Source: https://github.com/scleradb/sclera/blob/099cb1d15c8c2a951ac6c746ca42e2c561c671eb/modules/core/src/main/scala/analytics/sequence/matcher/aggregate/SeqAggregate.scala#L660

package com.scleradb.sql.types {

  import stainless.lang.*

  /** Abstract base class for all SQL types */
  sealed abstract class SqlType {
    /** The underlying "NOT NULL" SQL type */
    def baseType: SqlType
  }

  /** Abstract base class for all "NOT NULL" SQL types */
  sealed abstract class SqlBaseType extends SqlType {
    override def baseType: SqlType = this
  }

  /** SQL type for FLOAT
    *
    * @param precOpt precision (optional)
    */
  case class SqlFloat(precOpt: Option[Int]) extends SqlBaseType
}

package com.scleradb.sql.expr {

  import com.scleradb.sql.types.SqlType

  /** Scalar valued expressions that can appear as column values */
  sealed abstract class ScalColValue

  /** Double constant */
  case class DoubleConst(value: Double) extends ScalColValue

  /** SQL NULL */
  sealed abstract class SqlNull extends ScalColValue

  /** Typed SQL NULL */
  case class SqlTypedNull(sqlBaseType: SqlType) extends SqlNull

  object SqlNull {
    def apply(t: SqlType): SqlNull = new SqlTypedNull(t.baseType)
  }
}

package com.scleradb.analytics.sequence.matcher.aggregate {

  import com.scleradb.sql.expr.{DoubleConst, ScalColValue, SqlNull}
  import com.scleradb.sql.types.SqlFloat
  import stainless.annotation.*
  import stainless.lang.*

  case class SeqRegrR2Aggregate(
      sumy: Double = 0.0,
      sumx: Double = 0.0,
      sumyx: Double = 0.0,
      sumyy: Double = 0.0,
      sumxx: Double = 0.0,
      count: Long = 0L
  ) {
      @roundoff
      def valueExprs: ScalColValue = {
          require(1L <= count && count <= 1000000L)
          require(-1e9 <= sumx && sumx <= 1e9)
          require(-1e9 <= sumy && sumy <= 1e9)
          require(0.0 <= sumxx && sumxx <= 1e12)
          require(0.0 <= sumyy && sumyy <= 1e12)
          require(-1e12 <= sumyx && sumyx <= 1e12)
          if( count == 0 ) SqlNull(SqlFloat(None())) else {
              val ex: Double = sumx/count
              val exx: Double = sumxx/count

              val varx: Double = exx - ex*ex
              if( varx == 0.0 ) SqlNull(SqlFloat(None())) else {
                  val ey: Double = sumy/count
                  val eyy: Double = sumyy/count

                  val vary: Double = eyy - ey*ey
                  if( vary == 0.0 ) DoubleConst(1.0) else {
                      val eyx: Double = sumyx/count
                      val covaryx: Double = eyx - ey*ex

                      val regrR2: Double = (covaryx/vary) * (covaryx/varx)
                      DoubleConst(regrR2)
                  }
              }
          }
      }
  }
}
