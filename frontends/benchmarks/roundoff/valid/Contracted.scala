import stainless.annotation.*
import stainless.lang.*

object Contracted {

  /** The callee's own contract is dropped when its body is inlined, because the range each
    * parameter really takes follows from the argument bound to it. The precondition is
    * still discharged as its own obligation at the call site.
    */
  private def perUnit(total: Double, count: Double): Double = {
    require(1.0 <= count)
    total / count
  }.ensuring(res => res <= total)

  @roundoff
  def average(total: Double, count: Double): Double = {
    require(10.0 <= total && total <= 1000.0)
    require(2.0 <= count && count <= 50.0)

    perUnit(total, count) * 1.05
  }
}
