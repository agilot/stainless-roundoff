import stainless.annotation.*

object ExternHelper {

  @extern
  private def hardwareGain(v: Double): Double = v * 3.0

  /** An `@extern` body is not available to the analysis, so the obligation is unsupported
    * rather than answered from a body Stainless is not meant to look at.
    */
  @roundoff
  def amplify(signal: Double): Double = {
    require(1.0 <= signal && signal <= 100.0)

    hardwareGain(signal) + 1.0
  }
}
