import stainless.annotation.*

object Hysteresis {

  private def belowSetpoint(measured: Double, setpoint: Double): Boolean =
    measured - setpoint < 0.0

  /** Without inlining the guard is an opaque boolean and marks no region two paths can be
    * compared over. Inlined, it is an ordinary comparison the solver can work with.
    */
  @roundoff
  def demand(temperature: Double, setpoint: Double, gain: Double): Double = {
    require(-10.0 <= temperature && temperature <= 40.0)
    require(15.0 <= setpoint && setpoint <= 25.0)
    require(0.5 <= gain && gain <= 4.0)

    if (belowSetpoint(temperature, setpoint)) gain * (setpoint - temperature)
    else 0.0
  }
}
