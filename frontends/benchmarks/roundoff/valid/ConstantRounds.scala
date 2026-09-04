import stainless.annotation.*

object ConstantRounds {

  private def toFahrenheit(celsius: Double): Double = celsius * 1.8 + 32.0

  /** A value with no inputs left in it still rounds, and its error has to be counted.
    *
    * Inlining the fallback turns it into `21.5 * 1.8 + 32.0`, which computes to `70.7` and
    * sits `1.887…e-15` away from what those three literals are worth exactly. Folding the
    * expression into the literal `70.7` would lose precisely that, because both sides of
    * the analysis read a literal as the double it names and would then find no error at
    * all.
    *
    * The other path returns an input untouched and the guard compares an input against a
    * literal, so under `--roundoff-exact-inputs=true` neither contributes anything. The
    * reported error is therefore this leaf alone. Exactly it is
    *
    *   1.88737914186276611872017383575439453125E-15
    *
    * and a report carries 34 digits, shortened away from zero so that it stays a bound:
    *
    *   1.887379141862766118720173835754395E-15
    */
  @roundoff
  def display(reading: Double, sensorOk: Double): Double = {
    require(-40.0 <= reading && reading <= 60.0)
    require(0.0 <= sensorOk && sensorOk <= 1.0)

    if (sensorOk < 0.5) toFahrenheit(21.5) else reading
  }
}
