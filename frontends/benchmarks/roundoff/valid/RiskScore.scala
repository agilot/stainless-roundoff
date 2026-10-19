import stainless.annotation.*

object RiskScore {

  /** A balanced tree of three nestings, so eight leaves sit under the outermost guard. */
  @roundoff
  def score(income: Double, debt: Double, history: Double, age: Double): Double = {
    require(1.0 <= income && income <= 20.0)
    require(0.5 <= debt && debt <= 10.0)
    require(0.0 <= history && history <= 1.0)
    require(18.0 <= age && age <= 80.0)

    if (debt * 3.0 < income) {
      if (history > 0.6) {
        if (age < 30.0) 0.95 * history + 0.02 * income
        else 0.90 * history + 0.03 * income
      } else {
        if (age < 45.0) 0.70 * history + 0.05 * income
        else 0.65 * history + 0.04 * income
      }
    } else {
      if (history > 0.4) {
        if (age < 35.0) 0.50 * history + 0.01 * income - 0.02 * debt
        else 0.45 * history + 0.02 * income - 0.03 * debt
      } else {
        if (age < 55.0) 0.25 * history - 0.04 * debt
        else 0.20 * history - 0.05 * debt
      }
    }
  }
}
