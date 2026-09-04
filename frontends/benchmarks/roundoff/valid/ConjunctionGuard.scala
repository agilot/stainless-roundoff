import stainless.annotation.*

object ConjunctionGuard {

  /** A guard that is a conjunction, which repeats everything under its else branch.
    *
    * `a && b` is written out as the nesting it stands for, so the else branch is reached twice:
    * once by failing the second conjunct and once by failing the first. Both paths end in the
    * same expression, and bounded over the whole box they are the same question, asked once.
    *
    * Narrowing each leaf to the inputs that reach it stops them being the same question. One
    * path holds `x` under 10 and `y` at or above it; the other holds `x` at or above 10 and says
    * nothing about `y`. So the analyzer is asked twice and the worse answer taken, which is
    * tighter than one answer over both regions together.
    *
    * This is the only benchmark whose number of queries depends on that narrowing, two without
    * it and three with, and the only one where a leaf is shared across paths that disagree about
    * where it runs.
    */
  @roundoff
  def gate(x: Double, y: Double): Double = {
    require(0.0 <= x && x <= 1000.0)
    require(0.0 <= y && y <= 1000.0)

    if (x < 10.0 && y < 10.0) x * y else x * 0.001
  }
}
