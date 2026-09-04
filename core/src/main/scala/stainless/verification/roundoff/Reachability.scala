/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification
package roundoff

import trees._

/** Answers whether a branch is worth walking into, given the branches already taken.
  *
  * `block` runs inside the assumption, so an implementation that holds a solver accumulates
  * one condition per level and a nested question is asked under everything above it.
  */
trait BranchOracle {

  /** `None` where `condition` is refuted under what is already assumed, and the outcome of
    * `block` otherwise.
    *
    * Only a refutation may answer `None`: a question left open has to keep the branch.
    */
  def assuming[A](condition: Expr)(block: => A): Option[A]
}

object BranchOracle {

  /** Refutes nothing, so enumeration reaches every path the body spells out. */
  val open: BranchOracle = new BranchOracle {
    def assuming[A](condition: Expr)(block: => A): Option[A] = Some(block)
  }
}

/** How a guard reads to the floating-point program that tests it. */
private[roundoff] object FPPathCondition {

  /** What one choice at a guard says about the values it compares.
    *
    * Taking a guard puts its `lhs` below its `rhs`, which is how `PathExtractor` orients one.
    * Not taking it is the negation of that comparison and not the swap of its two sides: the
    * two readings agree over the reals, but a NaN operand makes every comparison false, so
    * only the negation says what the program does.
    */
  def of(guard: Guard, taken: Boolean): Expr = {
    val below =
      if (guard.strict) FPLessThan(guard.lhs, guard.rhs) else FPLessEquals(guard.lhs, guard.rhs)
    if (taken) below else Not(below)
  }
}
