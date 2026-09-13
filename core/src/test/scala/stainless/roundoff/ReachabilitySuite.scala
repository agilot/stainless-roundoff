/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package roundoff

import org.scalatest.funsuite.AnyFunSuite
import stainless.trees._
import stainless.verification.roundoff._

/** Covers how the paths of a body are enumerated, and what asking about a branch changes.
  *
  * Nothing here needs a solver: the oracle is a stub that records what it was asked and
  * refuses whatever it is told to.
  */
class ReachabilitySuite extends AnyFunSuite with Unwrapping {

  private val f64 = FPType(11, 53)

  private val a = Variable.fresh("a", f64)
  private val b = Variable.fresh("b", f64)
  private val c = Variable.fresh("c", f64)

  private val one = Float64Literal(1.0)
  private val two = Float64Literal(2.0)
  private val three = Float64Literal(3.0)

  /** `if (a < b) { if (b < c) 1.0 else 2.0 } else 3.0` */
  private val nested =
    IfExpr(FPLessThan(a, b), IfExpr(FPLessThan(b, c), one, two), three)

  /** Records every question and refuses the ones it is told to. */
  private class Stub(refuse: Expr => Boolean = _ => false) extends BranchOracle {
    val asked = scala.collection.mutable.ArrayBuffer.empty[Expr]

    def assuming[A](condition: Expr)(block: => A): Option[A] = {
      asked += condition
      if (refuse(condition)) None else Some(block)
    }
  }

  private def extract(body: Expr, oracle: BranchOracle)
    : (Seq[Guard], Seq[ProgramPath]) =
    PathExtractor(body, oracle).orFail

  test("an equality is the two comparisons that make it, so it marks two bands") {
    val (guards, paths) = extract(IfExpr(FPEquals(a, b), one, two), BranchOracle.open)

    assert(guards == Seq(Guard(a, b, strict = false), Guard(b, a, strict = false)))
    // The else branch is reached either way of the band, which is what a conjunction written
    // out as nesting always does, so it appears once per side.
    assert(paths.map(_.leaf) == Seq(one, two, two))
    assert(paths.map(_.choices.map(_.taken)) ==
             Seq(Seq(true, true), Seq(true, false), Seq(false)))
  }

  test("an inequality is that same pair with the branches the other way about") {
    val (guards, paths) = extract(IfExpr(Not(FPEquals(a, b)), one, two), BranchOracle.open)

    assert(guards == Seq(Guard(a, b, strict = false), Guard(b, a, strict = false)))
    assert(paths.map(_.leaf) == Seq(two, one, one))
  }

  test("a branch refused above an equality cuts both of its guards at once") {
    val stub = new Stub(refuse = _ == FPLessThan(a, b))
    val (_, paths) = extract(IfExpr(FPLessThan(a, b), IfExpr(FPEquals(b, c), one, two), three),
                             stub)

    assert(paths.count(_.reachable) == 1)
    assert(paths.filter(_.reachable).map(_.leaf) == Seq(three))
    // Nothing below the refusal is asked about, so only the outer guard's two sides are.
    assert(stub.asked.size == 2)
  }

  test("refusing nothing leaves every path the body spells out") {
    val (guards, paths) = extract(nested, BranchOracle.open)

    assert(guards.size == 2)
    assert(paths.map(_.leaf) == Seq(one, two, three))
    assert(paths.forall(_.reachable))
  }

  test("the default oracle is the open one, so an unasked caller sees no change") {
    val (_, paths) = PathExtractor(nested).orFail
    assert(paths.map(_.leaf) == Seq(one, two, three))
    assert(paths.forall(_.reachable))
  }

  test("not taking a guard is the negation of its comparison, never the swap of its sides") {
    val stub = new Stub()
    extract(IfExpr(FPLessThan(a, b), one, two), stub)

    assert(stub.asked == Seq(FPLessThan(a, b), Not(FPLessThan(a, b))))
    // The swap would be `b <= a`, which agrees over the reals and disagrees on a NaN.
    assert(!stub.asked.contains(FPLessEquals(b, a)))
  }

  test("a guard written the other way round is oriented, and stays exact once negated") {
    val stub = new Stub()
    extract(IfExpr(FPGreaterEquals(a, b), one, two), stub)

    // `a >= b` is `b <= a`, and its two sides agree on every input, NaN included.
    assert(stub.asked == Seq(FPLessEquals(b, a), Not(FPLessEquals(b, a))))
  }

  test("questions arrive in preorder, one guard at a time") {
    val stub = new Stub()
    extract(nested, stub)

    assert(stub.asked == Seq(
      FPLessThan(a, b),                 // into the outer then
      FPLessThan(b, c),                 // into the inner then, under the outer one
      Not(FPLessThan(b, c)),            // into the inner else, still under it
      Not(FPLessThan(a, b))             // into the outer else
    ))
  }

  test("a refused branch is walked for its paths but asked nothing further") {
    val stub = new Stub(refuse = _ == FPLessThan(a, b))
    val (guards, paths) = extract(nested, stub)

    // One question cut the whole subtree: the inner guard was never asked about.
    assert(stub.asked == Seq(FPLessThan(a, b), Not(FPLessThan(a, b))))

    // Its paths are still there, so the exact run can still be said to take them.
    assert(paths.map(_.leaf) == Seq(one, two, three))
    assert(paths.map(_.reachable) == Seq(false, false, true))

    // And the guard below the refusal still exists, since a surviving region can name it.
    assert(guards.size == 2)
  }

  test("refusing both sides of the only guard leaves nothing reachable") {
    val stub = new Stub(refuse = _ => true)
    val (_, paths) = extract(IfExpr(FPLessThan(a, b), one, two), stub)

    assert(paths.size == 2)
    assert(!paths.exists(_.reachable))
  }

  test("a connective is written out as nesting and costs no question of its own") {
    val stub = new Stub()
    val body = IfExpr(And(Seq(FPLessThan(a, b), FPLessThan(b, c))), one, two)
    val (guards, paths) = extract(body, stub)

    // Two comparisons, so two guards and four questions; the `And` itself is asked nothing.
    assert(guards.size == 2)
    assert(stub.asked.size == 4)
    assert(stub.asked.head == FPLessThan(a, b))
    // The else leaf is reached both by failing the first conjunct and by failing the second.
    assert(paths.map(_.leaf) == Seq(one, two, two))
  }

  private val spec = InputSpec(FPPrecision.Binary64,
                              Map(a.id -> (0.0, 100.0), b.id -> (0.0, 100.0)))

  /** `a < 2.0`, as `PathExtractor` orients it. */
  private val below = Guard(a, two, strict = true)

  private def narrow(guard: Guard, taken: Boolean): (Double, Double) =
    FPCoreEmitter.narrowed(spec, Seq(guard), Seq(BranchChoice(0, taken))).ranges(a.id)

  test("taking a guard against a literal caps the input at it") {
    assert(narrow(below, taken = true) == (0.0, 2.0))
  }

  test("not taking it floors the input at the literal instead") {
    assert(narrow(below, taken = false) == (2.0, 100.0))
  }

  test("a literal on the left narrows the other way round") {
    val above = Guard(two, a, strict = true)
    assert(narrow(above, taken = true) == (2.0, 100.0))
    assert(narrow(above, taken = false) == (0.0, 2.0))
  }

  test("a guard between two inputs narrows nothing, since neither side is a literal") {
    val between = Guard(a, b, strict = true)
    assert(FPCoreEmitter.narrowed(spec, Seq(between), Seq(BranchChoice(0, true))).ranges == spec.ranges)
  }

  test("a guard on a computed value says nothing about the inputs under it") {
    val computed = Guard(FPMul(RoundNearestTiesToEven, a, a), two, strict = true)
    assert(FPCoreEmitter.narrowed(spec, Seq(computed), Seq(BranchChoice(0, true))).ranges == spec.ranges)
  }

  test("a guard the box already decides leaves the range as it was") {
    val wide = Guard(a, Float64Literal(500.0), strict = true)
    assert(narrow(wide, taken = true) == (0.0, 100.0))
  }

  test("an empty intersection is left alone, since reachability has already asked about it") {
    val impossible = Guard(a, Float64Literal(-5.0), strict = true)
    assert(narrow(impossible, taken = true) == (0.0, 100.0))
  }

  test("nested guards narrow from both sides") {
    val lower = Guard(Float64Literal(10.0), a, strict = true)
    val upper = Guard(a, Float64Literal(40.0), strict = true)
    val both = FPCoreEmitter.narrowed(spec, Seq(lower, upper),
                                      Seq(BranchChoice(0, true), BranchChoice(1, true)))
    assert(both.ranges(a.id) == (10.0, 40.0))
  }

  test("refusing the first conjunct cuts the second along with it") {
    val stub = new Stub(refuse = _ == FPLessThan(a, b))
    val body = IfExpr(And(Seq(FPLessThan(a, b), FPLessThan(b, c))), one, two)
    val (_, paths) = extract(body, stub)

    assert(stub.asked == Seq(FPLessThan(a, b), Not(FPLessThan(a, b))))
    assert(paths.map(_.reachable) == Seq(false, false, true))
  }
}
