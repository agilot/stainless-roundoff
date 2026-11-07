/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package roundoff

import org.scalatest.funsuite.AnyFunSuite
import stainless.trees._
import stainless.verification.roundoff._

/** Covers how the paths of a body are enumerated, how they become Ibex regions, and how a
  * branch narrows the input ranges. Nothing here needs a solver.
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

  private def extract(body: Expr): (Seq[Guard], Seq[ProgramPath]) = PathExtractor(body).orFail

  test("an equality is the two comparisons that make it, so it marks two bands") {
    val (guards, paths) = extract(IfExpr(FPEquals(a, b), one, two))

    assert(guards == Seq(Guard(a, b, strict = false), Guard(b, a, strict = false)))
    // The else branch is reached either way of the band, which is what a conjunction written
    // out as nesting always does, so it appears once per side.
    assert(paths.map(_.leaf) == Seq(one, two, two))
    assert(paths.map(_.choices.map(_.taken)) ==
             Seq(Seq(true, true), Seq(true, false), Seq(false)))
  }

  test("an inequality is that same pair with the branches the other way about") {
    val (guards, paths) = extract(IfExpr(Not(FPEquals(a, b)), one, two))

    assert(guards == Seq(Guard(a, b, strict = false), Guard(b, a, strict = false)))
    assert(paths.map(_.leaf) == Seq(two, one, one))
  }

  private val unitBox = InputSpec(FPPrecision.Binary64,
                                  Seq(a, b, c).map(v => v.id -> (0.0, 1.0)).toMap)

  private def encodingOf(body: Expr, mode: DiscontinuityMode): Either[String, IbexEncoding] = {
    val (guards, paths) = extract(body)
    GuardRegions.encode(guards, paths, unitBox, mode)
  }

  private def regionsOf(body: Expr, mode: DiscontinuityMode): Either[String, Seq[GuardRegion]] =
    encodingOf(body, mode).map(_.regions)

  private val four = Float64Literal(4.0)

  /** `if (a < b) { if (b < c) 1.0 else 2.0 } else { if (a < c) 3.0 else 4.0 }`: four pairs
    * across the outer guard, one across each inner one.
    */
  private def balanced(first: Expr = one) =
    IfExpr(FPLessThan(a, b), IfExpr(FPLessThan(b, c), first, two),
           IfExpr(FPLessThan(a, c), three, four))

  test("linear-refine starts with one extrema query per guard, with max and min") {
    val regions = regionsOf(balanced(), DiscontinuityMode.LinearRefine).orFail

    // The outer guard has four pairs: one extrema query, with both a max and a min per side.
    assert(regions(0).comparisons.map(_.pairLeaves) == Seq(None))
    assert(regions(0).comparisons.head.choices.isEmpty)
    val objective = regions(0).comparisons.head.objective
    assert(inox.trees.exprOps.exists { case _: inox.trees.RealMin => true; case _ => false }(objective))
    assert(inox.trees.exprOps.exists { case _: inox.trees.RealMax => true; case _ => false }(objective))
  }

  test("linear-refine bounds a guard with fewer than three pairs pair by pair") {
    val regions = regionsOf(balanced(), DiscontinuityMode.LinearRefine).orFail
    assert(regions.drop(1).map(_.comparisons.flatMap(_.pairLeaves)) == Seq(Seq((0, 1)), Seq((2, 3))))
  }

  test("without refinement, a guard with fewer than three pairs is one block too") {
    val (guards, paths) = extract(balanced())
    val regions = GuardRegions.encode(guards, paths, unitBox, DiscontinuityMode.LinearRefine,
                                      smallGuardsByPairs = false).orFail.regions
    assert(regions.map(_.comparisons.map(_.pairLeaves)) == Seq(Seq(None), Seq(None), Seq(None)))
  }

  test("linear-refine asks nothing about a guard whose leaves all compute the same thing") {
    val sameLeaves = IfExpr(FPLessThan(a, b), one, one)
    val regions = regionsOf(sameLeaves, DiscontinuityMode.LinearRefine).orFail
    assert(regions.map(_.comparisons) == Seq(Seq.empty))
  }

  private val rm = RoundNearestTiesToEven

  /** The mode `balanced(leaf)` is bounded with when `linear-refine` is asked for. */
  private def modeWith(leaf: Expr): DiscontinuityMode =
    encodingOf(balanced(leaf), DiscontinuityMode.LinearRefine).orFail.mode

  test("linear-refine keeps a leaf that is defined everywhere on the input box") {
    // On [0, 1], `a + 1` is in [1, 2] and `a` is not negative.
    assert(modeWith(FPDiv(rm, one, FPAdd(rm, a, one))) == DiscontinuityMode.LinearRefine)
    assert(modeWith(Sqrt(rm, a)) == DiscontinuityMode.LinearRefine)
  }

  test("linear-refine falls back to pairs when a leaf may be undefined on the input box") {
    // On [0, 1], `a` can be 0 and `a - b` can be negative.
    assert(modeWith(FPDiv(rm, one, a)) == DiscontinuityMode.Pairs)
    assert(modeWith(Sqrt(rm, FPSub(rm, a, b))) == DiscontinuityMode.Pairs)

    // The fallback holds for the whole function: the outer guard is bounded pair by pair too.
    val regions = regionsOf(balanced(FPDiv(rm, one, a)), DiscontinuityMode.LinearRefine).orFail
    assert(regions.head.comparisons.map(_.pairLeaves) ==
             Seq(Some((0, 2)), Some((0, 3)), Some((1, 2)), Some((1, 3))))
  }

  test("a leaf on a path neither run reaches is in no comparison, and does not make " +
       "linear-refine fall back") {
    val (guards, paths) = extract(balanced(FPDiv(rm, one, a)))
    val encoding = GuardRegions.encode(guards, paths, unitBox, DiscontinuityMode.LinearRefine,
                                       reachedByNeither = Set(0)).orFail
    assert(encoding.mode == DiscontinuityMode.LinearRefine)
    val compared = encoding.regions.flatMap(_.comparisons).flatMap {
      case Comparison.Pair(taken, untaken, _, _) => Seq(taken, untaken)
      case Comparison.Block(_, taken, untaken) => (taken ++ untaken).map(_.leaf)
    }
    assert(compared.nonEmpty && !compared.contains(0))
  }

  private val minusInfinity = Float64Literal(Double.NegativeInfinity)
  private val nan = Float64Literal(Double.NaN)

  test("a leaf that returns an infinity or NaN is in no comparison") {
    // Leaf 0 is the one taken out: the outer guard compares leaf 1 with leaves 2 and 3 only.
    def outerPairs(leaf: Expr) =
      regionsOf(balanced(leaf), DiscontinuityMode.LinearRefine).orFail.head.comparisons.flatMap(_.pairLeaves)
    val named = ValDef.fresh("average", f64)
    assert(outerPairs(minusInfinity) == Seq((1, 2), (1, 3)))
    assert(outerPairs(nan) == Seq((1, 2), (1, 3)))
    assert(outerPairs(Let(named, nan, named.toVariable)) == Seq((1, 2), (1, 3)))
  }

  test("an input with a range is neither an infinity nor NaN, so the branches testing it go") {
    val body = IfExpr(FPIsInfinite(a), one, IfExpr(Not(FPIsNaN(b)), b, two))
    assert(Preprocessor.withFiniteInputs(body, unitBox.ranges) == Right(b))
  }

  test("an input bounded on one side only may be an infinity, so its test is refused") {
    val body = IfExpr(FPIsInfinite(a), one, a)
    Preprocessor.withFiniteInputs(body, Map(a.id -> (0.0, Double.PositiveInfinity))) match {
      case Left(why) => assert(why.contains(s"'${a.id.name}'"))
      case Right(answered) => fail(s"the test was answered: $answered")
    }
  }

  test("a power takes any exponent, as `exp(y * log(b))`") {
    val pow = FreshIdentifier("stainless.math.pow")
    def power(base: Expr) = FunctionInvocation(pow, Seq.empty, Seq(base, FPMul(rm, a, b)))

    // `2^(a * b)` is written `exp(a * b * log(2))`, which is defined everywhere.
    assert(modeWith(power(two)) == DiscontinuityMode.LinearRefine)
    val objectives = regionsOf(balanced(power(two)), DiscontinuityMode.LinearRefine).orFail
      .flatMap(_.comparisons.map(_.objective))
    assert(objectives.exists(inox.trees.exprOps.exists {
      case inox.trees.RealExp(inox.trees.Times(_, inox.trees.RealLog(_))) => true
      case _ => false
    }))
    // On [0, 1], `a` can be 0, where `log(a)` is undefined, as `a^(a * b)` is at `a = 0`
    // when `b = 0`.
    assert(modeWith(power(a)) == DiscontinuityMode.Pairs)
    // `(a + 1)^(a * b)` is defined everywhere on [0, 1].
    assert(modeWith(power(FPAdd(rm, a, one))) == DiscontinuityMode.LinearRefine)
  }

  /** The block of the outer guard of `balanced()`. */
  private def rootBlock: Comparison.Block =
    regionsOf(balanced(), DiscontinuityMode.LinearRefine).orFail.head.comparisons.head match {
      case block: Comparison.Block => block
      case pair => fail(s"the outer guard was bounded pair by pair: $pair")
    }

  test("linear-refine splits a block along the next guard of its larger side, down to pairs") {
    val root = rootBlock
    def leavesOf(block: Comparison.Block) = (block.taken ++ block.untaken).map(_.leaf).sorted

    // Both sides have two leaves, so the taken side is split at `b < c` (guard 1).
    val halves = GuardRegions.splitBlock(root)
    assert(halves.map(_.choices) == Seq(Seq(BranchChoice(1, true)), Seq(BranchChoice(1, false))))
    assert(halves.map(leavesOf) == Seq(Seq(0, 2, 3), Seq(1, 2, 3)))

    // Then the untaken side, at `a < c` (guard 2), which leaves single pairs.
    val quarters = GuardRegions.splitBlock(halves.head)
    assert(quarters.map(_.choices) == Seq(Seq(BranchChoice(1, true), BranchChoice(2, true)),
                                          Seq(BranchChoice(1, true), BranchChoice(2, false))))
    assert(quarters.map(leavesOf) == Seq(Seq(0, 2), Seq(0, 3)))
    assert(quarters.forall(q => GuardRegions.splitBlock(q).isEmpty))
  }

  test("an extrema block holds the branches its leaves left on a side share") {
    val root = rootBlock
    // Nothing is shared while both leaves of each side are left.
    assert(GuardRegions.withSharedBranchesFactoredOut(root) == root)

    // As if leaf 1 had been found unreachable: leaf 0 alone is left on the taken side.
    val narrowed = root.copy(taken = root.taken.filterNot(_.leaf == 1))
    val tightened = GuardRegions.withSharedBranchesFactoredOut(narrowed)
    assert(tightened.choices == Seq(BranchChoice(1, true)))
    assert(tightened.taken.map(_.leaf) == Seq(0))
    assert(tightened.untaken.map(_.leaf).sorted == Seq(2, 3))
    assert(tightened.taken.head.choices.isEmpty)
  }

  test("a block with one leaf left on each side holds both paths, and is a pair") {
    val root = rootBlock
    val leftOver = root.copy(taken = root.taken.filter(_.leaf == 0), untaken = root.untaken.filter(_.leaf == 2))
    val pair = GuardRegions.withSharedBranchesFactoredOut(leftOver)
    assert(pair.choices == Seq(BranchChoice(1, true), BranchChoice(2, true)))
    assert(GuardRegions.splitBlock(pair).isEmpty)
  }

  test("the discontinuity modes are read by their command-line names") {
    assert(DiscontinuityMode.values.toSeq.map(m => DiscontinuityMode.tryFromString(m.label)) ==
             DiscontinuityMode.values.toSeq.map(Some(_)))
    assert(DiscontinuityMode.tryFromString("linear-refine") == Some(DiscontinuityMode.LinearRefine))
  }

  test("only the constraints linked to an objective are kept for its search") {
    import inox.trees.{LessEquals => Le, Plus => Add, FractionLiteral => Lit, RealType, Variable => RVar}
    val Seq(p, q, r, s) = Seq("p", "q", "r", "s").map(RVar.fresh(_, RealType()))
    val onP = Le(p, Lit(1, 1))            // read by the objective
    val pq = Le(Add(p, q), Lit(2, 1))     // linked to the objective through p
    val onQ = Le(q, Lit(3, 1))            // linked through pq
    val rs = Le(Add(r, s), Lit(4, 1))     // r and s are never read
    val constant = Le(Lit(1, 1), Lit(2, 1))

    assert(IbexRunner.constraintsLinkedTo(p, Seq(rs, onP, onQ, pq, constant)) == Seq(onP, onQ, pq, constant))
    // A constant objective keeps everything, since Ibex needs at least one variable.
    assert(IbexRunner.constraintsLinkedTo(Lit(5, 1), Seq(rs, onP)) == Seq(rs, onP))
  }

  test("every path the body spells out is listed, in order") {
    val (guards, paths) = extract(nested)

    assert(guards.size == 2)
    assert(paths.map(_.leaf) == Seq(one, two, three))
  }

  test("a match is one conditional per case, and a literal case is matched with ==") {
    // `a match { case 0.0 => 1.0; case s if s < b => 2.0; case _ => 3.0 }`
    val s = ValDef.fresh("s", f64)
    val body = MatchExpr(a, Seq(
      MatchCase(LiteralPattern(None, Float64Literal(0.0)), None, one),
      MatchCase(WildcardPattern(Some(s)), Some(FPLessThan(s.toVariable, b)), two),
      MatchCase(WildcardPattern(None), None, three)))
    val fd = new FunDef(FreshIdentifier("f"), Seq.empty, Seq(a.toVal, b.toVal), f64, body,
                        Seq.empty)
    given Symbols = NoSymbols.withFunctions(Seq(fd))

    val (rewritten, _, _) = Preprocessor(fd).orFail
    val (guards, paths) = extract(rewritten)

    // Each side reads the matched value through the binding the match introduced.
    def withoutBindings(e: Expr): Expr = e match {
      case Let(vd, value, body) => withoutBindings(exprOps.replaceFromSymbols(Map(vd -> value), body))
      case other => other
    }
    val zero = Float64Literal(0.0)
    // `a == 0.0` is two guards, and the case after it is reached either way of its band.
    assert(guards.map(g => (withoutBindings(g.lhs), withoutBindings(g.rhs), g.strict)) ==
             Seq((a, zero, false), (zero, a, false), (a, b, true), (a, b, true)))
    assert(paths.map(_.leaf) == Seq(one, two, three, two, three))
  }

  test("a guard written the other way round is oriented") {
    val (guards, _) = extract(IfExpr(FPGreaterEquals(a, b), one, two))

    // `a >= b` is `b <= a`.
    assert(guards == Seq(Guard(b, a, strict = false)))
  }

  test("a connective is written out as nesting, one guard per comparison") {
    val body = IfExpr(And(Seq(FPLessThan(a, b), FPLessThan(b, c))), one, two)
    val (guards, paths) = extract(body)

    assert(guards == Seq(Guard(a, b, strict = true), Guard(b, c, strict = true)))
    // The else leaf is reached both by failing the first conjunct and by failing the second.
    assert(paths.map(_.leaf) == Seq(one, two, two))
  }

  private val spec = InputSpec(FPPrecision.Binary64,
                              Map(a.id -> (0.0, 100.0), b.id -> (0.0, 100.0)))

  /** `a < 2.0`, as `PathExtractor` orients it. */
  private val below = Guard(a, two, strict = true)

  private def narrow(guard: Guard, taken: Boolean): (Double, Double) =
    InputRanges.rangesAlongPath(spec, Seq(guard), exactInputs = true)(Seq(BranchChoice(0, taken)))
      .get.ranges(a.id)

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
    val kept =
      InputRanges.rangesAlongPath(spec, Seq(between), exactInputs = true)(Seq(BranchChoice(0, true)))
    assert(kept.get.ranges == spec.ranges)
  }

  test("a guard on a computed value says nothing about the inputs under it") {
    val computed = Guard(FPMul(RoundNearestTiesToEven, a, a), two, strict = true)
    val kept =
      InputRanges.rangesAlongPath(spec, Seq(computed), exactInputs = true)(Seq(BranchChoice(0, true)))
    assert(kept.get.ranges == spec.ranges)
  }

  private def quotient(n: Double, d: Double): Expr =
    FPDiv(RoundNearestTiesToEven, Float64Literal(n), Float64Literal(d))

  test("a side with no inputs narrows as the literal it computes, as in `x <= 3.0 / 8.0`") {
    assert(narrow(Guard(a, quotient(3.0, 8.0), strict = false), taken = true) == (0.0, 0.375))
    assert(narrow(Guard(quotient(3.0, 8.0), a, strict = false), taken = true) == (0.375, 100.0))
  }

  test("that literal is the one the floating-point program compares against, rounded") {
    assert(narrow(Guard(a, quotient(1.0, 3.0), strict = false), taken = true) == (0.0, 1.0 / 3.0))
  }

  test("a side with no inputs that is not finite narrows nothing") {
    assert(narrow(Guard(a, quotient(1.0, 0.0), strict = false), taken = true) == (0.0, 100.0))
  }

  test("for both runs, a side with no inputs narrows only when it is computed exactly") {
    def narrowForBothRuns(guard: Guard): (Double, Double) =
      InputRanges.rangesAlongPath(spec, Seq(guard), exactInputs = true, forBothRuns = true)(
        Seq(BranchChoice(0, taken = true))).get.ranges(a.id)
    // 3/8 is a double, but 1/3 is not: the exact run compares with 1/3 itself.
    assert(narrowForBothRuns(Guard(a, quotient(3.0, 8.0), strict = false)) == (0.0, 0.375))
    assert(narrowForBothRuns(Guard(a, quotient(1.0, 3.0), strict = false)) == (0.0, 100.0))
  }

  test("a guard the box already decides leaves the range as it was") {
    val wide = Guard(a, Float64Literal(500.0), strict = true)
    assert(narrow(wide, taken = true) == (0.0, 100.0))
  }

  test("a guard that rules out every value of an input leaves the path unreachable") {
    val impossible = Guard(a, Float64Literal(-5.0), strict = true)
    def along(taken: Boolean) =
      InputRanges.rangesAlongPath(spec, Seq(impossible), exactInputs = false)(Seq(BranchChoice(0, taken)))
    assert(along(taken = true).isEmpty)
    assert(along(taken = false).isDefined)
  }

  test("with rounded inputs, the literal moves one step out, as the input may round onto it") {
    val below = Guard(a, two, strict = false)
    def along(taken: Boolean) =
      InputRanges.rangesAlongPath(spec, Seq(below), exactInputs = false)(Seq(BranchChoice(0, taken)))
        .get.ranges(a.id)
    // `round(a) <= 2.0` holds for an `a` just above 2.0, which rounds down onto it.
    assert(along(taken = true) == (0.0, Math.nextUp(2.0)))
    assert(along(taken = false) == (Math.nextDown(2.0), 100.0))
  }

  test("nested guards narrow from both sides") {
    val lower = Guard(Float64Literal(10.0), a, strict = true)
    val upper = Guard(a, Float64Literal(40.0), strict = true)
    val both = InputRanges.rangesAlongPath(spec, Seq(lower, upper), exactInputs = true)(
                 Seq(BranchChoice(0, true), BranchChoice(1, true)))
    assert(both.get.ranges(a.id) == (10.0, 40.0))
  }
}
