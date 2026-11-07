/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification
package roundoff

import trees._
import inox.{trees => real}
import inox.solvers.SolverResponses._
import inox.solvers.smtlib.optimization.{IbexOptimizer, ObjectiveBounds}
import scala.collection.mutable

/* How far reading a guard the wrong way can move the result:
 *  - [[GuardRegions]]: the paths of a function as real-arithmetic problems, one region per guard;
 *  - [[DivergenceSearch]]: which comparisons to ask about, in which order, with how much time;
 *  - [[IbexRunner]]: one comparison asked to Ibex;
 *  - [[Witness]]: what each query found, for people and for the fuzzer.
 *
 * A divergence across a guard is bounded where the guard can be read the wrong way: its two
 * sides are within the sum of their errors (the band). Above the guard, both runs took the
 * same branches, so those hold exactly. Below it, each run took its own, so each branch is
 * relaxed by its guard's error.
 */

/** How far apart leaves on the two sides of one guard can be. */
enum Comparison {
  /** Two leaves, by index: their difference can have either sign.
    * @param choices the conditions that hold for the two paths to be taken
   *                at the same time after the guard
    */
  case Pair(taken: Int, untaken: Int, choices: Seq[BranchChoice], difference: real.Expr)

  /** Every pair of a taken leaf `t` and an untaken leaf `u` at once (an extrema query), since
    * `|u - t| <= max(max(U) - min(T), max(T) - min(U))`.
    *
    * @param choices the conditions that hold for all the paths in the block
    * @param taken   the leaves `T` on the then-side of the guard
    * @param untaken the leaves `U` on the else-side of the guard
    */
  case Block(choices: Seq[BranchChoice], taken: Seq[Candidate], untaken: Seq[Candidate])

  def choices: Seq[BranchChoice]

  /** The distance to bound. */
  def objective: real.Expr = this match {
    case Pair(_, _, _, difference) => difference
    case block: Block => GuardRegions.extremaDistance(block).getOrElse(real.FractionLiteral(0, 1))
  }

  /** `(taken, untaken)` for a pair. */
  def pairLeaves: Option[(Int, Int)] = this match {
    case Pair(taken, untaken, _, _) => Some((taken, untaken))
    case _: Block => None
  }
}

/** One leaf of a block: its value, and the branches its path takes below the block's
  * `choices`.
  */
case class Candidate(leaf: Int, value: real.Expr, choices: Seq[BranchChoice])

/** Where reading one guard the wrong way can move the result.
  *
  * @param shared          the input ranges and the branches above the guard
  * @param comparisons     pairs, built only as far as they are read since there can be
  *                        quadratically many, or one block
  * @param comparisonCount how many `comparisons` there are, known without building them
  */
case class GuardRegion(
  guard: Int,
  vars: Seq[real.ValDef],
  shared: Seq[real.Expr],
  comparisons: Seq[Comparison],
  comparisonCount: Long
)

/** What one function's paths become for Ibex.
  *
  * @param guardDifferences per guard, `lhs - rhs`
  * @param mode             the mode asked for, unless [[GuardRegions.modeUsed]] fell back to `pairs`
  */
case class IbexEncoding(guardDifferences: Seq[real.Expr], regions: Seq[GuardRegion],
                    mode: DiscontinuityMode)

object GuardRegions {

  /** One region per guard, and per guard `lhs - rhs`.
    *
    * @param reachedByNeither   the paths no input reaches in either run, whose leaves are in no
    *                           comparison: they cannot diverge, and one undefined somewhere would
    *                           make a block lose points where others diverge, or fall back to
    *                           `pairs` ([[modeUsed]])
    * @param smallGuardsByPairs in `linear-refine` mode, whether a guard with few pairs
    *                           ([[minPairsForBlock]]) is bounded pair by pair, as refinement would
    *                           end up doing. Without refinement every guard has one block
    */
  def encode(guards: Seq[Guard], paths: Seq[ProgramPath], spec: InputSpec,
             asked: DiscontinuityMode, timeLimit: TimeLimit = TimeLimit.never,
             reachedByNeither: Set[Int] = Set.empty, smallGuardsByPairs: Boolean = true)
    : Either[String, IbexEncoding] = {

    val splits = splitsOf(paths)

    val inputs = (paths.map(_.leaf) ++ guards.flatMap(g => Seq(g.lhs, g.rhs)))
      .flatMap(exprOps.variablesOf)
      .distinctBy(_.id)
      .sortBy(_.id.globalId)

    // The real variables keep the identifiers of the floating-point ones, so that a
    // counter-example stays readable. The two kinds never appear in the same query.
    val realVariables: Map[Identifier, real.Variable] =
      inputs.map(v => v.id -> real.Variable(v.id, real.RealType(), Seq.empty)).toMap

    // An infinity or NaN has no real counterpart, so its leaf is in no comparison. Where an
    // input may reach it the obligation is unknown anyway ([[RoundingError.Infinite]]), and
    // where none does neither run returns it.
    val nonFinite = paths.indices
      .filter(i => valueWithoutInputs(paths(i).leaf, spec.precision)
                     .exists(d => d.isInfinite || d.isNaN))
      .toSet
    val leftOut = nonFinite ++ reachedByNeither

    for {
      _ <- spec.missingRangeMessage(inputs.map(_.id)).toLeft(())
      realLeaves <- traverse(paths.indices.filterNot(leftOut)) { i =>
        timeLimit.check()
        RealEncoder(paths(i).leaf, realVariables).map(i -> _)
      }.map(_.toMap)
      realGuardOperands <- traverse(guards) { guard =>
        for {
          lhs <- RealEncoder(guard.lhs, realVariables)
          rhs <- RealEncoder(guard.rhs, realVariables)
        } yield (lhs, rhs)
      }
    } yield {
      val mode = modeUsed(asked, realLeaves.values.toSeq, spec)

      val rangeConstraints = inputs.flatMap { input =>
        val (low, high) = spec.ranges(input.id)
        Seq(real.LessEquals(Fraction.toExpr(low), realVariables(input.id)),
            real.LessEquals(realVariables(input.id), Fraction.toExpr(high)))
      }

      def branchCondition(choice: BranchChoice): real.Expr = {
        val (lhs, rhs) = realGuardOperands(choice.guard)
        val guard = guards(choice.guard)
        // Negating a comparison swaps its sides and its strictness. Between integers,
        // `a < b` is `a <= b - 1`, which keeps Ibex off the values in between.
        def orderedConstraint(small: real.Expr, large: real.Expr, strict: Boolean): real.Expr =
          if (!strict) real.LessEquals(small, large)
          else if (guard.integral)
            real.LessEquals(small, real.Minus(large, real.FractionLiteral(1, 1)))
          else real.LessThan(small, large)

        if (choice.taken) orderedConstraint(lhs, rhs, guard.strict) else orderedConstraint(rhs, lhs, !guard.strict)
      }

      def pairComparisons(split: GuardSplit): Seq[Comparison] =
        for (((takenPath, takenLeaf), (untakenPath, untakenLeaf)) <- split.pairs)
        yield Comparison.Pair(takenLeaf, untakenLeaf,
                              split.choicesBelow(takenPath) ++ split.choicesBelow(untakenPath),
                              real.Minus(realLeaves(untakenLeaf), realLeaves(takenLeaf)))

      def blockComparison(split: GuardSplit): Option[Comparison] =
        if (!split.hasDistinctLeaves) None
        else {
          def candidatesOf(entries: Seq[(ProgramPath, Int)]) = entries.map {
            case (path, i) => Candidate(i, realLeaves(i), split.choicesBelow(path))
          }
          val block: Comparison.Block =
            Comparison.Block(Seq.empty, candidatesOf(split.taken), candidatesOf(split.untaken))
          Option.when(canDiverge(block))(block)
        }

      val vars = inputs.map(input => realVariables(input.id).toVal)

      val regions = splits.map { split =>
        timeLimit.check()
        val withoutLeftOut = split.withoutPaths(leftOut)
        val (comparisons, count) =
          if (mode == DiscontinuityMode.Pairs || (smallGuardsByPairs && withoutLeftOut.hasFewPairs))
            (pairComparisons(withoutLeftOut), withoutLeftOut.pairCount)
          else {
            val blockIfAny = blockComparison(withoutLeftOut).toSeq
            (blockIfAny, blockIfAny.size.toLong)
          }
        GuardRegion(split.guard, vars, rangeConstraints ++ split.above.map(branchCondition), comparisons, count)
      }

      IbexEncoding(realGuardOperands.map { case (lhs, rhs) => real.Minus(lhs, rhs) }, regions, mode)
    }
  }

  /** `linear-refine` falls back to `pairs` for the whole function when one of its leaves may be
    * undefined somewhere on the input box. Ibex drops the points where an objective is
    * undefined, and a block evaluates every leaf outside its own branches, so an unrelated leaf
    * could hide the point where a divergence happens.
    */
  private def modeUsed(asked: DiscontinuityMode, leaves: Seq[real.Expr], spec: InputSpec)
    : DiscontinuityMode =
    if (asked == DiscontinuityMode.LinearRefine &&
        !leaves.distinct.forall(IntervalChecks.definedEverywhere(_, spec.ranges)))
      DiscontinuityMode.Pairs
    else asked

  /** `block` holding the branches all its candidates on a side share. Every pair it compares
    * needs them, so adding them shrinks its region without losing a pair.
    */
  def withSharedBranchesFactoredOut(block: Comparison.Block): Comparison.Block = {
    def sharedBranches(side: Seq[Candidate]): Seq[BranchChoice] =
      side.map(_.choices).reduceOption { (a, b) =>
        a.zip(b).takeWhile { case (x, y) => x == y }.map(_._1)
      }.getOrElse(Seq.empty)

    def withoutShared(side: Seq[Candidate], shared: Seq[BranchChoice]): Seq[Candidate] =
      side.map(c => c.copy(choices = c.choices.drop(shared.size)))

    val takenShared = sharedBranches(block.taken)
    val untakenShared = sharedBranches(block.untaken)
    Comparison.Block(block.choices ++ takenShared ++ untakenShared,
                     withoutShared(block.taken, takenShared),
                     withoutShared(block.untaken, untakenShared))
  }

  /** A [[withSharedBranchesFactoredOut]] block split in two: the side with more leaves is cut at the guard where its
    * leaves part, and each half holds its branch of that guard and the whole other side. Every
    * pair of the block is in exactly one half.
    *
    * Nothing when the block holds one leaf on each side, so it is a pair. A half whose leaves
    * all compute the same thing cannot diverge and is left out.
    */
  def splitBlock(block: Comparison.Block): Seq[Comparison.Block] = {
    def splittable(side: Seq[Candidate]) = side.size > 1 && side.forall(_.choices.nonEmpty)

    /** `side` cut at its next guard: each half with its branch of that guard, then-branch first. */
    def halvesOf(side: Seq[Candidate]): Seq[(BranchChoice, Seq[Candidate])] =
      side.groupBy(_.choices.head).toSeq.sortBy { case (branch, _) => !branch.taken }
        .map { case (branch, half) => (branch, half.map(c => c.copy(choices = c.choices.tail))) }

    // The side with more leaves is cut, the then-side when both have as many.
    val cutTaken = splittable(block.taken) &&
      (!splittable(block.untaken) || block.taken.size >= block.untaken.size)
    val halves: Seq[Comparison.Block] =
      if (cutTaken)
        halvesOf(block.taken).map[Comparison.Block] { case (branch, half) =>
          Comparison.Block(block.choices :+ branch, half, block.untaken)
        }
      else if (splittable(block.untaken))
        halvesOf(block.untaken).map[Comparison.Block] { case (branch, half) =>
          Comparison.Block(block.choices :+ branch, block.taken, half)
        }
      else Seq.empty
    halves.filter(canDiverge)
  }

  /** In `linear-refine` mode with refinement, a guard with fewer pairs is bounded pair by pair.
    */
  private val minPairsForBlock = 3

  /** The paths through one guard, split by the side they take.
    *
    * @param above the conditions above the guard, the same for every path through it
    */
  private case class GuardSplit(guard: Int, above: Seq[BranchChoice],
                           taken: Seq[(ProgramPath, Int)], untaken: Seq[(ProgramPath, Int)]) {

    def choicesBelow(path: ProgramPath): Seq[BranchChoice] =
      path.choices.drop(path.choices.indexWhere(_.guard == guard) + 1)

    /** The pairs of a taken and an untaken leaf that compute different things. */
    lazy val pairs: LazyList[((ProgramPath, Int), (ProgramPath, Int))] =
      for {
        t @ (takenPath, _) <- taken.to(LazyList)
        u @ (untakenPath, _) <- untaken
        if takenPath.leaf != untakenPath.leaf
      } yield (t, u)

    /** How many [[pairs]] there are, counted by leaf without building them. */
    def pairCount: Long = {
      val untakenPerLeaf = untaken.groupMapReduce(_._1.leaf)(_ => 1L)(_ + _)
      val sameLeaf = taken.map { case (path, _) => untakenPerLeaf.getOrElse(path.leaf, 0L) }.sum
      taken.size.toLong * untaken.size - sameLeaf
    }

    def hasFewPairs: Boolean = pairs.lengthCompare(minPairsForBlock) < 0

    def hasDistinctLeaves: Boolean = (taken ++ untaken).map(_._1.leaf).distinct.size > 1

    def withoutPaths(leftOut: Int => Boolean): GuardSplit =
      copy(taken = taken.filterNot(entry => leftOut(entry._2)),
           untaken = untaken.filterNot(entry => leftOut(entry._2)))
  }

  /** For each guard at least two paths go through, in the order of the guards, the paths that
    * take its then-branch and those that take its else-branch. One pass over the paths'
    * branches, so that it stays linear in their total length.
    */
  private def splitsOf(paths: Seq[ProgramPath]): Seq[GuardSplit] = {
    /** Path number `index` where it passes a guard: the branch it takes, at `depth` on it. */
    case class PathAtGuard(path: ProgramPath, index: Int, choice: BranchChoice, depth: Int)

    val pathsAtGuard: Map[Int, Seq[PathAtGuard]] =
      paths.zipWithIndex
        .flatMap { case (path, index) =>
          path.choices.zipWithIndex.map { case (choice, depth) => PathAtGuard(path, index, choice, depth) }
        }
        .groupBy(_.choice.guard)

    pathsAtGuard.toSeq.sortBy { case (guard, _) => guard }.collect {
      case (guard, atGuard) if atGuard.size > 1 =>
        val (taken, untaken) = atGuard.partition(_.choice.taken)
        // Every path through a guard takes the same branches above it.
        val first = atGuard.head
        GuardSplit(guard, first.path.choices.take(first.depth),
                   taken.map(p => (p.path, p.index)), untaken.map(p => (p.path, p.index)))
    }
  }

  /** Whether some pair of `block` can diverge: both sides hold a leaf, and two leaves compute
    * different things.
    */
  private def canDiverge(block: Comparison.Block): Boolean = distanceTerms(block).isDefined

  /** `max(max(U) - min(T), max(T) - min(U))` over the values of the leaves of `block`. */
  def extremaDistance(block: Comparison.Block): Option[real.Expr] =
    distanceTerms(block).map(realMaxOf)

  /** The two directions a jump can go, which can be bounded one at a time: an untaken leaf
    * above a taken one, `max(U) - min(T)`, and a taken leaf above an untaken one,
    * `max(T) - min(U)`.
    */
  def distanceTerms(block: Comparison.Block): Option[Seq[real.Expr]] = {
    def values(side: Seq[Candidate]) = side.map(_.value).distinct
    val (taken, untaken) = (values(block.taken), values(block.untaken))

    Option.when(taken.nonEmpty && untaken.nonEmpty && (taken ++ untaken).distinct.size > 1) {
      Seq(real.Minus(realMaxOf(untaken), realMinOf(taken)),
          real.Minus(realMaxOf(taken), realMinOf(untaken)))
    }
  }

  private def realMaxOf(es: Seq[real.Expr]): real.Expr =
    if (es.size == 1) es.head else real.RealMax(es)

  private def realMinOf(es: Seq[real.Expr]): real.Expr =
    if (es.size == 1) es.head else real.RealMin(es)
}

/** A floating-point expression as the real-arithmetic expression it approximates. */
private[roundoff] object RealEncoder {

  import inox.trees.{Plus, Minus, Times, Division, UMinus}

  def apply(e: Expr, realVariables: Map[Identifier, inox.trees.Variable])
    : Either[String, inox.trees.Expr] = {

    def encodeBoth(build: (inox.trees.Expr, inox.trees.Expr) => inox.trees.Expr, l: Expr, r: Expr) =
      apply(l, realVariables).flatMap(a => apply(r, realVariables).map(build(a, _)))

    e match {
      case v: Variable => realVariables.get(v.id).toRight(s"unbound variable '${v.id.name}'")
      case FPLit(d) =>
        Fraction(d).map(r => inox.trees.FractionLiteral(r.num, r.den))

      // Rounding modes do not matter: this is the exact computation.
      case FPAdd(_, l, r) => encodeBoth(Plus(_, _), l, r)
      case FPSub(_, l, r) => encodeBoth(Minus(_, _), l, r)
      case FPMul(_, l, r) => encodeBoth(Times(_, _), l, r)
      case FPDiv(_, l, r) => encodeBoth(Division(_, _), l, r)
      case FPUMinus(a) => apply(a, realVariables).map(UMinus(_))
      case FPFMA(_, a, b, c) =>
        for {
          product <- encodeBoth(Times(_, _), a, b)
          addend <- apply(c, realVariables)
        } yield Plus(product, addend)

      // Integer arithmetic is exact, since Stainless checks that it does not overflow, and so
      // is its conversion: to `Double` up to 2^53, so an `Int` always, and to `Float` up to
      // 2^24, which [[InputRanges.inexactIntegerConversion]] checks.
      case IntLit(n) => Right(inox.trees.FractionLiteral(n, BigInt(1)))
      case trees.Plus(l, r) => encodeBoth(Plus(_, _), l, r)
      case trees.Minus(l, r) => encodeBoth(Minus(_, _), l, r)
      case trees.Times(l, r) => encodeBoth(Times(_, _), l, r)
      case trees.UMinus(a) => apply(a, realVariables).map(UMinus(_))
      case FPCast(_, _, _, inner) if isIntegral(inner) => apply(inner, realVariables)
      case BVWideningCast(inner, _) => apply(inner, realVariables)

      case Let(vd, value, body) =>
        val realVar = inox.trees.Variable(vd.id, inox.trees.RealType(), Seq.empty)

        for {
          realValue <- apply(value, realVariables)
          realBody <- apply(body, realVariables + (vd.id -> realVar))
        } yield inox.trees.Let(realVar.toVal, realValue, realBody)

      case TranscendentalFunctionCall(f, args) =>
        traverse(args)(apply(_, realVariables)).flatMap(realFunctionCall(f, _))

      case _: IfExpr =>
        Left("a conditional appears inside an expression, and only conditionals that shape " +
          "the body are supported")

      case other =>
        Left(s"no real-arithmetic equivalent for '$other'")
    }
  }

  /** Only Ibex among the solvers evaluates these. */
  private def realFunctionCall(f: TranscendentalFunction, args: Seq[inox.trees.Expr])
    : Either[String, inox.trees.Expr] = {
    import inox.trees.{FractionLiteral, RealAcos, RealAsin, RealAtan, RealCos, RealExp,
                       RealLog, RealPow, RealSin, RealSqrt, RealTan}

    (f, args) match {
      case (TranscendentalFunction.Sqrt, Seq(a)) => Right(RealSqrt(a))
      case (TranscendentalFunction.Exp, Seq(a)) => Right(RealExp(a))
      case (TranscendentalFunction.Log, Seq(a)) => Right(RealLog(a))
      case (TranscendentalFunction.Sin, Seq(a)) => Right(RealSin(a))
      case (TranscendentalFunction.Cos, Seq(a)) => Right(RealCos(a))
      case (TranscendentalFunction.Tan, Seq(a)) => Right(RealTan(a))
      case (TranscendentalFunction.Asin, Seq(a)) => Right(RealAsin(a))
      case (TranscendentalFunction.Acos, Seq(a)) => Right(RealAcos(a))
      case (TranscendentalFunction.Atan, Seq(a)) => Right(RealAtan(a))

      // Ibex takes only whole-number exponents. Any other power is `exp(y * log(b))`, as Daisy
      // reads it: the same number wherever `b` is positive. Where `b` may be zero or negative,
      // `log(b)` is undefined, as for any other partial function: [[IntervalChecks]] sends the
      // function to `pairs`, and Daisy refuses the leaf.
      case (TranscendentalFunction.Pow, Seq(base, exponent @ FractionLiteral(_, one)))
          if one == 1 =>
        Right(RealPow(base, exponent))
      case (TranscendentalFunction.Pow, Seq(base, exponent)) =>
        Right(RealExp(inox.trees.Times(exponent, RealLog(base))))

      case _ => Left(s"'${f.symbol}' was given ${args.size} arguments")
    }
  }
}

/** What interval arithmetic over a box of inputs shows about a real expression, computed over
  * exact fractions. It overestimates ranges, so a check can answer `false` where the property
  * holds, but never `true` where it does not.
  */
private[roundoff] object IntervalChecks {

  /** Whether every divisor leaves out 0 and every other partial function stays in its domain. */
  def definedEverywhere(e: real.Expr, box: Map[Identifier, (Double, Double)]): Boolean =
    !hasPartialOperation(e) || rangeOf(e, intervalOfInput(box)).isDefined

  /** Whether `-bound <= e <= bound` at every point of `box`. */
  def boundedBy(e: real.Expr, box: Map[Identifier, (Double, Double)], bound: Rational): Boolean =
    rangeOf(e, intervalOfInput(box)).exists(_.within(-bound, bound))

  private def intervalOfInput(box: Map[Identifier, (Double, Double)]): Identifier => Option[Interval] =
    id => box.get(id).map { case (low, high) =>
      Interval(Fraction(low).toOption, Fraction(high).toOption)
    }

  private def hasPartialOperation(e: real.Expr): Boolean = real.exprOps.exists {
    case _: real.Division | _: real.RealSqrt | _: real.RealLog | _: real.RealTan |
         _: real.RealAsin | _: real.RealAcos | _: real.RealPow => true
    case _ => false
  }(e)

  /** A range holding every value of `e`, or nothing when `e` may be undefined somewhere. */
  private def rangeOf(e: real.Expr, variables: Identifier => Option[Interval]): Option[Interval] = {
    def rangeOfPart(e: real.Expr) = rangeOf(e, variables)
    import Rational.{zero, one}

    e match {
      case real.FractionLiteral(n, d) => Some(Interval.point(Rational.of(n, d)))
      case v: real.Variable => variables(v.id)
      case real.Let(vd, value, body) =>
        rangeOfPart(value).flatMap { bound =>
          rangeOf(body, id => if (id == vd.id) Some(bound) else variables(id))
        }

      case real.Plus(a, b) => for (x <- rangeOfPart(a); y <- rangeOfPart(b)) yield x + y
      case real.Minus(a, b) => for (x <- rangeOfPart(a); y <- rangeOfPart(b)) yield x + -y
      case real.Times(a, b) => for (x <- rangeOfPart(a); y <- rangeOfPart(b)) yield x * y
      case real.Division(a, b) =>
        for (x <- rangeOfPart(a); y <- rangeOfPart(b); inverse <- y.reciprocal) yield x * inverse
      case real.UMinus(a) => rangeOfPart(a).map(-_)

      case real.RealPow(base, real.FractionLiteral(n, d)) if d == 1 && n.isValidInt =>
        rangeOfPart(base).flatMap { x =>
          if (n >= 0) Some(x.power(n.toInt)) else x.reciprocal.map(_.power(-n.toInt))
        }
      case real.RealSqrt(a) => rangeOfPart(a).filter(_.low.exists(_ >= zero)).map(_.sqrt)
      case real.RealLog(a) => rangeOfPart(a).filter(_.low.exists(_ > zero)).map(_ => Interval.whole)
      case real.RealExp(a) => rangeOfPart(a).map(_ => Interval(Some(zero), None))
      case real.RealSin(a) => rangeOfPart(a).map(_ => Interval.between(-one, one))
      case real.RealCos(a) => rangeOfPart(a).map(_ => Interval.between(-one, one))
      case real.RealAtan(a) => rangeOfPart(a).map(_ => Interval.whole)
      // The poles of `tan` nearest to 0 are at -pi/2 and pi/2, and 3/2 < pi/2.
      case real.RealTan(a) =>
        rangeOfPart(a).filter(_.within(Rational.of(-3, 2), Rational.of(3, 2))).map(_ => Interval.whole)
      case real.RealAsin(a) => rangeOfPart(a).filter(_.within(-one, one)).map(_ => Interval.whole)
      case real.RealAcos(a) => rangeOfPart(a).filter(_.within(-one, one)).map(_ => Interval.whole)

      case _ => None
    }
  }

  /** A closed range of reals, where `None` is an end without a bound. */
  private case class Interval(low: Option[Rational], high: Option[Rational]) {
    import Rational.{zero, one}

    def +(o: Interval): Interval =
      Interval(for (a <- low; b <- o.low) yield a + b, for (a <- high; b <- o.high) yield a + b)

    def unary_- : Interval = Interval(high.map(-_), low.map(-_))

    def *(o: Interval): Interval = (low, high, o.low, o.high) match {
      case (Some(a), Some(b), Some(c), Some(d)) =>
        val products = Seq(a * c, a * d, b * c, b * d)
        Interval(Some(products.min), Some(products.max))
      case _ => Interval.whole
    }

    def within(lowest: Rational, highest: Rational): Boolean =
      low.exists(_ >= lowest) && high.exists(_ <= highest)

    /** The range of `1 / x`, when 0 is left out. */
    def reciprocal: Option[Interval] = {
      def inverse(r: Rational) = one / r
      if (low.exists(_ > zero)) Some(Interval(Some(high.map(inverse).getOrElse(zero)), low.map(inverse)))
      else if (high.exists(_ < zero)) Some(Interval(high.map(inverse), Some(low.map(inverse).getOrElse(zero))))
      else None
    }

    /** The range of `x^n`, for `n >= 0`. */
    def power(n: Int): Interval = {
      val base = if (n % 2 == 0) absolute else this
      Interval(base.low.map(_.pow(n)), base.high.map(_.pow(n)))
    }

    def absolute: Interval =
      if (low.exists(_ >= zero)) this
      else if (high.exists(_ <= zero)) -this
      else Interval(Some(zero), for (a <- low; b <- high) yield Seq(-a, b).max)

    /** For `x >= 0`: `sqrt(x)` always lies between `x` and 1. */
    def sqrt: Interval =
      Interval(low.map(a => Seq(a, one).min), high.map(b => Seq(b, one).max))
  }

  private object Interval {
    val whole: Interval = Interval(None, None)
    def point(r: Rational): Interval = between(r, r)
    def between(low: Rational, high: Rational): Interval = Interval(Some(low), Some(high))
  }
}

/** The guards of one function over the reals: `lhs - rhs` for each, and how far the rounded
  * run can be from it, or nothing when a side may overflow.
  */
private[roundoff] final class GuardBands(differences: Seq[real.Expr],
                                         errors: Seq[Option[BigDecimal]]) {

  /** Whether both runs read `guard` the same way: its two sides are computed exactly. */
  def isExact(guard: Int): Boolean = errors(guard).exists(_ <= 0)

  /** Where `guard` can be read the wrong way: anywhere when a side may overflow. */
  def bandConstraints(guard: Int): Seq[real.Expr] =
    errors(guard).toSeq.flatMap { error =>
      val width = Fraction.toExpr(roundedUp(error))
      Seq(real.LessEquals(differences(guard), width),
          real.LessEquals(real.UMinus(differences(guard)), width))
    }

  /** `choices` as the rounded run reads them: relaxed by their errors, and dropped when a side
    * may overflow, since the guard can then be read either way.
    */
  def relaxedBranchConstraints(choices: Seq[BranchChoice]): Seq[real.Expr] =
    choices.flatMap { choice =>
      val difference = differences(choice.guard)
      errors(choice.guard).map { error =>
        real.LessEquals(if (choice.taken) difference else real.UMinus(difference),
                        Fraction.toExpr(roundedUp(error)))
      }
    }

  /** `d` rounded up to a double, which the solver reads exactly. Rounding up only makes the
    * region larger.
    */
  private def roundedUp(d: BigDecimal): Double = {
    val nearest = d.toDouble
    if (BigDecimal(nearest) >= d) nearest else Math.nextUp(nearest)
  }
}

/** How far apart the leaves of `comparison` in `region` can be.
  *
  * @param comparison   as it was bounded: a block holds only the leaves the region can reach
  * @param stoppedEarly Ibex's time limit stopped the search before it settled
  * @param isIncumbent  the bound is the incumbent, which the comparison was only shown not to
  *                     reach (dominated), rather than its own
  * @param seconds      the time its query was offered
  */
case class ComparisonBound(region: GuardRegion, comparison: Comparison, bound: BigDecimal,
                           stoppedEarly: Boolean = false, isIncumbent: Boolean = false,
                           seconds: Double = 0.0) {

  /** Whether asking again could lower the bound. */
  def improvable: Boolean = stoppedEarly || isIncumbent
}

/** Queries that share `seconds`: each may use the time left divided by the queries left, so
  * time one does not use goes to the next ones. Once that share is less than the shortest
  * search Ibex allows, the queries left share what is left of `limit` instead: going over
  * `seconds` then takes time from what was to come after them, rather than failing.
  */
private[roundoff] final class SharedQueryTime(seconds: Double, queries: Long, val limit: TimeLimit) {
  def this(seconds: Double, queries: Long) = this(seconds, queries, new TimeLimit(seconds))

  private val ownTime = new TimeLimit(seconds)
  private var queriesLeft = queries

  /** The bound a query must be able to reach to be worth bounding (`--roundoff-incumbent`).
    * The result must already include it: a dominated query reports it as its own bound.
    */
  var incumbent: BigDecimal = 0

  /** The seconds the next query may use, counted as asked. Throws [[OutOfTime]] instead when
    * that is less than the shortest search Ibex allows.
    */
  def secondsForNextQuery(): Double = {
    def shareOf(clock: TimeLimit) = clock.secondsLeft / queriesLeft.max(1)
    val planned = shareOf(ownTime)
    val share = if (planned >= IbexRunner.shortestSearchSeconds) planned else shareOf(limit)
    if (share < IbexRunner.shortestSearchSeconds)
      throw new OutOfTime(
        f"${limit.secondsLeft}%.3fs left for ${queriesLeft.max(0)} divergence queries, " +
        "less than the shortest search Ibex allows for each")
    queriesLeft -= 1
    share
  }
}

/** Bounds the divergences of one decomposition: a first pass, pair by pair or by linear
  * refinement, then a second pass on the time the first one left.
  */
private[roundoff] final class DivergenceSearch(ibex: IbexRunner, settings: RoundoffSettings,
                                               function: String,
                                               parts: RoundoffErrorDecomposition,
                                               guardErrors: Seq[Option[BigDecimal]]) {

  private val bands = new GuardBands(parts.guardDifferences, guardErrors)

  /** The comparisons Ibex is asked about, which share the time: one across a guard that both
    * runs read the same way is answered without Ibex.
    */
  private val queryCount: Long =
    parts.regions.filterNot(region => bands.isExact(region.guard)).map(_.comparisonCount).sum

  /** The largest divergence in each guard region, within `seconds`. */
  def largestDivergencePerGuard(seconds: Double): Either[String, Seq[BigDecimal]] = {
    val time = new TimeLimit(seconds)

    val firstPass =
      if (parts.discontinuity == DiscontinuityMode.LinearRefine) linearRefine(seconds)
      else pairByPair(parts.regions, new SharedQueryTime(seconds, queryCount))

    firstPass.map { firstBounds =>
      val byGuard = secondPass(firstBounds, time.secondsLeft)
        .groupMapReduce(_.region.guard)(_.bound)(_ max _)
      parts.regions.map(region => byGuard.getOrElse(region.guard, BigDecimal(0)))
    }
  }

  private def boundComparison(region: GuardRegion, comparison: Comparison, pass: SharedQueryTime)
    : Either[String, ComparisonBound] = {
    // Also for a comparison answered without Ibex, which `secondsForNextQuery` never sees.
    if (pass.limit.secondsLeft <= 0)
      throw new OutOfTime("the divergence queries took longer than their share of the budget")
    ibex.boundComparison(function, bands, region, comparison, pass)
  }

  /** A region across a guard both runs read the same way is answered by its first comparison
    * alone: every comparison in it has a bound of 0, and there can be millions of them.
    */
  private def pairByPair(regions: Seq[GuardRegion], pass: SharedQueryTime)
    : Either[String, Seq[ComparisonBound]] =
    traverse(regions) { region =>
      val asked =
        if (bands.isExact(region.guard)) region.comparisons.take(1) else region.comparisons
      traverse(asked)(boundComparison(region, _, pass))
    }.map(_.flatten)

  /** The time left goes to the comparisons that can still lower the result, the largest bound.
    *
    * A comparison can lower it if its bound is above every bound more time cannot lower, and
    * more time could lower its own. Those are asked again, largest first, with the largest
    * settled bound as the incumbent, and each keeps the smaller of its two bounds, since both
    * hold. A search stopped by its time limit is only asked again if it would get
    * [[secondPassGain]] times the time it was first offered; an incumbent bound needs no such
    * margin. The first comparison in order whose bound is not above all the kept ones ends
    * the pass.
    */
  private def secondPass(firstPass: Seq[ComparisonBound], seconds: Double)
    : Seq[ComparisonBound] = {
    val firstBounds = firstPass.toVector
    val largestSettledBound = (BigDecimal(0) +: firstBounds.filterNot(_.improvable).map(_.bound)).max
    val improvableIndices = firstBounds.indices.filter(i => firstBounds(i).improvable && firstBounds(i).bound > largestSettledBound)
    val toAskAgain = improvableIndices
      .filter(i => firstBounds(i).isIncumbent ||
                   firstBounds(i).seconds * secondPassGain <= seconds / improvableIndices.size)
      .sortBy(i => -firstBounds(i).bound)

    val secondBounds = mutable.Map.empty[Int, ComparisonBound]
    def bestBound(i: Int): ComparisonBound = secondBounds.get(i).map { second =>
      firstBounds(i).copy(bound = firstBounds(i).bound min second.bound,
                    stoppedEarly = second.stoppedEarly, isIncumbent = second.isIncumbent)
    }.getOrElse(firstBounds(i))

    var largestBound = (largestSettledBound +: improvableIndices.diff(toAskAgain).map(firstBounds(_).bound)).max
    if (toAskAgain.nonEmpty) {
      val pass = new SharedQueryTime(seconds, toAskAgain.size)
      pass.incumbent = largestSettledBound
      // `takeWhile` reads `largestBound` before each comparison, after the one before it was asked.
      try toAskAgain.iterator.takeWhile(firstBounds(_).bound > largestBound).foreach { i =>
        boundComparison(firstBounds(i).region, firstBounds(i).comparison, pass).foreach(secondBounds(i) = _)
        largestBound = largestBound max bestBound(i).bound
      } catch {
        case _: OutOfTime => ()
      }
    }

    firstBounds.indices.map(bestBound)
  }

  /** Ibex's bounds move by about one bisection level each time its time doubles, so the same
    * question with about the same time gets about the same answer.
    */
  private val secondPassGain = 4.0

  /** `linear-refine` mode, in three steps:
    *  1. the guards with few pairs are bounded pair by pair; their bounds are settled;
    *  2. every other guard is bounded as one block, which is open;
    *  3. while the largest open bound is above the largest settled one, that block is split
    *     in two ([[GuardRegions.splitBlock]]). Each half keeps the smaller of its own bound and
    *     its parent's, which covers every pair it holds. A block that cannot be split is a
    *     pair, and its bound is settled.
    *
    * Step 3 asks at most `--roundoff-refine-budget` queries per path, which keeps it linear,
    * and gets `--roundoff-refine-share` of `seconds` plus what steps 1 and 2 leave. Steps 1 and
    * 2 share the rest, and take step 3's time when they need more: they time out only when all
    * of `seconds` is used up, as without refinement, since there is no bound until every guard
    * has one. Step 3 only stops: its bounds are sound at every step. Each block is bounded with
    * the settled bound as the incumbent, so that it is never charged the bound of an open one.
    */
  private def linearRefine(seconds: Double): Either[String, Seq[ComparisonBound]] = {
    val refineQueryBudget = (settings.refineBudget * parts.leaves.size).toInt
    val withBlocks = parts.regions.map(region =>
      region -> region.comparisons.collectFirst { case block: Comparison.Block => block })
    val regionsWithoutBlock = withBlocks.collect { case (region, None) => region }
    val rootBlocks = withBlocks.collect { case (region, Some(block)) => (region, block) }

    val settledBounds = mutable.ArrayBuffer.empty[ComparisonBound]
    var largestSettledBound = BigDecimal(0)
    // A dominated query reports the incumbent as a double rounded up, so a block at that bound
    // cannot beat it either.
    def beatsSettled(b: BigDecimal) = b > (BigDecimal(largestSettledBound.toDouble) max largestSettledBound)
    def settle(settledBound: ComparisonBound): Unit = {
      settledBounds += settledBound
      largestSettledBound = largestSettledBound max settledBound.bound
    }
    def boundBlock(region: GuardRegion, block: Comparison.Block, pass: SharedQueryTime) = {
      pass.incumbent = largestSettledBound
      boundComparison(region, block, pass)
    }

    val time = new TimeLimit(seconds)
    // Without a refinement budget, no time is set aside for refining.
    val refineShare = if (refineQueryBudget == 0) 0.0 else settings.refineShare
    val firstStepsPass = new SharedQueryTime(seconds * (1.0 - refineShare), queryCount, limit = time)
    val rootBounds = for {
      directBounds <- pairByPair(regionsWithoutBlock, firstStepsPass)
      _ = directBounds.foreach(settle)
      blocks <- traverse(rootBlocks) { case (region, block) => boundBlock(region, block, firstStepsPass) }
    } yield blocks

    rootBounds.flatMap { blocks =>
      val openBlocks = mutable.PriorityQueue.from(blocks)(using Ordering.by[ComparisonBound, BigDecimal](_.bound))
      val pass = new SharedQueryTime(time.secondsLeft, refineQueryBudget)
      var refineQueriesAsked = 0
      var failure: Option[String] = None
      var outOfTime = false

      while (failure.isEmpty && !outOfTime && openBlocks.nonEmpty && beatsSettled(openBlocks.head.bound) &&
             refineQueriesAsked < refineQueryBudget) {
        val loosestBlock = openBlocks.dequeue()
        val halves = loosestBlock.comparison match {
          case block: Comparison.Block => GuardRegions.splitBlock(block)
          case _: Comparison.Pair => Seq.empty
        }
        if (halves.isEmpty) settle(loosestBlock)
        else if (refineQueriesAsked + halves.size > refineQueryBudget) {
          openBlocks += loosestBlock
          refineQueriesAsked = refineQueryBudget
        } else {
          refineQueriesAsked += halves.size
          try {
            traverse(halves)(half => boundBlock(loosestBlock.region, half, pass).map { child =>
              child.copy(bound = child.bound min loosestBlock.bound)
            }) match {
              case Left(why) => failure = Some(why)
              case Right(children) => openBlocks ++= children
            }
          } catch {
            // The block keeps its own bound, which covers both halves.
            case _: OutOfTime =>
              openBlocks += loosestBlock
              outOfTime = true
          }
        }
      }

      failure.toLeft(settledBounds.toSeq ++ openBlocks.toSeq)
    }
  }
}

/** Asks Ibex how far apart the leaves on two sides of a guard can be.
  *
  * Ibex encloses an optimum between two numbers. Only the outer end is used, because it holds
  * over the whole region, so a search stopped by its time limit loses precision but never
  * soundness.
  */
class IbexRunner(ctx: inox.Context, settings: RoundoffSettings, recordWitnesses: Boolean) {

  /** The problems use no functions and no data types. */
  private val program: inox.InoxProgram = inox.InoxProgram(inox.trees.NoSymbols)

  import inox.trees._

  /** `comparison` includes the `feasibility`, `dominated` and `optimum` queries made inside it. */
  private val timers: inox.utils.TimerStorage = ctx.timers.verification.roundoff.ibex

  private var server: Option[IbexOptimizer { val program: IbexRunner.this.program.type }] = None

  /** The running server, started when first needed, and again after one was stopped. */
  private def optimizer: IbexOptimizer { val program: IbexRunner.this.program.type } =
    server.getOrElse {
      val started = IbexOptimizer(program, ctx)
      server = Some(started)
      started
    }

  private val recorded = mutable.ArrayBuffer.empty[Witness]

  /** The divergences recorded so far, empty unless witnesses were asked for. */
  def witnesses: Seq[Witness] = synchronized(recorded.toSeq)

  def free(): Unit = synchronized {
    server.foreach(_.free())
    server = None
  }

  /** How far apart the leaves of `comparison` can be where `region.guard` is read the wrong
    * way, in three steps, each cheaper than the next:
    *  1. is there a point where both paths can be taken? If not, it is infeasible;
    *  2. can the distance reach the incumbent? If not, it cannot change the result (only with
    *     `--roundoff-incumbent`);
    *  3. otherwise, bound the distance: at both ends for a pair, whose difference can have
    *     either sign, and only from above for a block, which is never negative.
    *
    * Step 1 uses every constraint, steps 2 and 3 only those linked to the objective. For a
    * block, steps 2 and 3 run once for each direction of the jump ([[GuardRegions.distanceTerms]]).
    *
    * Every call to Ibex gets its time from what is left of the query's share when it is made,
    * so the query never takes more than its share: what one call costs beyond its search is
    * paid by the next calls of the same query, not by the queries after it. Step 1 gets
    * `--roundoff-feasibility-share` of the share, and each objective an equal part of the rest.
    * A call can still run past its time while Ibex builds the problem, which takes time from
    * the queries after it. One still running once the time of `pass` is up is stopped
    * ([[checkWithin]]), and the query then throws [[OutOfTime]].
    */
  def boundComparison(function: String, bands: GuardBands, region: GuardRegion, comparison: Comparison,
            pass: SharedQueryTime): Either[String, ComparisonBound] = synchronized {
    val site = DivergenceSite(function, region.guard, comparison.pairLeaves)

    if (bands.isExact(region.guard)) {
      recordWitness(Witness(site, DivergenceStatus.Unreachable))
      Right(ComparisonBound(region, comparison, 0))
    } else timers.comparison.run(restartingIfStopped {
      val seconds = pass.secondsForNextQuery()
      val queryTime = new TimeLimit(seconds)
      val feasibilityTime = new TimeLimit(seconds * settings.feasibilityShare)
      val regionConstraints = region.shared ++ bands.bandConstraints(region.guard)
      val constraints = regionConstraints ++ bands.relaxedBranchConstraints(comparison.choices)

      val feasible = withProblem(region.vars, constraints, comparison.objective) {
        // A block's reachability checks share step 1 with it.
        val feasibilityPart = if (comparison.pairLeaves.isDefined) 1.0 else 0.5
        checkWithin(feasibilityTime.secondsLeft * feasibilityPart, pass.limit) {
          timers.feasibility.run(optimizer.check(Simple))
        } match {
          case Unsat =>
            recordWitness(Witness(site, DivergenceStatus.Infeasible))
            false
          case _ =>
            // Recorded now: a comparison skipped in step 2 gets no other box, and the fuzzer
            // needs a region to search.
            recordWitness(Witness(site, DivergenceStatus.Feasible, box = Some(certifiedBox)))
            true
        }
      }

      if (!feasible) Right(ComparisonBound(region, comparison, 0, seconds = seconds))
      else {
        val (boundedComparison, objectives) = comparison match {
          case pair: Comparison.Pair => (pair, Some(Seq(pair.difference)))
          case block: Comparison.Block =>
            val reachable =
              reachableCandidates(block.taken ++ block.untaken, region.vars, constraints, bands,
                                  feasibilityTime, pass.limit).toSet
            val factoredBlock = GuardRegions.withSharedBranchesFactoredOut(
              block.copy(taken = block.taken.filter(reachable), untaken = block.untaken.filter(reachable)))
            (factoredBlock, GuardRegions.distanceTerms(factoredBlock))
        }

        objectives match {
          case None =>
            recordWitness(Witness(site, DivergenceStatus.Infeasible))
            Right(ComparisonBound(region, comparison, 0, seconds = seconds))
          case Some(terms) =>
            val boundedConstraints = regionConstraints ++ bands.relaxedBranchConstraints(boundedComparison.choices)
            traverse(terms.zipWithIndex) { case (objective, i) =>
              boundObjective(objective, region.vars, boundedConstraints,
                             signed = comparison.pairLeaves.isDefined,
                             new TimeLimit(queryTime.secondsLeft / (terms.size - i)), pass, site)
            }.map { objectiveResults =>
              val worst = objectiveResults.maxBy(_.bound)
              ComparisonBound(region, boundedComparison, worst.bound, worst.stoppedEarly, worst.isIncumbent,
                              seconds)
            }
        }
      }
    })
  }

  /** Runs `query`, a comparison whose calls [[checkWithin]] may stop. Once it has unwound,
    * the stopped server is freed, so that the next query starts a new one, and the query
    * throws [[OutOfTime]].
    */
  private def restartingIfStopped[A](query: => A): A =
    try query
    catch {
      case _: IbexStopped =>
        free()
        throw new OutOfTime(
          s"Ibex was still building a divergence problem ${IbexRunner.stopMarginSeconds}s after " +
          "the budget ran out, and was stopped")
    }

  /** Runs `check`, a call to Ibex given `seconds` to search, and stops the server if it is
    * still running [[IbexRunner.stopMarginSeconds]] after `limit` is up, or after `seconds` if that is
    * later: Ibex applies its time limit to the search only, after building the problem, and
    * building a large one can take minutes. Throws [[IbexStopped]] then.
    */
  private def checkWithin[A](seconds: Double, limit: TimeLimit)(check: => A): A = {
    optimizer.setSearchTimeout(seconds)
    val running = optimizer
    val finishedOrStopped = new java.util.concurrent.atomic.AtomicBoolean(false)
    val stopped = new java.util.concurrent.CountDownLatch(1)
    val stopServer: Runnable = () =>
      if (finishedOrStopped.compareAndSet(false, true)) {
        running.interrupt()
        stopped.countDown()
      }
    val watchdog = IbexRunner.watchdog.schedule(stopServer,
      ((seconds.max(limit.secondsLeft).max(IbexRunner.shortestSearchSeconds) + IbexRunner.stopMarginSeconds) *
        1e9).toLong,
      java.util.concurrent.TimeUnit.NANOSECONDS)
    val answer = try check finally watchdog.cancel(false)
    if (!finishedOrStopped.compareAndSet(false, true)) {
      // Once the stop is complete, the server reads as stopped on this thread too, so the
      // commands sent to it while the comparison unwinds fail quietly.
      stopped.await()
      throw new IbexStopped
    }
    answer
  }

  /** What bounding one objective found. */
  private case class ObjectiveResult(bound: BigDecimal, stoppedEarly: Boolean = false,
                           isIncumbent: Boolean = false)

  private def boundObjective(objective: Expr, vars: Seq[ValDef], constraints: Seq[Expr],
                             signed: Boolean, time: TimeLimit, pass: SharedQueryTime,
                             site: DivergenceSite): Either[String, ObjectiveResult] =
    IbexRunner.constantValue(objective) match {
      // A constant needs no search: once the region may hold a point, it is its own bound.
      case Some(value) =>
        recordWitness(Witness(site, DivergenceStatus.Bounded))
        Right(updatingIncumbent(pass, ObjectiveResult(if (signed) value.abs.toBigDecimal else value.toBigDecimal max 0)))

      case None =>
        withProblem(vars, IbexRunner.constraintsLinkedTo(objective, constraints), objective) {
          val target = pass.incumbent
          if (settings.incumbent && target > 0 &&
              !canReach(objective, signed, target, time, pass.limit)) {
            recordWitness(Witness(site, DivergenceStatus.Dominated))
            // The distance stays below the double `canReach` compared it with, so that double,
            // or the incumbent if it is larger, also bounds it.
            Right(ObjectiveResult(BigDecimal(target.toDouble) max target, isIncumbent = true))
          } else {
            val searched =
              if (signed) boundBothEnds(objective, time, pass.limit, site)
              else boundAbove(objective, time, pass.limit, site)
            searched.map(updatingIncumbent(pass, _))
          }
        }
    }

  /** `found`, which becomes the incumbent if it is larger. */
  private def updatingIncumbent(pass: SharedQueryTime, found: ObjectiveResult): ObjectiveResult = {
    if (found.bound > pass.incumbent) pass.incumbent = found.bound
    found
  }

  /** The candidates the region can reach.
    *
    * A leaf is left out when Ibex shows that no point of the region satisfies its own branches
    * (relaxed, as for a pair): every pair with it has an empty region. The leaves' branches share
    * prefixes, so each prefix is checked once, the shortest first: a refuted one drops every leaf
    * below it, and the more the shorter it is. The checks stop once `time`, step 1's time, is
    * used up, since each costs Ibex's setup whatever its timeout; a leaf not refuted by then is
    * kept, as for an unknown answer. A check still running once `limit` is up is stopped.
    */
  private def reachableCandidates(candidates: Seq[Candidate], vars: Seq[ValDef],
                                  constraints: Seq[Expr], bands: GuardBands, time: TimeLimit,
                                  limit: TimeLimit): Seq[Candidate] = {
    val refuted = mutable.ArrayBuffer.empty[Seq[BranchChoice]]
    def belowRefuted(choices: Seq[BranchChoice]): Boolean = refuted.exists(choices.startsWith(_))

    val deepest = candidates.map(_.choices.size).maxOption.getOrElse(0)
    for (length <- 1 to deepest if time.secondsLeft > 0) {
      val prefixes = candidates.collect {
        case c if c.choices.size >= length && !belowRefuted(c.choices) => c.choices.take(length)
      }.distinct
      for ((prefix, i) <- prefixes.zipWithIndex if time.secondsLeft > 0) {
        val prefixFeasible = withProblem(vars, constraints ++ bands.relaxedBranchConstraints(prefix), BooleanLiteral(true)) {
          checkWithin(time.secondsLeft / (prefixes.size - i), limit) {
            timers.feasibility.run(optimizer.check(Simple))
          } != Unsat
        }
        if (!prefixFeasible) refuted += prefix
      }
    }

    candidates.filterNot(c => belowRefuted(c.choices))
  }

  /** The largest absolute value of `objective`: its maximum, with half of what is left of
    * `time`, then its minimum, with the rest.
    */
  private def boundBothEnds(objective: Expr, time: TimeLimit, limit: TimeLimit,
                            site: DivergenceSite): Either[String, ObjectiveResult] =
    for {
      high <- boundOneEnd(objective, maximizing = true, time.secondsLeft / 2, limit, site)
      low <- boundOneEnd(objective, maximizing = false, time.secondsLeft, limit, site)
    } yield ObjectiveResult(high.bound.abs max low.bound.abs, high.stoppedEarly || low.stoppedEarly)

  /** The maximum of `objective`, or 0 if it is lower, with what is left of `time`. */
  private def boundAbove(objective: Expr, time: TimeLimit, limit: TimeLimit,
                         site: DivergenceSite): Either[String, ObjectiveResult] =
    boundOneEnd(objective, maximizing = true, time.secondsLeft, limit, site)
      .map(high => high.copy(bound = high.bound max 0))

  /** Whether `objective` can reach `target`, in absolute value when it is `signed`. Each check
    * gets `--roundoff-feasibility-share` of what is left of `time`, and is stopped if it is
    * still running once `limit` is up.
    */
  private def canReach(objective: Expr, signed: Boolean, target: BigDecimal,
                       time: TimeLimit, limit: TimeLimit): Boolean = {
    val targetLiteral = Fraction.toExpr(target.toDouble)

    def reachableOn(side: Expr): Boolean = {
      optimizer.push()
      try {
        optimizer.assertCnstr(GreaterEquals(side, targetLiteral))
        checkWithin(time.secondsLeft * settings.feasibilityShare, limit) {
          timers.dominated.run(optimizer.check(Simple))
        } != Unsat
      } finally optimizer.pop()
    }

    reachableOn(objective) || (signed && reachableOn(UMinus(objective)))
  }

  /** One end of `objective`, and whether Ibex's time limit stopped the search. The search is
    * stopped if it is still running once `limit` is up.
    */
  private def boundOneEnd(objective: Expr, maximizing: Boolean, seconds: Double,
                          limit: TimeLimit, site: DivergenceSite): Either[String, ObjectiveResult] = {
    if (maximizing) optimizer.maximize(objective) else optimizer.minimize(objective)

    checkWithin(seconds, limit)(timers.optimum.run(optimizer.check(Simple))) match {
      // Ibex proved the region empty, so nothing diverges in it, as when the feasibility check
      // finds no point. The region can be smaller than the one checked: a block adds the
      // branches its remaining leaves share, and the check may have stopped with "unknown".
      case Unsat =>
        recordWitness(Witness(site, DivergenceStatus.Infeasible))
        Right(ObjectiveResult(0))

      case answer =>
        // Read before the box, so that asking for the box cannot change the bounds.
        val bounds = optimizer.getObjectiveBounds
        recordWitness(Witness(site, DivergenceStatus.Bounded, Some(maximizing), Some(certifiedBox)))

        // An "unknown" answer still carries the bound reached when the search stopped.
        val stoppedEarly = answer == Unknown
        bounds match {
          case Some(ObjectiveBounds(_, Some(high))) if maximizing => Right(ObjectiveResult(high, stoppedEarly))
          case Some(ObjectiveBounds(Some(low), _)) if !maximizing => Right(ObjectiveResult(low, stoppedEarly))
          case _ => Left("Ibex found no bound for the difference between two paths")
        }
    }
  }

  /** Runs `block` with `constraints` asserted, declaring only the variables of `vars` that
    * they or `objective` use: Ibex splits every declared variable, and one no constraint
    * bounds is an infinite interval it never finishes splitting.
    */
  private def withProblem[A](vars: Seq[ValDef], constraints: Seq[Expr], objective: Expr)
                            (block: => A): A = {
    val used = (objective +: constraints).flatMap(exprOps.variablesOf).map(_.id).toSet
    optimizer.push()
    try {
      vars.filter(v => used(v.id)).foreach(optimizer.declare)
      constraints.foreach(optimizer.assertCnstr)
      block
    } finally {
      optimizer.pop()
    }
  }

  /** By name, so that the box is only fetched from Ibex when it is kept. */
  private def recordWitness(witness: => Witness): Unit =
    if (recordWitnesses) recorded += witness

  /** The box Ibex certified around the point it found. */
  private def certifiedBox: Box =
    optimizer.getVariableBounds.map {
      case (v, ObjectiveBounds(low, high)) => v.id.name -> (low, high)
    }
}

object IbexRunner {
  import inox.trees._

  /** In seconds. Inox raises any shorter timeout to it. */
  val shortestSearchSeconds = 0.001

  /** In seconds, how long a call to Ibex may run past the time of its pass before it is stopped. */
  val stopMarginSeconds = 1.0

  /** Stops the calls to Ibex that run past [[stopMarginSeconds]]. */
  private val watchdog: java.util.concurrent.ScheduledThreadPoolExecutor = {
    val executor = new java.util.concurrent.ScheduledThreadPoolExecutor(1, (task: Runnable) => {
      val thread = new Thread(task, "ibex-watchdog")
      thread.setDaemon(true)
      thread
    })
    // A call that answers in time cancels its stop, which would otherwise wait in the queue.
    executor.setRemoveOnCancelPolicy(true)
    executor
  }

  /** The value of `e` when it reads no variable. */
  def constantValue(e: Expr): Option[Rational] = e match {
    case FractionLiteral(n, d) => Some(Rational.of(n, d))
    case UMinus(a) => constantValue(a).map(-_)
    case Plus(a, b) => for (x <- constantValue(a); y <- constantValue(b)) yield x + y
    case Minus(a, b) => for (x <- constantValue(a); y <- constantValue(b)) yield x - y
    case Times(a, b) => for (x <- constantValue(a); y <- constantValue(b)) yield x * y
    case RealMax(args) =>
      traverse(args)(a => constantValue(a).toRight("")).toOption
        .map(_.maxBy(r => BigDecimal(r.num) / BigDecimal(r.den)))
    case RealMin(args) =>
      traverse(args)(a => constantValue(a).toRight("")).toOption
        .map(_.minBy(r => BigDecimal(r.num) / BigDecimal(r.den)))
    case _ => None
  }

  /** The constraints that share a variable with `objective`, directly or through other
    * constraints, and those without variables.
    *
    * The others only restrict variables the objective does not read, so once the region is
    * known to have a point they cannot change the objective's range. Leaving them in can stop
    * Ibex from converging.
    *
    * A constant objective keeps every constraint: Ibex needs at least one variable, and the
    * region's constraints are what make the search fail where the region is empty.
    */
  def constraintsLinkedTo(objective: Expr, constraints: Seq[Expr]): Seq[Expr] =
    if (exprOps.variablesOf(objective).isEmpty) constraints
    else {
      val variables = constraints.map(c => exprOps.variablesOf(c).map(_.id))
      var reached = exprOps.variablesOf(objective).map(_.id)
      var kept = Set.empty[Int]
      var growing = true
      while (growing) {
        val linked = variables.indices.filter { i =>
          !kept(i) && (variables(i).isEmpty || variables(i).exists(reached))
        }
        kept ++= linked
        reached ++= linked.flatMap(variables)
        growing = linked.nonEmpty
      }
      constraints.zipWithIndex.collect { case (constraint, i) if kept(i) => constraint }
    }
}

private final class IbexStopped extends Exception

/** One comparison across one guard of one function: a pair `(taken, untaken)` of leaves, or
  * `None` for a block.
  */
case class DivergenceSite(function: String, guard: Int, pair: Option[(Int, Int)])

/** The interval Ibex narrowed each variable to, with `None` for an open end. */
type Box = Map[String, (Option[BigDecimal], Option[BigDecimal])]

enum DivergenceStatus {
  /** The guard is computed exactly, so it is never read the wrong way. Ibex is not asked. */
  case Unreachable

  /** Ibex found no point where both paths can be taken. */
  case Infeasible

  case Bounded

  /** Ibex found a point where both paths can be taken. Recorded before bounding. */
  case Feasible

  /** The difference cannot reach the incumbent, so it was not bounded. */
  case Dominated
}

/** What one divergence query found, for the JSON report and the fuzzer. Every query is
  * recorded, refused ones included, so that an empty report means nothing was asked.
  */
case class Witness(
  site: DivergenceSite,
  status: DivergenceStatus,
  maximizing: Option[Boolean] = None,
  box: Option[Box] = None
) {
  def function: String = site.function
}

object Witness {
  import io.circe.Json

  /** Every witness, grouped by function, as JSON. A box lists its variables in the order
    * `parametersOf` gives, the declaration order, to match the fuzzer configuration, whose
    * intervals are positional.
    */
  def toJson(witnesses: Seq[Witness], parametersOf: String => Seq[String]): Json = {
    def boundToJson(d: Option[BigDecimal]): Json = d.map(Json.fromBigDecimal).getOrElse(Json.Null)

    def boxToJson(box: Box, parameters: Seq[String]): Json = {
      // Variables that are not parameters go last.
      def declarationOrder(name: String): (Int, String) =
        (parameters.indexOf(name) match { case -1 => parameters.size; case i => i }, name)

      Json.obj(box.toSeq.sortBy { case (name, _) => declarationOrder(name) }.map {
        case (name, (low, high)) => name -> Json.obj("lo" -> boundToJson(low), "hi" -> boundToJson(high))
      }*)
    }

    def witnessToJson(w: Witness): Json = Json.obj(
      Seq("guard" -> Json.fromInt(w.site.guard)) ++
      (w.site.pair match {
        case Some((taken, untaken)) =>
          Seq("untaken" -> Json.fromInt(untaken), "taken" -> Json.fromInt(taken))
        case None => Seq("leaves" -> Json.fromString("all"))
      }) ++
      Seq("status" -> Json.fromString(w.status.toString.toLowerCase)) ++
      w.maximizing.map(m => "objective" -> Json.fromString(if (m) "maximum" else "minimum")) ++
      w.box.map(b => "box" -> boxToJson(b, parametersOf(w.function)))*
    )

    Json.obj(witnesses.groupBy(_.function).toSeq.sortBy(_._1).map {
      case (function, functionWitnesses) => function -> Json.arr(functionWitnesses.map(witnessToJson)*)
    }*)
  }
}
