/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification
package roundoff

import trees._

import scala.collection.mutable.ArrayBuffer

/** A comparison a conditional branches on. */
case class Guard(lhs: Expr, rhs: Expr, strict: Boolean)

/** Which side of one guard a path took. */
case class BranchChoice(guard: Int, taken: Boolean)

/** A straight-line branch in the execution tree */
case class ProgramPath(choices: Seq[BranchChoice], leaf: Expr, reachable: Boolean = true)

/** Splits a function body into the straight-line paths through it. */
object PathExtractor {

  /** A chain of `let` bindings, outermost first. */
  private type Scope = Seq[(ValDef, Expr)]

  /** @param oracle consulted at every guard, so that a branch no input takes is walked for
    *               its paths but asked nothing further about
    */
  def apply(body: Expr, oracle: BranchOracle = BranchOracle.open)
    : Either[String, (Seq[Guard], Seq[ProgramPath])] = {
    val guards = ArrayBuffer.empty[Guard]
    val paths = ArrayBuffer.empty[ProgramPath]

    def walk(e: Expr, scope: Scope, choices: Seq[BranchChoice], live: Boolean)
      : Either[String, Unit] = e match {
      case Let(vd, value, body) => walk(body, scope :+ (vd, value), choices, live)

      case IfExpr(condition, thenBranch, elseBranch) =>
        val (conditionScope, logic) = resolveCondition(condition, bindingsOf(scope))
        val inner = scope ++ conditionScope

        logic match {
          // A short-circuit connective is the nesting it stands for, so it is written out
          // as that nesting; every path condition then stays a conjunction, which is what
          // the solver bounding discontinuities can accept.
          case And(conjuncts) if conjuncts.size > 1 =>
            walk(IfExpr(conjuncts.head, IfExpr(conjunction(conjuncts.tail), thenBranch, elseBranch),
                        elseBranch), inner, choices, live)
          case Or(disjuncts) if disjuncts.size > 1 =>
            walk(IfExpr(disjuncts.head, thenBranch,
                        IfExpr(disjunction(disjuncts.tail), thenBranch, elseBranch)), inner,
                 choices, live)
          case And(Seq(single)) => walk(IfExpr(single, thenBranch, elseBranch), inner, choices, live)
          case Or(Seq(single)) => walk(IfExpr(single, thenBranch, elseBranch), inner, choices, live)
          case Not(negated) => walk(IfExpr(negated, elseBranch, thenBranch), inner, choices, live)

          // `a == b` is `a <= b` and `b <= a`, which is the same test on every value a float
          // takes: both are false where either side is a NaN, and both hold of the two zeros.
          // Written that way it is two guards rather than none, and each marks a band with a
          // side either way of it, which is what a divergence is measured across. `a != b` is
          // the `Not` above and needs nothing of its own.
          case FPEquals(lhs, rhs) =>
            walk(IfExpr(And(FPLessEquals(lhs, rhs), FPGreaterEquals(lhs, rhs)),
                        thenBranch, elseBranch), inner, choices, live)

          case BooleanLiteral(true) => walk(thenBranch, inner, choices, live)
          case BooleanLiteral(false) => walk(elseBranch, inner, choices, live)

          case comparison =>
            asGuard(comparison).flatMap { guard =>
              val index = guards.size
              val closed = Guard(close(inner, guard.lhs), close(inner, guard.rhs), guard.strict)
              guards += closed
              descend(closed, taken = true, thenBranch, inner, choices, index, live).flatMap(_ =>
                descend(closed, taken = false, elseBranch, inner, choices, index, live))
            }
        }

      case leaf =>
        paths += ProgramPath(choices, close(scope, leaf), live)
        Right(())
    }

    /** Walks one side of a guard, asking about it first where the way there is still open.
      *
      * The question covers this guard alone: the oracle holds everything above it, so a
      * refusal here refuses the whole subtree at once. Below a refusal the walk carries on
      * unasked, since those paths still have to be recorded.
      */
    def descend(guard: Guard, taken: Boolean, branch: Expr, scope: Scope,
                choices: Seq[BranchChoice], index: Int, live: Boolean): Either[String, Unit] = {
      val below = choices :+ BranchChoice(index, taken)
      def unreached = walk(branch, scope, below, live = false)

      if (!live) unreached
      else oracle.assuming(FPPathCondition.of(guard, taken))(walk(branch, scope, below, live = true))
                 .getOrElse(unreached)
    }

    walk(body, Seq.empty, Seq.empty, live = true).map(_ => (guards.toSeq, paths.toSeq))
  }

  /** Follows a condition to the comparison or connective underneath, with the bindings met
    * on the way, since the frontend hoists a condition and its operands into bindings.
    */
  private def resolveCondition(condition: Expr, bindings: Map[Identifier, Expr])
    : (Scope, Expr) = condition match {
    case Let(vd, value, body) =>
      val (inner, logic) = resolveCondition(body, bindings + (vd.id -> value))
      ((vd, value) +: inner, logic)
    case v: Variable =>
      bindings.get(v.id).map(resolveCondition(_, bindings)).getOrElse((Seq.empty, v))
    case other => (Seq.empty, other)
  }

  private def asGuard(comparison: Expr): Either[String, Guard] = comparison match {
    case FPLessThan(l, r)      => Right(Guard(l, r, strict = true))
    case FPLessEquals(l, r)    => Right(Guard(l, r, strict = false))
    case FPGreaterThan(l, r)   => Right(Guard(r, l, strict = true))
    case FPGreaterEquals(l, r) => Right(Guard(r, l, strict = false))

    case v: Variable =>
      Left(s"the guard is the opaque boolean '${v.id.name}'")

    case other =>
      Left(s"the guard is not a floating-point comparison (${other.getClass.getSimpleName})")
  }

  /** Puts an expression back under the bindings it needs, dropping the rest. */
  private def close(scope: Scope, expr: Expr): Expr =
    scope.foldRight(expr) { case ((vd, value), kept) =>
      if (exprOps.variablesOf(kept).exists(_.id == vd.id)) Let(vd, value, kept) else kept
    }

  private def bindingsOf(scope: Scope): Map[Identifier, Expr] =
    scope.map { case (vd, value) => vd.id -> value }.toMap

  private def conjunction(es: Seq[Expr]): Expr = if (es.size == 1) es.head else And(es)
  private def disjunction(es: Seq[Expr]): Expr = if (es.size == 1) es.head else Or(es)
}

/** A path the rounded program can take instead of the exact one.
  *
  * `divergingChoices` are the guards it must choose differently, from the divergence point
  * onwards; each needs that guard's two sides within their combined error.
  */
case class DivergentPath(toPath: Int, divergingChoices: Seq[BranchChoice],
                         difference: inox.trees.Expr)

/** The region one path holds over, and the divergent paths reachable inside it. */
case class DiscontinuityProblem(
  vars: Seq[inox.trees.ValDef],
  constraints: Seq[inox.trees.Expr],
  divergentPaths: Seq[DivergentPath]
)

/** One leaf measured against the reference of its region.
  *
  * `choices` are the branches it takes below the guard, each of which the rounded program
  * reads on its own values and so is relaxed by that guard's error.
  */
case class ReferenceComparison(leaf: Int, choices: Seq[BranchChoice],
                               difference: inox.trees.Expr)

/** How far reading one guard the other way can move the result.
  *
  * Every leaf below the guard is measured against one of them rather than against each of
  * the others, so a region costs a query per leaf rather than a query per pair of them.
  * Whichever side the exact run was on, the distance between the two sides is at most the
  * two furthest distances from the reference added together.
  */
case class DivergenceRegion(
  guard: Int,
  vars: Seq[inox.trees.ValDef],
  shared: Seq[inox.trees.Expr],
  reference: Int,
  taken: Seq[ReferenceComparison],
  untaken: Seq[ReferenceComparison]
)

/** Two leaves compared across the guard they part at, from either side of it at once.
  *
  * `choices` are the branches both of them take below that guard, all relaxed, because a
  * region has to hold whichever of the two the exact run was on and the other's conditions
  * cannot be asserted exactly at the same time.
  */
case class CrossComparison(taken: Int, untaken: Int, choices: Seq[BranchChoice],
                           difference: inox.trees.Expr)

/** How far reading one guard the other way can move the result, both ways in one region.
  *
  * The two directions of a divergence differ only in which side's conditions below the
  * guard hold exactly, so putting them in one region costs the width of a guard error
  * around those conditions and saves half the queries.
  */
case class MergedRegion(
  guard: Int,
  vars: Seq[inox.trees.ValDef],
  shared: Seq[inox.trees.Expr],
  pairs: Seq[CrossComparison]
)

/** The queries that bound how far a misread guard moves the result of one function. */
enum DiscontinuityPlan {
  case Pairwise(problems: Seq[DiscontinuityProblem])
  case Merged(regions: Seq[MergedRegion])
  case ViaReference(regions: Seq[DivergenceRegion])

  /** How many regions were built, which is one per path or one per guard. */
  def size: Int = this match {
    case Pairwise(problems) => problems.size
    case Merged(regions) => regions.size
    case ViaReference(regions) => regions.size
  }

  /** How many divergences will be asked about, so that a budget can be divided among them.
    *
    * An upper bound: one of these is refused without being asked wherever the guard it
    * crosses rounds exactly. That only leaves the queries after it a larger share.
    */
  def queries: Int = this match {
    case Pairwise(problems) => problems.map(_.divergentPaths.size).sum
    case Merged(regions) => regions.map(_.pairs.size).sum
    case ViaReference(regions) => regions.map(r => r.taken.size + r.untaken.size).sum
  }
}

/** Turns the paths of one function into the real-arithmetic problems that bound how far
  * a guard evaluated the other way moves the result.
  */
object DiscontinuityEncoder {

  /** The plan, along with `lhs - rhs` for each guard. */
  def apply(guards: Seq[Guard], paths: Seq[ProgramPath], spec: InputSpec,
            mode: DiscontinuityMode, normalise: Boolean = true)
    : Either[String, (Seq[Seq[inox.trees.Expr]], DiscontinuityPlan)] = {

    val inputs = (paths.map(_.leaf) ++ guards.flatMap(g => Seq(g.lhs, g.rhs)))
      .flatMap(exprOps.variablesOf)
      .distinctBy(_.id)
      .sortBy(_.id.globalId)

    // Identifiers are reused so a counter-example stays readable; floating-point and real
    // variables never meet in one query.
    val realVariables: Map[Identifier, inox.trees.Variable] =
      inputs.map(v => v.id -> inox.trees.Variable(v.id, inox.trees.RealType(), Seq.empty)).toMap

    val unbounded = inputs.map(_.id).find(!spec.ranges.contains(_))

    // The leaves and the two sides of every guard, all read as real arithmetic.
    val encoded: Either[String, (Seq[inox.trees.Expr], Seq[(inox.trees.Expr, inox.trees.Expr)])] =
      if (unbounded.isDefined)
        Left(s"no range in the precondition for '${unbounded.get.name}'; " +
             "add bounds of the form 'lo <= x && x <= hi'")
      else
        traverse(paths)(path => RealEncoder(path.leaf, realVariables)).flatMap { leaves =>
          traverse(guards) { guard =>
            RealEncoder(guard.lhs, realVariables).flatMap { lhs =>
              RealEncoder(guard.rhs, realVariables).map((lhs, _))
            }
          }.map((leaves, _))
        }

    encoded.map { case (leaves, guardOperands) =>

      val ranges = inputs.flatMap { input =>
        val (low, high) = spec.ranges(input.id)
        Seq(inox.trees.LessEquals(Fraction.toExpr(low), realVariables(input.id)),
            inox.trees.LessEquals(realVariables(input.id), Fraction.toExpr(high)))
      }

      /** What a guard is worth, as written. */
      val written = guardOperands.map { case (lhs, rhs) => inox.trees.Minus(lhs, rhs) }

      // Which guard, if any, an objective is a multiple of. Memoised because every objective is
      // a difference of two leaves, and a function has far fewer distinct leaves than paths.
      val divisors =
        scala.collection.mutable.Map.empty[inox.trees.Expr, Option[(Int, inox.trees.Expr)]]

      def divisorOf(e: inox.trees.Expr): Option[(Int, inox.trees.Expr)] =
        if (!normalise) None else divisors.getOrElseUpdate(e, Normalisation.divisor(e, written))

      // A guard difference some objective is made of becomes a variable of its own, tied to what
      // it stands for by an equation the region carries. The band is then a range on that
      // variable rather than a relation between the inputs, which is the difference between
      // reading an objective off and bisecting towards it.
      //
      // Only a guard that divides something earns one. The equation is carried by every region
      // of the function, so naming a guard no objective is written over costs a variable and a
      // nonlinear constraint per region that nothing ever reads. That is affordable where there
      // are two or three guards and is the entire cost of the search where there are twenty:
      // on `OrientationIndexFilter`, twenty-two guards over twenty-two regions took the Ibex
      // time from 1.5 s to 36 s and bought a bound tighter by a thousandth.
      val named: Map[Int, inox.trees.Variable] = {
        val distinct = leaves.distinct
        val fires = for {
          reference <- distinct
          other <- distinct
          if other != reference
          (guard, _) <- divisorOf(inox.trees.Minus(other, reference))
        } yield guard

        fires.distinct.map { guard =>
          guard -> inox.trees.Variable.fresh(s"guard$guard", inox.trees.RealType())
        }.toMap
      }

      /** The named guards, in the order a region declares and equates them. */
      val naming = named.toSeq.sortBy(_._1)

      // The band goes on both forms rather than only the variable. Stating it on the expression
      // is what holds the inputs of a region to each other: told only that the variable is small,
      // the solver satisfies the equation to about a part in a billion and hands back a point
      // whose inputs are nowhere near the boundary, which is a bound one can trust and a witness
      // one cannot. Stating it on the variable as well is what lets the objective be read off.
      /** The named guard whose difference divides `e`, where there is one. */
      def overNamed(e: inox.trees.Expr): Option[inox.trees.Expr] =
        Normalisation.divisor(e, naming.map { case (guard, _) => written(guard) })
          .map { case (which, quotient) => inox.trees.Times(quotient, naming(which)._2) }

      // A guard that is a multiple of one already named is bounded on that name as well. Two
      // occurrences of the same quantity are two boxes to the solver, so a band stated on one
      // of them says nothing about the other: `a * b == c` becomes the two guards `a*b <= c`
      // and `c <= a*b`, and without this the region of the second bounds an objective written
      // over the first's variable by bisection, at 0.031 where the truth is 1.3e-15.
      val differences: Seq[Seq[inox.trees.Expr]] =
        written.zipWithIndex.map { case (difference, guard) =>
          Seq(difference) ++ named.get(guard).orElse(overNamed(difference))
        }

      val box = ranges ++ naming.map { case (guard, name) =>
        inox.trees.Equals(name, written(guard))
      }

      /** An objective written over the guard it turns out to be a multiple of. */
      def objective(e: inox.trees.Expr): inox.trees.Expr =
        divisorOf(e).map { case (guard, quotient) =>
          inox.trees.Times(quotient, named(guard))
        }.getOrElse(e)

      /** The path condition one choice contributes. */
      def pathCondition(choice: BranchChoice): inox.trees.Expr = {
        val (lhs, rhs) = guardOperands(choice.guard)
        // Negating swaps both the sides and the strictness, exactly, over the reals.
        (choice.taken, guards(choice.guard).strict) match {
          case (true, false) => inox.trees.LessEquals(lhs, rhs)
          case (true, true) => inox.trees.LessThan(lhs, rhs)
          case (false, false) => inox.trees.LessThan(rhs, lhs)
          case (false, true) => inox.trees.LessEquals(rhs, lhs)
        }
      }

      /** The first guard two paths choose differently. */
      def divergencePoint(one: ProgramPath, other: ProgramPath): Int =
        one.choices.zip(other.choices).indexWhere { case (a, b) => a != b }

      val vars = inputs.map(input => realVariables(input.id).toVal) ++ naming.map(_._2.toVal)

      def pairwise: Seq[DiscontinuityProblem] = paths.zipWithIndex.map { case (path, i) =>
        val divergentPaths = paths.zipWithIndex.collect {
          // Reaching a leaf that computes the same thing is not a divergence, and neither is
          // a leaf no run reaches, since the rounded program never lands there.
          case (other, j) if j != i && other.leaf != path.leaf && other.reachable =>
            DivergentPath(j, other.choices.drop(divergencePoint(path, other)),
                          objective(inox.trees.Minus(leaves(j), leaves(i))))
        }
        DiscontinuityProblem(vars, box ++ path.choices.map(pathCondition), divergentPaths)
      }

      /** The leaves either side of one guard, the conditions holding above it, and where
        * in a path's choices it sits. Absent where the guard has fewer than two leaves
        * under it, which leaves nothing to diverge to.
        *
        * Every path through a guard reaches it through the same branches, so any of them
        * gives the conditions above it.
        */
      def under(guard: Int): Option[(Seq[(ProgramPath, Int)], Seq[(ProgramPath, Int)],
                                     Seq[inox.trees.Expr], ProgramPath => Int)] = {
        def at(path: ProgramPath): Int = path.choices.indexWhere(_.guard == guard)

        val reached = paths.zipWithIndex.filter { case (path, _) => at(path) >= 0 }

        // One leaf on its own has nothing to diverge to.
        Option.when(reached.size > 1) {
          val (first, _) = reached.head
          val (taken, untaken) = reached.partition { case (path, _) => path.choices(at(path)).taken }
          (taken, untaken, box ++ first.choices.take(at(first)).map(pathCondition), at)
        }
      }

      def viaReference: Seq[DivergenceRegion] = guards.indices.flatMap { guard =>
        under(guard).map { case (taken, untaken, shared, at) =>
          val reference = (taken ++ untaken).head._2

          def measured(entry: (ProgramPath, Int)): Option[ReferenceComparison] = {
            val (path, leaf) = entry
            // Reaching a leaf that computes the same thing is no distance at all, and the
            // reference is no distance from itself.
            Option.when(leaf != reference && path.leaf != paths(reference).leaf)(
              ReferenceComparison(leaf, path.choices.drop(at(path) + 1),
                                  objective(inox.trees.Minus(leaves(leaf), leaves(reference)))))
          }

          DivergenceRegion(guard, vars, shared, reference,
                           taken.flatMap(measured), untaken.flatMap(measured))
        }
      }

      def merged: Seq[MergedRegion] = guards.indices.flatMap { guard =>
        under(guard).map { case (taken, untaken, shared, at) =>
          val crossings = for {
            (onePath, one) <- taken
            (otherPath, other) <- untaken
            // Reaching a leaf that computes the same thing is not a divergence.
            if onePath.leaf != otherPath.leaf
          } yield CrossComparison(
            one, other,
            onePath.choices.drop(at(onePath) + 1) ++ otherPath.choices.drop(at(otherPath) + 1),
            objective(inox.trees.Minus(leaves(other), leaves(one))))

          MergedRegion(guard, vars, shared, crossings)
        }
      }

      val plan = mode match {
        case DiscontinuityMode.Pairwise => DiscontinuityPlan.Pairwise(pairwise)
        case DiscontinuityMode.Merged => DiscontinuityPlan.Merged(merged)
        case DiscontinuityMode.Reference => DiscontinuityPlan.ViaReference(viaReference)
      }

      (differences, plan)
    }
  }
}

/** Reads a floating-point expression as the exact computation it approximates. */
private[roundoff] object RealEncoder {

  import inox.trees.{Plus, Minus, Times, Division, UMinus}

  def apply(e: Expr, realVariables: Map[Identifier, inox.trees.Variable])
    : Either[String, inox.trees.Expr] = {

    def binary(build: (inox.trees.Expr, inox.trees.Expr) => inox.trees.Expr, l: Expr, r: Expr) =
      apply(l, realVariables).flatMap(a => apply(r, realVariables).map(build(a, _)))

    e match {
      case v: Variable => realVariables.get(v.id).toRight(s"unbound variable '${v.id.name}'")
      case FPLit(d) =>
        Fraction.apply(d).map { case (num, den) => inox.trees.FractionLiteral(num, den) }

      // Rounding modes are irrelevant: this is the exact computation the rounded one is
      // measured against.
      case FPAdd(_, l, r) => binary(Plus(_, _), l, r)
      case FPSub(_, l, r) => binary(Minus(_, _), l, r)
      case FPMul(_, l, r) => binary(Times(_, _), l, r)
      case FPDiv(_, l, r) => binary(Division(_, _), l, r)
      case FPUMinus(a) => apply(a, realVariables).map(UMinus(_))
      case FPFMA(_, a, b, c) =>
        binary(Times(_, _), a, b).flatMap { product =>
          apply(c, realVariables).map(Plus(product, _))
        }

      case Let(vd, value, body) =>
        val realVar = inox.trees.Variable(vd.id, inox.trees.RealType(), Seq.empty)

        apply(value, realVariables).flatMap { realValue =>
          apply(body, realVariables + (vd.id -> realVar)).map(
            inox.trees.Let(realVar.toVal, realValue, _))
        }

      case TranscendentalFunctionCall(f, args) =>
        traverse(args)(apply(_, realVariables)).flatMap(realCall(f, _))

      case _: IfExpr =>
        Left("a conditional appears inside an expression, and only conditionals that shape " +
          "the body are supported")

      case other =>
        Left(s"no real-arithmetic equivalent for ${other.getClass.getSimpleName}")
    }
  }

  /** The exact counterpart of one call, which only Ibex among the solvers can evaluate. */
  private def realCall(f: TranscendentalFunction, args: Seq[inox.trees.Expr])
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

      // Ibex reads any other exponent as exp(y * log(x)), which holds only where the
      // base is positive, so it refuses one rather than answering on a smaller region.
      case (TranscendentalFunction.Pow, Seq(base, exponent @ FractionLiteral(_, one))) if one == 1 =>
        Right(RealPow(base, exponent))
      case (TranscendentalFunction.Pow, _) =>
        Left("a power on a branching path needs a whole-number exponent")

      case _ => Left(s"'${f.symbol}' was given ${args.size} arguments")
    }
  }
}

/** Where the rounding error of one expression comes from. */
enum RoundingError {
  /** A constant is stored as the value it names, so it rounds by nothing. */
  case Exact

  /** A value with no inputs left in it, whose error is worked out rather than measured,
    * because the analyzer answers about a range of inputs and there is none to give it.
    */
  case Computed(error: BigDecimal)

  /** Anything else needs a bound from the analyzer, which this query asks for. */
  case FromAnalyzer(query: RoundingQuery)

  /** A leaf no input reaches, so no run rounds it and nothing is worked out or asked for.
    *
    * This is what keeps an unsupported dead branch from answering for the whole function: a
    * leaf nothing reaches is never read, so it never has to be understood either.
    */
  case Unreachable

  def asQuery: Option[RoundingQuery] = this match {
    case FromAnalyzer(q) => Some(q)
    case _ => None
  }
}

/** What the guard tree of a function turned out to look like.
  *
  * Everything after enumeration is sized by these figures — how many questions the pruning
  * budget is cut among, how many regions the search builds, how many comparisons each holds —
  * so an analysis that took a long time or came out wide is usually explained here rather than
  * in the search that followed.
  *
  * @param guards   comparisons the walk found, after a conjunction or a disjunction has been
  *                 written out as the nesting it stands for and a call has been inlined
  * @param paths    leaves, which for a tree of comparisons is `guards + 1`
  * @param depth    guards above the deepest leaf
  * @param distinct leaves that compute different things; two paths ending in the same
  *                 expression are no divergence and are never compared
  */
case class Shape(guards: Int, paths: Int, depth: Int, distinct: Int)

/** The parts a function's roundoff error is built from. */
case class RoundoffErrorDecomposition(
  leaves: Seq[RoundingError],
  shape: Shape,
  flattening: ADTParametersFlattening,
  guardOperandErrors: Seq[(RoundingError, RoundingError)],
  guardDifferences: Seq[Seq[inox.trees.Expr]],
  discontinuities: DiscontinuityPlan,
  spec: InputSpec,
  body: Expr
) {
  def reachableLeaves: Seq[RoundingError] =
    leaves.filterNot(_ == RoundingError.Unreachable)

  def queries: Seq[RoundingQuery] =
    (reachableLeaves ++ guardOperandErrors.flatMap { case (lhs, rhs) => Seq(lhs, rhs) })
      .flatMap(_.asQuery)
}

object RoundoffErrorDecomposition {

  /** @param timers where each phase reports how long it took; detached by default, so a
    *               caller with no context of its own measures nothing
    */
  def of(fd: FunDef, exactInputs: Boolean, mode: DiscontinuityMode,
         oracle: BranchOracle = BranchOracle.open,
         timers: inox.utils.TimerStorage = inox.utils.TimerStorage(),
         normalise: Boolean = true,
         pathRanges: Boolean = true,
         emitter: RoundingSourceEmitter = FPCoreEmitter)(using Symbols)
    : Either[String, Seq[(AccessPath, RoundoffErrorDecomposition)]] = {
    val options = DecompositionOptions(exactInputs, mode, normalise, pathRanges, timers, emitter)

    read(fd, oracle, options).flatMap(reading => traverse(reading.fields)(reading.decompose(_)))
  }

  /** What the caller asked for, carried unchanged through the reading of one function. */
  private case class DecompositionOptions(exactInputs: Boolean, mode: DiscontinuityMode,
                                          normalise: Boolean, pathRanges: Boolean,
                                          timers: inox.utils.TimerStorage,
                                          emitter: RoundingSourceEmitter)

  /** What one function's body came to, before its result is read one number at a time.
    *
    * The body is enumerated once for the whole result: every number in it is computed by the
    * same branches, so the guards, the questions asked about them and the errors of their
    * operands are shared, and only the leaves are read field by field.
    */
  private def read(fd: FunDef, oracle: BranchOracle, options: DecompositionOptions)(using Symbols)
    : Either[String, Reading] = {
    import options.timers

    timers.preprocessing.run(Preprocessor(fd)).flatMap { case (whole, fields, flattening) =>
      timers.preprocessing.run(FPCoreEmitter.specOf(fd, whole, flattening)).flatMap { spec =>
        brief(oracle, fd, whole, flattening, timers)

        timers.paths.run(PathExtractor(whole, oracle)).flatMap { case (guards, paths) =>
          // Every leaf refused leaves the function with nothing a run can compute, which is
          // what an unsatisfiable precondition looks like from here.
          if (!paths.exists(_.reachable))
            Left("no path through this function is reachable, so its precondition may be " +
                 "unsatisfiable; --sat-precond checks that on its own")
          else
            guardOperandErrors(fd, guards, spec, options).map(
              Reading(fd, whole, fields, flattening, spec, guards, paths, _, options))
        }
      }
    }
  }

  /** Tells the oracle what the questions are about, and how many of them to expect.
    *
    * Two per guard, counted by walking the body once with nothing asked of it. The walk is the
    * same one that follows and finds the same guards, so the figure is exact for a run that
    * refutes nothing and an over-estimate for one that does.
    */
  private def brief(oracle: BranchOracle, fd: FunDef, whole: Expr,
                    flattening: ADTParametersFlattening, timers: inox.utils.TimerStorage)
                   (using Symbols): Unit = {
    oracle.knowing(flattening.parameters, FPCoreEmitter.assumptions(fd, flattening))
    oracle.expecting(timers.pruning.counting.run(
      PathExtractor(whole) match {
        case Right((guards, _)) => guards.size * 2
        case Left(_) => 0
      }))
  }

  /** How far the two sides of each guard can fall from their exact values. */
  private def guardOperandErrors(fd: FunDef, guards: Seq[Guard], spec: InputSpec,
                                 options: DecompositionOptions)(using Symbols)
    : Either[String, Seq[(RoundingError, RoundingError)]] = {
    val guardNames = guards.distinct.zipWithIndex.toMap

    options.timers.queries.conditions.run(traverse(guards) { guard =>
      val k = guardNames(guard)

      errorOf(fd, s"${prefix(fd)}_guard${k}_lhs", s"${fd.id.name} (guard ${k + 1}, left)",
              guard.lhs, spec, options).flatMap { lhs =>
        errorOf(fd, s"${prefix(fd)}_guard${k}_rhs", s"${fd.id.name} (guard ${k + 1}, right)",
                guard.rhs, spec, options).map((lhs, _))
      }
    })
  }

  /** One function's body, read as far as it can be without picking a number out of its result. */
  private case class Reading(fd: FunDef, whole: Expr, fields: Seq[AccessPath],
                             flattening: ADTParametersFlattening, spec: InputSpec,
                             guards: Seq[Guard], paths: Seq[ProgramPath],
                             operandErrors: Seq[(RoundingError, RoundingError)],
                             options: DecompositionOptions) {

    /** What the error of one number of the result is built from. */
    def decompose(field: AccessPath)(using Symbols)
      : Either[String, (AccessPath, RoundoffErrorDecomposition)] = {
      val narrowed = paths.map(path => path.copy(leaf = field.project(path.leaf)))
      val named = if (field.steps.isEmpty) fd.id.name else s"${fd.id.name}.${field.displayName}"
      val tag = if (field.steps.isEmpty) prefix(fd) else s"${prefix(fd)}_${field.displayName("_")}"

      // The ranges each leaf is bounded over, which the guards above it can narrow.
      val leafSpecs = narrowed.map(path =>
        if (options.pathRanges) FPCoreEmitter.narrowed(spec, guards, path.choices) else spec)

      // A connective written out as nesting repeats what it guards, so one expression can
      // appear on several paths and only needs analyzing once. What is asked about is the
      // expression over a range, so two paths share a query only where both agree.
      val leafKeys = narrowed.map(_.leaf).zip(leafSpecs.map(_.ranges))
      val leafNames = leafKeys.distinct.zipWithIndex.toMap

      val leafErrors = options.timers.queries.branches.run(traverse(narrowed.indices) { i =>
        if (!narrowed(i).reachable) Right(RoundingError.Unreachable)
        else {
          val k = leafNames(leafKeys(i))
          errorOf(fd, s"${tag}_leaf$k", s"$named (leaf ${k + 1})",
                  narrowed(i).leaf, leafSpecs(i), options)
        }
      })

      leafErrors.flatMap { leaves =>
        regions(narrowed).map { case (differences, plan) =>
          field -> RoundoffErrorDecomposition(
            leaves,
            Shape(guards.size, narrowed.size,
                  narrowed.map(_.choices.size).maxOption.getOrElse(0),
                  narrowed.map(_.leaf).distinct.size),
            flattening, operandErrors, differences, plan, spec, field.project(whole))
        }
      }
    }

    /** The regions a divergence is searched in. Without guards there is no other path to
      * take, so none has to be built.
      */
    private def regions(narrowed: Seq[ProgramPath])(using Symbols)
      : Either[String, (Seq[Seq[inox.trees.Expr]], DiscontinuityPlan)] =
      if (guards.isEmpty) Right((Seq.empty, DiscontinuityPlan.Pairwise(Seq.empty)))
      else options.timers.encoding.run(
        DiscontinuityEncoder(guards, narrowed, spec, options.mode, options.normalise))
  }

  private def errorOf(fd: FunDef, name: String, label: String, expr: Expr, spec: InputSpec,
                      options: DecompositionOptions)(using Symbols)
    : Either[String, RoundingError] =
    if (isExact(expr, options.exactInputs)) Right(RoundingError.Exact)
    else if (exprOps.variablesOf(expr).isEmpty)
      ConstantEvaluator.error(expr, spec.precision).map(RoundingError.Computed(_))
    else options.emitter.emit(name, label, expr, spec)
           .map(source => RoundingError.FromAnalyzer(
             RoundingQuery(fd.id, name, spec.precision, source)))

  /** Whether a value is reached without rounding, so no analyzer has to be asked for it. */
  private def isExact(e: Expr, exactInputs: Boolean): Boolean =
    constantOf(e).isDefined || (exactInputs && isRoundingFree(e))

  /** Whether every step is exact in floating point, which holds of a sign flip but of no
    * arithmetic; an input counts only where inputs are taken to be exact reals.
    */
  private def isRoundingFree(e: Expr): Boolean = e match {
    case FPLit(_) => true
    case _: Variable => true
    case FPUMinus(a) => isRoundingFree(a)
    case Let(_, value, body) => isRoundingFree(value) && isRoundingFree(body)
    case _ => false
  }

  /** The value of an expression that is a constant, seen through its bindings. */
  private def constantOf(e: Expr, known: Map[Identifier, Expr] = Map.empty): Option[Double] = e match {
    case FPLit(d) => Some(d)
    case v: Variable => known.get(v.id).flatMap(constantOf(_, known))
    case Let(vd, value, body) => constantOf(body, known + (vd.id -> value))
    case _ => None
  }

  private def prefix(fd: FunDef): String = s"f_${fd.id.globalId}"
}

private[roundoff] object ConstantEvaluator {

  def error(e: Expr, precision: FPPrecision): Either[String, BigDecimal] =
    evaluate(e, Map.empty, precision).flatMap { value =>
      if (value.rounded.isNaN || value.rounded.isInfinite)
        Left(s"a value with no inputs is not finite (${value.rounded})")
      else
        Exact.ofDouble(value.rounded).map(landed => decimal((landed - value.exact).abs))
    }

  /** What the program computes, beside what the same expression is worth exactly. */
  private case class Value(rounded: Double, exact: Exact)

  private def evaluate(e: Expr, bound: Map[Identifier, Value], precision: FPPrecision)
  : Either[String, Value] = {

    /** Single precision is computed in `Float` rather than rounded from a `Double` result,
     * which would round it twice and can land on the wrong value.
     */
    def binary(single: (Float, Float) => Float,
               double: (Double, Double) => Double,
               exact: (Exact, Exact) => Either[String, Exact])
              (l: Expr, r: Expr): Either[String, Value] =
      evaluate(l, bound, precision).flatMap { a =>
        evaluate(r, bound, precision).flatMap { b =>
          val rounded = precision match {
            case FPPrecision.Binary32 => single(a.rounded.toFloat, b.rounded.toFloat).toDouble
            case FPPrecision.Binary64 => double(a.rounded, b.rounded)
          }
          exact(a.exact, b.exact).map(Value(rounded, _))
        }
      }

    e match {
      // Ahead of the arithmetic, since a literal reaches here wrapped in a sign flip or a
      // cast as readily as on its own.
      case FPLit(d) => Exact.ofDouble(d).map(Value(d, _))

      case FPAdd(_, l, r) => binary(_ + _, _ + _, (a, b) => Right(a + b))(l, r)
      case FPSub(_, l, r) => binary(_ - _, _ - _, (a, b) => Right(a - b))(l, r)
      case FPMul(_, l, r) => binary(_ * _, _ * _, (a, b) => Right(a * b))(l, r)
      case FPDiv(_, l, r) => binary(_ / _, _ / _, (a, b) => a / b)(l, r)

      case FPUMinus(a) => evaluate(a, bound, precision).map(v => Value(-v.rounded, -v.exact))

      case FPFMA(_, a, b, c) =>
        evaluate(a, bound, precision).flatMap { x =>
          evaluate(b, bound, precision).flatMap { y =>
            evaluate(c, bound, precision).map { z =>
              val rounded = precision match {
                case FPPrecision.Binary32 =>
                  Math.fma(x.rounded.toFloat, y.rounded.toFloat, z.rounded.toFloat).toDouble
                case FPPrecision.Binary64 => Math.fma(x.rounded, y.rounded, z.rounded)
              }
              Value(rounded, x.exact * y.exact + z.exact)
            }
          }
        }

      case Let(vd, value, body) =>
        evaluate(value, bound, precision)
          .flatMap(v => evaluate(body, bound + (vd.id -> v), precision))

      case v: Variable =>
        bound.get(v.id).toRight(s"'${v.id.name}' is not bound in a value with no inputs")

      // The exact side is a fraction, and none of these is one.
      case TranscendentalFunctionCall(f, _) =>
        Left(s"a value with no inputs calls '${f.symbol}', which is not a fraction")

      case other =>
        Left(s"${other.getClass.getSimpleName} cannot be evaluated without inputs")
    }
  }

  private def decimal(value: Exact): BigDecimal =
    new BigDecimal(BigDecimal(value.numerator).bigDecimal.divide(
      BigDecimal(value.denominator).bigDecimal, reportedPrecision), reportedPrecision)

  /** A fraction in lowest terms, with the sign carried by the numerator. */
  private case class Exact(numerator: BigInt, denominator: BigInt) {

    def +(other: Exact): Exact =
      Exact.of(numerator * other.denominator + other.numerator * denominator,
        denominator * other.denominator)

    def -(other: Exact): Exact = this + -other

    def *(other: Exact): Exact =
      Exact.of(numerator * other.numerator, denominator * other.denominator)

    def /(other: Exact): Either[String, Exact] =
      if (other.numerator == 0) Left("a value with no inputs divides by zero")
      else Right(Exact.of(numerator * other.denominator, denominator * other.numerator))

    def unary_- : Exact = Exact(-numerator, denominator)

    def abs: Exact = if (numerator < 0) -this else this
  }

  private object Exact {

    def of(numerator: BigInt, denominator: BigInt): Exact = {
      val shared = numerator.gcd(denominator)
      val divisor = if (shared == 0) BigInt(1) else shared
      val sign = if (denominator < 0) BigInt(-1) else BigInt(1)
      Exact(sign * numerator / divisor, sign * denominator / divisor)
    }

    /** Seeded the same way the rest of the analysis reads a literal. */
    def ofDouble(d: Double): Either[String, Exact] =
      Fraction.apply(d).map { case (numerator, denominator) => Exact(numerator, denominator) }
  }
}