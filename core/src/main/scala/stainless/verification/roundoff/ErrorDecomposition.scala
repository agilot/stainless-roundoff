/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification
package roundoff

import trees._

import scala.collection.mutable.ArrayBuffer

/** A comparison a conditional branches on, oriented so that taking it puts `lhs` below `rhs`. */
case class Guard(lhs: Expr, rhs: Expr, strict: Boolean)

/** Which side of one guard a path took. */
case class BranchChoice(guard: Int, taken: Boolean)

/** One straight-line path: what it chose at each guard, and the expression it ends in.
  *
  * `reachable` is false where no input reaches the leaf in floating point. Such a leaf is
  * never rounded by a run and is never the path a run takes instead of the exact one, but it
  * stays a path the exact run can take, so it is recorded rather than dropped.
  */
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

          case BooleanLiteral(true) => walk(thenBranch, inner, choices, live)
          case BooleanLiteral(false) => walk(elseBranch, inner, choices, live)

          case comparison =>
            asGuard(comparison).flatMap { guard =>
              val index = guards.size
              val closed = Guard(close(inner, guard.lhs), close(inner, guard.rhs), guard.strict)
              guards += closed
              for {
                _ <- descend(closed, taken = true, thenBranch, inner, choices, index, live)
                _ <- descend(closed, taken = false, elseBranch, inner, choices, index, live)
              } yield ()
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

    case FPEquals(_, _) =>
      Left("the guard tests for equality, which marks no region two paths can be compared over")

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
            mode: DiscontinuityMode)
    : Either[String, (Seq[inox.trees.Expr], DiscontinuityPlan)] = {

    val inputs = (paths.map(_.leaf) ++ guards.flatMap(g => Seq(g.lhs, g.rhs)))
      .flatMap(exprOps.variablesOf)
      .distinctBy(_.id)
      .sortBy(_.id.globalId)

    // Identifiers are reused so a counter-example stays readable; floating-point and real
    // variables never meet in one query.
    val realVariables: Map[Identifier, inox.trees.Variable] =
      inputs.map(v => v.id -> inox.trees.Variable(v.id, inox.trees.RealType(), Seq.empty)).toMap

    for {
      _ <- inputs.map(_.id).find(!spec.ranges.contains(_)) match {
             case Some(id) => Left(s"no range in the precondition for '${id.name}'; " +
               "add bounds of the form 'lo <= x && x <= hi'")
             case None => Right(())
           }
      leaves <- traverse(paths)(path => RealEncoder(path.leaf, realVariables))
      guardOperands <- traverse(guards) { guard =>
                         for {
                           lhs <- RealEncoder(guard.lhs, realVariables)
                           rhs <- RealEncoder(guard.rhs, realVariables)
                         } yield (lhs, rhs)
                       }
    } yield {
      val box = inputs.flatMap { input =>
        val (low, high) = spec.ranges(input.id)
        Seq(inox.trees.LessEquals(Fraction.literal(low), realVariables(input.id)),
            inox.trees.LessEquals(realVariables(input.id), Fraction.literal(high)))
      }

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

      val vars = inputs.map(input => realVariables(input.id).toVal)

      def pairwise: Seq[DiscontinuityProblem] = paths.zipWithIndex.map { case (path, i) =>
        val divergentPaths = paths.zipWithIndex.collect {
          // Reaching a leaf that computes the same thing is not a divergence, and neither is
          // a leaf no run reaches, since the rounded program never lands there.
          case (other, j) if j != i && other.leaf != path.leaf && other.reachable =>
            DivergentPath(j, other.choices.drop(divergencePoint(path, other)),
                          inox.trees.Minus(leaves(j), leaves(i)))
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
                                  inox.trees.Minus(leaves(leaf), leaves(reference))))
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
            inox.trees.Minus(leaves(other), leaves(one)))

          MergedRegion(guard, vars, shared, crossings)
        }
      }

      val plan = mode match {
        case DiscontinuityMode.Pairwise => DiscontinuityPlan.Pairwise(pairwise)
        case DiscontinuityMode.Merged => DiscontinuityPlan.Merged(merged)
        case DiscontinuityMode.Reference => DiscontinuityPlan.ViaReference(viaReference)
      }

      (guardOperands.map { case (lhs, rhs) => inox.trees.Minus(lhs, rhs) }, plan)
    }
  }
}

/** Reads a floating-point expression as the exact computation it approximates. */
private[roundoff] object RealEncoder {

  import inox.trees.{Plus, Minus, Times, Division, UMinus}

  def apply(e: Expr, realVariables: Map[Identifier, inox.trees.Variable])
    : Either[String, inox.trees.Expr] = {

    def binary(build: (inox.trees.Expr, inox.trees.Expr) => inox.trees.Expr, l: Expr, r: Expr) =
      for { a <- apply(l, realVariables); b <- apply(r, realVariables) } yield build(a, b)

    e match {
      case v: Variable => realVariables.get(v.id).toRight(s"unbound variable '${v.id.name}'")
      case FPLit(d) =>
        Fraction.ofDouble(d).map { case (num, den) => inox.trees.FractionLiteral(num, den) }

      // Rounding modes are irrelevant: this is the exact computation the rounded one is
      // measured against.
      case FPAdd(_, l, r) => binary(Plus(_, _), l, r)
      case FPSub(_, l, r) => binary(Minus(_, _), l, r)
      case FPMul(_, l, r) => binary(Times(_, _), l, r)
      case FPDiv(_, l, r) => binary(Division(_, _), l, r)
      case FPUMinus(a) => apply(a, realVariables).map(UMinus(_))
      case FPFMA(_, a, b, c) =>
        for { x <- apply(a, realVariables); y <- apply(b, realVariables); z <- apply(c, realVariables) }
          yield Plus(Times(x, y), z)

      case Let(vd, value, body) =>
        val realVar = inox.trees.Variable(vd.id, inox.trees.RealType(), Seq.empty)
        for {
          realValue <- apply(value, realVariables)
          realBody <- apply(body, realVariables + (vd.id -> realVar))
        } yield inox.trees.Let(realVar.toVal, realValue, realBody)

      case MathCall(f, args) =>
        traverse(args)(apply(_, realVariables)).flatMap(realCall(f, _))

      case _: IfExpr =>
        Left("a conditional appears inside an expression, and only conditionals that shape " +
          "the body are supported")

      case other =>
        Left(s"no real-arithmetic equivalent for ${other.getClass.getSimpleName}")
    }
  }

  /** The exact counterpart of one call, which only Ibex among the solvers can evaluate. */
  private def realCall(f: MathFunction, args: Seq[inox.trees.Expr])
    : Either[String, inox.trees.Expr] = {
    import inox.trees.{FractionLiteral, RealAcos, RealAsin, RealAtan, RealCos, RealExp,
                       RealLog, RealPow, RealSin, RealSqrt, RealTan}

    (f, args) match {
      case (MathFunction.Sqrt, Seq(a)) => Right(RealSqrt(a))
      case (MathFunction.Exp, Seq(a)) => Right(RealExp(a))
      case (MathFunction.Log, Seq(a)) => Right(RealLog(a))
      case (MathFunction.Sin, Seq(a)) => Right(RealSin(a))
      case (MathFunction.Cos, Seq(a)) => Right(RealCos(a))
      case (MathFunction.Tan, Seq(a)) => Right(RealTan(a))
      case (MathFunction.Asin, Seq(a)) => Right(RealAsin(a))
      case (MathFunction.Acos, Seq(a)) => Right(RealAcos(a))
      case (MathFunction.Atan, Seq(a)) => Right(RealAtan(a))

      // Ibex reads any other exponent as exp(y * log(x)), which holds only where the
      // base is positive, so it refuses one rather than answering on a smaller region.
      case (MathFunction.Pow, Seq(base, exponent @ FractionLiteral(_, one))) if one == 1 =>
        Right(RealPow(base, exponent))
      case (MathFunction.Pow, _) =>
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

/** The parts a function's roundoff error is built from.
  *
  * A run misses the exact result by the rounding along its path plus the distance to the
  * path it should have taken; `leaves` and `guards` give the first, `discontinuities` the
  * second.
  */
case class ErrorDecomposition(
  leaves: Seq[RoundingError],
  guardOperandErrors: Seq[(RoundingError, RoundingError)],
  guardDifferences: Seq[inox.trees.Expr],
  discontinuities: DiscontinuityPlan,
  spec: InputSpec,
  body: Expr
) {
  /** The leaves a run can round, which are the only ones its error is made of. */
  def reachableLeaves: Seq[RoundingError] =
    leaves.filterNot(_ == RoundingError.Unreachable)

  /** How many leaves no input reaches. */
  def unreachableCount: Int = leaves.count(_ == RoundingError.Unreachable)

  def queries: Seq[RoundingQuery] =
    (reachableLeaves ++ guardOperandErrors.flatMap { case (lhs, rhs) => Seq(lhs, rhs) })
      .flatMap(_.asQuery)
}

object ErrorDecomposition {

  /** @param timers where each phase reports how long it took; detached by default, so a
    *               caller with no context of its own measures nothing
    */
  def of(fd: FunDef, exactInputs: Boolean, mode: DiscontinuityMode,
         oracle: BranchOracle = BranchOracle.open,
         timers: inox.utils.TimerStorage = inox.utils.TimerStorage())(using Symbols)
    : Either[String, ErrorDecomposition] =
    for {
      body <- timers.preprocessing.run(Preprocessor(fd))
      spec <- timers.preprocessing.run(FPCoreEmitter.specOf(fd, body))
      // The questions asked while enumerating are timed inside this, under `paths.pruning`.
      (guards, paths) <- timers.paths.run(PathExtractor(body, oracle))

      // Every leaf refused leaves the function with nothing a run can compute, which is what
      // an unsatisfiable precondition looks like from here.
      _ <- Either.cond(paths.exists(_.reachable), (),
             "no path through this function is reachable, so its precondition may be " +
             "unsatisfiable; --sat-precond checks that on its own")

      // A connective written out as nesting repeats what it guards, so one expression can
      // appear on several paths and only needs analyzing once.
      leafNames = paths.map(_.leaf).distinct.zipWithIndex.toMap
      guardNames = guards.distinct.zipWithIndex.toMap

      leaves <- timers.queries.branches.run(traverse(paths) { path =>
                  if (!path.reachable) Right(RoundingError.Unreachable)
                  else {
                    val k = leafNames(path.leaf)
                    errorOf(fd, s"${prefix(fd)}_leaf$k", s"${fd.id.name} (leaf ${k + 1})",
                            path.leaf, spec, exactInputs)
                  }
                })
      operandErrors <- timers.queries.conditions.run(traverse(guards) { guard =>
                         val k = guardNames(guard)
                         for {
                           lhs <- errorOf(fd, s"${prefix(fd)}_guard${k}_lhs",
                                          s"${fd.id.name} (guard ${k + 1}, left)",
                                          guard.lhs, spec, exactInputs)
                           rhs <- errorOf(fd, s"${prefix(fd)}_guard${k}_rhs",
                                          s"${fd.id.name} (guard ${k + 1}, right)",
                                          guard.rhs, spec, exactInputs)
                         } yield (lhs, rhs)
                       })
      // Without guards there is no other path to take, so no region has to be built.
      (differences, plan) <- if (guards.isEmpty)
                               Right((Seq.empty, DiscontinuityPlan.Pairwise(Seq.empty)))
                             else timers.encoding.run(
                                    DiscontinuityEncoder(guards, paths, spec, mode))
    } yield ErrorDecomposition(leaves, operandErrors, differences, plan, spec, body)

  private def errorOf(fd: FunDef, name: String, label: String, expr: Expr, spec: InputSpec,
                      exactInputs: Boolean)(using Symbols): Either[String, RoundingError] =
    if (isExact(expr, exactInputs)) Right(RoundingError.Exact)
    else if (exprOps.variablesOf(expr).isEmpty)
      ConstantEvaluator.error(expr, spec.precision).map(RoundingError.Computed(_))
    else FPCoreEmitter.emit(name, label, expr, spec)
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