/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification
package roundoff

import trees._
import scala.collection.mutable.ArrayBuffer
import inox.solvers.SolverResponses._
import scala.concurrent.duration._

/** A comparison a conditional branches on: `lhs < rhs` when strict, `lhs <= rhs` otherwise. */
case class Guard(lhs: Expr, rhs: Expr, strict: Boolean)

/** Which side of one guard a path took. */
case class BranchChoice(guard: Int, taken: Boolean)

/** One path through the body: the side taken at each guard, and the straight-line leaf it
  * ends in. `reachable` is false when no input satisfying the precondition takes it.
  */
case class ProgramPath(choices: Seq[BranchChoice], leaf: Expr, reachable: Boolean = true)

/** Splits a function body into the straight-line paths through it. */
object PathExtractor {

  /** A chain of `let` bindings, outermost first. */
  private type Scope = Seq[(ValDef, Expr)]

  /** The guards of `body` and every path through them.
    *
    * @param oracle asked at every guard whether the branch is reachable. A branch it refutes
    *               is still walked, so its paths are recorded, but they are marked unreachable.
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
          // `&&` and `||` are rewritten as nested conditionals, so that every path condition
          // is a conjunction of comparisons, which is what Ibex accepts.
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

          // `a == b` is the same test as `a <= b && b <= a` for every float, NaN and both
          // zeros included. Written that way it becomes two guards, each with a band on either
          // side, which is what a divergence is measured across. `a != b` is the `Not` above.
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

    /** Walks one side of a guard, first asking the oracle whether it is reachable.
      *
      * The oracle already assumes every guard above, so one refutation covers the whole
      * subtree. Below a refutation nothing more is asked, but the paths are still recorded.
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

  /** The comparison or connective under a condition, with the bindings on the way to it.
    * The frontend puts a condition and its operands in `let` bindings.
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

  /** `expr` wrapped in the bindings of `scope` that it uses. */
  private def close(scope: Scope, expr: Expr): Expr =
    scope.foldRight(expr) { case ((vd, value), kept) =>
      if (exprOps.variablesOf(kept).exists(_.id == vd.id)) Let(vd, value, kept) else kept
    }

  private def bindingsOf(scope: Scope): Map[Identifier, Expr] =
    scope.map { case (vd, value) => vd.id -> value }.toMap

  private def conjunction(es: Seq[Expr]): Expr = if (es.size == 1) es.head else And(es)
  private def disjunction(es: Seq[Expr]): Expr = if (es.size == 1) es.head else Or(es)
}

/** Answers whether a branch is worth walking into, given the branches already taken.
  *
  * `block` runs inside the assumption, so an implementation that holds a solver accumulates
  * one condition per level and a nested question is asked under everything above it.
  */
trait BranchOracle extends AutoCloseable {

  /** `None` where `condition` is refuted under what is already assumed, and the outcome of
    * `block` otherwise.
    *
    * Only a refutation may answer `None`: a question left open has to keep the branch.
    */
  def assuming[A](condition: Expr)(block: => A): Option[A]

  /** Releases whatever the oracle holds once the walk over one function is over. */
  def close(): Unit = ()
}

object BranchOracle {

  /** Refutes nothing, so every path is reachable. */
  val open: BranchOracle = new BranchOracle {
    def assuming[A](condition: Expr)(block: => A): Option[A] = Some(block)
  }
}

/** Builds the oracle for one function.
  *
  * @param values      the function's inputs, with every field it reads as a value of its own,
  *                    so an oracle never has to reason about an object
  * @param assumptions the precondition and the invariants, over those same values
  * @param questions   the most questions there will be, so that time can be divided among
  *                    them. By name, because counting costs a walk over the body and an open
  *                    oracle does not need it.
  */
trait BranchOracleFactory {
  def apply(fd: FunDef, values: Seq[ValDef], assumptions: Expr, questions: => Int): BranchOracle
}

object BranchOracleFactory {
  val open: BranchOracleFactory = new BranchOracleFactory {
    def apply(fd: FunDef, values: Seq[ValDef], assumptions: Expr, questions: => Int) =
      BranchOracle.open
  }
}

/** What one branch choice says about a guard's operands, in floating point. */
private[roundoff] object FPPathCondition {

  /** Taking a guard means `lhs < rhs` (or `<=`). Not taking it is the negation of that, not
    * `rhs <= lhs`: the two agree over the reals but differ when an operand is NaN.
    */
  def of(guard: Guard, taken: Boolean): Expr = {
    val below =
      if (guard.strict) FPLessThan(guard.lhs, guard.rhs) else FPLessEquals(guard.lhs, guard.rhs)
    if (taken) below else Not(below)
  }
}

/** A solver factory whose solvers read Stainless trees and accept a timeout. */
type PruningSolverFactory = inox.solvers.SolverFactory {
  val program: StainlessProgram
  type S <: inox.solvers.combinators.TimeoutSolver { val program: StainlessProgram }
}

/** Builds one solver-backed oracle per function, so that paths no input takes are set aside.
  *
  * The questions of one function share `pruningShare` of its budget. Not every solver reads
  * floating point; once one turns out not to, no further question is asked in this run.
  */
private[roundoff] final class SolverBranchOracles(
  ctx: inox.Context,
  settings: RoundoffSettings,
  newFactory: () => PruningSolverFactory,
  timers: inox.utils.TimerStorage
)(using symbols: Symbols) extends BranchOracleFactory {

  import ctx.reporter

  private given PrinterOptions = PrinterOptions.fromSymbols(symbols, ctx)

  private lazy val factory: PruningSolverFactory = newFactory()

  /** The shortest time a question is worth asking for, in seconds. */
  private val minQueryTimeout = 0.001

  private var solverRejectsFloats = false
  private var warnedUnanswered = false

  def apply(fd: FunDef, values: Seq[ValDef], assumptions: Expr, questions: => Int): BranchOracle =
    if (!settings.pruning || solverRejectsFloats) BranchOracle.open
    else {
      // Built before the budget starts, so that its start-up is not charged to the questions.
      val _ = factory
      new SolverBranchOracle(fd, values, assumptions, questions)
    }

  private final class SolverBranchOracle(fd: FunDef, values: Seq[ValDef], assumptions: Expr,
                                         questions: Int) extends BranchOracle {

    private val share = settings.budget * settings.pruningShare
    private val budget = new TimeBudget(share, questions)

    private var solver: Option[factory.S] = None

    /** The timeout `--timeout` puts on every solver. A question never gets more than that. */
    private var globalTimeout: Option[Duration] = None

    private var asked, refuted, unanswered, skipped = 0
    private var waitedMillis = 0L

    /** Built by the first question, since most bodies have no conditional and ask nothing. */
    private def started: factory.S = solver.getOrElse {
      val fresh = timers.pruning.setup.run {
        val s = factory.getNewSolver()
        globalTimeout = s.optTimeout.map(_.millis)
        values.foreach(s.declare)
        s.assertCnstr(assumptions)
        s
      }
      solver = Some(fresh)
      fresh
    }

    def assuming[A](condition: Expr)(block: => A): Option[A] = {
      // Over-estimating how many questions are left only makes each share smaller, so the
      // questions keep to their part of the budget either way.
      val allowance = budget.nextShare

      if (solverRejectsFloats || allowance < minQueryTimeout) { skipped += 1; Some(block) }
      else {
        budget.markAsked()
        asked += 1
        if (isRefuted(condition, allowance)) None else Some(block)
      }
    }

    /** Whether no input satisfies `condition` under the branches already taken. A question
      * left open keeps its branch: only a refutation says no input reaches it.
      */
    private def isRefuted(condition: Expr, allowance: Double): Boolean =
      try {
        val s = started
        s.setTimeout(globalTimeout.map(_.min(allowance.seconds)).getOrElse(allowance.seconds))
        s.push()
        try {
          s.assertCnstr(condition)
          val (took, answer) = timers.pruning.questions.runAndGetTime(s.check(Simple))
          waitedMillis += took
          logQuestion(condition, answer)
          answer match {
            case scala.util.Success(Unsat) => refuted += 1; true
            case scala.util.Success(Unknown) => unanswered += 1; warnUnanswered(); false
            case scala.util.Success(_) => false
            case scala.util.Failure(e) => unanswered += 1; rejectFloats(e); false
          }
        } finally s.pop()
      } catch {
        case e: inox.Unsupported => rejectFloats(e); false
      }

    override def close(): Unit = {
      if (asked + skipped > 0) logSummary()
      solver.foreach(factory.reclaim)
    }

    private def logQuestion(condition: Expr, answer: scala.util.Try[SimpleResponse]): Unit = {
      val outcome = answer match {
        case scala.util.Success(Unsat) => "no input reaches it"
        case scala.util.Success(response) => s"kept ($response)"
        case scala.util.Failure(e) => s"kept, unanswered: ${e.getMessage}"
      }
      reporter.debug(s"Reachability of ${fd.id.name} under ${condition.asString}: $outcome")(
        using inox.solvers.DebugSectionSolver)
    }

    private def logSummary(): Unit = {
      val usedMillis = ((share - budget.left) * 1000).toInt.max(0)
      reporter.debug(
        s"Roundoff pruning of ${fd.id.asString}: $asked of " +
        s"${counted(asked + skipped, "branch question")} asked, $refuted refuted, " +
        s"$unanswered unanswered, $skipped skipped for lack of time; $usedMillis ms of a " +
        s"${(share * 1000).toInt} ms share, $waitedMillis ms of it waiting for the solver"
      )(using DebugSectionRoundoff)
    }

    /** Warned about once per run: one hard branch says little, but a run that settles none
      * prunes nothing.
      */
    private def warnUnanswered(): Unit = {
      if (!warnedUnanswered)
        reporter.warning(fd.getPos,
          "A question about which branches are taken was left unanswered, so a leaf that no " +
          "input reaches may still count towards the bound. The questions of one function share " +
          s"${settings.pruningShare} of --roundoff-timeout; raising either gives them more " +
          "time, and a solver that reads floating point, such as --solvers=smt-bitwuzla, " +
          "answers more of them")
      warnedUnanswered = true
    }

    private def rejectFloats(e: Throwable): Unit = {
      if (!solverRejectsFloats)
        reporter.warning(fd.getPos,
          s"The selected solver cannot answer about floating-point values (${e.getMessage}), " +
          "so no unreachable path was set aside and every leaf counts towards the bound; " +
          "--solvers=smt-bitwuzla answers these")
      solverRejectsFloats = true
    }
  }
}
