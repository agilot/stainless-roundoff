/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification
package roundoff

import inox.solvers.SolverResponses._
import inox.solvers.smtlib.optimization.{IbexOptimizer, ObjectiveBounds}

import scala.collection.mutable.ArrayBuffer

/** Drives Ibex to bound how far a misread guard can move a result.
  *
  * Ibex brackets an optimum between two numbers. Only the outer end of that bracket is
  * read here, the one that holds over the whole region rather than at the single point
  * the search happened to find, so a search cut short by its time limit loses precision
  * but never soundness.
  */
class IbexRunner(ctx: inox.Context, recordWitnesses: Boolean) {

  /** The problems carry no functions and no data types, so they go to a bare program of
    * their own rather than through the one being verified.
    */
  private val program: inox.InoxProgram = inox.InoxProgram(inox.trees.NoSymbols)

  import ctx.reporter
  import inox.trees._

  /** Where this runner reports its time, beside the other phases of the analysis.
    *
    * `region` covers a whole region and so contains the `feasibility` and `optimum` queries
    * made inside it; they are listed beside it rather than under it because one region holds
    * many of each.
    */
  private val phases: inox.utils.TimerStorage = ctx.timers.verification.roundoff.ibex

  /** What share of a query goes on deciding whether its region is empty. */
  private val feasibilityShare: Double =
    ctx.options.findOptionOrDefault(optRoundoffFeasibilityShare).max(0.0).min(1.0)

  /** Whether a query that cannot be the widest is set aside rather than bracketed. */
  private val incumbent: Boolean = ctx.options.findOptionOrDefault(optRoundoffIncumbent)

  private var cake: Cake = new Cake(0.0, 0)

  /** The widest divergence answered so far, which the ones after it have to beat. */
  private var widest: BigDecimal = 0

  /** Bounds the divergences of one function inside a budget divided among its queries. */
  def within[A](seconds: Double, queries: Int)(block: => A): A = synchronized {
    cake = new Cake(seconds, queries)
    widest = 0
    try block finally { cake = new Cake(0.0, 0); widest = 0 }
  }

  private lazy val optimizer: IbexOptimizer { val program: IbexRunner.this.program.type } =
    IbexOptimizer(program, ctx)

  private var used = false
  private var freed = false

  private val collected = ArrayBuffer.empty[Witness]

  /** What one divergence established: how far it moves the result, and why. */
  private case class Verdict(status: DivergenceStatus, bound: BigDecimal)

  /** The divergences recorded so far, empty unless witnesses were asked for. */
  def witnesses: Seq[Witness] = synchronized(collected.toSeq)

  def free(): Unit = synchronized {
    if (used && !freed) {
      freed = true
      optimizer.free()
    }
  }

  /** The largest jump possible inside one region.
    *
    * `guardErrors` gives, per guard, how far its two sides can be from their exact
    * values; further apart than that, the rounded comparison agrees with the exact one.
    */
  def discontinuityBound(problem: DiscontinuityProblem,
                         guardDifferences: Seq[Seq[Expr]],
                         guardErrors: Seq[BigDecimal],
                         site: Site): Either[String, BigDecimal] =
    synchronized {
      // Only the guard a path diverges at has to be misread. The ones below it the
      // rounded program reads on its own values and takes for real, so a guard that
      // rounds exactly there narrows the region rather than emptying it.
      val (reachable, unreachable) = problem.divergentPaths.partition(
        _.divergingChoices.headOption.forall(choice => guardErrors(choice.guard) > 0))

      unreachable.foreach(path => record(Witness.unreachable(site, path.toPath)))
      val refused = unreachable.map(_ => Verdict(DivergenceStatus.Unreachable, BigDecimal(0)))

      val searched: Either[String, Seq[Verdict]] =
        if (reachable.isEmpty) Right(Seq.empty)
        else phases.region.run(searching(problem.vars, problem.constraints) {
          traverse(reachable)(divergenceBound(_, guardDifferences, guardErrors, site))
        })

      searched.map { verdicts =>
        val worst = (BigDecimal(0) +: verdicts.map(_.bound)).max
        summarize(s"${site.function} path ${site.region}", refused ++ verdicts, worst)
        worst
      }
    }

  /** The largest jump possible where one guard is read the other way.
    *
    * Every leaf below the guard is measured against the region's reference instead of
    * against every other leaf, so whichever side the exact run was on, the two sides are
    * at most their two furthest distances from the reference apart. That over-estimates,
    * but it costs a query per leaf rather than a query per pair of them.
    */
  def referenceBound(region: DivergenceRegion,
                     guardDifferences: Seq[Seq[Expr]],
                     guardErrors: Seq[BigDecimal],
                     site: Site): Either[String, BigDecimal] =
    synchronized {
      val error = guardErrors(region.guard)
      val comparisons = region.taken ++ region.untaken

      // A guard whose two sides round exactly is read the same way by both programs, so
      // nothing below it is ever reached the other way.
      if (error <= 0 || comparisons.isEmpty) {
        comparisons.foreach(comparison =>
          record(Witness.unreachable(site, comparison.leaf, Some(region.reference))))
        val refused = comparisons.map(_ => Verdict(DivergenceStatus.Unreachable, BigDecimal(0)))
        summarize(s"${site.function} guard ${site.region}", refused, BigDecimal(0))
        Right(BigDecimal(0))
      } else {
        val searched = phases.region.run(searching(region.vars,
                                 region.shared ++ band(region.guard, error, guardDifferences)) {
          def measured(comparisons: Seq[ReferenceComparison]) =
            traverse(comparisons)(
              referenceDistance(_, region.reference, guardDifferences, guardErrors, site))

          measured(region.taken).flatMap { near =>
            measured(region.untaken).map(far => (near, far))
          }
        })

        searched.map { case (near, far) =>
          val worst = furthest(near) + furthest(far)
          summarize(s"${site.function} guard ${site.region}", near ++ far, worst)
          worst
        }
      }
    }

  /** The largest jump possible where one guard is read the other way, both ways at once.
    *
    * The two directions of a divergence sit either side of the same band, so one region
    * covering the whole of it answers for both. What that costs is the conditions below
    * the guard: only the side the exact run took holds those exactly, and a region cannot
    * say which side that was, so both are relaxed by their own guard errors.
    */
  def mergedBound(region: MergedRegion,
                  guardDifferences: Seq[Seq[Expr]],
                  guardErrors: Seq[BigDecimal],
                  site: Site): Either[String, BigDecimal] =
    synchronized {
      val error = guardErrors(region.guard)

      // A guard whose two sides round exactly is read the same way by both programs, so
      // nothing below it is ever reached the other way.
      if (error <= 0 || region.pairs.isEmpty) {
        region.pairs.foreach(pair =>
          record(Witness.unreachable(site, pair.untaken, Some(pair.taken),
                                     DiscontinuityMode.Merged)))
        val refused = region.pairs.map(_ => Verdict(DivergenceStatus.Unreachable, BigDecimal(0)))
        summarize(s"${site.function} guard ${site.region}", refused, BigDecimal(0))
        Right(BigDecimal(0))
      } else {
        val searched = phases.region.run(searching(region.vars,
                                 region.shared ++ band(region.guard, error, guardDifferences)) {
          traverse(region.pairs)(crossDistance(_, guardDifferences, guardErrors, site))
        })

        searched.map { verdicts =>
          val worst = furthest(verdicts)
          summarize(s"${site.function} guard ${site.region}", verdicts, worst)
          worst
        }
      }
    }

  /** Where the two readings of one guard part company, which is only where its two sides
    * are within their combined error of each other.
    */
  private def band(guard: Int, error: BigDecimal, guardDifferences: Seq[Seq[Expr]]): Seq[Expr] = {
    val width = Fraction.toExpr(roundedUp(error))
    guardDifferences(guard).flatMap { difference =>
      Seq(LessEquals(difference, width), LessEquals(UMinus(difference), width))
    }
  }

  /** Runs a block over one region, declared and asserted once for every query inside it. */
  private def searching[A](vars: Seq[ValDef], constraints: Seq[Expr])
                          (block: => Either[String, A]): Either[String, A] = {
    used = true
    optimizer.push()
    try {
      vars.foreach(optimizer.declare)
      constraints.foreach(optimizer.assertCnstr)
      block
    } finally {
      optimizer.pop()
    }
  }

  private def furthest(verdicts: Seq[Verdict]): BigDecimal =
    (BigDecimal(0) +: verdicts.map(_.bound)).max

  /** How far one divergent path's result can be from this path's, where it is reachable. */
  private def divergenceBound(path: DivergentPath,
                              guardDifferences: Seq[Seq[Expr]],
                              guardErrors: Seq[BigDecimal],
                              site: Site): Either[String, Verdict] = {
    val verdict = measure(path.divergingChoices, path.difference, guardDifferences, guardErrors,
                          Witness.infeasible(site, path.toPath),
                          (maximizing, box) => Witness.bounded(site, path.toPath, maximizing, box),
                          Witness.dominated(site, path.toPath),
                          box => Witness.feasible(site, path.toPath, box), compare = true)
    told(site, s"path ${site.region}, divergence to path ${path.toPath}", verdict)
    verdict
  }

  /** How far one leaf can be from the reference its region measures against. */
  private def referenceDistance(comparison: ReferenceComparison, reference: Int,
                                guardDifferences: Seq[Seq[Expr]],
                                guardErrors: Seq[BigDecimal],
                                site: Site): Either[String, Verdict] = {
    val against = Some(reference)
    val scheme = DiscontinuityMode.Reference
    val verdict = measure(comparison.choices, comparison.difference, guardDifferences, guardErrors,
                          Witness.infeasible(site, comparison.leaf, against, scheme),
                          (maximizing, box) =>
                            Witness.bounded(site, comparison.leaf, maximizing, box, against, scheme),
                          Witness.dominated(site, comparison.leaf, against, scheme),
                          box => Witness.feasible(site, comparison.leaf, box, against, scheme),
                          // A region measured against a reference adds two of these together,
                          // so one of them being below the widest says nothing about the sum.
                          compare = false)
    told(site, s"guard ${site.region}, leaf ${comparison.leaf} against $reference", verdict)
    verdict
  }

  /** How far two leaves either side of one guard can be from each other. */
  private def crossDistance(pair: CrossComparison,
                            guardDifferences: Seq[Seq[Expr]],
                            guardErrors: Seq[BigDecimal],
                            site: Site): Either[String, Verdict] = {
    val against = Some(pair.taken)
    val scheme = DiscontinuityMode.Merged
    val verdict = measure(pair.choices, pair.difference, guardDifferences, guardErrors,
                          Witness.infeasible(site, pair.untaken, against, scheme),
                          (maximizing, box) =>
                            Witness.bounded(site, pair.untaken, maximizing, box, against, scheme),
                          Witness.dominated(site, pair.untaken, against, scheme),
                          box => Witness.feasible(site, pair.untaken, box, against, scheme),
                          compare = true)
    told(site, s"guard ${site.region}, leaf ${pair.untaken} across from ${pair.taken}", verdict)
    verdict
  }

  /** Brackets one difference over the region narrowed by the branches a path takes. */
  private def measure(choices: Seq[BranchChoice], objective: Expr,
                      guardDifferences: Seq[Seq[Expr]], guardErrors: Seq[BigDecimal],
                      refused: => Witness,
                      bounded: (Boolean, Box) => Witness,
                      outdone: => Witness,
                      reached: Box => Witness,
                      compare: Boolean): Either[String, Verdict] = {
    val budget = cake.slice()
    cake.taken()

    optimizer.push()
    try {
      choices.foreach { choice =>
        val width = Fraction.toExpr(roundedUp(guardErrors(choice.guard)))
        guardDifferences(choice.guard).foreach { difference =>
          optimizer.assertCnstr(
            LessEquals(if (choice.taken) difference else UMinus(difference), width))
        }
      }

      // An empty region means no point of it takes this path, so there is nothing to
      // optimize over. Deciding that is the cheap half of the question, so it is asked
      // first and given the smaller part of the budget.
      optimizer.setSearchTimeout(budget * feasibilityShare)
      phases.feasibility.run(optimizer.check(Simple)) match {
        case Unsat =>
          record(refused)
          Right(Verdict(DivergenceStatus.Infeasible, BigDecimal(0)))

        // The region holds a point, so it is recorded before anything is optimized. That is
        // what a fuzzer is given to search, and it has to be recorded here: a divergence set
        // aside below is never bracketed, and would otherwise leave no region to look in.
        case _ =>
          record(reached(certifiedBox))

          // A divergence narrower than one already answered cannot be the widest, and the
          // widest is all the function is asked for, so how far this one reaches is never
          // worked out.
          if (compare && incumbent && widest > 0 && !reaches(objective, widest, budget)) {
            record(outdone)
            Right(Verdict(DivergenceStatus.Dominated, BigDecimal(0)))
          } else bracket(objective, budget, bounded)
      }
    } finally {
      optimizer.pop()
    }
  }

  /** How far a difference reaches at either end of the region it is measured over. */
  private def bracket(objective: Expr, budget: Double,
                      bounded: (Boolean, Box) => Witness): Either[String, Verdict] = {

    // Whatever the emptiness check left goes to the two ends, which share it evenly.
    val each = budget * (1.0 - feasibilityShare) / 2.0
    extremum(objective, maximizing = true, each, bounded).flatMap { high =>
      extremum(objective, maximizing = false, each, bounded).map { low =>
        val bound = high.abs max low.abs
        if (bound > widest) widest = bound
        Verdict(DivergenceStatus.Bounded, bound)
      }
    }
  }

  /** Whether the objective can reach `target` at either end, which is a question with a yes or
    * a no rather than a figure, and so is settled where working the figure out would not be.
    */
  private def reaches(objective: Expr, target: BigDecimal, budget: Double): Boolean = {
    val far = Fraction.toExpr(target.toDouble)

    def possible(side: Expr): Boolean = {
      optimizer.push()
      try {
        optimizer.assertCnstr(GreaterEquals(side, far))
        optimizer.setSearchTimeout(budget * feasibilityShare)
        phases.dominated.run(optimizer.check(Simple)) != Unsat
      } finally optimizer.pop()
    }

    possible(objective) || possible(UMinus(objective))
  }

  private def extremum(objective: Expr, maximizing: Boolean, budget: Double,
                       bounded: (Boolean, Box) => Witness): Either[String, BigDecimal] = {
    optimizer.setSearchTimeout(budget)
    if (maximizing) optimizer.maximize(objective) else optimizer.minimize(objective)

    phases.optimum.run(optimizer.check(Simple)) match {
      case Unsat => Left("the region became infeasible while bounding a difference")

      case _ =>
        // Read before the box, so that asking for one cannot disturb the other.
        val bounds = optimizer.getObjectiveBounds
        record(bounded(maximizing, certifiedBox))

        // "unknown" still carries the bound the search had established when it stopped.
        bounds match {
          case Some(ObjectiveBounds(_, Some(high))) if maximizing => Right(high)
          case Some(ObjectiveBounds(Some(low), _)) if !maximizing => Right(low)
          case Some(_) => Left("the difference between two paths is unbounded")
          case None => Left("Ibex reported no bounds for the difference between two paths")
        }
    }
  }

  private def told(site: Site, what: String, verdict: Either[String, Verdict]): Unit = {
    val outcome = verdict match {
      case Right(found) => s"${found.status.label}, bound ${found.bound}"
      case Left(why) => s"no bound: $why"
    }
    reporter.debug(s"Ibex on ${site.function} $what: $outcome")(
      using inox.solvers.DebugSectionSolver)
  }

  /** Says what became of every query of one region, so that a report with no boxes in it
    * can still be told apart from a run that never reached Ibex.
    */
  private def summarize(where: String, verdicts: Seq[Verdict], worst: BigDecimal): Unit = {
    def count(status: DivergenceStatus): Int = verdicts.count(_.status == status)

    reporter.debug(
      s"Ibex on $where: ${verdicts.size} queries, " +
      s"${count(DivergenceStatus.Unreachable)} unreachable, " +
      s"${count(DivergenceStatus.Infeasible)} refuted, " +
      s"${count(DivergenceStatus.Dominated)} dominated, " +
      s"${count(DivergenceStatus.Bounded)} bounded, worst $worst"
    )(using DebugSectionVerification)
  }

  private def record(witness: => Witness): Unit =
    if (recordWitnesses) collected += witness

  /** The box Ibex certified around the point it found. */
  private def certifiedBox: Box =
    optimizer.getVariableBounds.map {
      case (v, ObjectiveBounds(low, high)) => v.id.name -> (low, high)
    }

  /** Rounds up to a double, because a double is an exact fraction the solver reads
    * without widening it, and a wider region keeps the answer sound.
    */
  private def roundedUp(d: BigDecimal): Double = {
    val nearest = d.toDouble
    if (BigDecimal(nearest) >= d) nearest else Math.nextUp(nearest)
  }
}