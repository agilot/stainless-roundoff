/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification
package roundoff

import inox.solvers.SolverResponses._
import inox.solvers.smtlib.optimization.{IbexOptimizer, ObjectiveBounds}
import scala.collection.mutable.ArrayBuffer

/** Uses Ibex to bound how far reading a guard the wrong way can move a result.
  *
  * Ibex encloses an optimum between two numbers. Only the outer end of that enclosure is used,
  * because it holds over the whole region. A search stopped by its time limit therefore loses
  * precision but never soundness.
  */
class IbexRunner(ctx: inox.Context, settings: RoundoffSettings, recordWitnesses: Boolean) {

  /** The problems use no functions and no data types, so they go to an empty program. */
  private val program: inox.InoxProgram = inox.InoxProgram(inox.trees.NoSymbols)

  import ctx.reporter
  import inox.trees._

  /** Timers. `region` covers a whole region and therefore includes the `feasibility`,
    * `dominated` and `optimum` queries made inside it.
    */
  private val phases: inox.utils.TimerStorage = ctx.timers.verification.roundoff.ibex

  private lazy val optimizer: IbexOptimizer { val program: IbexRunner.this.program.type } =
    IbexOptimizer(program, ctx)

  private var started = false
  private var freed = false

  /** The time of the function being analysed, shared by its queries. */
  private var budget: TimeBudget = new TimeBudget(0.0, 0)

  /** The largest divergence bounded so far in the current function. */
  private var largestSoFar: BigDecimal = 0

  private val recorded = ArrayBuffer.empty[Witness]

  /** What one query found: its status, and how far the divergence moves the result. */
  private case class Verdict(status: DivergenceStatus, bound: BigDecimal)

  /** Runs `block` for one function, whose `queries` share `seconds`. */
  def within[A](seconds: Double, queries: Int)(block: => A): A = synchronized {
    budget = new TimeBudget(seconds, queries)
    largestSoFar = 0
    try block finally { budget = new TimeBudget(0.0, 0); largestSoFar = 0 }
  }

  /** The divergences recorded so far, empty unless witnesses were asked for. */
  def witnesses: Seq[Witness] = synchronized(recorded.toSeq)

  def free(): Unit = synchronized {
    if (started && !freed) {
      freed = true
      optimizer.free()
    }
  }

  /** The largest jump in the result when `region.guard` is read the wrong way.
    *
    * @param guardDifferences per guard, `lhs - rhs` and any name it was given
    * @param guardErrors      per guard, how far its two sides can be from their exact values
    */
  def regionBound(function: String,
                  region: GuardRegion,
                  guardDifferences: Seq[Seq[Expr]],
                  guardErrors: Seq[BigDecimal]): Either[String, BigDecimal] =
    synchronized {
      val error = guardErrors(region.guard)
      val where = s"$function guard ${region.guard}"
      def siteOf(pair: LeafPair) = LeafPairSite(function, region.guard, pair.taken, pair.untaken)

      // A guard whose two sides are computed exactly is read the same way by the exact and the
      // rounded program, so no pair below it can diverge.
      if (error <= 0 || region.pairs.isEmpty) {
        region.pairs.foreach(pair => record(Witness(siteOf(pair), DivergenceStatus.Unreachable)))
        val verdicts = region.pairs.map(_ => Verdict(DivergenceStatus.Unreachable, BigDecimal(0)))
        logRegion(where, verdicts, BigDecimal(0))
        Right(BigDecimal(0))
      } else {
        val constraints = region.shared ++ band(guardDifferences(region.guard), error)
        val searched = phases.region.run(inRegion(region.vars, constraints) {
          traverse(region.pairs) { pair =>
            val verdict = boundPair(pair, guardDifferences, guardErrors, siteOf(pair))
            logPair(where, pair, verdict)
            verdict
          }
        })

        searched.map { verdicts =>
          val worst = largestBound(verdicts)
          logRegion(where, verdicts, worst)
          worst
        }
      }
    }

  /** The values where a guard can be read the wrong way: its two sides are within `error`. */
  private def band(differences: Seq[Expr], error: BigDecimal): Seq[Expr] = {
    val width = Fraction.toExpr(roundedUp(error))
    differences.flatMap { difference =>
      Seq(LessEquals(difference, width), LessEquals(UMinus(difference), width))
    }
  }

  /** Runs `block` with the region's variables declared and its constraints asserted. */
  private def inRegion[A](vars: Seq[ValDef], constraints: Seq[Expr])
                         (block: => Either[String, A]): Either[String, A] = {
    started = true
    optimizer.push()
    try {
      vars.foreach(optimizer.declare)
      constraints.foreach(optimizer.assertCnstr)
      block
    } finally {
      optimizer.pop()
    }
  }

  private def largestBound(verdicts: Seq[Verdict]): BigDecimal =
    (BigDecimal(0) +: verdicts.map(_.bound)).max

  /** Bounds the difference between the two leaves of `pair`.
    *
    * In three steps, each cheaper than the next:
    *  1. is there any point where both paths can be taken? If not, the pair is infeasible;
    *  2. can the difference reach the largest bound so far? If not, it cannot change the
    *     function's result (only with `--roundoff-incumbent`);
    *  3. otherwise, bound the difference from above and from below.
    */
  private def boundPair(pair: LeafPair, guardDifferences: Seq[Seq[Expr]],
                        guardErrors: Seq[BigDecimal], site: LeafPairSite): Either[String, Verdict] = {
    val share = budget.takeShare()

    optimizer.push()
    try {
      // The guards below the split, relaxed by their errors, since the rounded program reads
      // them on rounded values.
      pair.choices.foreach { choice =>
        val width = Fraction.toExpr(roundedUp(guardErrors(choice.guard)))
        guardDifferences(choice.guard).foreach { difference =>
          optimizer.assertCnstr(
            LessEquals(if (choice.taken) difference else UMinus(difference), width))
        }
      }

      optimizer.setSearchTimeout(share * settings.feasibilityShare)
      phases.feasibility.run(optimizer.check(Simple)) match {
        case Unsat =>
          record(Witness(site, DivergenceStatus.Infeasible))
          Right(Verdict(DivergenceStatus.Infeasible, BigDecimal(0)))

        case _ =>
          // Recorded now, because a pair skipped in step 2 gets no other box, and the fuzzer
          // needs a region to search.
          record(Witness(site, DivergenceStatus.Feasible, box = Some(certifiedBox)))

          if (settings.incumbent && largestSoFar > 0 &&
              !canReach(pair.difference, largestSoFar, share)) {
            record(Witness(site, DivergenceStatus.Dominated))
            Right(Verdict(DivergenceStatus.Dominated, BigDecimal(0)))
          } else boundBothEnds(pair.difference, share, site)
      }
    } finally {
      optimizer.pop()
    }
  }

  /** The largest absolute value of `objective`: its maximum and minimum, each given half of
    * the time the feasibility check did not use.
    */
  private def boundBothEnds(objective: Expr, share: Double,
                            site: LeafPairSite): Either[String, Verdict] = {
    val each = share * (1.0 - settings.feasibilityShare) / 2.0
    for {
      high <- boundOneEnd(objective, maximizing = true, each, site)
      low <- boundOneEnd(objective, maximizing = false, each, site)
    } yield {
      val bound = high.abs max low.abs
      if (bound > largestSoFar) largestSoFar = bound
      Verdict(DivergenceStatus.Bounded, bound)
    }
  }

  /** Whether `objective` can reach `target` in absolute value. A yes-or-no question is
    * usually settled faster than computing the bound itself.
    */
  private def canReach(objective: Expr, target: BigDecimal, share: Double): Boolean = {
    val far = Fraction.toExpr(target.toDouble)

    def possible(side: Expr): Boolean = {
      optimizer.push()
      try {
        optimizer.assertCnstr(GreaterEquals(side, far))
        optimizer.setSearchTimeout(share * settings.feasibilityShare)
        phases.dominated.run(optimizer.check(Simple)) != Unsat
      } finally optimizer.pop()
    }

    possible(objective) || possible(UMinus(objective))
  }

  private def boundOneEnd(objective: Expr, maximizing: Boolean, seconds: Double,
                          site: LeafPairSite): Either[String, BigDecimal] = {
    optimizer.setSearchTimeout(seconds)
    if (maximizing) optimizer.maximize(objective) else optimizer.minimize(objective)

    phases.optimum.run(optimizer.check(Simple)) match {
      case Unsat => Left("the region became infeasible while bounding a difference")

      case _ =>
        // Read before the box, so that asking for the box cannot change the bounds.
        val bounds = optimizer.getObjectiveBounds
        record(Witness(site, DivergenceStatus.Bounded, Some(maximizing), Some(certifiedBox)))

        // An "unknown" answer still carries the bound reached when the search stopped.
        bounds match {
          case Some(ObjectiveBounds(_, Some(high))) if maximizing => Right(high)
          case Some(ObjectiveBounds(Some(low), _)) if !maximizing => Right(low)
          case Some(_) => Left("the difference between two paths is unbounded")
          case None => Left("Ibex reported no bounds for the difference between two paths")
        }
    }
  }

  private def logPair(where: String, pair: LeafPair, verdict: Either[String, Verdict]): Unit = {
    val outcome = verdict match {
      case Right(found) => s"${found.status.label}, bound ${found.bound}"
      case Left(why) => s"no bound: $why"
    }
    reporter.debug(
      s"Ibex on $where, leaf ${pair.untaken} across from ${pair.taken}: $outcome")(
      using inox.solvers.DebugSectionSolver)
  }

  /** What became of every query of one region, so that a report without boxes can be told
    * apart from a run that never reached Ibex.
    */
  private def logRegion(where: String, verdicts: Seq[Verdict], worst: BigDecimal): Unit = {
    def count(status: DivergenceStatus): Int = verdicts.count(_.status == status)

    reporter.debug(
      s"Ibex on $where: ${verdicts.size} queries, " +
      s"${count(DivergenceStatus.Unreachable)} unreachable, " +
      s"${count(DivergenceStatus.Infeasible)} refuted, " +
      s"${count(DivergenceStatus.Dominated)} dominated, " +
      s"${count(DivergenceStatus.Bounded)} bounded, worst $worst"
    )(using DebugSectionVerification)
  }

  /** By name, so that the box is only fetched from Ibex when it is kept. */
  private def record(witness: => Witness): Unit =
    if (recordWitnesses) recorded += witness

  /** The box Ibex certified around the point it found. */
  private def certifiedBox: Box =
    optimizer.getVariableBounds.map {
      case (v, ObjectiveBounds(low, high)) => v.id.name -> (low, high)
    }

  /** `d` rounded up to a double. A double is an exact fraction, so the solver reads it without
    * widening it, and rounding up only makes the region larger, which keeps the bound sound.
    */
  private def roundedUp(d: BigDecimal): Double = {
    val nearest = d.toDouble
    if (BigDecimal(nearest) >= d) nearest else Math.nextUp(nearest)
  }
}

/** One pair of leaves on either side of one guard of one function. */
case class LeafPairSite(function: String, guard: Int, taken: Int, untaken: Int)

/** The interval Ibex narrowed each variable to, with `None` for an open end. */
type Box = Map[String, (Option[BigDecimal], Option[BigDecimal])]

/** What one divergence query found. */
enum DivergenceStatus {
  /** The guard is computed exactly, so it is never read the wrong way. Ibex is not asked. */
  case Unreachable

  /** Ibex found no point where both paths can be taken. */
  case Infeasible

  /** Ibex bounded the difference between the two leaves. */
  case Bounded

  /** Ibex found a point where both paths can be taken. Recorded before bounding. */
  case Feasible

  /** Ibex showed the difference cannot reach the largest one found so far, so it cannot
    * change the result and was not bounded.
    */
  case Dominated

  def label: String = toString.toLowerCase
}

/** What one divergence query found, for the JSON report and the fuzzer.
  *
  * Every query is recorded, including refused ones, so that an empty report means nothing was
  * asked.
  */
case class Witness(
  site: LeafPairSite,
  status: DivergenceStatus,
  maximizing: Option[Boolean] = None,
  box: Option[Box] = None
) {
  def function: String = site.function
}

object Witness {
  import io.circe.Json

  /** Every witness, grouped by function, as JSON.
    *
    * A box lists the variables in the order `parametersOf` gives, which is the declaration
    * order, so that it matches the fuzzer configuration, whose intervals are positional.
    */
  def report(witnesses: Seq[Witness], parametersOf: String => Seq[String]): Json = {
    def end(d: Option[BigDecimal]): Json = d.map(Json.fromBigDecimal).getOrElse(Json.Null)

    def bounds(box: Box, parameters: Seq[String]): Json = {
      // Variables that are not parameters, such as guard names, go last.
      def position(name: String): (Int, String) =
        (parameters.indexOf(name) match { case -1 => parameters.size; case i => i }, name)

      Json.obj(box.toSeq.sortBy { case (name, _) => position(name) }.map {
        case (name, (low, high)) => name -> Json.obj("lo" -> end(low), "hi" -> end(high))
      }*)
    }

    def entry(w: Witness): Json = Json.obj(
      Seq("guard" -> Json.fromInt(w.site.guard),
          "untaken" -> Json.fromInt(w.site.untaken),
          "taken" -> Json.fromInt(w.site.taken),
          "status" -> Json.fromString(w.status.label)) ++
      w.maximizing.map(m => "objective" -> Json.fromString(if (m) "maximum" else "minimum")) ++
      w.box.map(b => "box" -> bounds(b, parametersOf(w.function)))*
    )

    Json.obj(witnesses.groupBy(_.function).toSeq.sortBy(_._1).map {
      case (function, found) => function -> Json.arr(found.map(entry)*)
    }*)
  }
}
