/* Copyright 2009-2021 EPFL, Lausanne */

package stainless.verification.roundoff

import inox.solvers.*
import inox.solvers.SolverResponses.*
import stainless.verification.{DebugSectionVerification, VCKind, VCStatus, VerificationChecker}
import stainless.{Identifier, StainlessProgram}

import scala.concurrent.duration.*

/** Discharges `@roundoff` obligations by bounding the error of the annotated function. */
trait RoundoffChecker extends VerificationChecker {
  self =>
  val program: StainlessProgram

  import context.{*, given}
  import program.*
  import program.symbols.{*, given}
  import program.trees.*

  override def checkVC(vc: VC, origVC: VC,
                       sf: SolverFactory { val program: self.program.type }): VCResult =
    vc.kind match {
      case VCKind.RoundoffError(bound, field) => checkRoundoff(vc, bound, field)
      case _ => super.checkVC(vc, origVC, sf)
    }

  /** Ibex runs as a server that outlives a single query, so it is shut down once the
    * last obligation has been answered rather than after each one.
    */
  override def verify(vcs: Seq[VC], stopWhen: VCResult => Boolean)
    : scala.concurrent.Future[Map[VC, VCResult]] = {
    readAll(vcs)
    super.verify(vcs, stopWhen)
      .andThen { case _ => ibex.free() }(using stainless.executionContext(using context))
  }

  /** Reads every roundoff obligation, and then hands what all of them found to the fuzzer.
    *
    * The fuzzer searches the regions where a divergence was seen, and one is recorded as each
    * obligation is read, so it is asked once the last of them has been read rather than once
    * the first has. The readings are kept, and the obligations answered from them.
    *
    * An interrupted run stops reading and answers with what it has, since the obligations it
    * has yet to read are not going to be answered either.
    */
  private def readAll(vcs: Seq[VC]): Unit = {
    val obligations = vcs.flatMap { vc =>
      vc.kind match {
        case VCKind.RoundoffError(_, field) => Some(vc.fid -> field)
        case _ => None
      }
    }

    if (obligations.nonEmpty) {
      obligations.foreach { case (fid, field) =>
        if (!interruptManager.isInterrupted) reading(fid, field)
      }

      // A witness file that cannot be written is not a reason to leave the obligations
      // unanswered, since every one of them has been read by now.
      witnessFile.foreach { file =>
        scala.util.Try(phases.witnesses.run(writeFuzzerInput(file))).failed.foreach(e =>
          reporter.warning(s"Could not write the divergences to $file: ${e.getMessage}"))
      }

      val _ = fuzzed
    }
  }

  private lazy val analyzer: RoundingAnalyzer = new DaisyRunner(context)

  /** File containing the regions where divergences may occur */
  private lazy val witnessFile: Option[java.io.File] =
    Some(context.options.findOptionOrDefault(optRoundoffWitnesses))
      .filter(_.nonEmpty)
      .map(new java.io.File(_))

  /** Fuzzer to detect divergences dynamically and return a lower bound on the worst
   * case roundoff error.
   */
  private lazy val fuzzer = new FuzzRunner(context)

  private lazy val ibex =
    new IbexRunner(context, recordWitnesses = witnessFile.isDefined || fuzzer.enabled)

  private lazy val exactInputs: Boolean =
    context.options.findOptionOrDefault(optRoundoffExactInputs)

  private lazy val prune: Boolean =
    context.options.findOptionOrDefault(optRoundoffPruning)

  private lazy val pathRanges: Boolean =
    context.options.findOptionOrDefault(optRoundoffPathRanges)

  private lazy val normalise: Boolean =
    context.options.findOptionOrDefault(optRoundoffNormalisation)

  private lazy val mode: DiscontinuityMode =
    context.options.findOptionOrDefault(optRoundoffDiscontinuity)

  private lazy val annotated: Seq[FunDef] =
    program.symbols.functions.values.toSeq
      .filter(_.flags.exists { case Roundoff(_) => true; case _ => false })
      .sortBy(_.id.globalId)

  private lazy val phases: inox.utils.TimerStorage = timers.verification.roundoff

  /** Debug information */
  private lazy val announced: Unit = {
    val on = (name: String, flag: Boolean) => if (flag) name else s"no $name"
    reporter.debug(
      s"Roundoff settings: ${mode.toString.toLowerCase} discontinuities, " +
      s"${budget}s per function of which ${(pruningShare * 100).toInt}% for the branch " +
      s"questions, ${(context.options.findOptionOrDefault(optRoundoffFeasibilityShare) * 100).toInt}% " +
      s"of a search for feasibility, " +
      Seq(on("pruning", prune), on("normalisation", normalise), on("path ranges", pathRanges),
          on("incumbent", context.options.findOptionOrDefault(optRoundoffIncumbent)),
          if (exactInputs) "exact inputs" else "rounded inputs").mkString(", ") +
      s", solvers ${context.options.findOptionOrDefault(inox.optSelectedSolvers).mkString(",")}"
    )(using DebugSectionRoundoff)
  }

  /** TO REVIEW */
  private lazy val analysed
    : Seq[(Identifier, Long, Either[String, Seq[(ResultPath, ErrorDecomposition)]])] =
    annotated.map { fd =>
      announced
      val start = System.nanoTime()
      val outcome = withOracle(fd) { oracle =>
        ErrorDecomposition.of(fd, exactInputs, mode, oracle, phases, normalise, pathRanges)(
          using program.symbols)
      }
      (fd.id, (System.nanoTime() - start) / 1000000, outcome)
    }

  /**
   *  TO REVIEW
   * What was made of each function: one decomposition per number in its result.
    *
    * A result that is one number gives one, under the empty path. A tuple or a case class gives
    * one per number anywhere inside it, all over the same guards, since an error of several
    * numbers is several errors and not one.
    */
  private lazy val decompositions
    : Map[Identifier, Either[String, Seq[(ResultPath, ErrorDecomposition)]]] =
    analysed.map { case (id, _, outcome) => id -> outcome }.toMap

  /** One field's decomposition, by the label the obligation was raised under. */
  private def decompositionOf(fid: Identifier, field: Option[String])
    : Either[String, ErrorDecomposition] =
    decompositions.getOrElse(fid, Left("this function was not analyzed")).flatMap { fields =>
      fields.find { case (path, _) => field.forall(_ == path.label) }
        .map { case (_, parts) => parts }
        .toRight(s"nothing in the result of this function is called '${field.getOrElse("")}'")
    }

  /** The first decomposition of a function, which is all of it where the result is one number. */
  private def firstOf(fid: Identifier): Either[String, ErrorDecomposition] =
    decompositionOf(fid, None)

  /** How many numbers a function's result holds, as far as it was read. */
  private def fieldsOf(fid: Identifier): Int =
    decompositions.get(fid).flatMap(_.toOption).map(_.size).getOrElse(1)

  /** How one obligation reads: the function, and the field where the result holds several. */
  private def label(fid: Identifier, field: Option[String]): String =
    field.filter(_.nonEmpty).fold(getFunction(fid).id.name)(f => s"${getFunction(fid).id.name}.$f")

  /** How long everything before the divergence queries took, for each function.
    *
    * The budget is net of this, so that it bounds the analysis of a function rather than only
    * its search. What the analyzer takes is not counted: it answers one batch for every
    * function at once, and there is no honest way to charge that to any one of them.
    */
  private lazy val spentOn: Map[Identifier, Long] =
    analysed.map { case (id, spent, _) => id -> spent }.toMap

  private lazy val budget: Double = context.options.findOptionOrDefault(optRoundoffTimeout)

  /** What fraction of a function's budget its reachability questions may take together. */
  private lazy val pruningShare: Double =
    context.options.findOptionOrDefault(optRoundoffPruningShare).max(0.0).min(1.0)

  /** Minimum time that can be allowed to a query */
  private val minQueryTimeout = 0.001

  /** Set once the selected solver turns out not to reason about floating-point values, after
    * which nothing is asked of it again.
    *
    * Only ever touched while `decompositions` is being computed, which one thread does under
    * the lock of that lazy value, so no guard of its own is needed.
    */
  private var solverRefused = false

  /** Whether a question has been left unanswered, which is worth saying once. */
  private var solverUnsettled = false

  /** Runs `block` with an oracle backed by one solver, which lives exactly as long as the
    * enumeration it prunes.
    *
    * Not every solver reads floating point: the native Z3 interface has none of the theory,
    * and `--solvers` names it by default. Such a solver keeps what it could not encode to
    * itself until the first `check`, and throws on every `check` after that, so the run stops
    * asking rather than trying again. One that reads the theory but cannot settle a question
    * answers `Unknown`, which keeps the branch and is worth saying once rather than giving up
    * on the rest.
    */
  private def withOracle[A](fd: FunDef)(block: BranchOracle => A): A =
    if (!prune || solverRefused) block(BranchOracle.open)
    else {
      val factory = getFactory(options + optCheckModels(false) + optSilentErrors(true))
      var started: Option[factory.S] = None

      // What the questions will be about, told before the first of them is asked. These are the
      // values the function's fields became rather than the objects holding them, so the solver
      // is never handed a datatype: the one this analysis recommends has none.
      var values: Seq[ValDef] = fd.params
      var assumptions: Expr = fd.precondition.map(Preprocessor.stripAnnotations)
                                .getOrElse(BooleanLiteral(true))

      // Cut once the count is known, which is before the first question is asked. A function
      // that turns out to ask none never builds it and never walks its body to count them.
      var cake: Option[Cake] = None

      // What the questions came to, said once the walk is over: a run that prunes nothing is
      // worth telling apart from one that had no time to try.
      var asked, refuted, unanswered, skipped = 0
      var spent = 0L

      // What `--timeout` asked for, where it was asked for at all. A question is never given
      // longer than that, since a budget of its own is no reason to overrun the one the run
      // was given.
      var ambient: Option[Duration] = None

      // Built by the first question rather than up front, since a function whose body has no
      // conditional in it asks none at all, and most of them do not.
      def solver: factory.S = started match {
        case Some(ready) => ready
        case None =>
          val fresh = phases.pruning.setup.run {
            val s = factory.getNewSolver()
            ambient = s.optTimeout.map(_.millis)
            values.foreach(s.declare)
            s.assertCnstr(assumptions)
            s
          }
          started = Some(fresh)
          fresh
      }

      try {
        block(new BranchOracle {
          override def knowing(known: Seq[ValDef], taken: Expr): Unit = {
            values = known
            assumptions = taken
          }

          override def expecting(questions: => Int): Unit =
            cake = Some(new Cake(budget * pruningShare, questions))

          def assuming[B](condition: Expr)(block: => B): Option[B] = {
            // What this question may take: the share left over the questions left. An
            // over-estimate of how many are left only makes the shares smaller, so the phase
            // keeps to its part of the budget either way.
            val allowance = cake.fold(budget * pruningShare)(_.slice())

            if (solverRefused || allowance < minQueryTimeout) { skipped += 1; Some(block) }
            else {
              cake.foreach(_.taken())
              asked += 1
              val questioned = solver
              questioned.setTimeout(ambient.fold(allowance.seconds)(_.min(allowance.seconds)))
              questioned.push()
              try {
                questioned.assertCnstr(condition)
                // A question left open has to keep the branch: only a refutation says that
                // no input reaches it.
                val (took, answer) = phases.pruning.questions.runAndGetTime(questioned.check(Simple))
                spent += took
                told(fd, condition, answer)
                answer match {
                  case scala.util.Success(Unsat) => refuted += 1; None
                  case scala.util.Success(Unknown) =>
                    unanswered += 1; unsettled(fd); Some(block)
                  case scala.util.Success(_) => Some(block)
                  case scala.util.Failure(e) =>
                    unanswered += 1; refused(fd, e); Some(block)
                }
              } finally questioned.pop()
            }
          }
        })
      } catch {
        case e: inox.Unsupported => refused(fd, e); block(BranchOracle.open)
      } finally {
        if (asked + skipped > 0) {
          val share = budget * pruningShare
          val used = ((share - cake.fold(0.0)(_.left)) * 1000).toInt.max(0)
          reporter.debug(
            s"Roundoff pruning of ${fd.id.asString}: $asked of " +
            s"${counted(asked + skipped, "branch question")} asked, $refuted refuted, " +
            s"$unanswered unanswered, $skipped skipped for want of time; $used ms of a " +
            s"${(share * 1000).toInt} ms share, $spent ms of it waiting on an answer and the " +
            "rest on building the solver and stating the guards"
          )(using DebugSectionRoundoff)
        }
        started.foreach(factory.reclaim)
      }
    }

  /** Says what became of one question, so that a run can be watched cutting a subtree rather
    * than refusing its leaves one at a time.
    */
  private def told(fd: FunDef, condition: Expr,
                   answer: scala.util.Try[SolverResponses.SimpleResponse]): Unit = {
    val outcome = answer match {
      case scala.util.Success(Unsat) => "no input reaches it"
      case scala.util.Success(response) => s"kept ($response)"
      case scala.util.Failure(e) => s"kept, unanswered: ${e.getMessage}"
    }
    reporter.debug(s"Reachability of ${fd.id.name} under ${condition.asString}: $outcome")(
      using inox.solvers.DebugSectionSolver)
  }

  /** A question that answers nothing is still followed by the rest of them, since one hard
    * branch says little about the next, but a run where that is happening throughout is worth
    * telling apart from one where every branch was settled.
    */
  private def unsettled(fd: FunDef): Unit = {
    if (!solverUnsettled)
      reporter.warning(fd.getPos,
        "A question about which branches are taken was left unanswered, so some leaf no input " +
        "reaches may still count towards the bound; the questions of one function share " +
        s"${pruningShare} of --roundoff-timeout, which raising either gives them more of, and a " +
        "solver reading floating point, such as --solvers=smt-bitwuzla, settles more of them")
    solverUnsettled = true
  }

  private def refused(fd: FunDef, e: Throwable): Unit = {
    if (!solverRefused)
      reporter.warning(fd.getPos,
        s"The selected solver cannot answer about floating-point values (${e.getMessage}), so " +
        "no unreachable path was set aside and every leaf counts towards the bound; " +
        "--solvers=smt-bitwuzla answers these")
    solverRefused = true
  }

  /** What each function calls its inputs, in the order it declares them. */
  private lazy val parametersOf: Map[String, Seq[String]] =
    annotated.map { fd =>
      fd.id.name -> firstOf(fd.id).toOption
        .map(_.flattening.parameters).getOrElse(fd.params).map(_.id.name)
    }.toMap

  /** The functions handed to the fuzzer, each with the program written for it.
    *
    * A witness names the function it belongs to and nothing more, so two annotated
    * functions of the same name cannot be told apart, and only the first is written.
    */
  private lazy val subjects: Seq[(FuzzSubject, String)] =
    annotated.filter(_.flags.contains(Fuzz)).foldLeft(
      (Set.empty[String], Seq.empty[(FuzzSubject, String)])) {
      case ((taken, built), fd) =>
        val name = fd.id.name
        val subject =
          if (taken(name))
            Left(s"another annotated function is called '$name', and a witness names only " +
                 "the function it belongs to, so the two cannot be told apart")
          else
            for {
              _ <- Either.cond(!ResultPath.isCompound(fd.returnType), (),
                     "the fuzzer returns one double, and this function's result holds several " +
                     "numbers; the analysis answers about each of them but the fuzzer is not " +
                     "asked about any")
              parts <- firstOf(fd.id)
              values = parts.flattening.parameters
              domain <- traverse(values)(p => parts.spec.ranges.get(p.id).toRight(
                          s"no range in the precondition for '${p.id.name}'"))
              source <- FuzzProgramEmitter.emit(fd, name, parts.spec, parts.body, values,
                          FPCoreEmitter.assumptions(fd, parts.flattening))(using program.symbols)
            } yield (FuzzSubject(name, values.map(_.id.name), domain), source)

        subject match {
          case Right(one) => (taken + name, built :+ one)
          case Left(why) =>
            reporter.warning(fd.getPos, s"No fuzzer program for ${fd.id.asString}: $why")
            (taken, built)
        }
    }._2

  /** Every query of every annotated function goes out in one batch, because the analyzer
    * pays its startup cost once per run.
    */
  /** Every query of every annotated function goes out in one batch, because the analyzer
    * pays its startup cost once per run.
    *
    * That one batch holds the branches and the conditions together, and the analyzer's own
    * timing cannot separate them either: its results carry a figure for the whole run, repeated
    * against every function in it. So `rounding` is one phase covering both.
    */
  private lazy val measured: Map[String, Either[String, RoundingResult]] = {
    val queries = decompositions.values
      .collect { case Right(fields) => fields.flatMap { case (_, parts) => parts.queries } }
      .flatten.toSeq
      .distinctBy(_.name)

    if (queries.isEmpty) Map.empty else phases.rounding.run(analyzer.analyze(queries))
  }

  /** What was made of one obligation, and how long that took.
    *
    * Every obligation is read before any of them is answered, so that the fuzzer can be
    * handed the regions all of them found; this is where the reading waits until the
    * obligation's own turn comes. One that was not read then, because the run was
    * interrupted, is read here instead.
    */
  private val readings = scala.collection.mutable.Map
    .empty[(Identifier, Option[String]), (Long, scala.util.Try[Either[String, BigDecimal]])]

  private def reading(fid: Identifier, field: Option[String])
    : (Long, scala.util.Try[Either[String, BigDecimal]]) =
    synchronized {
      readings.getOrElseUpdate((fid, field),
        timers.verification.runAndGetTime(errorOf(fid, field)))
    }

  private def checkRoundoff(vc: VC, bound: Option[BigDecimal],
                           field: Option[String]): VCResult = {
    val fd = getFunction(vc.fid)
    val named = label(vc.fid, field)

    val (time, found) = reading(vc.fid, field)
    // The fuzzer has already searched the regions that every reading established, so this
    // only reads what it made of this function.
    val observed = fuzz(fd)

    val (status, error, lower) = found match {
      case scala.util.Success(Right(error)) =>
        reporter.info(fd.getPos, s"Inferred a roundoff error of $error for $named")
        observed.foreach(reported(fd, error, _))
        (verdict(fd, named, error, bound), Some(error), observed)

      case scala.util.Success(Left(why)) =>
        reporter.warning(fd.getPos, s"Cannot bound the roundoff error of $named: $why")
        (VCStatus.Unsupported, None, observed)

      case scala.util.Failure(thrown) =>
        reporter.warning(fd.getPos, s"Roundoff analysis of $named failed: ${thrown.getMessage}")
        reporter.debug(thrown.getStackTrace.take(12).mkString("\n"))(
          using DebugSectionVerification)
        (VCStatus.Unsupported, None, None)
    }

    def round(e: BigDecimal, towards: java.math.RoundingMode): String =
      e.round(new java.math.MathContext(4, towards)).toString

    // Displays the error next to the solvers
    val figures =
      error.map(e => s"${analyzer.name}: ${round(e, java.math.RoundingMode.CEILING)}").toSeq ++
        lower.map(l => s"${fuzzer.name}: ${round(l, java.math.RoundingMode.FLOOR)}")

    val solver = if (figures.isEmpty) analyzer.name else figures.mkString(", ")
    VCResult(status, Some(solver), Some(time), None)
  }

  /** Says what the fuzzer made of a function, and whether the two bounds agree.
    *
    * A fuzzed error above the inferred one is not a loose bound but a broken one: either
    * the bound is unsound, or the program handed to the fuzzer is not the one analyzed.
    */
  private def reported(fd: FunDef, inferred: BigDecimal, observed: BigDecimal): Unit = {
    reporter.info(fd.getPos,
      s"Fuzzing ${fd.id.asString} made an error of $observed, so the true worst case " +
      s"lies in [$observed, $inferred]")

    if (observed > inferred)
      reporter.warning(fd.getPos,
        s"The fuzzer made an error of $observed on ${fd.id.asString}, which is above the " +
        s"inferred bound $inferred: the bound is unsound, or the program the fuzzer ran " +
        "is not the one that was analyzed")
  }

  private def verdict(fd: FunDef, named: String, error: BigDecimal,
                      bound: Option[BigDecimal]): VCStatus =
    bound match {
      case None => VCStatus.Valid
      case Some(limit) if error <= limit => VCStatus.Valid
      case Some(limit) =>
        reporter.warning(fd.getPos,
          s"Roundoff error for $named is $error, which exceeds the bound $limit")
        VCStatus.Invalid(VCStatus.Unsatisfiable)
    }

  /** The error bound for one number of one function's result, or why none was established. */
  private def errorOf(fid: Identifier, field: Option[String]): Either[String, BigDecimal] =
    decompositionOf(fid, field).flatMap { parts =>
      for {
        // A guard can only be misread where its two sides are within their combined error.
        guardErrors <- traverse(parts.guardOperandErrors) { case (lhs, rhs) =>
                         for { l <- errorFrom(lhs); r <- errorFrom(rhs) } yield l + r
                       }
        rounding <- traverse(parts.reachableLeaves)(errorFrom)
        name = label(fid, field)
        // What is left of the function's budget, cut equally among the numbers in its result:
        // they are separate obligations, and none of them is told what the others will need,
        // so each is given the same share.
        remaining = remainingFor(fid) / fieldsOf(fid).max(1)
        bounds <- ibex.within(remaining, parts.discontinuities.queries) {
                    parts.discontinuities match {
                      case DiscontinuityPlan.Pairwise(problems) =>
                        traverse(problems.zipWithIndex) { case (problem, path) =>
                          ibex.discontinuityBound(problem, parts.guardDifferences, guardErrors,
                                                  Site(name, path))
                        }
                      case DiscontinuityPlan.Merged(regions) =>
                        traverse(regions) { region =>
                          ibex.mergedBound(region, parts.guardDifferences, guardErrors,
                                           Site(name, region.guard))
                        }
                      case DiscontinuityPlan.ViaReference(regions) =>
                        traverse(regions) { region =>
                          ibex.referenceBound(region, parts.guardDifferences, guardErrors,
                                              Site(name, region.guard))
                        }
                    }
                  }
      } yield {
        val worstDiscontinuity = (BigDecimal(0) +: bounds).max
        val worstRounding = rounding.max
        // Named by the field as well, since a result of several numbers gives one of these
        // lines per number and they otherwise read alike.
        val shown = label(fid, field)
        val shape = parts.shape

        reporter.debug(
          s"Roundoff shape of $shown: ${counted(shape.guards, "guard")} over " +
          s"${counted(shape.paths, "path")}, nested ${shape.depth} deep, " +
          s"${counted(shape.distinct, "leaf", "leaves")} computing something different, " +
          s"${counted(parts.unreachableCount, "path")} that no input reaches"
        )(using DebugSectionRoundoff)

        reporter.debug(
          s"Roundoff plan of $shown (${mode.toString.toLowerCase}): " +
          s"${counted(parts.discontinuities.size, "region")} holding " +
          s"${counted(parts.discontinuities.queries, "comparison")}, " +
          s"${bounds.count(_ > 0)} of which ${if (bounds.count(_ > 0) == 1) "holds" else "hold"} " +
          "a divergence; " +
          s"${counted(parts.queries.map(_.name).distinct.size, "analyzer query", "analyzer queries")}"
        )(using DebugSectionRoundoff)

        // The two halves of the bound, on the section that carries a line per obligation.
        // What they were worked out from is on `roundoff`, in the three lines above.
        reporter.debug(
          s"Roundoff for $shown (${mode.toString.toLowerCase}): " +
          s"worst discontinuity $worstDiscontinuity, worst rounding $worstRounding"
        )(using DebugSectionVerification)
        // Added under a rounding of the analysis's own choosing, because the default one
        // shortens a long sum towards zero as readily as away from it, and a bound that
        // has been shortened towards zero is no longer a bound.
        new BigDecimal(worstDiscontinuity.bigDecimal, reportedPrecision) + worstRounding
      }
    }

  /** What is left of a function's budget once the phases before the queries are taken off.
    *
    * The reachability questions are one of those phases and are held to their own share of the
    * budget, so what they leave behind is here rather than lost: a function whose branches
    * settle at once hands the queries more than the share the split nominally gives them.
    */
  private def remainingFor(fid: Identifier): Double = {
    val spent = spentOn.getOrElse(fid, 0L) / 1000.0
    val left = budget - spent

    if (left <= 0)
      reporter.warning(getFunction(fid).getPos,
        s"Reading ${getFunction(fid).id.asString} took ${spent}s of a ${budget}s budget, so its " +
        "divergences are bounded on whatever is left of it; --roundoff-timeout raises it")

    left
  }

  private def errorFrom(source: RoundingError): Either[String, BigDecimal] = source match {
    case RoundingError.Exact => Right(BigDecimal(0))
    // Only the leaves a run reaches are ever asked about, so this says the decomposition and
    // the reading of it have come apart rather than that the error is nothing.
    case RoundingError.Unreachable =>
      Left("the error of a leaf no run reaches was asked for")
    case RoundingError.Computed(error) => Right(error)
    case RoundingError.FromAnalyzer(query) =>
      measured
        .getOrElse(query.name, Left(s"${analyzer.name} reported no result for '${query.name}'"))
        .map(_.absError)
  }

  /** The witnesses, and beside them the program and the configuration the fuzzer reads.
    *
    * All three take their name from the file the witnesses were asked for, because the
    * fuzzer finds a program from its configuration by that very rule.
    */
  private def writeFuzzerInput(file: java.io.File): Unit = {
    stainless.utils.JsonUtils.writeFile(file,
      Witness.report(ibex.witnesses, name => parametersOf.getOrElse(name, Seq.empty)))
    if (subjects.nonEmpty) writeSubjects(file)
  }

  private def write(file: java.io.File, content: String): Unit = {
    val out = new java.io.FileWriter(file)
    try out.write(content) finally out.close()
  }

  /** The program and the configuration for every `@fuzz` function, beside `base`.
    *
    * @return the configuration, which is what the fuzzer is pointed at
    */
  private def writeSubjects(base: java.io.File): java.io.File = {
    val found = ibex.witnesses.groupBy(_.function)
    val conf = sibling(base, "conf")

    write(sibling(base, "scala"), subjects.map(_._2).mkString("\n"))
    write(conf, FuzzConfEmitter.emit(subjects.map {
      case (subject, _) => subject -> found.getOrElse(subject.name, Seq.empty)
    }))
    conf
  }

  /** Where the fuzzer's input goes when no witnesses were asked to be written out. */
  private lazy val scratch: java.io.File = {
    val directory = java.nio.file.Files.createTempDirectory("stainless-roundoff").toFile
    directory.deleteOnExit()
    new java.io.File(directory, "roundoff.json")
  }

  /** Fuzzes all functions to compute a lower bound worst-case roundoff error for each of them
    */
  private lazy val fuzzed: Either[String, Map[String, BigDecimal]] =
    if (!fuzzer.enabled || subjects.isEmpty) Left("the fuzzer was not run")
    else
      scala.util.Try(
        phases.fuzzing.run(fuzzer.run(writeSubjects(witnessFile.getOrElse(scratch)))))
        .fold(e => Left(s"the fuzzer could not be run: ${e.getMessage}"), identity)

  /** The lower bound returned by the fuzzer on a specific function. */
  private def fuzz(fd: FunDef): Option[BigDecimal] =
    if (!fuzzer.enabled || subjects.isEmpty) None
    else
      fuzzed.flatMap(_.get(fd.id.name).toRight("the fuzzer reported nothing for it")) match {
        case Right(error) => Some(error)
        case Left(why) =>
          reporter.warning(fd.getPos, s"No fuzzed error for ${fd.id.asString}: $why")
          None
      }

  private def sibling(file: java.io.File, extension: String): java.io.File = {
    val name = file.getName
    val base = name.lastIndexOf('.') match { case -1 => name; case dot => name.take(dot) }
    new java.io.File(file.getParentFile, s"$base.$extension")
  }




}