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
      case VCKind.RoundoffError(bound) => checkRoundoff(vc, bound)
      case _ => super.checkVC(vc, origVC, sf)
    }

  /** Ibex runs as a server that outlives a single query, so it is shut down once the
    * last obligation has been answered rather than after each one.
    */
  override def verify(vcs: Seq[VC], stopWhen: VCResult => Boolean)
    : scala.concurrent.Future[Map[VC, VCResult]] =
    super.verify(vcs, stopWhen)
      .andThen { case _ => ibex.free() }(using stainless.executionContext(using context))

  private lazy val analyzer: RoundingAnalyzer = new DaisyRunner(context)

  private lazy val witnessFile: Option[java.io.File] =
    Some(context.options.findOptionOrDefault(optRoundoffWitnesses))
      .filter(_.nonEmpty)
      .map(new java.io.File(_))

  private lazy val fuzzer = new FuzzRunner(context)

  // The fuzzer searches the regions the witnesses name, so it needs them recorded even
  // where none were asked to be written out.
  private lazy val ibex =
    new IbexRunner(context, recordWitnesses = witnessFile.isDefined || fuzzer.enabled)

  private lazy val exactInputs: Boolean =
    context.options.findOptionOrDefault(optRoundoffExactInputs)

  private lazy val mode: DiscontinuityMode =
    context.options.findOptionOrDefault(optRoundoffDiscontinuity)

  private lazy val annotated: Seq[FunDef] =
    program.symbols.functions.values.toSeq
      .filter(_.flags.exists { case Roundoff(_) => true; case _ => false })
      .sortBy(_.id.globalId)

  private lazy val decompositions: Map[Identifier, Either[String, ErrorDecomposition]] =
    annotated
      .map(fd => fd.id -> withOracle(fd) { oracle =>
        ErrorDecomposition.of(fd, exactInputs, mode, oracle)(using program.symbols)
      })
      .toMap

  /** How long one question about a branch may take where no timeout was asked for, so that a
    * hard floating-point query costs the run a moment rather than the whole of it.
    */
  private val branchTimeout = 3.seconds

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
    if (solverRefused) block(BranchOracle.open)
    else {
      val factory = getFactory(options + optCheckModels(false) + optSilentErrors(true))
      val solver = factory.getNewSolver()
      if (solver.optTimeout.isEmpty) solver.setTimeout(branchTimeout)

      try {
        fd.params.foreach(solver.declare)
        fd.precondition.map(Preprocessor.stripAnnotations).foreach(solver.assertCnstr)

        block(new BranchOracle {
          def assuming[B](condition: Expr)(block: => B): Option[B] =
            if (solverRefused) Some(block)
            else {
              solver.push()
              try {
                solver.assertCnstr(condition)
                // A question left open has to keep the branch: only a refutation says that
                // no input reaches it.
                val answer = scala.util.Try(solver.check(Simple))
                told(fd, condition, answer)
                answer match {
                  case scala.util.Success(Unsat) => None
                  case scala.util.Success(Unknown) => unsettled(fd); Some(block)
                  case scala.util.Success(_) => Some(block)
                  case scala.util.Failure(e) => refused(fd, e); Some(block)
                }
              } finally solver.pop()
            }
        })
      } catch {
        case e: inox.Unsupported => refused(fd, e); block(BranchOracle.open)
      } finally {
        factory.reclaim(solver)
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

  /** A solver that answers nothing is still asked the rest of the questions, since one hard
    * branch says little about the next, but a run where that is happening throughout is worth
    * telling apart from one where every branch was settled.
    */
  private def unsettled(fd: FunDef): Unit = {
    if (!solverUnsettled)
      reporter.warning(fd.getPos,
        "The selected solver left a question about which branches are taken unanswered, so " +
        "some leaf no input reaches may still count towards the bound; a solver reading " +
        "floating point, such as --solvers=smt-bitwuzla, settles more of them")
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
    annotated.map(fd => fd.id.name -> fd.params.map(_.id.name)).toMap

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
              parts <- decompositions.getOrElse(fd.id, Left("this function was not analyzed"))
              domain <- traverse(fd.params)(p => parts.spec.ranges.get(p.id).toRight(
                          s"no range in the precondition for '${p.id.name}'"))
              source <- FuzzProgramEmitter.emit(fd, name, parts.spec, parts.body)(
                          using program.symbols)
            } yield (FuzzSubject(name, fd.params.map(_.id.name), domain), source)

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
  private lazy val measured: Map[String, Either[String, RoundingResult]] = {
    val queries = decompositions.values
      .collect { case Right(parts) => parts.queries }
      .flatten.toSeq
      .distinctBy(_.name)

    if (queries.isEmpty) Map.empty else analyzer.analyze(queries)
  }

  private def checkRoundoff(vc: VC, bound: Option[BigDecimal]): VCResult = {
    val fd = getFunction(vc.fid)

    val (time, outcome) = timers.verification.runAndGetTime {
      val result = errorOf(vc.fid)
      witnessFile.foreach(writeFuzzerInput)
      // Asked for only once the function has been analyzed, since the fuzzer searches the
      // regions that analysis established.
      val observed = fuzzedError(fd)

      result match {
        case Right(error) =>
          reporter.info(fd.getPos, s"Inferred a roundoff error of $error for ${fd.id.asString}")
          observed.foreach(reported(fd, error, _))
          (verdict(fd, error, bound), Some(error), observed)

        case Left(why) =>
          reporter.warning(fd.getPos, s"Cannot bound the roundoff error of ${fd.id.asString}: $why")
          (VCStatus.Unsupported, None, observed)
      }
    }

    val (status, error, observed) = outcome match {
      case scala.util.Success(result) => result
      case scala.util.Failure(e) =>
        reporter.warning(fd.getPos, s"Roundoff analysis of ${fd.id.asString} failed: ${e.getMessage}")
        reporter.debug(e.getStackTrace.take(12).mkString("\n"))(using DebugSectionVerification)
        (VCStatus.Unsupported, None, None)
    }

    // The summary table has no column for an inferred value, so it rides along in the
    // solver cell, which is the one field of a result this checker fills in itself.
    val figures =
      error.map(e => s"${analyzer.name}: ${shortenedUp(e)}").toSeq ++
        observed.map(l => s"${fuzzer.name}: ${shortenedDown(l)}")

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

  private def verdict(fd: FunDef, error: BigDecimal, bound: Option[BigDecimal]): VCStatus =
    bound match {
      case None => VCStatus.Valid
      case Some(limit) if error <= limit => VCStatus.Valid
      case Some(limit) =>
        reporter.warning(fd.getPos,
          s"Roundoff error for ${fd.id.asString} is $error, which exceeds the bound $limit")
        VCStatus.Invalid(VCStatus.Unsatisfiable)
    }

  /** The error bound for one function, or why none could be established. */
  private def errorOf(fid: Identifier): Either[String, BigDecimal] =
    decompositions.getOrElse(fid, Left("this function was not analyzed")).flatMap { parts =>
      for {
        // A guard can only be misread where its two sides are within their combined error.
        guardErrors <- traverse(parts.guardOperandErrors) { case (lhs, rhs) =>
                         for { l <- errorFrom(lhs); r <- errorFrom(rhs) } yield l + r
                       }
        rounding <- traverse(parts.reachableLeaves)(errorFrom)
        name = getFunction(fid).id.name
        bounds <- parts.discontinuities match {
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
      } yield {
        val worstDiscontinuity = (BigDecimal(0) +: bounds).max
        val worstRounding = rounding.max
        reporter.debug(
          s"Roundoff for ${getFunction(fid).id.asString} (${mode.toString.toLowerCase}): " +
          s"${parts.leaves.size} paths of which ${parts.unreachableCount} unreachable, " +
          s"${parts.discontinuities.size} regions of which " +
          s"${bounds.count(_ > 0)} hold a divergence, " +
          s"worst discontinuity $worstDiscontinuity, worst rounding $worstRounding"
        )(using DebugSectionVerification)
        // Added under a rounding of the analysis's own choosing, because the default one
        // shortens a long sum towards zero as readily as away from it, and a bound that
        // has been shortened towards zero is no longer a bound.
        new BigDecimal(worstDiscontinuity.bigDecimal, reportedPrecision) + worstRounding
      }
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

  private val observed = scala.collection.mutable.Map.empty[String, Either[String, BigDecimal]]

  /** The widest error the fuzzer made on one function, where one was asked for.
    *
    * The fuzzer searches the regions the analysis established, so it cannot be asked about
    * a function before that function has been analyzed. One run answers for everything
    * analyzed so far, and a later one picks up whatever has been added since.
    */
  private def fuzzedError(fd: FunDef): Option[BigDecimal] = synchronized {
    val function = fd.id.name

    if (!fuzzer.enabled || subjects.isEmpty) None
    else {
      if (!observed.contains(function)) {
        val outcome = fuzzer.run(writeSubjects(witnessFile.getOrElse(scratch)))
        outcome.foreach(errors => observed ++= errors.view.mapValues(Right(_)))
        if (!observed.contains(function))
          observed(function) =
            Left(outcome.fold(identity, _ => "the fuzzer reported nothing for it"))
      }

      observed(function) match {
        case Right(error) => Some(error)
        case Left(why) =>
          reporter.warning(fd.getPos,
            s"No fuzzed error for ${fd.id.asString}: $why")
          None
      }
    }
  }

  private def sibling(file: java.io.File, extension: String): java.io.File = {
    val name = file.getName
    val base = name.lastIndexOf('.') match { case -1 => name; case dot => name.take(dot) }
    new java.io.File(file.getParentFile, s"$base.$extension")
  }

  private def write(file: java.io.File, content: String): Unit = {
    val out = new java.io.FileWriter(file)
    try out.write(content) finally out.close()
  }

  /** Shortened away from the value it bounds, so that shortening leaves it a bound: the
    * inferred ceiling rounds up, and the error actually made rounds down.
    */
  private def shortenedUp(e: BigDecimal): String = shortened(e, java.math.RoundingMode.CEILING)
  private def shortenedDown(e: BigDecimal): String = shortened(e, java.math.RoundingMode.FLOOR)

  private def shortened(e: BigDecimal, towards: java.math.RoundingMode): String =
    e.round(new java.math.MathContext(4, towards)).toString
}