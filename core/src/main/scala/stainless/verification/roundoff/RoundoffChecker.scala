/* Copyright 2009-2021 EPFL, Lausanne */

package stainless.verification.roundoff

import inox.solvers.*
import stainless.verification.{DebugSectionVerification, VCKind, VCStatus, VerificationChecker}
import stainless.{Identifier, StainlessProgram}

/** Discharges `@roundoff` obligations by bounding the error of the annotated function.
  *
  * The work runs in stages, each one a member below:
  *  1. `decomposed`: every `@roundoff` function split into leaves, guards and regions
  *  2. `analyzerResults`: the rounding error of every leaf, in one analyzer run
  *  3. `upperBound`: per obligation, the worst rounding plus the worst divergence (Ibex)
  *  4. `writeWitnesses` and `fuzzing`: the regions Ibex found, and a lower bound from them
  */
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
      case VCKind.RoundoffError(maxUpperBound, field) =>
        val fd: FunDef = getFunction(vc.fid)
        val named = displayName(vc.fid, field)
        val (upperBoundTime, upperBoundResult) = upperBound(vc.fid, field)
        val lowerBoundResult = fuzzing.lowerBound(fd)

        val (vcStatus, uB, lB) = upperBoundResult match {
          case scala.util.Success(Right(uB)) =>
            reporter.info(fd.getPos, s"Inferred a roundoff error of $uB for $named")
            lowerBoundResult.foreach(compare(fd, uB, _))
            (checkBound(fd, named, uB, maxUpperBound), Some(uB), lowerBoundResult)

          case scala.util.Success(Left(why)) =>
            reporter.warning(fd.getPos, s"Cannot bound the roundoff error of $named: $why")
            (VCStatus.Unsupported, None, lowerBoundResult)

          case scala.util.Failure(thrown) =>
            reporter.warning(fd.getPos, s"Roundoff analysis of $named failed: ${thrown.getMessage}")
            reporter.debug(thrown.getStackTrace.take(12).mkString("\n"))(
              using DebugSectionVerification)
            (VCStatus.Unsupported, None, None)
        }

        val figures =
          uB.map(e => s"${analyzer.name}: ${round(e, java.math.RoundingMode.CEILING)}").toSeq ++
            lB.map(l => s"${fuzzer.name}: ${round(l, java.math.RoundingMode.FLOOR)}")

        val solver = if (figures.isEmpty) analyzer.name else figures.mkString(", ")
        VCResult(vcStatus, Some(solver), Some(upperBoundTime), None)

      case _ => super.checkVC(vc, origVC, sf)
    }

  /** Bounds every roundoff obligation before the checks start, because the witnesses and the
    * fuzzer need the results of all of them.
    */
  override def verify(vcs: Seq[VC], stopWhen: VCResult => Boolean)
    : scala.concurrent.Future[Map[VC, VCResult]] = {
    val obligations: Seq[(Identifier, Option[String])] = vcs.flatMap { vc =>
      vc.kind match {
        case VCKind.RoundoffError(_, field) => Some(vc.fid -> field)
        case _ => None
      }
    }

    if (obligations.nonEmpty) {
      obligations.foreach { case (fid, field) =>
        if (!interruptManager.isInterrupted) upperBound(fid, field)
      }
      settings.witnessFile.foreach(writeWitnesses)
      fuzzing.run()
    }

    super.verify(vcs, stopWhen)
      .andThen { case _ => ibex.free() }(using stainless.executionContext(using context))
  }

  private lazy val settings: RoundoffSettings = RoundoffSettings.from(context)

  private lazy val analyzer: RoundingAnalyzer = settings.analyzer match {
    case AnalyzerChoice.Daisy => new DaisyRunner(context, settings)
    case AnalyzerChoice.FPTaylor => new FPTaylorRunner(context, settings)
  }

  private lazy val fuzzer = new FuzzRunner(context, settings)

  private lazy val ibex = new IbexRunner(context, settings,
    recordWitnesses = settings.witnessFile.isDefined || settings.fuzzingEnabled)

  private lazy val oracles: BranchOracleFactory =
    new SolverBranchOracles(context, settings,
      () => getFactory(options + optCheckModels(false) + optSilentErrors(true)),
      phases)

  private lazy val fuzzing = new FuzzDriver(context, settings, fuzzer, annotatedFunctions,
    fd => decompositionOf(fd.id, None), () => ibex.witnesses, phases)

  private lazy val phases: inox.utils.TimerStorage = timers.verification.roundoff

  /** The `@roundoff` functions, in the order they were declared. */
  private lazy val annotatedFunctions: Seq[FunDef] =
    program.symbols.functions.values.toSeq
      .filter(_.flags.exists { case Roundoff(_) => true; case _ => false })
      .sortBy(_.id.globalId)

  // Stage 1: decompose every @roundoff function.

  /** One function's decomposition, one entry per number in its result, and how many
    * milliseconds reading it took.
    */
  private case class Decomposed(millis: Long,
                                fields: Either[String, Seq[(AccessPath, RoundoffErrorDecomposition)]])

  private lazy val decomposed: Map[Identifier, Decomposed] = {
    logSettings()
    annotatedFunctions.map { fd =>
      val start = System.nanoTime()
      val fields = RoundoffErrorDecomposition.of(fd, settings, oracles, phases,
                                                 analyzer.emitter)(using program.symbols)
      fd.id -> Decomposed((System.nanoTime() - start) / 1000000, fields)
    }.toMap
  }

  /** One field's decomposition, by the label the obligation was raised under. */
  private def decompositionOf(fid: Identifier, field: Option[String])
    : Either[String, RoundoffErrorDecomposition] =
    decomposed.get(fid).map(_.fields).getOrElse(Left("this function was not analyzed"))
      .flatMap { fields =>
        fields.find { case (path, _) => field.forall(_ == path.displayName) }
          .map { case (_, parts) => parts }
          .toRight(s"nothing in the result of this function is called '${field.getOrElse("")}'")
      }

  // Stage 2: every analyzer query of every function, in one batch, so the analyzer starts once.

  private lazy val analyzerResults: Map[String, Either[String, BigDecimal]] = {
    val queries = decomposed.values.map(_.fields)
      .collect { case Right(fields) => fields.flatMap { case (_, parts) => parts.queries } }
      .flatten.toSeq
      .distinctBy(_.name)

    if (queries.isEmpty) Map.empty else phases.rounding.run(analyzer.analyze(queries))
  }

  // Stage 3: the bound of each obligation, computed once and timed.

  private val upperBounds = scala.collection.mutable.Map
    .empty[(Identifier, Option[String]), (Long, scala.util.Try[Either[String, BigDecimal]])]

  private def upperBound(fid: Identifier, field: Option[String])
    : (Long, scala.util.Try[Either[String, BigDecimal]]) =
    synchronized {
      upperBounds.getOrElseUpdate((fid, field),
        timers.verification.runAndGetTime(computeUpperBound(fid, field)))
    }

  /** The worst rounding of a leaf, plus the worst divergence between two leaves. */
  private def computeUpperBound(fid: Identifier, field: Option[String])
    : Either[String, BigDecimal] =
    for {
      parts <- decompositionOf(fid, field)
      name = displayName(fid, field)
      // A guard can only be read the wrong way where its two sides are within the sum of
      // their errors.
      guardErrors <- traverse(parts.guardOperandErrors) { case (lhs, rhs) =>
        for (l <- errorBound(lhs); r <- errorBound(rhs)) yield l + r
      }
      rounding <- traverse(parts.reachableLeaves)(errorBound)
      divergences <- divergenceBounds(fid, name, parts, guardErrors)
    } yield {
      val worstDivergence = (BigDecimal(0) +: divergences).max
      val worstRounding = rounding.max

      logFunction(name, parts, divergences, worstDivergence, worstRounding)
      // Added under our own rounding: the default one may round a long sum towards zero, and
      // a bound rounded towards zero is no longer a bound.
      new BigDecimal(worstDivergence.bigDecimal, reportedPrecision) + worstRounding
    }

  /** The largest divergence Ibex found in each guard region. */
  private def divergenceBounds(fid: Identifier, name: String, parts: RoundoffErrorDecomposition,
                               guardErrors: Seq[BigDecimal]): Either[String, Seq[BigDecimal]] = {
    // What is left of the function's budget, divided equally among the numbers in its result:
    // they are separate obligations, and none knows what the others will need.
    val remaining = budgetLeft(fid) / fieldCount(fid).max(1)

    ibex.within(remaining, parts.pairCount) {
      traverse(parts.regions)(ibex.regionBound(name, _, parts.guardDifferences, guardErrors))
    }
  }

  /** The error of one leaf, or of one side of one guard. */
  private def errorBound(source: RoundingError): Either[String, BigDecimal] = source match {
    case RoundingError.Exact => Right(BigDecimal(0))
    // Only reachable leaves are asked about, so reaching this is a bug, not an error of zero.
    case RoundingError.Unreachable =>
      Left("the error of a leaf no run reaches was asked for")
    case RoundingError.Computed(error) => Right(error)
    case RoundingError.FromAnalyzer(query) =>
      analyzerResults
        .getOrElse(query.name, Left(s"${analyzer.name} reported no result for '${query.name}'"))
  }

  /** How many numbers the function's result holds. */
  private def fieldCount(fid: Identifier): Int =
    decomposed.get(fid).flatMap(_.fields.toOption).map(_.size).getOrElse(1)

  /** What is left of a function's budget once the time spent reading it is taken off. */
  private def budgetLeft(fid: Identifier): Double = {
    val spent = decomposed.get(fid).map(_.millis).getOrElse(0L) / 1000.0
    val left = settings.budget - spent
    if (left <= 0)
      reporter.warning(getFunction(fid).getPos,
        s"Reading ${getFunction(fid).id.asString} took ${spent}s of a ${settings.budget}s " +
        "budget, so its divergences are bounded on whatever is left of it; " +
        "--roundoff-timeout raises it")
    left
  }

  // Stage 4: the regions Ibex found, for people and for the fuzzer.

  private def writeWitnesses(file: java.io.File): Unit =
    scala.util.Try(phases.witnesses.run {
      val parameters = (name: String) => parameterNames.getOrElse(name, Seq.empty)
      stainless.utils.JsonUtils.writeFile(file, Witness.report(ibex.witnesses, parameters))
      fuzzing.writeInputs(file)
    }).failed.foreach(e =>
      reporter.warning(s"Could not write the divergences to $file: ${e.getMessage}"))

  /** What each function calls its inputs, in the order it declares them. */
  private lazy val parameterNames: Map[String, Seq[String]] =
    annotatedFunctions.map { fd =>
      fd.id.name -> decompositionOf(fd.id, None).toOption
        .map(_.flattening.parameters).getOrElse(fd.params).map(_.id.name)
    }.toMap

  // Reporting.

  private def checkBound(fd: FunDef, named: String, upperBound: BigDecimal,
                         maxUpperBound: Option[BigDecimal]): VCStatus =
    maxUpperBound match {
      case None => VCStatus.Valid
      case Some(max) if upperBound <= max => VCStatus.Valid
      case Some(max) =>
        reporter.warning(fd.getPos,
          s"Roundoff error for $named is $upperBound, which exceeds the bound $max")
        VCStatus.Invalid(VCStatus.Unsatisfiable)
    }

  private def compare(fd: FunDef, upperBound: BigDecimal, lowerBound: BigDecimal): Unit = {
    reporter.info(fd.getPos,
      s"Fuzzing ${fd.id.asString} made an error of $lowerBound, so the true worst case " +
        s"lies in [$lowerBound, $upperBound]")

    if (lowerBound > upperBound)
      reporter.warning(fd.getPos,
        s"The fuzzer made an error of $lowerBound on ${fd.id.asString}, which is above the " +
          s"inferred bound $upperBound: the bound is unsound, or the program the fuzzer ran " +
          "is not the one that was analyzed")
  }

  /** Display name of a given part of a VC */
  private def displayName(fid: Identifier, field: Option[String]): String =
    field.filter(_.nonEmpty)
      .map(f => s"${getFunction(fid).id.name}.$f").getOrElse(getFunction(fid).id.name)

  private def round(e: BigDecimal, towards: java.math.RoundingMode): String =
    e.round(new java.math.MathContext(4, towards)).toString

  private def logSettings(): Unit =
    reporter.debug(
      s"Roundoff settings: ${settings.describe}, " +
      s"solvers ${context.options.findOptionOrDefault(inox.optSelectedSolvers).mkString(",")}"
    )(using DebugSectionRoundoff)

  private def logFunction(name: String, parts: RoundoffErrorDecomposition,
                          divergences: Seq[BigDecimal],
                          worstDivergence: BigDecimal, worstRounding: BigDecimal): Unit = {
    val shape = parts.shape
    val found = divergences.count(_ > 0)

    reporter.debug(
      s"Roundoff shape of $name: ${counted(shape.guards, "guard")} over " +
      s"${counted(shape.paths, "path")}, nested ${shape.depth} deep, " +
      s"${counted(shape.distinct, "leaf", "leaves")} computing something different, " +
      s"${counted(parts.leaves.size - parts.reachableLeaves.size, "path")} that no input reaches"
    )(using DebugSectionRoundoff)

    reporter.debug(
      s"Roundoff plan of $name: " +
      s"${counted(parts.regions.size, "region")} holding " +
      s"${counted(parts.pairCount, "comparison")}, " +
      s"$found of which ${if (found == 1) "holds" else "hold"} a divergence; " +
      s"${counted(parts.queries.map(_.name).distinct.size, "analyzer query", "analyzer queries")}"
    )(using DebugSectionRoundoff)

    reporter.debug(
      s"Roundoff for $name: " +
      s"worst discontinuity $worstDivergence, worst rounding $worstRounding"
    )(using DebugSectionVerification)
  }
}
