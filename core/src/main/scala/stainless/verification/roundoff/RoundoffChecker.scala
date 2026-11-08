/* Copyright 2009-2021 EPFL, Lausanne */

package stainless.verification.roundoff

import inox.solvers.*
import io.circe.Json
import stainless.verification.{DebugSectionVerification, VCKind, VCStatus, VerificationChecker}
import stainless.{Identifier, StainlessProgram}

/** Discharges `@roundoff` obligations by bounding the error of the annotated function. */
trait RoundoffChecker extends VerificationChecker {
  self =>
  val program: StainlessProgram

  import context.{*, given}
  import program.*
  import program.symbols.{*, given}
  import program.trees.*

  private lazy val settings: RoundoffSettings = RoundoffSettings.from(context)

  private lazy val analyzer: RoundingAnalyzer = settings.analyzer match {
    case AnalyzerChoice.Daisy => new DaisyRunner(context, settings)
    case AnalyzerChoice.FPTaylor => new FPTaylorRunner(context, settings)
  }

  private lazy val fuzzer = new FuzzRunner(context, settings)

  private lazy val ibex = new IbexRunner(context, settings,
    recordWitnesses = settings.witnessFile.isDefined || settings.fuzzingEnabled)

  // A variant can hold no input reaching one number of the result and reach another, so the
  // variants are gathered over every number.
  private lazy val fuzzDriver = new FuzzDriver(context, settings, fuzzer, roundoffFunctions,
    fd => decomposedFunctions.get(fd.id).map(_.decompositionsByField).getOrElse(Left("this function was not analyzed"))
      .map(_.flatMap { case (_, variants) => variants }.distinctBy(_.variant.description))
      .filterOrElse(_.nonEmpty, "no input reaches any number of its result"),
    () => ibex.witnesses, roundoffTimers)

  private lazy val roundoffTimers: inox.utils.TimerStorage = timers.verification.roundoff

  /** The `@roundoff` functions, in the order they were declared. */
  private lazy val roundoffFunctions: Seq[FunDef] =
    program.symbols.functions.values.toSeq
      .filter(_.flags.exists { case Roundoff(_) => true; case _ => false })
      .sortBy(_.id.globalId)


  override def checkVC(vc: VC, origVC: VC,
                       sf: SolverFactory { val program: self.program.type }): VCResult =
    vc.kind match {
      case VCKind.RoundoffError(_, _) | VCKind.RoundoffCases if settings.timeout.isEmpty =>
        reporter.warning(getFunction(vc.fid).getPos,
          s"Cannot analyse the roundoff of ${vc.fid.name}: timeout missing")
        VCResult(VCStatus.Unsupported, None, None, None)
      case VCKind.RoundoffError(maxUpperBound, field) => reportErrorUpperAndLowerBounds(vc.fid, field, maxUpperBound)
      case VCKind.RoundoffCases => reportCaseAgreement(vc.fid)
      // Bitwuzla first, then cvc5 when Bitwuzla gives no answer.
      case VCKind.RoundoffFinite(_) =>
        val bitwuzla = super.checkVC(vc, origVC, factoryFor("smt-bitwuzla"))
        if (bitwuzla.status != VCStatus.Unknown && bitwuzla.status != VCStatus.Timeout) bitwuzla
        else {
          val cvc5 = super.checkVC(vc, origVC, factoryFor("smt-cvc5"))
          cvc5.copy(time = bitwuzla.time.zip(cvc5.time).map(_ + _).orElse(cvc5.time))
        }
      case _ => super.checkVC(vc, origVC, sf)
    }

  private def factoryFor(solver: String): TimeoutSolverFactory =
    getFactory(options + inox.optSelectedSolvers(Set(solver)))

  private def isFinitenessObligation(vc: VC): Boolean = vc.kind match {
    case VCKind.RoundoffFinite(_) => true
    case _ => false
  }

  private def isRoundoffObligation(vc: VC): Boolean = vc.kind match {
    case VCKind.RoundoffError(_, _) | VCKind.RoundoffCases | VCKind.RoundoffFinite(_) => true
    case _ => false
  }

  override def verify(vcs: Seq[VC], stopWhen: VCResult => Boolean)
    : scala.concurrent.Future[Map[VC, VCResult]] = {
    val obligations: Seq[(Identifier, Option[String])] = vcs.flatMap { vc =>
      vc.kind match {
        case VCKind.RoundoffError(_, field) => Some(vc.fid -> field)
        case VCKind.RoundoffCases => Some(vc.fid -> Some(RoundoffErrorDecomposition.caseVCLabel))
        case _ => None
      }
    }

    if (obligations.nonEmpty && settings.timeout.isDefined) {
      obligations.foreach { case (fid, field) =>
        if (!interruptManager.isInterrupted) upperBound(fid, field)
      }
      settings.witnessFile.foreach(writeDivergenceWitnesses)
      fuzzDriver.run()
    }

    // With `--roundoff-only`, the other obligations are neither checked nor reported, and
    // neither are the finiteness ones with `--roundoff-finiteness=false`.
    val checked = vcs.filter(vc => !settings.roundoffOnly || isRoundoffObligation(vc))
      .filter(vc => settings.finiteness || !isFinitenessObligation(vc))
    val witnessFile = settings.witnessFile
      .filter(file => obligations.nonEmpty && settings.timeout.isDefined && fuzzDriver.sourcesReplacedBy(file).isEmpty)
    super.verify(checked, stopWhen)
      .andThen { case verified =>
        ibex.free()
        // Written again, now that every obligation has its result.
        witnessFile.zip(verified.toOption).foreach { case (file, results) =>
          scala.util.Try(writeWitnessFile(file, obligationRecords(results))).failed.foreach(e =>
            reporter.warning(s"Could not write the results to $file: ${e.getMessage}"))
        }
      }(using stainless.executionContext(using context))
  }

  /** Writes the witnesses, and the fuzzer's inputs beside them, before any obligation is
    * checked: the fuzzer needs them to give its lower bounds.
    */
  private def writeDivergenceWitnesses(file: java.io.File): Unit =
    fuzzDriver.sourcesReplacedBy(file) match {
      case Seq() =>
        scala.util.Try(roundoffTimers.witnesses.run {
          writeWitnessFile(file, Seq.empty)
          fuzzDriver.writeFuzzerInputs(file)
        }).failed.foreach(e =>
          reporter.warning(s"Could not write the divergences to $file: ${e.getMessage}"))
      case replaced =>
        reporter.warning(s"Did not write the divergences to $file: that would replace " +
          s"${replaced.mkString(" and ")}, which the program was read from")
    }

  /** The witness file: what each obligation came to, then every witness Ibex recorded. */
  private def writeWitnessFile(file: java.io.File, obligations: Seq[Json]): Unit = {
    val parameters = (name: String) => parameterNames.getOrElse(name, Seq.empty)
    stainless.utils.JsonUtils.writeFile(file, Json.obj(
      "obligations" -> Json.arr(obligations*),
      "witnesses" -> Witness.toJson(ibex.witnesses, parameters)))
  }

  /** What bounding each obligation found besides its status, by function, kind of obligation
    * and number of the result, as fields of its record in the witness file.
    */
  private val obligationDetails =
    scala.collection.concurrent.TrieMap.empty[(Identifier, String, Option[String]), Seq[(String, Json)]]

  private def recordDetails(fid: Identifier, obligation: String, field: Option[String],
                            details: (String, Option[Json])*): Unit =
    obligationDetails.update((fid, obligation, field), details.collect { case (key, Some(value)) => key -> value })

  /** What each roundoff obligation came to, for the witness file: where it is, its status, time
    * and solver column as in the summary, then what bounding it found, with every digit.
    */
  private def obligationRecords(results: Map[VC, VCResult]): Seq[Json] =
    results.toSeq.flatMap { case (vc, result) =>
      val obligationAndField = vc.kind match {
        case VCKind.RoundoffError(_, field) => Some(("error", field))
        case VCKind.RoundoffCases => Some(("case agreement", None))
        case VCKind.RoundoffFinite(field) => Some(("finiteness", field))
        case _ => None
      }
      obligationAndField.map { case (obligation, field) =>
        val fd = getFunction(vc.fid)
        val (file, line) = fd.getPos match {
          case pos: inox.utils.DefinedPosition => (pos.file.getPath, pos.line)
          case _ => ("", 0)
        }
        val where = Seq(
          "function" -> Json.fromString(fd.id.name), "file" -> Json.fromString(file),
          "line" -> Json.fromInt(line), "obligation" -> Json.fromString(obligation),
          "field" -> field.map(Json.fromString).getOrElse(Json.Null))
        val outcome = Seq(
          "status" -> Json.fromString(result.status.name),
          "seconds" -> result.time.map(ms => Json.fromDoubleOrNull(ms / 1000.0)).getOrElse(Json.Null),
          "solver" -> result.solverName.map(Json.fromString).getOrElse(Json.Null))
        val details = obligationDetails.getOrElse((vc.fid, obligation, field), Seq.empty)
        ((file, line, fd.id.name, obligation, field.getOrElse("")), Json.obj(where ++ outcome ++ details*))
      }
    }.sortBy(_._1).map(_._2)

  /** What each function calls its inputs, in the order it declares them. */
  private lazy val parameterNames: Map[String, Seq[String]] =
    roundoffFunctions.flatMap { fd =>
      decompositionOf(fd.id, None) match {
        case Right(variants) => variants.map(parts =>
          displayName(fd.id, None, parts) -> parts.flattening.parameters.map(_.id.name))
        case Left(_) => Seq(fd.id.name -> fd.params.map(_.id.name))
      }
    }.toMap


  /** What reading one function gave: for each number of its result, by label, one
    * decomposition per input variant, or why it could not be read; and how long reading took.
    */
  private case class FunctionRoundoffErrorDecomposition(
    readingSeconds: Double,
    decompositionsByField: Either[String, Seq[(String, Seq[RoundoffErrorDecomposition])]]
  )

  private lazy val decomposedFunctions: Map[Identifier, FunctionRoundoffErrorDecomposition] = {
    roundoffFunctions.map { fd =>
      val start = System.nanoTime()
      val limit = settings.timeout.map(new TimeLimit(_)).getOrElse(TimeLimit.never)
      val decompositionsByField =
        try new QueryBuilder(settings, roundoffTimers, analyzer.emitter, limit).buildQueries(fd)
        catch { case outOfTime: OutOfTime => Left(outOfTime.getMessage) }
      fd.id -> FunctionRoundoffErrorDecomposition((System.nanoTime() - start) / 1e9, decompositionsByField)
    }.toMap
  }

  /** The decompositions of one number of a function's result, one per input variant: the one
    * labelled `field`, or the first for `None`.
    */
  private def decompositionOf(fid: Identifier, field: Option[String])
    : Either[String, Seq[RoundoffErrorDecomposition]] =
    decomposedFunctions.get(fid).map(_.decompositionsByField).getOrElse(Left("this function was not analyzed"))
      .flatMap { decompositionsByField =>
        decompositionsByField.find { case (label, _) => field.forall(_ == label) }
          .map { case (_, parts) => parts }
          .toRight(s"nothing in the result of this function is called '${field.getOrElse("")}'")
      }


  /** What bounding one number of a result gives: a bound, why the error may be infinite or
    * NaN, or that no input reaches it.
    */
  private sealed trait StaticAnalysisOutcome {
    def variant: String
  }

  /** The rounding error of the leaves, plus the divergence across the guards when there are
    * any (`guarded`).
    */
  private case class ErrorBound(rounding: BigDecimal, divergence: BigDecimal, guarded: Boolean,
                                variant: String) extends StaticAnalysisOutcome {
    def total: BigDecimal = new BigDecimal(divergence.bigDecimal, reportedPrecision) + rounding
  }

  /** The error may be infinite or NaN (`mayBe`), for `reason`. */
  private case class Unbounded(mayBe: String, reason: String, variant: String)
    extends StaticAnalysisOutcome

  /** No input reaches a path holding the number, so it has no error. */
  private case object Unreachable extends StaticAnalysisOutcome {
    def variant: String = ""
  }

  private val upperBoundCache = scala.collection.mutable.Map
    .empty[(Identifier, Option[String]), (Long, scala.util.Try[Either[String, StaticAnalysisOutcome]])]

  /** The outcome of one obligation, and how many milliseconds it took, computed once. */
  private def upperBound(fid: Identifier, field: Option[String])
    : (Long, scala.util.Try[Either[String, StaticAnalysisOutcome]]) =
    synchronized {
      upperBoundCache.getOrElseUpdate((fid, field),
        timers.verification.runAndGetTime(computeUpperBound(fid, field)))
    }

  /** The worst outcome over the input variants: an [[Unbounded]] one if there is one,
    * otherwise the largest bound. The variants share the obligation's time.
    */
  private def computeUpperBound(fid: Identifier, field: Option[String])
    : Either[String, StaticAnalysisOutcome] =
      val time = new TimeLimit(secondsLeftAfterReading(fid))
      decompositionOf(fid, field).flatMap {
        case Seq() => Right(Unreachable)
        case variants =>
          traverse(variants.zipWithIndex) { case (parts, i) =>
            outcomeOf(fid, field, parts, time.secondsLeft / (variants.size - i))
          }.map { outcomes =>
            outcomes.collectFirst { case unbounded: Unbounded => unbounded }
              .getOrElse(outcomes.collect { case bound: ErrorBound => bound }.maxBy(_.total))
          }
      }

  /** The seconds one obligation may take for its analyzer run and its divergence queries:
    * `--timeout` less the time reading its function took. Every number of a result is an
    * obligation of its own, so each gets that time, and each is charged the reading it needed.
    */
  private def secondsLeftAfterReading(fid: Identifier): Double = {
    val timeout = settings.timeout.get
    val reading = decomposedFunctions.get(fid).map(_.readingSeconds).getOrElse(0.0)
    val seconds = timeout - reading
    if (seconds <= 0)
      throw new OutOfTime(
        f"reading ${getFunction(fid).id.asString} took $reading%.2fs of the ${timeout}s budget")
    seconds
  }

  /** The outcome of one variant: [[Unbounded]] when a path some input reaches returns NaN or
    * an infinity, otherwise [[finiteBoundOutcomeOf]].
    */
  private def outcomeOf(fid: Identifier, field: Option[String],
                        parts: RoundoffErrorDecomposition, seconds: Double)
    : Either[String, StaticAnalysisOutcome] =
    Seq((RoundingError.NotANumber, "NaN", "NaN"),
        (RoundingError.Infinite, "infinite", "an infinity"))
      .collectFirst { case (leaf, mayBe, value) if parts.reachableLeaves.contains(leaf) =>
        Unbounded(mayBe, s"a path returns $value, and the input ranges do not rule it out",
                  parts.variant.description)
      }
      .map(Right(_)).getOrElse(finiteBoundOutcomeOf(fid, field, parts, seconds))

  /** The bound of one variant: the largest rounding error of its leaves, from the analyzer,
    * plus the largest divergence across its guards, from Ibex, within `seconds` for both.
    */
  private def finiteBoundOutcomeOf(fid: Identifier, field: Option[String],
                                   parts: RoundoffErrorDecomposition, seconds: Double)
    : Either[String, StaticAnalysisOutcome] = {
    val obligationName = displayName(fid, field, parts)
    val (analyzerSeconds, roundingErrors) = roundingErrorsOf(parts, seconds)

    def guardError(lhs: RoundingError, rhs: RoundingError): Either[String, Option[BigDecimal]] =
      (errorOf(lhs, roundingErrors), errorOf(rhs, roundingErrors)) match {
        case (Left(why), _) => Left(why)
        case (_, Left(why)) => Left(why)
        case (Right(l), Right(r)) => Right(l.zip(r).map(_ + _))
      }

    val guardErrors = traverse(parts.guardOperandErrors) { case (lhs, rhs) => guardError(lhs, rhs) }
    val leafErrors = traverse(parts.reachableLeaves)(errorOf(_, roundingErrors))

    (guardErrors, leafErrors) match {
      case (Left(why), _) => Left(why)
      case (_, Left(why)) => Left(why)
      // Only a leaf that may overflow makes the error unbounded: a guard side that may
      // overflow only makes Ibex search the whole region.
      case (Right(_), Right(rounding)) if rounding.contains(None) =>
        Right(Unbounded("infinite",
          s"${analyzer.name} found that a value in a leaf may overflow on the leaf's input " +
          "ranges, and it cannot follow a value past an overflow", parts.variant.description))
      case (Right(guardErrors), Right(rounding)) =>
        val search = new DivergenceSearch(ibex, settings, obligationName, parts, guardErrors)
        search.largestDivergencePerGuard(seconds - analyzerSeconds).map { divergences =>
          val worstDivergence = (BigDecimal(0) +: divergences).max
          val worstRounding = rounding.flatten.max

          ErrorBound(worstRounding, worstDivergence, guarded = parts.regions.nonEmpty,
                     parts.variant.description)
        }
    }
  }

  /** The analyzer's result for every leaf and guard side of one variant, by query name, from
    * one run stopped after `seconds`, and how many seconds that run took.
    */
  private def roundingErrorsOf(parts: RoundoffErrorDecomposition, seconds: Double)
    : (Double, Map[String, Either[AnalyzerFailure, BigDecimal]]) = {
    val queries = parts.queries.distinctBy(_.name)
    val start = System.nanoTime()
    val results =
      if (queries.isEmpty) Map.empty else roundoffTimers.rounding.run(analyzer.analyze(queries, seconds))
    ((System.nanoTime() - start) / 1e9, results)
  }

  /** The error of one leaf or guard side, or `None` when it may be infinite. */
  private def errorOf(source: RoundingError, roundingErrors: Map[String, Either[AnalyzerFailure, BigDecimal]])
    : Either[String, Option[BigDecimal]] = source match {
    case RoundingError.Exact => Right(Some(BigDecimal(0)))
    case RoundingError.Unreachable | RoundingError.NotANumber | RoundingError.Infinite =>
      Left(s"the error of a leaf that is $source was asked for")
    case RoundingError.Computed(error) => Right(Some(error))
    case RoundingError.FromAnalyzer(query) =>
      roundingErrors.get(query.name) match {
        case Some(Right(error)) => Right(Some(error))
        case Some(Left(AnalyzerFailure.MayOverflow(_))) => Right(None)
        case Some(Left(AnalyzerFailure.Failed(why))) => Left(why)
        case None => Left(s"${analyzer.name} reported no result for '${query.name}'")
      }
  }

  // Reporting.

  /** The result of the obligation on the error of one number: the upper bound, against
    * `maxUpperBound` when the program states one, and the fuzzer's lower bound, if it ran.
    */
  private def reportErrorUpperAndLowerBounds(fid: Identifier, field: Option[String],
                         maxUpperBound: Option[BigDecimal]): VCResult = {
    val fd: FunDef = getFunction(fid)
    val obligationName = displayName(fid, field)
    val (upperBoundTime, upperBoundResult) = upperBound(fid, field)
    val lowerBoundResult = fuzzDriver.lowerBound(fd, field)
    val lower = lowerBoundResult.flatMap(_.toOption)

    // The status, the bound if there is one, and why there is none otherwise.
    val (vcStatus, upper, whyNoBound) = upperBoundResult match {
      case scala.util.Success(Right(bound: ErrorBound)) =>
        val worstVariant = if (bound.variant.isEmpty) "" else s", largest with ${bound.variant}"
        reporter.info(fd.getPos,
          s"Inferred a roundoff error of ${bound.total} for $obligationName$worstVariant")
        lower.foreach(reportFuzzedRange(fd, obligationName, bound.total, _))
        (statusAgainstMaxBound(fd, obligationName, bound.total, maxUpperBound), Some(bound), None)

      case scala.util.Success(Right(Unbounded(mayBe, reason, variant))) =>
        val inVariant = if (variant.isEmpty) "" else s" with $variant"
        reporter.warning(fd.getPos,
          s"The roundoff error of $obligationName$inVariant may be $mayBe: $reason")
        (VCStatus.Unknown, None, Some(s"may be $mayBe$inVariant: $reason"))

      case scala.util.Success(Right(Unreachable)) =>
        reporter.info(fd.getPos, s"No roundoff error possible for $obligationName")
        (VCStatus.Valid, None, Some("no input reaches a path holding it"))

      case scala.util.Success(Left(why)) =>
        reporter.warning(fd.getPos, s"Cannot bound the roundoff error of $obligationName: $why")
        (VCStatus.Unsupported, None, Some(why))

      case scala.util.Failure(outOfTime: OutOfTime) =>
        reporter.warning(fd.getPos, s"Roundoff analysis of $obligationName ran out of time: " +
          s"${outOfTime.getMessage}; --timeout raises it")
        (VCStatus.Timeout, None, Some(s"ran out of time: ${outOfTime.getMessage}"))

      case scala.util.Failure(thrown) =>
        reporter.warning(fd.getPos, s"Roundoff analysis of $obligationName failed: ${thrown.getMessage}")
        reporter.debug(thrown.getStackTrace.take(12).mkString("\n"))(
          using DebugSectionVerification)
        (VCStatus.Unsupported, None, Some(s"failed: ${thrown.getMessage}"))
    }

    recordDetails(fid, "error", field,
      "bound" -> upper.map(b => Json.fromBigDecimal(b.total)),
      "rounding" -> upper.map(b => Json.fromBigDecimal(b.rounding)),
      "divergence" -> upper.filter(_.guarded).map(b => Json.fromBigDecimal(b.divergence)),
      "largestWith" -> upper.map(_.variant).filter(_.nonEmpty).map(Json.fromString),
      "limit" -> maxUpperBound.map(Json.fromBigDecimal),
      "reason" -> whyNoBound.map(Json.fromString),
      "fuzzed" -> lower.map(Json.fromBigDecimal),
      "fuzzerReason" -> lowerBoundResult.flatMap(_.left.toOption).map(Json.fromString))

    // Shown in the solver column of the summary, such as `daisy: 1.2E-15 + ibex: 0.5`.
    val boundFigures =
      upper.map { b =>
        s"${analyzer.name}: ${round(b.rounding, java.math.RoundingMode.CEILING)}" +
          (if (b.guarded) s" + ibex: ${round(b.divergence, java.math.RoundingMode.CEILING)}" else "")
      }.toSeq ++
        lower.map(l => s"${fuzzer.name}: ${round(l, java.math.RoundingMode.FLOOR)}")

    val solverColumn = if (boundFigures.isEmpty) analyzer.name else boundFigures.mkString(", ")
    VCResult(vcStatus, Some(solverColumn), Some(upperBoundTime), None)
  }

  /** Valid unless the program states a bound and `upperBound` is above it. */
  private def statusAgainstMaxBound(fd: FunDef, obligationName: String, upperBound: BigDecimal,
                                    maxUpperBound: Option[BigDecimal]): VCStatus =
    maxUpperBound match {
      case None => VCStatus.Valid
      case Some(max) if upperBound <= max => VCStatus.Valid
      case Some(max) =>
        reporter.warning(fd.getPos,
          s"Roundoff error for $obligationName is $upperBound, which exceeds the bound $max")
        VCStatus.Invalid(VCStatus.Unsatisfiable)
    }

  /** Reports the range the worst-case error lies in, and warns when the fuzzer found an error
    * above the upper bound.
    */
  private def reportFuzzedRange(fd: FunDef, obligationName: String, upperBound: BigDecimal,
                                lowerBound: BigDecimal): Unit = {
    reporter.info(fd.getPos,
      s"Fuzzing $obligationName made an error of $lowerBound, so the true worst case " +
        s"lies in [$lowerBound, $upperBound]")

    if (lowerBound > upperBound)
      reporter.warning(fd.getPos,
        s"The fuzzer made an error of $lowerBound on $obligationName, which is above the " +
          s"inferred bound $upperBound: the bound is unsound, or the program the fuzzer ran " +
          "is not the one that was analyzed")
  }

  /** The result of the obligation that both runs end in the same case: valid when no
    * divergence between leaves of different cases is possible.
    */
  private def reportCaseAgreement(fid: Identifier): VCResult = {
    val fd: FunDef = getFunction(fid)
    val (time, result) = upperBound(fid, Some(RoundoffErrorDecomposition.caseVCLabel))
    val runs = s"the floating-point and the real-valued run of ${fid.name}"

    // The status, and why it is not valid.
    val (status, whyNotValid) = result match {
      case scala.util.Success(Right(bound: ErrorBound)) if bound.total == 0 =>
        reporter.info(fd.getPos, s"${runs.capitalize} end in the same case on every input")
        (VCStatus.Valid, None)

      case scala.util.Success(Right(Unreachable)) =>
        reporter.info(fd.getPos, s"${runs.capitalize} end in the same case: no input reaches any path")
        (VCStatus.Valid, None)

      case scala.util.Success(Right(_)) =>
        reporter.warning(fd.getPos,
          s"${runs.capitalize} may end in different cases: no Ibex query ruled it out ")
        (VCStatus.Unknown, Some("no Ibex query ruled out that the runs end in different cases"))

      case scala.util.Success(Left(why)) =>
        reporter.warning(fd.getPos, s"Cannot tell whether $runs end in the same case: $why")
        (VCStatus.Unsupported, Some(why))

      case scala.util.Failure(outOfTime: OutOfTime) =>
        reporter.warning(fd.getPos, s"Telling whether $runs end in the same case ran out " +
          s"of time: ${outOfTime.getMessage}; --timeout raises it")
        (VCStatus.Timeout, Some(s"ran out of time: ${outOfTime.getMessage}"))

      case scala.util.Failure(thrown) =>
        reporter.warning(fd.getPos,
          s"Telling whether $runs end in the same case failed: ${thrown.getMessage}")
        (VCStatus.Unsupported, Some(s"failed: ${thrown.getMessage}"))
    }

    val fuzzed = fuzzDriver.caseDivergences(fd)
    recordDetails(fid, "case agreement", None,
      "reason" -> whyNotValid.map(Json.fromString),
      "fuzzedCaseDivergences" -> fuzzed.map(divergences => Json.arr(divergences.map { divergence =>
        Json.obj(
          "cases" -> Json.arr(divergence.cases.map { case (path, floatingPoint, precise) =>
            Json.obj("path" -> Json.fromString(path), "floatingPoint" -> Json.fromString(floatingPoint),
                     "precise" -> Json.fromString(precise))
          }*),
          "runs" -> Json.fromLong(divergence.runs),
          "example" -> Json.fromString(divergence.example))
      }*)))
    fuzzed.filter(_.nonEmpty).foreach(reportFuzzedCases(fd, status, _))
    val fuzzedRuns = fuzzed.map { divergences =>
      divergences.map(_.runs).sum match {
        case 0 => s"${fuzzer.name}: none differ"
        case runs => s"${fuzzer.name}: $runs runs differ"
      }
    }
    VCResult(status, Some(("ibex" +: fuzzedRuns.toSeq).mkString(", ")), Some(time), None)
  }

  /** Reports the runs in which the fuzzer saw the floating-point and the precise version end in
    * different cases. The precise version computes with 113 bits rather than exactly, so they
    * show that the cases really can differ, short of a proof. A `status` that rules it out is
    * then contradicted.
    */
  private def reportFuzzedCases(fd: FunDef, status: VCStatus, divergences: Seq[CaseDivergence]): Unit = {
    val described = divergences.map { divergence =>
      val returned = divergence.cases.map { case (where, floating, precise) =>
        val at = if (where.isEmpty) "" else s"$where: "
        s"$at$floating in floating point, $precise in the precise run"
      }.mkString(" and ")
      s"$returned (${divergence.runs} runs, such as at ${divergence.example})"
    }
    val found = s"the fuzzer saw ${divergences.map(_.runs).sum} runs of ${fd.id.asString} end in " +
      s"different cases: ${described.mkString("; ")}"

    if (status == VCStatus.Valid)
      reporter.warning(fd.getPos, s"${found.capitalize}, although the analysis found they always " +
        "end in the same case: the analysis is unsound, or the program the fuzzer ran is not " +
        "the one that was analyzed")
    else reporter.info(fd.getPos, found.capitalize)
  }

  /** The function's name, followed by the name of a part of its output. */
  private def displayName(fid: Identifier, field: Option[String]): String = {
    field match {
      case Some(f) if f.nonEmpty => s"${fid.name}.$f"
      case _ => fid.name
    }
  }

  /** [[displayName]], followed by the name of the input constructors. */
  private def displayName(fid: Identifier, field: Option[String], parts: RoundoffErrorDecomposition)
    : String =
    displayName(fid, field) + (if (parts.variant.description.isEmpty) "" else s" [${parts.variant.description}]")


}