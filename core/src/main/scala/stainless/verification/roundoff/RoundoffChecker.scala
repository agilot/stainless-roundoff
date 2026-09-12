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
      case VCKind.RoundoffError(limit, field) => obligations.answer(vc, limit, field)
      case _ => super.checkVC(vc, origVC, sf)
    }

  /** Reads every obligation before any of them is answered, since the fuzzer is handed what
    * all of them found, and shuts Ibex down once the last one has been answered.
    */
  override def verify(vcs: Seq[VC], stopWhen: VCResult => Boolean)
    : scala.concurrent.Future[Map[VC, VCResult]] = {
    obligations.readAll(vcs)
    super.verify(vcs, stopWhen)
      .andThen { case _ => ibex.free() }(using stainless.executionContext(using context))
  }

  /** Bounds the rounding of a straight-line computation, one batch of queries per run. */
  private lazy val analyzer: RoundingAnalyzer = new DaisyRunner(context)

  /** Looks for a divergence by running the program, which bounds the error from below. */
  private lazy val fuzzer = new FuzzRunner(context)

  /** Searches the regions where a guard may be read differently by the two computations. */
  private lazy val ibex =
    new IbexRunner(context, recordWitnesses = Settings.witnessFile.isDefined || fuzzer.enabled)

  private lazy val phases: inox.utils.TimerStorage = timers.verification.roundoff

  /** The `@roundoff` functions, in the order they were declared. */
  private lazy val annotated: Seq[FunDef] =
    program.symbols.functions.values.toSeq
      .filter(_.flags.exists { case Roundoff(_) => true; case _ => false })
      .sortBy(_.id.globalId)

  /** How an obligation reads: the function, and the field where a result holds several numbers. */
  private def label(fid: Identifier, field: Option[String]): String =
    field.filter(_.nonEmpty).fold(getFunction(fid).id.name)(f => s"${getFunction(fid).id.name}.$f")

  /** Reads each obligation, then answers it from its reading and from what the fuzzer found. */
  private object obligations {

    /** Reads every roundoff obligation, then hands what all of them found to the fuzzer. */
    def readAll(vcs: Seq[VC]): Unit = {
      val asked = vcs.flatMap { vc =>
        vc.kind match {
          case VCKind.RoundoffError(_, field) => Some(vc.fid -> field)
          case _ => None
        }
      }

      if (asked.nonEmpty) {
        // An interrupted run answers with what it has, since the obligations it has yet to
        // read are not going to be answered either.
        asked.foreach { case (fid, field) =>
          if (!interruptManager.isInterrupted) reading(fid, field)
        }


        Settings.witnessFile.foreach { file =>
          scala.util.Try(phases.witnesses.run(Fuzzing.writeFuzzerInputs(file))).failed.foreach(e =>
            reporter.warning(s"Could not write the divergences to $file: ${e.getMessage}"))
        }

        Fuzzing.run()
      }
    }

    /** Answers one obligation from its reading, and from what the fuzzer made of the function. */
    def answer(vc: VC, limit: Option[BigDecimal], field: Option[String]): VCResult = {
      val fd = getFunction(vc.fid)
      val named = label(vc.fid, field)
      val (time, found) = reading(vc.fid, field)
      val lowerBound = Fuzzing.lowerBound(fd)

      val (status, inferred, lower) = found match {
        case scala.util.Success(Right(error)) =>
          reporter.info(fd.getPos, s"Inferred a roundoff error of $error for $named")
          lowerBound.foreach(compare(fd, error, _))
          (verdict(fd, named, error, limit), Some(error), lowerBound)

        case scala.util.Success(Left(why)) =>
          reporter.warning(fd.getPos, s"Cannot bound the roundoff error of $named: $why")
          (VCStatus.Unsupported, None, lowerBound)

        case scala.util.Failure(thrown) =>
          reporter.warning(fd.getPos, s"Roundoff analysis of $named failed: ${thrown.getMessage}")
          reporter.debug(thrown.getStackTrace.take(12).mkString("\n"))(
            using DebugSectionVerification)
          (VCStatus.Unsupported, None, None)
      }

      // Both bounds are shown where there are both, on the line the summary gives to solvers.
      val figures =
        inferred.map(e => s"${analyzer.name}: ${round(e, java.math.RoundingMode.CEILING)}").toSeq ++
          lower.map(l => s"${fuzzer.name}: ${round(l, java.math.RoundingMode.FLOOR)}")

      val solver = if (figures.isEmpty) analyzer.name else figures.mkString(", ")
      VCResult(status, Some(solver), Some(time), None)
    }

    private val readings = scala.collection.mutable.Map
      .empty[(Identifier, Option[String]), (Long, scala.util.Try[Either[String, BigDecimal]])]

    /** What one obligation came to, and how long that took, worked out once. */
    private def reading(fid: Identifier, field: Option[String])
      : (Long, scala.util.Try[Either[String, BigDecimal]]) =
      synchronized {
        readings.getOrElseUpdate((fid, field),
          timers.verification.runAndGetTime(bound.of(fid, field)))
      }

    private def verdict(fd: FunDef, named: String, error: BigDecimal,
                        limit: Option[BigDecimal]): VCStatus =
      limit match {
        case None => VCStatus.Valid
        case Some(most) if error <= most => VCStatus.Valid
        case Some(most) =>
          reporter.warning(fd.getPos,
            s"Roundoff error for $named is $error, which exceeds the bound $most")
          VCStatus.Invalid(VCStatus.Unsatisfiable)
      }

    /** Says where the true worst case lies, and warns if the fuzzer beat the inferred bound. */
    private def compare(fd: FunDef, inferred: BigDecimal, observed: BigDecimal): Unit = {
      reporter.info(fd.getPos,
        s"Fuzzing ${fd.id.asString} made an error of $observed, so the true worst case " +
        s"lies in [$observed, $inferred]")

      if (observed > inferred)
        reporter.warning(fd.getPos,
          s"The fuzzer made an error of $observed on ${fd.id.asString}, which is above the " +
          s"inferred bound $inferred: the bound is unsound, or the program the fuzzer ran " +
          "is not the one that was analyzed")
    }

    private def round(e: BigDecimal, towards: java.math.RoundingMode): String =
      e.round(new java.math.MathContext(4, towards)).toString
  }
  /** The bound for one obligation: the worst rounding of a leaf, plus the worst divergence. */
  private object bound {

    /** The error bound for one number of a function's result, or why none was established. */
    def of(fid: Identifier, field: Option[String]): Either[String, BigDecimal] =
      decompositions.of(fid, field).flatMap { parts =>
        val name = label(fid, field)

        for {
          // A guard can only be misread where its two sides are within their combined error.
          guards <- traverse(parts.guardOperandErrors) { case (lhs, rhs) =>
                      for { l <- errorFrom(lhs); r <- errorFrom(rhs) } yield l + r
                    }
          rounding <- traverse(parts.reachableLeaves)(errorFrom)
          divergences <- search(fid, name, parts, guards)
        } yield {
          val worstDivergence = (BigDecimal(0) +: divergences).max
          val worstRounding = rounding.max

          describe(name, parts, divergences, worstDivergence, worstRounding)
          // Added under a rounding of the analysis's own choosing: the default one shortens a
          // long sum towards zero as readily as away from it, and a bound shortened towards
          // zero is no longer a bound.
          new BigDecimal(worstDivergence.bigDecimal, reportedPrecision) + worstRounding
        }
      }

    /** What Ibex made of every region where the two computations may take different paths. */
    private def search(fid: Identifier, name: String, parts: ErrorDecomposition,
                       guards: Seq[BigDecimal]): Either[String, Seq[BigDecimal]] = {
      // What is left of the function's budget, cut equally among the numbers in its result:
      // they are separate obligations, and none is told what the others will need.
      val remaining = decompositions.budgetLeft(fid) / decompositions.fieldCount(fid).max(1)

      ibex.within(remaining, parts.discontinuities.queries) {
        parts.discontinuities match {
          case DiscontinuityPlan.Pairwise(problems) =>
            traverse(problems.zipWithIndex) { case (problem, path) =>
              ibex.discontinuityBound(problem, parts.guardDifferences, guards, Site(name, path))
            }
          case DiscontinuityPlan.Merged(regions) =>
            traverse(regions) { region =>
              ibex.mergedBound(region, parts.guardDifferences, guards, Site(name, region.guard))
            }
          case DiscontinuityPlan.ViaReference(regions) =>
            traverse(regions) { region =>
              ibex.referenceBound(region, parts.guardDifferences, guards, Site(name, region.guard))
            }
        }
      }
    }

    /** The error of one leaf, or of one side of one guard. */
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

    /** Every query of every annotated function, in one batch: the analyzer starts up once. */
    private lazy val measured: Map[String, Either[String, RoundingResult]] = {
      val queries = decompositions.byFunction.values
        .collect { case Right(fields) => fields.flatMap { case (_, parts) => parts.queries } }
        .flatten.toSeq
        .distinctBy(_.name)

      if (queries.isEmpty) Map.empty else phases.rounding.run(analyzer.analyze(queries))
    }

    /** The three lines a reading leaves on the debug sections, named by field as well. */
    private def describe(name: String, parts: ErrorDecomposition, divergences: Seq[BigDecimal],
                         worstDivergence: BigDecimal, worstRounding: BigDecimal): Unit = {
      val shape = parts.shape
      val found = divergences.count(_ > 0)

      reporter.debug(
        s"Roundoff shape of $name: ${counted(shape.guards, "guard")} over " +
        s"${counted(shape.paths, "path")}, nested ${shape.depth} deep, " +
        s"${counted(shape.distinct, "leaf", "leaves")} computing something different, " +
        s"${counted(parts.unreachableCount, "path")} that no input reaches"
      )(using DebugSectionRoundoff)

      reporter.debug(
        s"Roundoff plan of $name (${Settings.mode.toString.toLowerCase}): " +
        s"${counted(parts.discontinuities.size, "region")} holding " +
        s"${counted(parts.discontinuities.queries, "comparison")}, " +
        s"$found of which ${if (found == 1) "holds" else "hold"} a divergence; " +
        s"${counted(parts.queries.map(_.name).distinct.size, "analyzer query", "analyzer queries")}"
      )(using DebugSectionRoundoff)

      reporter.debug(
        s"Roundoff for $name (${Settings.mode.toString.toLowerCase}): " +
        s"worst discontinuity $worstDivergence, worst rounding $worstRounding"
      )(using DebugSectionVerification)
    }
  }
  /** What the analysis made of each annotated function, and what reading it cost. */
  private object decompositions {

    /** One decomposition per number in a function's result, since several numbers are several
      * errors: a tuple or a case class gives one per number inside it, over the same guards.
      */
    lazy val byFunction: Map[Identifier, Either[String, Seq[(ResultPath, ErrorDecomposition)]]] =
      read.map { case (id, _, outcome) => id -> outcome }.toMap

    /** One field's decomposition, by the label the obligation was raised under. */
    def of(fid: Identifier, field: Option[String]): Either[String, ErrorDecomposition] =
      byFunction.getOrElse(fid, Left("this function was not analyzed")).flatMap { fields =>
        fields.find { case (path, _) => field.forall(_ == path.label) }
          .map { case (_, parts) => parts }
          .toRight(s"nothing in the result of this function is called '${field.getOrElse("")}'")
      }

    /** The first decomposition of a function, which is all of it where the result is one number. */
    def first(fid: Identifier): Either[String, ErrorDecomposition] = of(fid, None)

    /** How many numbers a function's result holds, as far as it was read. */
    def fieldCount(fid: Identifier): Int =
      byFunction.get(fid).flatMap(_.toOption).map(_.size).getOrElse(1)

    /** What each function calls its inputs, in the order it declares them. */
    lazy val parameterNames: Map[String, Seq[String]] =
      annotated.map { fd =>
        fd.id.name -> first(fd.id).toOption
          .map(_.flattening.parameters).getOrElse(fd.params).map(_.id.name)
      }.toMap

    /** What is left of a function's budget once its reading is taken off. */
    def budgetLeft(fid: Identifier): Double = {
      val spent = timeSpent.getOrElse(fid, 0L) / 1000.0
      val left = Settings.budget - spent

      if (left <= 0)
        reporter.warning(getFunction(fid).getPos,
          s"Reading ${getFunction(fid).id.asString} took ${spent}s of a ${Settings.budget}s " +
          "budget, so its divergences are bounded on whatever is left of it; " +
          "--roundoff-timeout raises it")

      left
    }

    /** Every annotated function is read at once, since the analyzer is asked in one batch. */
    private lazy val read
      : Seq[(Identifier, Long, Either[String, Seq[(ResultPath, ErrorDecomposition)]])] =
      annotated.map { fd =>
        Settings.announced
        val start = System.nanoTime()
        val outcome = oracle.around(fd) { branches =>
          ErrorDecomposition.of(fd, Settings.exactInputs, Settings.mode, branches, phases,
                                Settings.normalise, Settings.pathRanges)(using program.symbols)
        }
        (fd.id, (System.nanoTime() - start) / 1000000, outcome)
      }

    /** How long reading each function took. The analyzer is not counted: one batch answers
      * every function and cannot honestly be charged to any one of them.
      */
    private lazy val timeSpent: Map[Identifier, Long] =
      read.map { case (id, spent, _) => id -> spent }.toMap
  }
  /** The solver questions that set aside the paths no input takes. */
  private object oracle {

    /** Runs `block` with an oracle backed by one solver, which lives as long as the
      * enumeration it prunes.
      *
      * Not every solver reads floating point: one that does not keeps what it could not encode
      * to itself until the first `check` and throws on every one after that, so the run stops
      * asking rather than trying again.
      */
    def around[A](fd: FunDef)(block: BranchOracle => A): A =
      if (!Settings.prune || refusedFloats) block(BranchOracle.open)
      else {
        val factory = getFactory(options + optCheckModels(false) + optSilentErrors(true))
        var started: Option[factory.S] = None

        // What the questions are about: the values the function's fields became rather than
        // the objects holding them, so the solver is never handed a datatype.
        var values: Seq[ValDef] = fd.params
        var assumptions: Expr = fd.precondition.map(Preprocessor.stripAnnotations)
                                  .getOrElse(BooleanLiteral(true))

        // Cut once the count is known, which is before the first question is asked.
        var cake: Option[Cake] = None

        var asked, refuted, unanswered, skipped = 0
        var spent = 0L

        // Said once the walk is over: a run that prunes nothing is worth telling apart from
        // one that had no time to try.
        def summarise(): Unit = {
          val share = Settings.budget * Settings.pruningShare
          val used = ((share - cake.fold(0.0)(_.left)) * 1000).toInt.max(0)
          reporter.debug(
            s"Roundoff pruning of ${fd.id.asString}: $asked of " +
            s"${counted(asked + skipped, "branch question")} asked, $refuted refuted, " +
            s"$unanswered unanswered, $skipped skipped for want of time; $used ms of a " +
            s"${(share * 1000).toInt} ms share, $spent ms of it waiting on an answer and the " +
            "rest on building the solver and stating the guards"
          )(using DebugSectionRoundoff)
        }

        // What `--timeout` asked for: a budget of its own is no reason for a question to
        // overrun the one the run was given.
        var ambient: Option[Duration] = None

        // Built by the first question, since a function whose body has no conditional in it
        // asks none at all, and most of them do not.
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
              cake = Some(new Cake(Settings.budget * Settings.pruningShare, questions))

            def assuming[B](condition: Expr)(block: => B): Option[B] = {
              // The share left over the questions left. Over-estimating how many are left only
              // makes the shares smaller, so the phase keeps to its part of the budget either way.
              val allowance = cake.fold(Settings.budget * Settings.pruningShare)(_.slice())

              if (refusedFloats || allowance < minQueryTimeout) { skipped += 1; Some(block) }
              else {
                cake.foreach(_.taken())
                asked += 1
                val questioned = solver
                questioned.setTimeout(ambient.fold(allowance.seconds)(_.min(allowance.seconds)))
                questioned.push()
                try {
                  questioned.assertCnstr(condition)
                  val (took, answer) =
                    phases.pruning.questions.runAndGetTime(questioned.check(Simple))
                  spent += took
                  trace(fd, condition, answer)
                  // A question left open has to keep the branch: only a refutation says that
                  // no input reaches it.
                  answer match {
                    case scala.util.Success(Unsat) => refuted += 1; None
                    case scala.util.Success(Unknown) =>
                      unanswered += 1; warnUnsettled(fd); Some(block)
                    case scala.util.Success(_) => Some(block)
                    case scala.util.Failure(e) =>
                      unanswered += 1; warnRefused(fd, e); Some(block)
                  }
                } finally questioned.pop()
              }
            }
          })
        } catch {
          case e: inox.Unsupported => warnRefused(fd, e); block(BranchOracle.open)
        } finally {
          if (asked + skipped > 0) summarise()
          started.foreach(factory.reclaim)
        }
      }

    /** The shortest time a question is worth asking for. */
    private val minQueryTimeout = 0.001

    /** Set once the solver turns out not to read floating point, after which it is not asked
      * again. Touched only while the decompositions are read, which one thread does under the
      * lock of that lazy value, so neither flag needs a guard of its own.
      */
    private var refusedFloats = false
    private var sawUnsettled = false

    /** Says what became of one question, so a run can be watched cutting whole subtrees. */
    private def trace(fd: FunDef, condition: Expr,
                      answer: scala.util.Try[SolverResponses.SimpleResponse]): Unit = {
      val outcome = answer match {
        case scala.util.Success(Unsat) => "no input reaches it"
        case scala.util.Success(response) => s"kept ($response)"
        case scala.util.Failure(e) => s"kept, unanswered: ${e.getMessage}"
      }
      reporter.debug(s"Reachability of ${fd.id.name} under ${condition.asString}: $outcome")(
        using inox.solvers.DebugSectionSolver)
    }

    /** Warned about once: one hard branch says little, but a run that settles none prunes
      * nothing, and that is worth telling apart from a run that pruned nothing to find.
      */
    private def warnUnsettled(fd: FunDef): Unit = {
      if (!sawUnsettled)
        reporter.warning(fd.getPos,
          "A question about which branches are taken was left unanswered, so some leaf no input " +
          "reaches may still count towards the bound; the questions of one function share " +
          s"${Settings.pruningShare} of --roundoff-timeout, which raising either gives them more " +
          "of, and a solver reading floating point, such as --solvers=smt-bitwuzla, settles " +
          "more of them")
      sawUnsettled = true
    }

    private def warnRefused(fd: FunDef, e: Throwable): Unit = {
      if (!refusedFloats)
        reporter.warning(fd.getPos,
          s"The selected solver cannot answer about floating-point values (${e.getMessage}), so " +
          "no unreachable path was set aside and every leaf counts towards the bound; " +
          "--solvers=smt-bitwuzla answers these")
      refusedFloats = true
    }
  }
  private object Fuzzing {

    /** The `@fuzz` functions, each with the program written for it. A witness names only the
      * function it belongs to, so of two functions of the same name only the first is written.
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
                parts <- decompositions.first(fd.id)
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

    /** Runs the fuzzer over all functions. */
    def run(): Unit = { val _ = fuzzerResult }

    /** The lower bound the fuzzer returned for a given function */
    def lowerBound(fd: FunDef): Option[BigDecimal] =
      if (!fuzzer.enabled || subjects.isEmpty) None
      else
        fuzzerResult.flatMap(_.get(fd.id.name).toRight("the fuzzer reported nothing for it")) match {
          case Right(error) => Some(error)
          case Left(why) =>
            reporter.warning(fd.getPos, s"No fuzzed error for ${fd.id.asString}: $why")
            None
        }

    def writeFuzzerInputs(file: java.io.File): Unit = {
      val parameters = (name: String) => decompositions.parameterNames.getOrElse(name, Seq.empty)

      stainless.utils.JsonUtils.writeFile(file, Witness.report(ibex.witnesses, parameters))
      if (subjects.nonEmpty) writeSubjects(file)
    }

    private lazy val fuzzerResult: Either[String, Map[String, BigDecimal]] =
      if (!fuzzer.enabled || subjects.isEmpty) Left("the fuzzer was not run")
      else
        scala.util.Try(
          phases.fuzzing.run(fuzzer.run(writeSubjects(Settings.witnessFile.getOrElse(scratch)))))
          .fold(e => Left(s"the fuzzer could not be run: ${e.getMessage}"), identity)

    /** Writes the program and the configuration. */
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

    private def sibling(file: java.io.File, extension: String): java.io.File = {
      val name = file.getName
      val base = name.lastIndexOf('.') match { case -1 => name; case dot => name.take(dot) }
      new java.io.File(file.getParentFile, s"$base.$extension")
    }

    private def write(file: java.io.File, content: String): Unit = {
      val out = new java.io.FileWriter(file)
      try out.write(content) finally out.close()
    }
  }

  private object Settings {

    /** Where the regions a divergence may occur in are written out, if they were asked for. */
    lazy val witnessFile: Option[java.io.File] =
      Some(context.options.findOptionOrDefault(optRoundoffWitnesses))
        .filter(_.nonEmpty)
        .map(new java.io.File(_))

    lazy val exactInputs: Boolean =
      context.options.findOptionOrDefault(optRoundoffExactInputs)

    lazy val prune: Boolean =
      context.options.findOptionOrDefault(optRoundoffPruning)

    lazy val pathRanges: Boolean =
      context.options.findOptionOrDefault(optRoundoffPathRanges)

    lazy val normalise: Boolean =
      context.options.findOptionOrDefault(optRoundoffNormalisation)

    lazy val mode: DiscontinuityMode =
      context.options.findOptionOrDefault(optRoundoffDiscontinuity)

    /** How long one function may be read and searched for, all phases together. */
    lazy val budget: Double = context.options.findOptionOrDefault(optRoundoffTimeout)

    /** What fraction of a function's budget its reachability questions may take together. */
    lazy val pruningShare: Double =
      context.options.findOptionOrDefault(optRoundoffPruningShare).max(0.0).min(1.0)

    /** Debug information. */
    lazy val announced: Unit = {
      val on = (name: String, flag: Boolean) => if (flag) name else s"no $name"
      reporter.debug(
        s"Roundoff Settings: ${mode.toString.toLowerCase} discontinuities, " +
        s"${budget}s per function of which ${(pruningShare * 100).toInt}% for the branch " +
        s"questions, ${(context.options.findOptionOrDefault(optRoundoffFeasibilityShare) * 100).toInt}% " +
        s"of a search for feasibility, " +
        Seq(on("pruning", prune), on("normalisation", normalise), on("path ranges", pathRanges),
            on("incumbent", context.options.findOptionOrDefault(optRoundoffIncumbent)),
            if (exactInputs) "exact inputs" else "rounded inputs").mkString(", ") +
        s", solvers ${context.options.findOptionOrDefault(inox.optSelectedSolvers).mkString(",")}"
      )(using DebugSectionRoundoff)
    }
  }
}
