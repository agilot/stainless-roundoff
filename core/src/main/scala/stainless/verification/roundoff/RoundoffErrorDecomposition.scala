/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification
package roundoff

import trees._

/** Where the rounding error of one expression comes from. */
enum RoundingError {
  /** Computed without rounding, such as a literal. */
  case Exact

  /** A value without inputs, whose error is computed directly (an analyzer needs inputs). */
  case Computed(error: BigDecimal)

  /** Bounded by the analyzer, through this query. */
  case FromAnalyzer(query: RoundingQuery)

  /** A leaf no floating-point run reaches. Its rounding error is not analysed, so an
    * operation the analyzer cannot express does not make the function unsupported. The exact
    * run can still reach it, so it is still compared with reachable leaves in Ibex.
    */
  case Unreachable

  def asQuery: Option[RoundingQuery] = this match {
    case FromAnalyzer(q) => Some(q)
    case _ => None
  }
}

/** The size of a function's tree of guards, for `--debug=roundoff`. These numbers explain
  * most of the analysis time.
  *
  * @param guards   comparisons, after inlining and after `&&` and `||` became nested guards
  * @param paths    leaves, which is `guards + 1`
  * @param depth    guards above the deepest leaf
  * @param distinct leaves that compute different expressions (only those are compared)
  */
case class Shape(guards: Int, paths: Int, depth: Int, distinct: Int)

/** What the roundoff error of one number in a function's result is built from.
  *
  * @param leaves             the rounding error of each path's leaf
  * @param guardOperandErrors the rounding error of each guard's two sides
  * @param guardDifferences   per guard, `lhs - rhs` over the reals, and its name if it has one
  * @param regions            the Ibex problems, one per guard
  * @param body               the preprocessed body, for the fuzzer
  */
case class RoundoffErrorDecomposition(
  leaves: Seq[RoundingError],
  shape: Shape,
  flattening: ParameterFlattening,
  guardOperandErrors: Seq[(RoundingError, RoundingError)],
  guardDifferences: Seq[Seq[inox.trees.Expr]],
  regions: Seq[GuardRegion],
  spec: InputSpec,
  body: Expr
) {
  /** How many leaf pairs Ibex will be asked about, so that a budget can be divided among them. */
  def pairCount: Int = regions.map(_.pairs.size).sum

  def reachableLeaves: Seq[RoundingError] =
    leaves.filterNot(_ == RoundingError.Unreachable)

  def queries: Seq[RoundingQuery] =
    (reachableLeaves ++ guardOperandErrors.flatMap { case (lhs, rhs) => Seq(lhs, rhs) })
      .flatMap(_.asQuery)
}

object RoundoffErrorDecomposition {

  /** The decomposition of each number in the result of `fd`, labelled by its access path.
    *
    * The body is preprocessed and its paths are enumerated once for the whole result, since
    * every number in it is computed by the same branches. Only the leaves differ per number.
    *
    * @param timers where each phase reports how long it took
    */
  def of(fd: FunDef, settings: RoundoffSettings, oracles: BranchOracleFactory,
         timers: inox.utils.TimerStorage, emitter: RoundingSourceEmitter)(using Symbols)
    : Either[String, Seq[(AccessPath, RoundoffErrorDecomposition)]] = {
    val config = Config(settings, timers, emitter)

    for {
      (whole, fields, flattening) <- timers.preprocessing.run(Preprocessor(fd))
      spec <- timers.preprocessing.run(InputRanges.specOf(fd, whole, flattening))
      (guards, paths) <- extractPaths(fd, whole, flattening, oracles, timers)
      // When every path is refuted, no input satisfies the precondition.
      _ <- Either.cond(paths.exists(_.reachable), (),
             "no path through this function is reachable, so its precondition may be " +
             "unsatisfiable; --sat-precond checks that on its own")
      operandErrors <- guardOperandErrors(fd, guards, spec, config)
      body = SharedBody(fd, whole, flattening, spec, guards, paths, operandErrors, config)
      decompositions <- traverse(fields)(field => body.forField(field).map(field -> _))
    } yield decompositions
  }

  /** What the caller passed in, carried unchanged through the decomposition of one function. */
  private case class Config(settings: RoundoffSettings,
                            timers: inox.utils.TimerStorage,
                            emitter: RoundingSourceEmitter)

  /** The guards and paths of `whole`, with the paths no input takes marked unreachable. */
  private def extractPaths(fd: FunDef, whole: Expr, flattening: ParameterFlattening,
                           oracles: BranchOracleFactory, timers: inox.utils.TimerStorage)
                          (using Symbols): Either[String, (Seq[Guard], Seq[ProgramPath])] = {
    val oracle = oracles(fd, flattening.parameters, InputRanges.assumptions(fd, flattening),
                         questionCount(whole, timers))
    try timers.paths.run(PathExtractor(whole, oracle)) finally oracle.close()
  }

  /** How many branch questions the walk can ask: two per guard.
    *
    * Counted by walking the body once without asking anything. That walk finds the same guards,
    * so the count is exact when nothing is refuted and too high otherwise.
    */
  private def questionCount(whole: Expr, timers: inox.utils.TimerStorage): Int =
    timers.pruning.counting.run(
      PathExtractor(whole) match {
        case Right((guards, _)) => guards.size * 2
        case Left(_) => 0
      })

  /** How far the two sides of each guard can be from their exact values. */
  private def guardOperandErrors(fd: FunDef, guards: Seq[Guard], spec: InputSpec,
                                 config: Config)(using Symbols)
    : Either[String, Seq[(RoundingError, RoundingError)]] = {
    val guardIndex = guards.distinct.zipWithIndex.toMap

    config.timers.queries.conditions.run(traverse(guards) { guard =>
      val k = guardIndex(guard)
      for {
        lhs <- roundingErrorOf(s"${queryPrefix(fd)}_guard${k}_lhs",
                               s"${fd.id.name} (guard ${k + 1}, left)", guard.lhs, spec, config)
        rhs <- roundingErrorOf(s"${queryPrefix(fd)}_guard${k}_rhs",
                               s"${fd.id.name} (guard ${k + 1}, right)", guard.rhs, spec, config)
      } yield (lhs, rhs)
    })
  }

  /** What every number of one function's result has in common. */
  private case class SharedBody(fd: FunDef, whole: Expr, flattening: ParameterFlattening,
                                spec: InputSpec, guards: Seq[Guard], paths: Seq[ProgramPath],
                                operandErrors: Seq[(RoundingError, RoundingError)],
                                config: Config) {

    /** The decomposition of the number at `field` in the result. */
    def forField(field: AccessPath)(using Symbols): Either[String, RoundoffErrorDecomposition] = {
      val projected = paths.map(path => path.copy(leaf = field.project(path.leaf)))
      val named = if (field.steps.isEmpty) fd.id.name else s"${fd.id.name}.${field.displayName}"
      val tag =
        if (field.steps.isEmpty) queryPrefix(fd)
        else s"${queryPrefix(fd)}_${field.displayName("_")}"

      // Each leaf is analysed over the input ranges its path allows.
      val leafSpecs = projected.map(path =>
        if (config.settings.pathRanges) InputRanges.narrowed(spec, guards, path.choices) else spec)

      // The same leaf can appear on several paths (a connective written out as nesting repeats
      // its branches). Paths share one analyzer query when both the leaf and its ranges agree.
      val leafKeys = projected.map(_.leaf).zip(leafSpecs.map(_.ranges))
      val leafIndex = leafKeys.distinct.zipWithIndex.toMap

      val leafErrors = config.timers.queries.branches.run(traverse(projected.indices) { i =>
        if (!projected(i).reachable) Right(RoundingError.Unreachable)
        else {
          val k = leafIndex(leafKeys(i))
          roundingErrorOf(s"${tag}_leaf$k", s"$named (leaf ${k + 1})",
                          projected(i).leaf, leafSpecs(i), config)
        }
      })

      for {
        leaves <- leafErrors
        (differences, regions) <- guardRegions(projected)
      } yield RoundoffErrorDecomposition(
        leaves,
        Shape(guards.size, projected.size,
              projected.map(_.choices.size).maxOption.getOrElse(0),
              projected.map(_.leaf).distinct.size),
        flattening, operandErrors, differences, regions, spec, field.project(whole))
    }

    /** The regions Ibex searches. Without guards there is nothing to diverge to. */
    private def guardRegions(projected: Seq[ProgramPath])(using Symbols)
      : Either[String, (Seq[Seq[inox.trees.Expr]], Seq[GuardRegion])] =
      if (guards.isEmpty) Right((Seq.empty, Seq.empty))
      else config.timers.encoding.run(
        GuardRegions.encode(guards, projected, spec, config.settings.normalisation))
  }

  /** Where the rounding error of `expr` comes from: nowhere, a direct computation, or an
    * analyzer query called `name`.
    */
  private def roundingErrorOf(name: String, label: String, expr: Expr, spec: InputSpec,
                              config: Config)(using Symbols): Either[String, RoundingError] =
    if (isExact(expr, config.settings.exactInputs)) Right(RoundingError.Exact)
    else if (exprOps.variablesOf(expr).isEmpty)
      ConstantEvaluator.error(expr, spec.precision).map(RoundingError.Computed(_))
    else config.emitter.emit(name, label, expr, spec)
           .map(source => RoundingError.FromAnalyzer(RoundingQuery(name, spec.precision, source)))

  /** Whether a value is computed without rounding, so no analyzer has to be asked. */
  private def isExact(e: Expr, exactInputs: Boolean): Boolean =
    constantOf(e).isDefined || (exactInputs && isRoundingFree(e))

  /** Whether every step is exact in floating point: literals, sign changes and, when inputs
    * are exact reals, the inputs themselves. No arithmetic operation qualifies.
    */
  private def isRoundingFree(e: Expr): Boolean = e match {
    case FPLit(_) => true
    case _: Variable => true
    case FPUMinus(a) => isRoundingFree(a)
    case Let(_, value, body) => isRoundingFree(value) && isRoundingFree(body)
    case _ => false
  }

  /** The value of `e` if it is a constant, looking through its bindings. */
  private def constantOf(e: Expr, known: Map[Identifier, Expr] = Map.empty): Option[Double] = e match {
    case FPLit(d) => Some(d)
    case v: Variable => known.get(v.id).flatMap(constantOf(_, known))
    case Let(vd, value, body) => constantOf(body, known + (vd.id -> value))
    case _ => None
  }

  /** Makes analyzer query names unique across functions. */
  private def queryPrefix(fd: FunDef): String = s"f_${fd.id.globalId}"
}

/** Computes the rounding error of an expression without inputs, by evaluating it both in
  * floating point and exactly.
  */
private[roundoff] object ConstantEvaluator {

  def error(e: Expr, precision: FPPrecision): Either[String, BigDecimal] =
    evaluate(e, Map.empty, precision).flatMap { value =>
      if (value.rounded.isNaN || value.rounded.isInfinite)
        Left(s"a value with no inputs is not finite (${value.rounded})")
      else
        Fraction(value.rounded).map(landed => (landed - value.exact).abs.toBigDecimal)
    }

  /** The value the program computes, and the exact value of the same expression. */
  private case class Value(rounded: Double, exact: Rational)

  private def evaluate(e: Expr, bound: Map[Identifier, Value], precision: FPPrecision)
  : Either[String, Value] = {

    /** Single precision is computed in `Float`. Rounding a `Double` result instead would
      * round twice and can give a different value.
      */
    def binary(single: (Float, Float) => Float,
               double: (Double, Double) => Double,
               exact: (Rational, Rational) => Either[String, Rational])
              (l: Expr, r: Expr): Either[String, Value] =
      for {
        a <- evaluate(l, bound, precision)
        b <- evaluate(r, bound, precision)
        exactValue <- exact(a.exact, b.exact)
      } yield {
        val rounded = precision match {
          case FPPrecision.Binary32 => single(a.rounded.toFloat, b.rounded.toFloat).toDouble
          case FPPrecision.Binary64 => double(a.rounded, b.rounded)
        }
        Value(rounded, exactValue)
      }

    e match {
      // First, because a literal can also be wrapped in a negation or a cast.
      case FPLit(d) => Fraction(d).map(Value(d, _))

      case FPAdd(_, l, r) => binary(_ + _, _ + _, (a, b) => Right(a + b))(l, r)
      case FPSub(_, l, r) => binary(_ - _, _ - _, (a, b) => Right(a - b))(l, r)
      case FPMul(_, l, r) => binary(_ * _, _ * _, (a, b) => Right(a * b))(l, r)
      case FPDiv(_, l, r) =>
        binary(_ / _, _ / _, (a, b) =>
          if (b.isZero) Left("a value with no inputs divides by zero") else Right(a / b))(l, r)

      case FPUMinus(a) => evaluate(a, bound, precision).map(v => Value(-v.rounded, -v.exact))

      case FPFMA(_, a, b, c) =>
        for {
          x <- evaluate(a, bound, precision)
          y <- evaluate(b, bound, precision)
          z <- evaluate(c, bound, precision)
        } yield {
          val rounded = precision match {
            case FPPrecision.Binary32 =>
              Math.fma(x.rounded.toFloat, y.rounded.toFloat, z.rounded.toFloat).toDouble
            case FPPrecision.Binary64 => Math.fma(x.rounded, y.rounded, z.rounded)
          }
          Value(rounded, x.exact * y.exact + z.exact)
        }

      case Let(vd, value, body) =>
        evaluate(value, bound, precision)
          .flatMap(v => evaluate(body, bound + (vd.id -> v), precision))

      case v: Variable =>
        bound.get(v.id).toRight(s"'${v.id.name}' is not bound in a value with no inputs")

      // The exact value must be a fraction, and these functions do not give one.
      case TranscendentalFunctionCall(f, _) =>
        Left(s"a value with no inputs calls '${f.symbol}', which is not a fraction")

      case other =>
        Left(s"${other.getClass.getSimpleName} cannot be evaluated without inputs")
    }
  }
}
