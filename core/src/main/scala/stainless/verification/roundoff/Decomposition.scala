/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification
package roundoff

import trees._
import scala.collection.mutable.ArrayBuffer

/* From a preprocessed body to what the error of each number in the result is built from:
 *  - [[RoundoffErrorDecomposition]]: the leaves, the guards, and the regions Ibex searches;
 *  - [[PathExtractor]]: the guards and the paths through them;
 *  - [[InputRanges]]: the range of each input, from the precondition and along a path;
 *  - [[ConstantEvaluator]]: the error of a value without inputs.
 */

/** Where the rounding error of one expression comes from. */
enum RoundingError {
  /** Computed without rounding, such as a literal. */
  case Exact

  /** A value without inputs, whose error is computed directly. */
  case Computed(error: BigDecimal)

  case FromAnalyzer(query: RoundingQuery)

  /** A leaf no input reaches. Not analysed: it could only loosen the bound or make the
    * analyzer fail.
    */
  case Unreachable

  /** A leaf that returns NaN on a path some input may reach. */
  case NotANumber

  /** A leaf that returns an infinity on a path some input may reach. */
  case Infinite
}

/** What the roundoff error of one number in a function's result is built from.
  *
  * @param leaves             the rounding error of each path's leaf
  * @param guards             the comparisons the paths branch on, with `&&` and `||` nested
  * @param guardOperandErrors the rounding error of each guard's two sides
  * @param guardDifferences   per guard, `lhs - rhs` over the reals
  * @param regions            the Ibex problems, one per guard
  * @param discontinuity      the mode `regions` are built for
  * @param variant            the constructors the inputs are built with
  */
case class RoundoffErrorDecomposition(
  leaves: Seq[RoundingError],
  flattening: FlattenedParameters,
  guards: Seq[Guard],
  guardOperandErrors: Seq[(RoundingError, RoundingError)],
  guardDifferences: Seq[inox.trees.Expr],
  regions: Seq[GuardRegion],
  discontinuity: DiscontinuityMode,
  spec: InputSpec,
  variant: InputVariant
) {
  def reachableLeaves: Seq[RoundingError] =
    leaves.filterNot(_ == RoundingError.Unreachable)

  def queries: Seq[RoundingQuery] =
    (reachableLeaves ++ guardOperandErrors.flatMap { case (lhs, rhs) => Seq(lhs, rhs) })
      .collect { case RoundingError.FromAnalyzer(query) => query }
}

object RoundoffErrorDecomposition {

  /** The label of the obligation that both runs end in the same case.
    */
  val caseVCLabel = "case"
}

/** Builds the analyzer queries and the Ibex regions of the `@roundoff` functions. */
private[roundoff] final class QueryBuilder(settings: RoundoffSettings, timers: inox.utils.TimerStorage,
                                           emitter: RoundingSourceEmitter, timeLimit: TimeLimit)
                                          (using Symbols) {
  import RoundoffErrorDecomposition.caseVCLabel

  /** Generates all the roundoff-error analysis queries for this function
    */
  def buildQueries(fd: FunDef): Either[String, Seq[(String, Seq[RoundoffErrorDecomposition])]] =
    for {
      variants <- timers.preprocessing.run(InputVariants.allowedVariants(fd))
      perVariant <- traverse(variants)(decomposeVariant).map(_.flatten)
      _ <- Either.cond(perVariant.nonEmpty, (), "no floating-point values")
    } yield perVariant.head.map(_._1).map { label =>
      label -> perVariant.flatMap(_.collect { case (`label`, Some(parts)) => parts })
    }

  /** Each number's decomposition for one variant, by label: `None` for a number no input
    * reaches, and `None` overall when the variant computes nothing in floating point.
    */
  private def decomposeVariant(variant: InputVariant)
    : Either[String, Option[Seq[(String, Option[RoundoffErrorDecomposition])]]] = {
    val fd = variant.function

    timers.preprocessing.run(Preprocessor(fd, timeLimit)).flatMap { (preprocessed, fields, flattening) =>
      if (!InputRanges.computesFloatingPoint(preprocessed)) Right(None)
      else for {
        spec <- timers.preprocessing.run(InputRanges.inputSpecOf(fd, preprocessed, flattening))
        _ <- InputRanges.inexactIntegerConversion(preprocessed, spec).toLeft(())
        bodyWithFiniteInputs <- Preprocessor.withFiniteInputs(preprocessed, spec.ranges)
        _ = timeLimit.check()
        (guards, paths) <- timers.paths.run(PathExtractor(bodyWithFiniteInputs, timeLimit))
        specAlongPath = InputRanges.rangesAlongPath(spec, guards, settings.exactInputs)
        specAlongPathForBothRuns =
          InputRanges.rangesAlongPath(spec, guards, settings.exactInputs, forBothRuns = true)
        operandErrors <- guardOperandErrors(fd, guards, paths, spec, specAlongPath)
        variantBody = VariantBody(fd, variant, flattening, spec, guards, paths,
                                  operandErrors, specAlongPath, specAlongPathForBothRuns)
        decompositions <- traverse(fields)(field =>
          variantBody.decompositionOfField(field).map(field.displayName -> _))
        caseAgreement <-
          if (!FieldPath.hasConstructorChoice(fd.returnType)) Right(Seq.empty)
          else variantBody.caseDecomposition(fd.returnType).map(parts => Seq(caseVCLabel -> parts))
      } yield Some(decompositions ++ caseAgreement)
    }
  }

  /** The rounding error of each guard's two sides, over the inputs that reach the guard. A
    * guard no input reaches is never read, so its sides count as exact.
    */
  private def guardOperandErrors(fd: FunDef, guards: Seq[Guard], paths: Seq[ProgramPath],
                                 spec: InputSpec,
                                 specAlongPath: Seq[BranchChoice] => Option[InputSpec])
    : Either[String, Seq[(RoundingError, RoundingError)]] = {
    // Every path through a guard takes the same branches above it.
    val choicesAboveGuard: Map[Int, Seq[BranchChoice]] =
      paths.flatMap(path => path.choices.indices.map(i => path.choices(i).guard -> path.choices.take(i)))
        .toMap
    val rangesReachingGuard = guards.indices.map(g => specAlongPath(choicesAboveGuard.getOrElse(g, Seq.empty)))
    val guardSpecs = rangesReachingGuard.map(reached =>
      if (settings.pathRanges) reached.getOrElse(spec) else spec)
    // The same guard can be on several paths, as a leaf can.
    val guardKeys = guards.zip(guardSpecs.map(_.ranges))
    val guardQueryIndex = guardKeys.distinct.zipWithIndex.toMap

    timers.queries.conditions.run(traverse(guards.indices) { g =>
      timeLimit.check()
      if (rangesReachingGuard(g).isEmpty) Right((RoundingError.Exact, RoundingError.Exact))
      else {
        val queryIndex = guardQueryIndex(guardKeys(g))
        for {
          lhs <- roundingErrorOf(s"${queryPrefix(fd)}_guard${queryIndex}_lhs",
                                 s"${fd.id.name} (guard ${queryIndex + 1}, left)", guards(g).lhs, guardSpecs(g))
          rhs <- roundingErrorOf(s"${queryPrefix(fd)}_guard${queryIndex}_rhs",
                                 s"${fd.id.name} (guard ${queryIndex + 1}, right)", guards(g).rhs, guardSpecs(g))
        } yield (lhs, rhs)
      }
    })
  }

  /** The body of one variant, read once for every number in its result. */
  private case class VariantBody(fd: FunDef, variant: InputVariant, flattening: FlattenedParameters,
                                 spec: InputSpec, guards: Seq[Guard], paths: Seq[ProgramPath],
                                 operandErrors: Seq[(RoundingError, RoundingError)],
                                 specAlongPath: Seq[BranchChoice] => Option[InputSpec],
                                 specAlongPathForBothRuns: Seq[BranchChoice] => Option[InputSpec]) {

    /** The decomposition of the number at `field`, over the paths that hold it. */
    def decompositionOfField(field: FieldPath): Either[String, Option[RoundoffErrorDecomposition]] = {
      val queryNamePrefix =
        if (field.steps.isEmpty) queryPrefix(fd)
        else s"${queryPrefix(fd)}_${field.joinedWith("_")}"
      val displayName = if (field.steps.isEmpty) fd.id.name else s"${fd.id.name}.${field.displayName}"
      traverse(paths)(path => field.heldBy(path.leaf).map(path -> _)).flatMap { held =>
        val pathsHoldingField = held.collect { case (path, true) => path }
        // Drops the bindings only the other fields read.
        decomposeNumber(
          pathsHoldingField.map(path => path.copy(leaf = withoutUnusedLets(field.extractFrom(path.leaf)))),
          queryNamePrefix, displayName)
      }
    }

    /** The decomposition whose leaves are the numbers of their cases, as exact `Int`s: two
      * leaves diverge exactly when the runs can end in different cases.
      */
    def caseDecomposition(tpe: Type): Either[String, Option[RoundoffErrorDecomposition]] =
      traverse(paths)(path => FieldPath.constructorsOf(path.leaf, tpe)).flatMap { cases =>
        val caseNumber = cases.distinct.zipWithIndex.toMap
        val pathsReturningCaseNumber = paths.zip(cases).map { case (path, constructors) =>
          path.copy(leaf = Int32Literal(caseNumber(constructors)))
        }
        decomposeNumber(pathsReturningCaseNumber, s"${queryPrefix(fd)}_$caseVCLabel",
                        s"${fd.id.name} ($caseVCLabel)")
      }

    /** The decomposition of one number from its value on each path, `None` when no input
      * reaches any of them.
      */
    private def decomposeNumber(numberPaths: Seq[ProgramPath], queryNamePrefix: String,
                                displayName: String)
      : Either[String, Option[RoundoffErrorDecomposition]] = {

      // Each leaf is analysed over the ranges its path allows.
      val narrowedSpecs = numberPaths.map { path =>
        timeLimit.check()
        specAlongPath(path.choices)
      }
      val leafSpecs = narrowedSpecs.map(narrowed =>
        if (settings.pathRanges) narrowed.getOrElse(spec) else spec)

      // Nested connectives repeat a leaf on several paths; copies with equal ranges share a query.
      val leafKeys = numberPaths.map(_.leaf).zip(leafSpecs.map(_.ranges))
      val leafQueryIndex = leafKeys.distinct.zipWithIndex.toMap

      val leafErrors = timers.queries.branches.run(traverse(numberPaths.indices) { i =>
        timeLimit.check()
        val constant = valueWithoutInputs(numberPaths(i).leaf, spec.precision)
        if (narrowedSpecs(i).isEmpty) Right(RoundingError.Unreachable)
        else if (constant.exists(_.isNaN)) Right(RoundingError.NotANumber)
        else if (constant.exists(_.isInfinite)) Right(RoundingError.Infinite)
        else {
          val queryIndex = leafQueryIndex(leafKeys(i))
          roundingErrorOf(s"${queryNamePrefix}_leaf$queryIndex", s"$displayName (leaf ${queryIndex + 1})",
                          numberPaths(i).leaf, leafSpecs(i))
        }
      })

      leafErrors.flatMap { leaves =>
        if (!leaves.exists(_ != RoundingError.Unreachable)) Right(None)
        else {
          val reachedByNeither =
            numberPaths.indices.filter(i => specAlongPathForBothRuns(numberPaths(i).choices).isEmpty).toSet
          encodeGuardRegions(numberPaths, reachedByNeither).map { encoding =>
            Some(RoundoffErrorDecomposition(
              leaves, flattening, guards, operandErrors, encoding.guardDifferences,
              encoding.regions, encoding.mode, spec, variant))
          }
        }
      }
    }

    /** The regions Ibex searches, none without guards. */
    private def encodeGuardRegions(numberPaths: Seq[ProgramPath], reachedByNeither: Set[Int])
      : Either[String, IbexEncoding] =
      if (guards.isEmpty) Right(IbexEncoding(Seq.empty, Seq.empty, settings.discontinuity))
      else timers.encoding.run(
        GuardRegions.encode(guards, numberPaths, spec, settings.discontinuity, timeLimit,
                            reachedByNeither, smallGuardsByPairs = settings.refineBudget > 0))
  }

  /** Where the rounding error of `expr` comes from: nowhere, a direct computation, or an
    * analyzer query called `name`.
    */
  private def roundingErrorOf(name: String, label: String, expr: Expr, spec: InputSpec)
    : Either[String, RoundingError] =
    if (isExact(expr)) Right(RoundingError.Exact)
    else if (exprOps.variablesOf(expr).isEmpty)
      ConstantEvaluator.roundingError(expr, spec.precision).map(RoundingError.Computed(_))
    else emitter.emit(name, label, expr, spec)
           .map(source => RoundingError.FromAnalyzer(RoundingQuery(name, spec.precision, source)))

  /** Whether a value is computed without rounding. An integer always is, inputs included. */
  private def isExact(e: Expr): Boolean =
    isIntegral(e) || constantOf(e).isDefined || (settings.exactInputs && isRoundingFree(e))

  /** Whether every step is exact: literals, negations, integers converted to `Double`, and the
    * inputs when they are exact reals.
    */
  private def isRoundingFree(e: Expr): Boolean = e match {
    case FPLit(_) => true
    case FPCast(_, _, _, inner) => isIntegral(inner)
    case _: Variable => true
    case FPUMinus(a) => isRoundingFree(a)
    case Let(_, value, body) => isRoundingFree(value) && isRoundingFree(body)
    case _ => false
  }

  /** Makes analyzer query names unique across functions. */
  private def queryPrefix(fd: FunDef): String = s"f_${fd.id.globalId}"
}

/** The rounding error of an expression without inputs, from evaluating it in floating point
  * and exactly.
  */
private[roundoff] object ConstantEvaluator {

  def roundingError(e: Expr, precision: FPPrecision): Either[String, BigDecimal] =
    evaluate(e, Map.empty, precision).flatMap { value =>
      if (!value.rounded.isFinite) Left(s"a value with no inputs is not finite (${value.rounded})")
      else value.exact.toRight("a value with no inputs divides by zero").flatMap(exact =>
        Fraction(value.rounded).map(landed => (landed - exact).abs.toBigDecimal))
    }

  /** What the floating-point program computes, and the exact value: `None` after a division by
    * zero, which floating point turns into an infinity or NaN.
    */
  case class Value(rounded: Double, exact: Option[Rational])

  /** The value of `e`, which has no inputs, `bindings` holding the `let` names in scope. */
  def evaluate(e: Expr, bindings: Map[Identifier, Value], precision: FPPrecision)
  : Either[String, Value] = {

    // In `Float` for single precision: rounding a `Double` result would round twice.
    def evaluateArithmetic(single: (Float, Float) => Float,
                           double: (Double, Double) => Double,
                           exact: (Rational, Rational) => Option[Rational])
                          (l: Expr, r: Expr): Either[String, Value] =
      evaluate(l, bindings, precision).flatMap { a =>
        evaluate(r, bindings, precision).map { b =>
          val rounded = precision match {
            case FPPrecision.Binary32 => single(a.rounded.toFloat, b.rounded.toFloat).toDouble
            case FPPrecision.Binary64 => double(a.rounded, b.rounded)
          }
          Value(rounded, a.exact.zip(b.exact).flatMap(exact.tupled))
        }
      }

    // An integer is never divided, so its exact value is always known.
    def evaluateIntegerArithmetic(op: (BigInt, BigInt) => BigInt)(l: Expr, r: Expr)
      : Either[String, Value] =
      evaluate(l, bindings, precision).flatMap { a =>
        evaluate(r, bindings, precision).map { b =>
          val n = op(a.exact.get.num, b.exact.get.num)
          Value(n.toDouble, Some(Rational(n, 1)))
        }
      }

    e match {
      // First, because a literal can also be wrapped in a negation or a cast.
      case FPLit(d) => Fraction(d).map(exact => Value(d, Some(exact)))

      case FPAdd(_, l, r) => evaluateArithmetic(_ + _, _ + _, (a, b) => Some(a + b))(l, r)
      case FPSub(_, l, r) => evaluateArithmetic(_ - _, _ - _, (a, b) => Some(a - b))(l, r)
      case FPMul(_, l, r) => evaluateArithmetic(_ * _, _ * _, (a, b) => Some(a * b))(l, r)
      case FPDiv(_, l, r) => evaluateArithmetic(_ / _, _ / _, (a, b) => Option.unless(b.isZero)(a / b))(l, r)

      case FPUMinus(a) => evaluate(a, bindings, precision).map(v => Value(-v.rounded, v.exact.map(-_)))

      case FPFMA(_, a, b, c) =>
        evaluate(a, bindings, precision).flatMap { x =>
          evaluate(b, bindings, precision).flatMap { y =>
            evaluate(c, bindings, precision).map { z =>
              val rounded = precision match {
                case FPPrecision.Binary32 =>
                  Math.fma(x.rounded.toFloat, y.rounded.toFloat, z.rounded.toFloat).toDouble
                case FPPrecision.Binary64 => Math.fma(x.rounded, y.rounded, z.rounded)
              }
              Value(rounded, x.exact.zip(y.exact).zip(z.exact).map { case ((p, q), s) => p * q + s })
            }
          }
        }

      // Integers are exact, since Stainless checks for overflow. Converting one above 2^53 to
      // `Double`, or above 2^24 to `Float`, rounds, which the two values then show.
      case IntLit(n) => Right(Value(n.toDouble, Some(Rational(n, 1))))
      case Plus(l, r) => evaluateIntegerArithmetic(_ + _)(l, r)
      case Minus(l, r) => evaluateIntegerArithmetic(_ - _)(l, r)
      case Times(l, r) => evaluateIntegerArithmetic(_ * _)(l, r)
      case UMinus(a) => evaluate(a, bindings, precision).map(v => Value(-v.rounded, v.exact.map(-_)))
      case BVWideningCast(inner, _) => evaluate(inner, bindings, precision)
      case FPCast(_, 24, _, inner) if isIntegral(inner) =>
        evaluate(inner, bindings, precision).map(v => Value(v.exact.get.num.toFloat.toDouble, v.exact))
      case FPCast(_, _, _, inner) if isIntegral(inner) => evaluate(inner, bindings, precision)

      case Let(vd, value, body) =>
        evaluate(value, bindings, precision)
          .flatMap(v => evaluate(body, bindings + (vd.id -> v), precision))

      case v: Variable =>
        bindings.get(v.id).toRight(s"'${v.id.name}' is not bindings in a value with no inputs")

      // The exact value must be a fraction, and these functions do not give one.
      case TranscendentalFunctionCall(f, _) =>
        Left(s"a value with no inputs calls '${f.symbol}', which is not a fraction")

      case other =>
        Left(s"'$other' cannot be evaluated without inputs")
    }
  }
}

/** A comparison a conditional branches on: `lhs < rhs` when strict, `lhs <= rhs` otherwise.
  *
  * @param integral whether it compares two integers
  */
case class Guard(lhs: Expr, rhs: Expr, strict: Boolean, integral: Boolean = false)

private[roundoff] object Inequality {
  def unapply(e: Expr): Option[Guard] = e match {
    case FPLessThan(l, r)      => Some(Guard(l, r, strict = true))
    case FPLessEquals(l, r)    => Some(Guard(l, r, strict = false))
    case FPGreaterThan(l, r)   => Some(Guard(r, l, strict = true))
    case FPGreaterEquals(l, r) => Some(Guard(r, l, strict = false))
    case LessThan(l, r)        => Some(Guard(l, r, strict = true, integral = true))
    case LessEquals(l, r)      => Some(Guard(l, r, strict = false, integral = true))
    case GreaterThan(l, r)     => Some(Guard(r, l, strict = true, integral = true))
    case GreaterEquals(l, r)   => Some(Guard(r, l, strict = false, integral = true))
    case _ => None
  }
}

case class BranchChoice(guard: Int, taken: Boolean)

case class ProgramPath(choices: Seq[BranchChoice], leaf: Expr)

/** Splits a function body into the straight-line paths through it. */
object PathExtractor {

  /** A chain of `let` bindings, outermost first. */
  private type Scope = Seq[(ValDef, Expr)]

  /** The guards of `body` and every path through them.
    */
  def apply(body: Expr, timeLimit: TimeLimit = TimeLimit.never)
    : Either[String, (Seq[Guard], Seq[ProgramPath])] = {
    val guards = ArrayBuffer.empty[Guard]
    val paths = ArrayBuffer.empty[ProgramPath]

    def collectPaths(e: Expr, scope: Scope, choices: Seq[BranchChoice]): Either[String, Unit] = e match {
      case Let(vd, value, body) => collectPaths(body, scope :+ (vd, value), choices)

      case IfExpr(condition, thenBranch, elseBranch) =>
        val (conditionScope, logic) =
          resolveCondition(condition, scope.map { case (vd, value) => vd.id -> value }.toMap)
        val inner = scope ++ conditionScope

        logic match {
          case And(conjuncts) if conjuncts.size > 1 =>
            collectPaths(IfExpr(conjuncts.head, IfExpr(andJoin(conjuncts.tail), thenBranch, elseBranch),
                                elseBranch), inner, choices)
          case Or(disjuncts) if disjuncts.size > 1 =>
            collectPaths(IfExpr(disjuncts.head, thenBranch,
                                IfExpr(orJoin(disjuncts.tail), thenBranch, elseBranch)), inner,
                         choices)
          case And(Seq(single)) => collectPaths(IfExpr(single, thenBranch, elseBranch), inner, choices)
          case Or(Seq(single)) => collectPaths(IfExpr(single, thenBranch, elseBranch), inner, choices)
          case Not(negated) => collectPaths(IfExpr(negated, elseBranch, thenBranch), inner, choices)


          case FPEquals(lhs, rhs) =>
            collectPaths(IfExpr(And(FPLessEquals(lhs, rhs), FPGreaterEquals(lhs, rhs)),
                                thenBranch, elseBranch), inner, choices)
          case Equals(lhs, rhs) =>
            collectPaths(IfExpr(And(LessEquals(lhs, rhs), GreaterEquals(lhs, rhs)),
                                thenBranch, elseBranch), inner, choices)

          case BooleanLiteral(true) => collectPaths(thenBranch, inner, choices)
          case BooleanLiteral(false) => collectPaths(elseBranch, inner, choices)

          case Inequality(guard) =>
            val index = guards.size
            val closed = guard.copy(lhs = wrapWithLetBindings(inner, guard.lhs),
                                    rhs = wrapWithLetBindings(inner, guard.rhs))
            guards += closed
            collectPaths(thenBranch, inner, choices :+ BranchChoice(index, taken = true)).flatMap(_ =>
              collectPaths(elseBranch, inner, choices :+ BranchChoice(index, taken = false)))

          case other => Left(s"the guard '$other' is not a comparison of numbers")
        }

      case leaf =>
        timeLimit.check()
        paths += ProgramPath(choices, wrapWithLetBindings(scope, leaf))
        Right(())
    }

    collectPaths(body, Seq.empty, Seq.empty).map(_ => (guards.toSeq, paths.toSeq))
  }

  /** Resolves the let bindings inside a condition of an if-then-else statement*/
  private def resolveCondition(condition: Expr, bindings: Map[Identifier, Expr])
    : (Scope, Expr) = condition match {
    case Let(vd, value, body) =>
      val (inner, logic) = resolveCondition(body, bindings + (vd.id -> value))
      ((vd, value) +: inner, logic)
    case v: Variable =>
      bindings.get(v.id).map(resolveCondition(_, bindings)).getOrElse((Seq.empty, v))
    case other => (Seq.empty, other)
  }

  private def wrapWithLetBindings(scope: Scope, expr: Expr): Expr =
    scope.foldRight(expr) { case ((vd, value), kept) =>
      if (exprOps.variablesOf(kept).exists(_.id == vd.id)) Let(vd, value, kept) else kept
    }
}

enum FPPrecision(val exponent: Int, val significand: Int,
                 val daisyName: String, val fptaylorRounding: String) {
  case Binary32 extends FPPrecision(8, 24, "Float32", "rnd32")
  case Binary64 extends FPPrecision(11, 53, "Float64", "rnd64")
}

/** The precision a function runs at, and the range its precondition gives each input. */
case class InputSpec(precision: FPPrecision, ranges: Map[Identifier, (Double, Double)]) {

  /** Why these inputs cannot be analysed: one of them has no range. */
  def missingRangeMessage(inputs: Seq[Identifier]): Option[String] =
    inputs.find(!ranges.contains(_)).map(id =>
      s"no range in the precondition for '${id.name}'; add bounds of the form 'lo <= x && x <= hi'")

  /** The inputs of `expr` in order. */
  def rangedInputs(expr: Expr): Either[String, Seq[Variable]] = {
    val inputs = exprOps.variablesOf(expr).toSeq.sortBy(_.id.globalId)
    if (inputs.isEmpty) Left("no floating-point inputs to bound")
    else missingRangeMessage(inputs.map(_.id)).toLeft(inputs)
  }
}

/** Reads what the precondition says about each input, and narrows it along a path. */
object InputRanges {

  /** The bounds the precondition gives one input. */
  private case class Bounds(low: Option[Double], high: Option[Double]) {
    def intersectLow(d: Double) = Bounds(Some(low.map(math.max(_, d)).getOrElse(d)), high)
    def intersectHigh(d: Double) = Bounds(low, Some(high.map(math.min(_, d)).getOrElse(d)))
  }

  /** The precision of `body` and the range the precondition gives each input. */
  def inputSpecOf(fd: FunDef, body: Expr, flattening: FlattenedParameters)(using Symbols)
    : Either[String, InputSpec] =
    uniformPrecision(body).map { precision =>
      val bounds = extractRanges(assumptions(fd, flattening))
      // A half-open or empty range is dropped, so the input is reported as unranged.
      val ranges = bounds.collect {
        case (id, Bounds(Some(low), Some(high))) if low <= high => id -> (low, high)
      }
      InputSpec(precision, ranges)
    }

  /** Why an integer that `body` converts to floating point may round, if it may: a `Double`
    * holds every integer up to 2^53 only, and a `Float` up to 2^24. Checked with interval
    * arithmetic over the input ranges, except for an `Int` converted to `Double`, which always
    * fits.
    */
  def inexactIntegerConversion(body: Expr, spec: InputSpec)(using Symbols): Option[String] = {
    def mayExceedExactIntegers(converted: Expr, significand: Int, integerLets: Seq[(ValDef, Expr)])
      : Option[String] = {
      val closed = withLets(integerLets, converted)
      val inputs = exprOps.variablesOf(closed).toSeq
      val realVariables =
        inputs.map(v => v.id -> inox.trees.Variable(v.id, inox.trees.RealType(), Seq.empty)).toMap
      val exactUpTo = Rational(BigInt(2).pow(significand), BigInt(1))
      val integer = if (converted.getType == Int64Type()) "Long" else "Int"
      val floatingPoint = if (significand == 24) "Float" else "Double"
      spec.missingRangeMessage(inputs.map(_.id)) orElse Option.unless(
        RealEncoder(closed, realVariables)
          .exists(IntervalChecks.boundedBy(_, spec.ranges, exactUpTo)))(
        s"a '$integer' converted to '$floatingPoint' may be larger than 2^$significand, beyond " +
        s"which a '$floatingPoint' does not hold every integer; narrow its range in the precondition")
    }

    def firstInexactConversion(e: Expr, integerLets: Seq[(ValDef, Expr)]): Option[String] = e match {
      case Let(vd, value, rest) =>
        val reachable = if (isIntegerType(vd.tpe)) integerLets :+ (vd -> value) else integerLets
        firstInexactConversion(value, integerLets) orElse firstInexactConversion(rest, reachable)
      case FPCast(_, significand, _, inner) if isIntegerType(inner.getType) &&
          !(inner.getType == Int32Type() && significand >= 31) =>
        mayExceedExactIntegers(inner, significand, integerLets)
      case Operator(es, _) => es.view.flatMap(firstInexactConversion(_, integerLets)).headOption
    }

    firstInexactConversion(body, Seq.empty)
  }

  /** Invariants of the parameters and preconditions of `fd` */
  def assumptions(fd: FunDef, flattening: FlattenedParameters)(using Symbols): Expr = {
    val invariants = flattening.enclosingObjects.flatMap(invariantOf)
    val stated = (fd.precondition.toSeq ++ invariants).map(Preprocessor.normalisedCondition)
    flattening.withFieldReadsReplaced(andJoin(stated))
  }

  /** For the branches a path takes, the ranges of `spec` narrowed by their guards, or `None`
    * when some input is left no value, so the rounded program never takes the path.
    *
    * Only guards between an input and a literal narrow, a side without inputs being the
    * literal the program computes for it. With rounded inputs, the literal moves one step
    * outward, since the input is rounded before it is compared. A strict comparison counts as
    * non-strict, except between integers (`n < 5` is `n <= 4`).
    *
    * With `forBothRuns`, a side without inputs counts only when it is computed exactly, so
    * that `None` means neither run takes the path.
    */
  def rangesAlongPath(spec: InputSpec, guards: Seq[Guard], exactInputs: Boolean,
                      forBothRuns: Boolean = false)
    : Seq[BranchChoice] => Option[InputSpec] = {
    def literalAtPrecision(d: Double): Expr = spec.precision match {
      case FPPrecision.Binary32 => Float32Literal(d.toFloat)
      case FPPrecision.Binary64 => Float64Literal(d)
    }
    // An integer side narrows by its own rule.
    def asLiteralIfConstant(side: Expr): Expr = withoutLets(side) match {
      case lit @ FPLit(_) => lit
      case integer if isIntegral(integer) => integer
      case computed =>
        ConstantEvaluator.evaluate(computed, Map.empty, spec.precision).toOption
          .filter(v => v.rounded.isFinite &&
                       (!forBothRuns || v.exact.exists(exact => Fraction(v.rounded).contains(exact))))
          .map(v => literalAtPrecision(v.rounded))
          .getOrElse(computed)
    }

    // Resolved once per guard: in a chain of `let`s, an operand holds everything before it.
    val resolvedOperands = scala.collection.mutable.Map.empty[Int, (Expr, Expr)]
    def resolvedOperandsOf(guard: Int): (Expr, Expr) =
      resolvedOperands.getOrElseUpdate(guard,
        (asLiteralIfConstant(guards(guard).lhs), asLiteralIfConstant(guards(guard).rhs)))

    def oneStepOutward(d: Double, upper: Boolean): Double =
      if (exactInputs) d
      else spec.precision match {
        case FPPrecision.Binary32 =>
          (if (upper) Math.nextUp(d.toFloat) else Math.nextDown(d.toFloat)).toDouble
        case FPPrecision.Binary64 => if (upper) Math.nextUp(d) else Math.nextDown(d)
      }

    choices => choices.foldLeft(Option(spec.ranges)) {
      case (None, _) => None
      case (Some(ranges), choice) =>
        val guard = guards(choice.guard)
        val (lhs, rhs) = resolvedOperandsOf(choice.guard)
        // Not taking `lhs < rhs` means `rhs <= lhs`: an input compared with a literal is
        // never NaN.
        val (small, large, strict) =
          if (choice.taken) (lhs, rhs, guard.strict) else (rhs, lhs, !guard.strict)

        // The input, whether the literal is an upper bound, and the bound.
        val bound: Option[(Identifier, Boolean, Double)] = (small, large) match {
          case (v: Variable, FPLit(d)) => Some((v.id, true, oneStepOutward(d, upper = true)))
          case (FPLit(d), v: Variable) => Some((v.id, false, oneStepOutward(d, upper = false)))
          case (v: Variable, IntLit(c)) => Some((v.id, true, (if (strict) c - 1 else c).toDouble))
          case (IntLit(c), v: Variable) => Some((v.id, false, (if (strict) c + 1 else c).toDouble))
          case _ => None
        }

        bound match {
          case Some((id, upper, d)) if ranges.contains(id) =>
            val (low, high) = ranges(id)
            val (tightLow, tightHigh) =
              if (upper) (low, math.min(high, d)) else (math.max(low, d), high)

            Option.when(tightLow <= tightHigh)(ranges.updated(id, (tightLow, tightHigh)))

          case _ => Some(ranges)
        }
    }.map(ranges => spec.copy(ranges = ranges))
  }

  /** The bounds a precondition gives each input, read from comparisons with constants. */
  private def extractRanges(precondition: Expr): Map[Identifier, Bounds] = {
    var found = Map.empty[Identifier, Bounds].withDefaultValue(Bounds(None, None))

    def readBounds(e: Expr, constants: Map[Identifier, Double]): Unit = {
      // The frontend binds each operand to a name, so `-10 <= x` arrives as a comparison of
      // two variables, one of which holds a constant.
      object Constant {
        def unapply(e: Expr): Option[Double] = e match {
          case FPLit(d) => Some(d)
          case IntLit(n) => Some(n.toDouble)
          case v: Variable => constants.get(v.id)
          case _ => None
        }
      }
      object Input {
        def unapply(e: Expr): Option[Identifier] = e match {
          case v: Variable if !constants.contains(v.id) => Some(v.id)
          case _ => None
        }
      }

      e match {
        case And(parts) => parts.foreach(readBounds(_, constants))
        case Not(Not(e)) => readBounds(e, constants)

        case Let(vd, Constant(d), body) => readBounds(body, constants + (vd.id -> d))
        // A bound on a copy of an input is a bound on the input.
        case Let(vd, v: Variable, body) =>
          readBounds(exprOps.replaceFromSymbols(Map(vd -> v), body), constants)
        case Let(_, _, body) => readBounds(body, constants)

        // A strict bound counts as non-strict, except between integers, where it is the next
        // integer in.
        case Inequality(Guard(Constant(d), Input(id), strict, integral)) =>
          found = found.updated(id, found(id).intersectLow(if (strict && integral) d + 1 else d))
        case Inequality(Guard(Input(id), Constant(d), strict, integral)) =>
          found = found.updated(id, found(id).intersectHigh(if (strict && integral) d - 1 else d))

        case _ => ()
      }
    }

    readBounds(precondition, Map.empty)
    found
  }

  def computesFloatingPoint(body: Expr)(using Symbols): Boolean = floatingPointTypes(body).nonEmpty

  /** The one precision `body` computes in. The analyzers cannot mix precisions. */
  private def uniformPrecision(body: Expr)(using Symbols): Either[String, FPPrecision] =
    floatingPointTypes(body).toSeq.sortBy(t => (t.exponent, t.significand)) match {
      case Seq() => Left("no floating-point values")
      case Seq(t) =>
        FPPrecision.values.find(p => p.exponent == t.exponent && p.significand == t.significand).toRight(
        s"unsupported precision (exponent ${t.exponent}, significand ${t.significand})")
      case several => Left("mixed floating-point precisions: " +
        several.map(t => s"(${t.exponent},${t.significand})").mkString(", "))
    }

  private def floatingPointTypes(body: Expr)(using Symbols): Set[FPType] =
    exprOps.collect[FPType] { e =>
      val declared = e match {
        case Let(vd, _, _) => Seq(vd.tpe)
        case _ => Seq.empty
      }
      (declared :+ e.getType).collect { case t: FPType => t }.toSet
    }(body)
}