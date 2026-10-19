/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification
package roundoff

import trees._
import inox.{trees => real}
import inox.trees.{Expr => RExpr}

/** Two leaves compared across the guard where their paths split.
  *
  * `choices` are the branches both leaves take below that guard. All of them are relaxed by
  * their guard error, because the region does not know which side the exact run took.
  */
case class LeafPair(taken: Int, untaken: Int, choices: Seq[BranchChoice], difference: real.Expr)

/** Where reading one guard the wrong way can move the result: the conditions above the guard,
  * and every pair of leaves on its two sides.
  */
case class GuardRegion(
  guard: Int,
  vars: Seq[real.ValDef],
  shared: Seq[real.Expr],
  pairs: Seq[LeafPair]
)

/** Turns the paths of one function into real-arithmetic problems for Ibex. */
object GuardRegions {

  /** One region per guard, and per guard the expressions that stand for `lhs - rhs`.
    *
    * @param normalise whether to rewrite a difference of two leaves as a multiple of a guard
    *                  difference where possible (see [[Normalisation]])
    */
  def encode(guards: Seq[Guard], paths: Seq[ProgramPath], spec: InputSpec, normalise: Boolean)
    : Either[String, (Seq[Seq[real.Expr]], Seq[GuardRegion])] = {

    val inputs = (paths.map(_.leaf) ++ guards.flatMap(g => Seq(g.lhs, g.rhs)))
      .flatMap(exprOps.variablesOf)
      .distinctBy(_.id)
      .sortBy(_.id.globalId)

    // The real variables keep the identifiers of the floating-point ones, so that a
    // counter-example stays readable. The two kinds never appear in the same query.
    val realVariables: Map[Identifier, real.Variable] =
      inputs.map(v => v.id -> real.Variable(v.id, real.RealType(), Seq.empty)).toMap

    for {
      _ <- spec.missingRange(inputs.map(_.id)).toLeft(())
      leaves <- traverse(paths)(path => RealEncoder(path.leaf, realVariables))
      guardOperands <- traverse(guards) { guard =>
        for {
          lhs <- RealEncoder(guard.lhs, realVariables)
          rhs <- RealEncoder(guard.rhs, realVariables)
        } yield (lhs, rhs)
      }
    } yield {
      val ranges = inputs.flatMap { input =>
        val (low, high) = spec.ranges(input.id)
        Seq(real.LessEquals(Fraction.toExpr(low), realVariables(input.id)),
            real.LessEquals(realVariables(input.id), Fraction.toExpr(high)))
      }

      val guardDifferences = guardOperands.map { case (lhs, rhs) => real.Minus(lhs, rhs) }

      // Memoised, because every objective is a difference of two leaves and a function has
      // far fewer distinct leaves than paths.
      val divisors = scala.collection.mutable.Map.empty[real.Expr, Option[(Int, real.Expr)]]

      /** The guard that `e` is a multiple of, and the quotient, if there is one. */
      def divisorOf(e: real.Expr): Option[(Int, real.Expr)] =
        if (!normalise) None
        else divisors.getOrElseUpdate(e, Normalisation.divisor(e, guardDifferences))

      // A guard difference that divides some objective gets a variable of its own, tied to the
      // difference by an equation in every region. The band is then a range on one variable
      // instead of a relation between inputs, which Ibex can read directly instead of
      // bisecting towards it.
      //
      // Only guards that divide an objective get a name: each name costs a variable and a
      // nonlinear constraint in every region. On `OrientationIndexFilter`, naming all 22 guards
      // took Ibex from 1.5 s to 36 s for a bound tighter by a thousandth.
      val guardNames: Map[Int, real.Variable] = {
        val distinct = leaves.distinct
        val divided = for {
          reference <- distinct
          other <- distinct
          if other != reference
          (guard, _) <- divisorOf(real.Minus(other, reference))
        } yield guard

        divided.distinct.map { guard =>
          guard -> real.Variable.fresh(s"guard$guard", real.RealType())
        }.toMap
      }

      /** The named guards, in the order a region declares them. */
      val namedGuards = guardNames.toSeq.sortBy(_._1)

      /** `e` as a multiple of a named guard variable, if one divides it. */
      def overNamedGuard(e: real.Expr): Option[real.Expr] =
        Normalisation.divisor(e, namedGuards.map { case (guard, _) => guardDifferences(guard) })
          .map { case (which, quotient) => real.Times(quotient, namedGuards(which)._2) }

      // The band of a guard is stated on its difference and on its name. On the difference, it
      // keeps the inputs of a witness near the boundary; on the name, it lets Ibex read the
      // objective directly.
      //
      // A guard that is a multiple of a named one gets that name too. Otherwise `a * b == c`,
      // which becomes the two guards `a*b <= c` and `c <= a*b`, bounds the second guard's
      // objective by bisection: 0.031 where the truth is 1.3e-15.
      val differencesPerGuard: Seq[Seq[real.Expr]] =
        guardDifferences.zipWithIndex.map { case (difference, guard) =>
          Seq(difference) ++ guardNames.get(guard).orElse(overNamedGuard(difference))
        }

      val box = ranges ++ namedGuards.map { case (guard, name) =>
        real.Equals(name, guardDifferences(guard))
      }

      /** `e` written over the guard variable it is a multiple of, where there is one. */
      def objective(e: real.Expr): real.Expr =
        divisorOf(e).map { case (guard, quotient) => real.Times(quotient, guardNames(guard)) }
          .getOrElse(e)

      /** What one branch choice says about the guard's operands, over the reals. */
      def pathCondition(choice: BranchChoice): real.Expr = {
        val (lhs, rhs) = guardOperands(choice.guard)
        // Over the reals, negating a comparison swaps its sides and its strictness.
        (choice.taken, guards(choice.guard).strict) match {
          case (true, false) => real.LessEquals(lhs, rhs)
          case (true, true) => real.LessThan(lhs, rhs)
          case (false, false) => real.LessThan(rhs, lhs)
          case (false, true) => real.LessEquals(rhs, lhs)
        }
      }

      val vars = inputs.map(input => realVariables(input.id).toVal) ++ namedGuards.map(_._2.toVal)

      /** The region of one guard, or nothing when fewer than two leaves lie below it.
        *
        * Every path through a guard reaches it through the same branches, so any of them
        * gives the conditions above it.
        */
      def regionOf(guard: Int): Option[GuardRegion] = {
        def positionIn(path: ProgramPath): Int = path.choices.indexWhere(_.guard == guard)

        val below = paths.zipWithIndex.filter { case (path, _) => positionIn(path) >= 0 }

        Option.when(below.size > 1) {
          val (first, _) = below.head
          val shared = box ++ first.choices.take(positionIn(first)).map(pathCondition)
          val (taken, untaken) =
            below.partition { case (path, _) => path.choices(positionIn(path)).taken }

          def choicesBelowGuard(path: ProgramPath): Seq[BranchChoice] =
            path.choices.drop(positionIn(path) + 1)

          val pairs = for {
            (takenPath, takenLeaf) <- taken
            (untakenPath, untakenLeaf) <- untaken
            // Two leaves that compute the same thing cannot diverge.
            if takenPath.leaf != untakenPath.leaf
            // The rounded program never takes an unreachable path. The exact program can, so
            // an unreachable leaf can still diverge from a reachable one, but two cannot.
            if takenPath.reachable || untakenPath.reachable
          } yield LeafPair(
            takenLeaf, untakenLeaf,
            choicesBelowGuard(takenPath) ++ choicesBelowGuard(untakenPath),
            objective(real.Minus(leaves(untakenLeaf), leaves(takenLeaf))))

          GuardRegion(guard, vars, shared, pairs)
        }
      }

      (differencesPerGuard, guards.indices.flatMap(regionOf))
    }
  }
}

/** Writes a floating-point expression as the real-arithmetic expression it approximates. */
private[roundoff] object RealEncoder {

  import inox.trees.{Plus, Minus, Times, Division, UMinus}

  def apply(e: Expr, realVariables: Map[Identifier, inox.trees.Variable])
    : Either[String, inox.trees.Expr] = {

    def binary(build: (inox.trees.Expr, inox.trees.Expr) => inox.trees.Expr, l: Expr, r: Expr) =
      apply(l, realVariables).flatMap(a => apply(r, realVariables).map(build(a, _)))

    e match {
      case v: Variable => realVariables.get(v.id).toRight(s"unbound variable '${v.id.name}'")
      case FPLit(d) =>
        Fraction(d).map(r => inox.trees.FractionLiteral(r.num, r.den))

      // Rounding modes do not matter: this is the exact computation.
      case FPAdd(_, l, r) => binary(Plus(_, _), l, r)
      case FPSub(_, l, r) => binary(Minus(_, _), l, r)
      case FPMul(_, l, r) => binary(Times(_, _), l, r)
      case FPDiv(_, l, r) => binary(Division(_, _), l, r)
      case FPUMinus(a) => apply(a, realVariables).map(UMinus(_))
      case FPFMA(_, a, b, c) =>
        for {
          product <- binary(Times(_, _), a, b)
          addend <- apply(c, realVariables)
        } yield Plus(product, addend)

      case Let(vd, value, body) =>
        val realVar = inox.trees.Variable(vd.id, inox.trees.RealType(), Seq.empty)

        for {
          realValue <- apply(value, realVariables)
          realBody <- apply(body, realVariables + (vd.id -> realVar))
        } yield inox.trees.Let(realVar.toVal, realValue, realBody)

      case TranscendentalFunctionCall(f, args) =>
        traverse(args)(apply(_, realVariables)).flatMap(realCall(f, _))

      case _: IfExpr =>
        Left("a conditional appears inside an expression, and only conditionals that shape " +
          "the body are supported")

      case other =>
        Left(s"no real-arithmetic equivalent for ${other.getClass.getSimpleName}")
    }
  }

  /** The real-arithmetic counterpart of a call. Only Ibex among the solvers evaluates these. */
  private def realCall(f: TranscendentalFunction, args: Seq[inox.trees.Expr])
    : Either[String, inox.trees.Expr] = {
    import inox.trees.{FractionLiteral, RealAcos, RealAsin, RealAtan, RealCos, RealExp,
                       RealLog, RealPow, RealSin, RealSqrt, RealTan}

    (f, args) match {
      case (TranscendentalFunction.Sqrt, Seq(a)) => Right(RealSqrt(a))
      case (TranscendentalFunction.Exp, Seq(a)) => Right(RealExp(a))
      case (TranscendentalFunction.Log, Seq(a)) => Right(RealLog(a))
      case (TranscendentalFunction.Sin, Seq(a)) => Right(RealSin(a))
      case (TranscendentalFunction.Cos, Seq(a)) => Right(RealCos(a))
      case (TranscendentalFunction.Tan, Seq(a)) => Right(RealTan(a))
      case (TranscendentalFunction.Asin, Seq(a)) => Right(RealAsin(a))
      case (TranscendentalFunction.Acos, Seq(a)) => Right(RealAcos(a))
      case (TranscendentalFunction.Atan, Seq(a)) => Right(RealAtan(a))

      // Ibex computes any other power as exp(y * log(x)), which is only valid for a
      // positive base, so other exponents are refused.
      case (TranscendentalFunction.Pow, Seq(base, exponent @ FractionLiteral(_, one)))
          if one == 1 =>
        Right(RealPow(base, exponent))
      case (TranscendentalFunction.Pow, _) =>
        Left("a power on a branching path needs a whole-number exponent")

      case _ => Left(s"'${f.symbol}' was given ${args.size} arguments")
    }
  }
}

/** A polynomial with rational coefficients, used to compare expressions up to algebra.
  *
  * Two expressions that compute the same thing in different ways become the same polynomial.
  * This is how a guard is recognised inside a leaf that never mentions it: for example,
  * `0.95 * limit - 0.95 * apparent` is `-0.95` times `apparent - limit`.
  *
  * Anything that is not `+`, `-` or `*` (a root, a call, a division) is one opaque term.
  */
private[roundoff] final case class Poly(terms: Map[Poly.Mono, Rational]) {
  def isZero: Boolean = terms.isEmpty

  def +(o: Poly): Poly = Poly.merge(terms, o.terms)
  def -(o: Poly): Poly = this + -o
  def unary_- : Poly = Poly(terms.view.mapValues(-_).toMap)

  def *(o: Poly): Poly =
    terms.foldLeft(Poly.zero) { case (outer, (m1, c1)) =>
      o.terms.foldLeft(outer) { case (inner, (m2, c2)) =>
        inner + Poly(Map(Poly.ordered(m1 ++ m2) -> (c1 * c2)))
      }
    }
}

private[roundoff] object Poly {

  /** A product of opaque terms, sorted so that equal products are equal sequences. */
  type Mono = Seq[RExpr]

  /** The most terms a polynomial may have. Expanding products and bindings can make a
    * polynomial very large; past this size the expression is used as written.
    */
  private val limit = 512

  val zero: Poly = Poly(Map.empty)

  def constant(r: Rational): Poly = if (r.isZero) zero else Poly(Map(Seq.empty[RExpr] -> r))
  def opaque(e: RExpr): Poly = Poly(Map(Seq(e) -> Rational.one))

  private def key(a: RExpr): String = a.toString
  private[roundoff] def ordered(m: Mono): Mono = m.sortBy(key)

  private def merge(a: Map[Mono, Rational], b: Map[Mono, Rational]): Poly =
    Poly((a.keySet ++ b.keySet).view
      .map(m => m -> (a.getOrElse(m, Rational.zero) + b.getOrElse(m, Rational.zero)))
      .filterNot(_._2.isZero)
      .toMap)

  /** Reads an expression as a polynomial, or nothing where it grows past what is worth it. */
  def of(e: RExpr): Option[Poly] = {
    import inox.trees.*

    def capped(p: Poly): Option[Poly] = Option.when(p.terms.size <= limit)(p)

    /** Both sides read, then combined, so long as the result is still worth carrying. */
    def combine(a: RExpr, b: RExpr)(f: (Poly, Poly) => Poly): Option[Poly] =
      rec(a).flatMap(x => rec(b).flatMap(y => capped(f(x, y))))

    def rec(e: RExpr): Option[Poly] = e match {
      case Plus(a, b) => combine(a, b)(_ + _)
      case Minus(a, b) => combine(a, b)(_ - _)
      case Times(a, b) => combine(a, b)(_ * _)
      case UMinus(a) => rec(a).map(-_)
      case FractionLiteral(n, d) => Some(constant(Rational.of(n, d)))

      // A binding is written out, since the same value reached through one is the same term.
      case Let(vd, value, body) =>
        rec(inox.trees.exprOps.replaceFromSymbols(Map(vd -> value), body))

      case other => Some(opaque(other))
    }

    rec(e)
  }

  /** A total order on monomials: by degree, then by their terms. */
  private def compare(a: Mono, b: Mono): Int =
    if (a.size != b.size) a.size.compare(b.size)
    else a.map(key).zip(b.map(key)).collectFirst { case (x, y) if x != y => x.compare(y) }.getOrElse(0)

  private def leading(p: Poly): Option[(Mono, Rational)] =
    p.terms.keys.reduceOption((x, y) => if (compare(x, y) >= 0) x else y).map(m => m -> p.terms(m))

  /** `a` with one of each term of `b` taken out, where `b` divides it. */
  private def without(a: Mono, b: Mono): Option[Mono] =
    b.foldLeft(Option(a)) { (left, x) =>
      left.flatMap { rest =>
        val at = rest.indexWhere(_ == x)
        Option.when(at >= 0)(rest.patch(at, Nil, 1))
      }
    }

  /** `p` written as `quotient * g + remainder`, by polynomial long division. */
  def divide(p: Poly, g: Poly): (Poly, Poly) = leading(g) match {
    case None => (zero, p)
    case Some((gm, gc)) =>
      var rest = p
      var quotient = zero
      var remainder = zero
      var steps = 0

      while (!rest.isZero && steps < limit) {
        steps += 1
        val (m, c) = leading(rest).get
        without(m, gm) match {
          case Some(q) =>
            val step = Poly(Map(ordered(q) -> (c / gc)))
            quotient = quotient + step
            rest = rest - (step * g)
          case None =>
            remainder = remainder + Poly(Map(m -> c))
            rest = Poly(rest.terms - m)
        }
      }

      (quotient, remainder + rest)
  }

  /** The expression a polynomial stands for, with its terms in a fixed order. */
  def toExpr(p: Poly): RExpr = {
    import inox.trees.*

    if (p.isZero) FractionLiteral(0, 1)
    else p.terms.toSeq
      .sortWith { case ((m1, _), (m2, _)) => compare(m1, m2) > 0 }
      .map { case (m, c) =>
        val coefficient: RExpr = FractionLiteral(c.num, c.den)
        if (m.isEmpty) coefficient
        else if (c.isOne) m.reduce(Times(_, _))
        else Times(coefficient, m.reduce(Times(_, _)))
      }
      .reduce(Plus(_, _))
  }
}

/** Finds objectives that are a multiple of a guard difference.
  *
  * Ibex searches a box, one interval per variable, and a box cannot express that two variables
  * are nearly equal. So the band `|temperature - setpoint| <= e` does not help when the
  * objective is evaluated, and Ibex has to bisect both variables about fifty times each.
  *
  * Giving the difference a variable of its own makes the band an interval of that variable.
  * An objective written over that variable is then bounded in one step.
  */
private[roundoff] object Normalisation {

  /** The index of the first difference that divides `objective` exactly, and the quotient.
    *
    * A division with a remainder is not used, even though `q * name + r` is equally correct:
    * `q * name` and `r` can each be much larger than their sum, and Ibex cannot see that they
    * cancel. On `Clamp`, using a remainder made the bound go from 1.7e-13 to 1.2.
    */
  def divisor(objective: RExpr, differences: Seq[RExpr]): Option[(Int, RExpr)] = {
    val exact = for {
      whole <- Poly.of(objective).toSeq
      (difference, k) <- differences.zipWithIndex
      guard <- Poly.of(difference).filterNot(_.isZero).toSeq
      (quotient, remainder) = Poly.divide(whole, guard)
      if remainder.isZero && !quotient.isZero
    } yield (k, Poly.toExpr(quotient))

    exact.headOption
  }
}
