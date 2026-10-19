/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification
package roundoff

import trees._

enum FPPrecision(val exponent: Int, val significand: Int,
                 val daisyName: String, val fptaylorRounding: String) {
  case Binary32 extends FPPrecision(8, 24, "Float32", "rnd32")
  case Binary64 extends FPPrecision(11, 53, "Float64", "rnd64")
}

object FPPrecision {
  def fromType(tpe: Type): Option[FPPrecision] = tpe match {
    case FPType(8, 24)  => Some(FPPrecision.Binary32)
    case FPType(11, 53) => Some(FPPrecision.Binary64)
    case _ => None
  }
}

/** The precision a function runs at, and the range its precondition gives each input. */
case class InputSpec(precision: FPPrecision, ranges: Map[Identifier, (Double, Double)]) {

  /** Why these inputs cannot be analysed: one of them has no range. */
  def missingRange(inputs: Seq[Identifier]): Option[String] =
    inputs.find(!ranges.contains(_)).map(id =>
      s"no range in the precondition for '${id.name}'; add bounds of the form 'lo <= x && x <= hi'")

  /** The inputs of `expr` in a fixed order, or why it cannot be sent to an analyzer. */
  def rangedInputs(expr: Expr): Either[String, Seq[Variable]] = {
    val inputs = exprOps.variablesOf(expr).toSeq.sortBy(_.id.globalId)
    if (inputs.isEmpty) Left("no floating-point inputs to bound")
    else missingRange(inputs.map(_.id)).toLeft(inputs)
  }
}

/** Reads what the precondition says about each input, and narrows it along a path. */
object InputRanges {

  /** The bounds the precondition gives one input, either of which may be missing.
    *
    * Two bounds on the same side are intersected, because the precondition is a conjunction:
    * `x <= 2 && x <= 1` leaves `x <= 1`. Preconditions often state a range twice, once loosely
    * and once tightly, so keeping the tighter bound matters.
    */
  private case class Bounds(low: Option[Double], high: Option[Double]) {
    def withLow(d: Double) = Bounds(Some(low.map(math.max(_, d)).getOrElse(d)), high)
    def withHigh(d: Double) = Bounds(low, Some(high.map(math.min(_, d)).getOrElse(d)))
  }

  private object Bounds { val empty = Bounds(None, None) }

  /** The precision of `body` and the range the precondition gives each input. */
  def specOf(fd: FunDef, body: Expr, flattening: ParameterFlattening)(using Symbols)
    : Either[String, InputSpec] =
    uniformPrecision(body).map { precision =>
      val bounds = extractRanges(assumptions(fd, flattening))
      // A half-open or empty range is dropped, so the input is reported as unranged. An empty
      // range comes from a contradictory precondition, which the reachability check reports.
      val ranges = bounds.collect {
        case (id, Bounds(Some(low), Some(high))) if low <= high => id -> (low, high)
      }
      InputSpec(precision, ranges)
    }

  /** The precondition of `fd` and the invariants of its parameters, over the flattened
    * parameters.
    */
  def assumptions(fd: FunDef, flattening: ParameterFlattening)(using Symbols): Expr = {
    val stated = fd.precondition.map(Preprocessor.stripAnnotations).toSeq ++ invariants(flattening)
    flattening.substituteAccessPaths(andJoin(stated))
  }

  /** The invariants of every object on the way to a flattened field. */
  private def invariants(flattening: ParameterFlattening)(using symbols: Symbols): Seq[Expr] =
    flattening.enclosingObjects.flatMap { obj =>
      obj.getType match {
        case adt: ADTType =>
          adt.getSort.invariant.flatMap { inv =>
            exprOps.withoutSpecs(inv.fullBody).map(inv.withParamSubst(Seq(obj), _))
          }
        case _ => None
      }
    }

  /** The ranges of `spec`, narrowed by the guards a path takes.
    *
    * Only guards between an input and a literal are used. Such a comparison involves no
    * rounding, so the branch really restricts the input. Guards on computed values are ignored.
    * A strict comparison is treated as non-strict, which is slightly wider and so still sound.
    */
  def narrowed(spec: InputSpec, guards: Seq[Guard], choices: Seq[BranchChoice]): InputSpec = {
    val ranges = choices.foldLeft(spec.ranges) { case (ranges, choice) =>
      val guard = guards(choice.guard)

      // Taking a guard means `lhs <= rhs`, not taking it means `rhs <= lhs` (an input compared
      // with a literal is never NaN). `capped` says whether the literal is an upper bound.
      val bound: Option[(Identifier, Boolean, Double)] =
        (resolved(guard.lhs), resolved(guard.rhs)) match {
          case (Input(id), FPLit(d)) => Some((id, choice.taken, d))
          case (FPLit(d), Input(id)) => Some((id, !choice.taken, d))
          case _ => None
        }

      bound match {
        case Some((id, capped, d)) if ranges.contains(id) =>
          val (low, high) = ranges(id)
          val (tightLow, tightHigh) =
            if (capped) (low, math.min(high, d)) else (math.max(low, d), high)

          // An empty range means no input reaches the leaf. The path walk decides that; here
          // the range is just left as it was.
          if (tightLow <= tightHigh) ranges.updated(id, (tightLow, tightHigh)) else ranges

        case _ => ranges
      }
    }

    spec.copy(ranges = ranges)
  }

  /** `e` with its `let` bindings substituted. */
  private def resolved(e: Expr): Expr = e match {
    case Let(vd, value, body) =>
      resolved(exprOps.replaceFromSymbols(Map(vd -> resolved(value)), body))
    case other => other
  }

  private object Input {
    def unapply(e: Expr): Option[Identifier] = e match {
      case v: Variable => Some(v.id)
      case _ => None
    }
  }

  /** The bounds a precondition gives each input, read from comparisons with constants. */
  private def extractRanges(precondition: Expr): Map[Identifier, Bounds] = {
    var found = Map.empty[Identifier, Bounds].withDefaultValue(Bounds.empty)
    def low(id: Identifier, d: Double): Unit = found = found.updated(id, found(id).withLow(d))
    def high(id: Identifier, d: Double): Unit = found = found.updated(id, found(id).withHigh(d))

    def rec(e: Expr, constants: Map[Identifier, Double]): Unit = {
      // The frontend binds each operand to a name, so `-10 <= x` arrives as a comparison of
      // two variables, one of which holds a constant.
      object Constant {
        def unapply(e: Expr): Option[Double] = e match {
          case FPLit(d) => Some(d)
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
        case And(parts) => parts.foreach(rec(_, constants))
        case Not(Not(e)) => rec(e, constants)

        case Let(vd, Constant(d), body) => rec(body, constants + (vd.id -> d))
        // A name bound to another name is replaced by it, so that a bound on the new name is
        // recorded for the original input.
        case Let(vd, v: Variable, body) =>
          rec(exprOps.replaceFromSymbols(Map(vd -> v), body), constants)
        case Let(_, _, body) => rec(body, constants)

        case FPLessEquals(Constant(d), Input(id))    => low(id, d)
        case FPLessThan(Constant(d), Input(id))      => low(id, d)
        case FPLessEquals(Input(id), Constant(d))    => high(id, d)
        case FPLessThan(Input(id), Constant(d))      => high(id, d)
        case FPGreaterEquals(Input(id), Constant(d)) => low(id, d)
        case FPGreaterThan(Input(id), Constant(d))   => low(id, d)
        case FPGreaterEquals(Constant(d), Input(id)) => high(id, d)
        case FPGreaterThan(Constant(d), Input(id))   => high(id, d)

        case _ => ()
      }
    }

    rec(precondition, Map.empty)
    found
  }

  /** The one precision `body` computes in. The analyzers cannot mix precisions. */
  private def uniformPrecision(body: Expr)(using Symbols): Either[String, FPPrecision] = {
    val types = exprOps.collect[Type] { e =>
      val declared: Set[Type] = e match {
        case Let(vd, _, _) => Set(vd.tpe)
        case _ => Set.empty
      }
      val here: Set[Type] = e.getType match {
        case t: FPType => Set(t)
        case _ => Set.empty
      }
      declared ++ here
    }(body)

    types.collect { case t: FPType => t }.toSeq.sortBy(t => (t.exponent, t.significand)) match {
      case Seq() => Left("no floating-point values")
      case Seq(t) => FPPrecision.fromType(t).toRight(
        s"unsupported precision (exponent ${t.exponent}, significand ${t.significand})")
      case several => Left("mixed floating-point precisions: " +
        several.map(t => s"(${t.exponent},${t.significand})").mkString(", "))
    }
  }
}
