/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification
package roundoff

import trees._

/** An integer literal of any width, possibly negated. */
private[roundoff] object IntLit {
  def unapply(e: Expr): Option[BigInt] = e match {
    case Int8Literal(n) => Some(BigInt(n))
    case Int16Literal(n) => Some(BigInt(n))
    case Int32Literal(n) => Some(BigInt(n))
    case Int64Literal(n) => Some(BigInt(n))
    case IntegerLiteral(n) => Some(n)
    case UMinus(IntLit(n)) => Some(-n)
    case _ => None
  }
}

/** A floating-point constant, seen through the wrappers the frontend puts around it. */
private[roundoff] object FPLit {
  def unapply(e: Expr): Option[Double] = e match {
    case Float64Literal(d) => Some(d)
    case Float32Literal(f) => Some(f.toDouble)

    // The frontend turns an integer written among floating-point operands into a cast,
    // which is only the value it names while the precision it casts to holds that exactly.
    case FPCast(_, significand, _, IntLit(n)) if n.abs <= BigInt(2).pow(significand) =>
      Some(n.toDouble)

    case FPUMinus(FPLit(d)) => Some(-d)
    case Assert(_, _, FPLit(d)) => Some(d)
    case Annotated(FPLit(d), _) => Some(d)

    case _ => None
  }
}

private[roundoff] object Fraction {

  /** The exact fraction a double stands for, as numerator and denominator.
    *
    * Read from the binary form, because the decimal form of a double runs to hundreds
    * of digits that a solver can only round.
    */
  def ofDouble(d: Double): Either[String, (BigInt, BigInt)] =
    if (d.isNaN || d.isInfinite) Left(s"non-finite literal ($d)")
    else if (d == 0.0) Right((BigInt(0), BigInt(1)))
    else {
      val bits = java.lang.Double.doubleToLongBits(d)
      val biasedExponent = ((bits >> 52) & 0x7ff).toInt
      val storedMantissa = bits & 0xfffffffffffffL

      // A subnormal has no implicit leading bit and uses the smallest exponent.
      val (mantissa, exponent) =
        if (biasedExponent == 0) (BigInt(storedMantissa), -1074)
        else (BigInt(storedMantissa | 0x10000000000000L), biasedExponent - 1075)

      val signed = if (d < 0) -mantissa else mantissa

      if (exponent >= 0) Right((signed * BigInt(2).pow(exponent), BigInt(1)))
      else {
        // Cancel what both sides share, so the fraction is in lowest terms.
        val shared = signed.abs.lowestSetBit min -exponent
        Right((signed >> shared, BigInt(2).pow(-exponent - shared)))
      }
    }

  /** The same as [[ofDouble]], but as an Inox literal. */
  def literal(d: Double): inox.trees.Expr = ofDouble(d) match {
    case Right((numerator, denominator)) => inox.trees.FractionLiteral(numerator, denominator)
    case Left(why) => throw new IllegalArgumentException(why)
  }
}

/** Writes a floating-point expression as an FPCore definition. */
object FPCoreEmitter {

  private case class Bounds(low: Option[Double], high: Option[Double]) {
    def withLow(d: Double) = Bounds(Some(low.fold(d)(math.min(_, d))), high)
    def withHigh(d: Double) = Bounds(low, Some(high.fold(d)(math.max(_, d))))
  }

  private object Bounds { val empty = Bounds(None, None) }

  /** Reads what every query about `fd` shares: its precision, and its input ranges. */
  def specOf(fd: FunDef, body: Expr)(using Symbols): Either[String, InputSpec] =
    for {
      precision <- uniformPrecision(body)
    } yield {
      val bounds = fd.precondition.map(Preprocessor.stripAnnotations).map(extractRanges).getOrElse(Map.empty)
      // A half-open range is no more usable than a missing one, and dropping it here lets
      // `emit` name the input that is missing one.
      val ranges = bounds.collect { case (id, Bounds(Some(low), Some(high))) => id -> (low, high) }
      InputSpec(precision, ranges)
    }

  /** The ranges of `spec`, narrowed by whatever the guards a path took say about an input.
    *
    * Only a guard between an input and a literal is read. Such a comparison is exact, since both
    * sides are already the doubles they name, so the branch really does hold the input to one
    * side of the literal and a leaf below it is never evaluated anywhere else. A guard on a
    * computed value says nothing about any input on its own and is passed over.
    *
    * A strict comparison is kept as a closed bound, which is wider than the truth by the last
    * value and keeps the box a box.
    */
  def narrowed(spec: InputSpec, guards: Seq[Guard], choices: Seq[BranchChoice]): InputSpec = {
    val ranges = choices.foldLeft(spec.ranges) { case (ranges, choice) =>
      val guard = guards(choice.guard)

      // Taking a guard puts its left side below its right, and not taking it puts the right at
      // or below the left, since an input compared against a literal is never NaN. `capped`
      // says whether the literal becomes the input's ceiling or its floor.
      val bound: Option[(Identifier, Boolean, Double)] =
        (resolved(guard.lhs), resolved(guard.rhs)) match {
          case (Input(id), Literal(d)) => Some((id, choice.taken, d))
          case (Literal(d), Input(id)) => Some((id, !choice.taken, d))
          case _ => None
        }

      bound match {
        case Some((id, capped, d)) if ranges.contains(id) =>
          val (low, high) = ranges(id)
          val (tightLow, tightHigh) =
            if (capped) (low, math.min(high, d)) else (math.max(low, d), high)

          // An empty range means no input reaches the leaf, which is a question the enumeration
          // has already asked; here it only says there is nothing left to narrow.
          if (tightLow <= tightHigh) ranges.updated(id, (tightLow, tightHigh)) else ranges

        case _ => ranges
      }
    }

    spec.copy(ranges = ranges)
  }

  /** An operand with its bindings written out, since a guard keeps the ones it needs. */
  private def resolved(e: Expr): Expr = e match {
    case Let(vd, value, body) =>
      resolved(exprOps.replaceFromSymbols(Map(vd -> resolved(value)), body))
    case other => other
  }

  private object Literal {
    def unapply(e: Expr): Option[Double] = FPLit.unapply(e)
  }

  private object Input {
    def unapply(e: Expr): Option[Identifier] = e match {
      case v: Variable => Some(v.id)
      case _ => None
    }
  }

  /** Writes `expr` as a self-contained FPCore definition called `name`. */
  def emit(name: String, label: String, expr: Expr, spec: InputSpec)(using Symbols)
    : Either[String, String] = {

    val inputs = exprOps.variablesOf(expr).toSeq.sortBy(_.id.globalId)

    for {
      _ <- if (inputs.nonEmpty) Right(()) else Left("no floating-point inputs to bound")

      // Daisy silently drops a function whose inputs are not all bounded.
      _ <- inputs.find(v => !spec.ranges.contains(v.id)) match {
             case Some(v) => Left(s"no range in the precondition for '${v.id.name}'; " +
               "add bounds of the form 'lo <= x && x <= hi'")
             case None => Right(())
           }

      precondition <- traverse(inputs) { v =>
                        val (low, high) = spec.ranges(v.id)
                        for { l <- numeral(low); h <- numeral(high) }
                          yield s"(<= $l ${symbol(v.id)}) (<= ${symbol(v.id)} $h)"
                      }

      body <- convert(expr, inputs.map(_.id).toSet)
    } yield {
      s"""|(FPCore $name (${inputs.map(v => symbol(v.id)).mkString(" ")})
          | :name "$label"
          | :pre (and ${precondition.mkString(" ")})
          | $body)
          |""".stripMargin
    }
  }

  /** Collects the `variable op literal` bounds a precondition states.
    *
    * Anything else, including disjunctions and comparisons between two variables, is
    * ignored, which widens the box and stays sound.
    */
  private def extractRanges(precondition: Expr): Map[Identifier, Bounds] = {
    var found = Map.empty[Identifier, Bounds].withDefaultValue(Bounds.empty)
    def low(id: Identifier, d: Double): Unit = found = found.updated(id, found(id).withLow(d))
    def high(id: Identifier, d: Double): Unit = found = found.updated(id, found(id).withHigh(d))

    def rec(e: Expr, constants: Map[Identifier, Double]): Unit = {
      // The frontend hoists each operand into its own binding, so `-10 <= x` arrives as a
      // comparison between two variables, one of which holds a constant.
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

  /** The single precision an expression runs at, since FPCore cannot state one per variable. */
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

  /** Writes a double as an exact FPCore numeral, sign included.
    *
    * The sign has to be part of the numeral, because Daisy only reads a range bound that
    * is literally a number and would not see one wrapped in a unary minus.
    */
  private def numeral(d: Double): Either[String, String] =
    Fraction.ofDouble(d).map { case (numerator, denominator) =>
      if (denominator == 1) numerator.toString else s"$numerator/$denominator"
    }

  private def symbol(id: Identifier): String = s"v_${id.globalId}"

  private def roundingModeName(e: Expr): String = e match {
    case RoundTowardZero => "toward zero"
    case RoundTowardPositive => "toward positive"
    case RoundTowardNegative => "toward negative"
    case RoundNearestTiesToAway => "nearest, ties to away"
    case _ => "unknown"
  }

  private def roundsToNearest(mode: Expr): Either[String, Unit] = mode match {
    case RoundNearestTiesToEven => Right(())
    case other => Left(s"unsupported rounding mode (${roundingModeName(other)}); " +
      "Daisy assumes round-to-nearest-ties-to-even")
  }

  private def convert(e: Expr, inScope: Set[Identifier]): Either[String, String] = {
    def binary(op: String, l: Expr, r: Expr): Either[String, String] =
      for { a <- convert(l, inScope); b <- convert(r, inScope) } yield s"($op $a $b)"

    def rounded(op: String, mode: Expr, args: Expr*): Either[String, String] =
      for {
        _ <- roundsToNearest(mode)
        as <- traverse(args)(convert(_, inScope))
      } yield s"($op ${as.mkString(" ")})"

    def nary(op: String, args: Seq[Expr]): Either[String, String] =
      traverse(args)(convert(_, inScope)).map(as => s"($op ${as.mkString(" ")})")

    e match {
      case v: Variable =>
        if (inScope(v.id)) Right(symbol(v.id)) else Left(s"unbound variable '${v.id.name}'")

      case FPLit(d) => numeral(d)

      case FPAdd(mode, l, r) => rounded("+", mode, l, r)
      case FPSub(mode, l, r) => rounded("-", mode, l, r)
      case FPMul(mode, l, r) => rounded("*", mode, l, r)
      case FPDiv(mode, l, r) => rounded("/", mode, l, r)
      case FPFMA(mode, a, b, c) => rounded("fma", mode, a, b, c)
      case FPUMinus(a) => convert(a, inScope).map(s => s"(- $s)")
      case MathCall(f, args) => nary(f.symbol, args)

      case Let(vd, value, body) =>
        for {
          v <- convert(value, inScope)
          b <- convert(body, inScope + vd.id)
        } yield s"(let ([${symbol(vd.id)} $v]) $b)"

      case IfExpr(condition, thenBranch, elseBranch) =>
        for {
          c <- convert(condition, inScope)
          t <- convert(thenBranch, inScope)
          f <- convert(elseBranch, inScope)
        } yield s"(if $c $t $f)"

      case FPLessThan(l, r)      => binary("<", l, r)
      case FPLessEquals(l, r)    => binary("<=", l, r)
      case FPGreaterThan(l, r)   => binary(">", l, r)
      case FPGreaterEquals(l, r) => binary(">=", l, r)
      case FPEquals(l, r)        => binary("==", l, r)

      case And(parts) => nary("and", parts)
      case Or(parts) => nary("or", parts)
      case Not(a) => convert(a, inScope).map(s => s"(not $s)")
      case BooleanLiteral(b) => Right(if (b) "TRUE" else "FALSE")

      case other => Left(s"no FPCore equivalent for ${other.getClass.getSimpleName}")
    }
  }
}