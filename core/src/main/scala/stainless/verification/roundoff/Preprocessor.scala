/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification
package roundoff

import trees.*

import scala.annotation.tailrec

object Preprocessor {

  def apply(fd: FunDef)(using Symbols)
    : Either[String, (Expr, Seq[AccessPath], ADTParametersFlattening)] = {
    val paths = AccessPath.list(fd.returnType)

    if (paths.isEmpty) Left(AccessPath.errorMessage(fd.returnType))
    else
      exprOps.withoutSpecs(fd.fullBody).toRight("function has no body")
        .flatMap(inlineFunctionCalls)
        .flatMap { bodyAfterInlining =>
          val bodyAfterADTResolution = resolveADTSelections(stripAnnotations(bodyAfterInlining))
          ADTParametersFlattening.flatten(fd, bodyAfterADTResolution).flatMap { case (bodyAfterFlattening, newParameters) =>
            val res = resolveADTSelections(hoistConditionals(unfoldMathOperators(bodyAfterFlattening)))
            cannotAnalyse(res, paths).toLeft((res, paths, newParameters))
          }
        }
  }

  /** Why the analysis cannot analyse an expression
    */
  private def cannotAnalyse(e: Expr, paths: Seq[AccessPath])(using Symbols): Option[String] =
    paths.view.map(_.project(e)).flatMap { body =>
      isUnsupported(body)
        .orElse(Option.when(conditionalsNotHoisted(body))(
          "a conditional remains inside an expression"))
    }.headOption



  private def traverse[A, B](xs: Seq[A])(f: A => Either[String, B]): Either[String, Seq[B]] =
    xs.foldLeft(Right(Vector.empty): Either[String, Vector[B]]) { (done, x) =>
      done.flatMap(built => f(x).map(built :+ _))
    }

  def stripAnnotations(e: Expr): Expr = exprOps.postMap {
    case Assert(_, _, body) => Some(body)
    case Assume(_, body) => Some(body)
    case Annotated(body, _) => Some(body)
    case Decreases(_, body) => Some(body)
    case _ => None
  }(e)

  /** Maximum number of calls inlined. */
  private val inliningBudget = 256

  private def inlineFunctionCalls(e: Expr)(using symbols: Symbols): Either[String, Expr] = {
    var remaining = inliningBudget

    def descend(e: Expr): Either[String, Expr] = e match {
      case Operator(operands, build) => traverse(operands)(rec).map(build)
    }

    def rec(e: Expr): Either[String, Expr] = e match {
      case TranscendentalFunctionCall(_, _) => descend(e)
      case call: FunctionInvocation => inlined(call)
      case other => descend(other)
    }

    def inlined(call: FunctionInvocation): Either[String, Expr] = {
      val name = call.id.name
      val hidden = call.tfd.fd.flags.collectFirst {
        case Extern => "extern"
        case Opaque => "opaque"
      }

      if (remaining <= 0)
        Left(s"inlining passed $inliningBudget calls, which is more than the analysis " +
             "can enumerate paths through")
      else if (symbols.isRecursive(call.id))
        Left(s"'$name' is recursive, so inlining it reaches no finite body")
      else if (hidden.isDefined)
        Left(s"'$name' is @${hidden.get}, so its body is hidden from the analysis")
      else exprOps.withoutSpecs(call.tfd.fullBody) match {
        case None => Left(s"'$name' has no body")

        case Some(body) =>
          remaining -= 1

          traverse(call.args)(rec).flatMap { arguments =>
            val renamedParameters = call.tfd.params.map(_.freshen)
            //alpha conversion
            val renamedBody = exprOps.freshenLocals(
                            exprOps.replaceFromSymbols(
                              call.tfd.params.zip(renamedParameters.map(_.toVariable)).toMap, body))

            // Parameters become bindings rather than substitutions
            rec(renamedBody).map { inlinedBody =>
              renamedParameters.zip(arguments).foldRight(inlinedBody) {
                case ((parameter, argument), kept) => Let(parameter, argument, kept)
              }
            }
          }
      }
    }

    rec(e)
  }

  /** Resolve ADT field selections and Tuple projections */
  private[roundoff] def resolveADTSelections(e: Expr)(using Symbols): Expr = {

    def pushADTSelectionInto(selection: Expr, expression: Expr,bindings: Map[Identifier, Expr])
                            (using symbols: Symbols): Option[Expr] = expression match {
      case Let(vd, value, body) =>
        pushADTSelectionInto(selection, body, bindings + (vd.id -> value)).map(Let(vd, value, _))

      case IfExpr(condition, thenBranch, elseBranch) =>
        pushADTSelectionInto(selection, thenBranch, bindings).flatMap { fromThenBranch =>
          pushADTSelectionInto(selection, elseBranch, bindings)
            .map(IfExpr(condition, fromThenBranch, _))
        }

      case variable: Variable =>
        bindings.get(variable.id).flatMap(pushADTSelectionInto(selection, _, bindings))

      case reached =>
        (selection, reached) match {
          case (TupleSelect(_, index), Tuple(fields)) => Some(fields(index - 1))

          case (ADTSelector(_, field), ADT(id, _, fields)) =>
            val position = symbols.getConstructor(id).fields.indexWhere(_.id == field)
            Option.when(position >= 0)(fields(position))

          case _ => None
        }
    }

    def rec(e: Expr, bindings: Map[Identifier, Expr]): Expr = e match {
      case Operator(Seq(receiver), rebuild) if AccessPath.isCompound(e) =>
        val resolvedReceiver = rec(receiver, bindings)


        pushADTSelectionInto(e, resolvedReceiver, bindings)
          .map(rec(_, bindings)).getOrElse(rebuild(Seq(resolvedReceiver)))

      case Let(vd, value, body) =>
        val resolvedValue = rec(value, bindings)
        val resolvedBody = rec(body, bindings + (vd.id -> resolvedValue))

        if (exprOps.variablesOf(resolvedBody).exists(_.id == vd.id))
          Let(vd, resolvedValue, resolvedBody)
        else resolvedBody

      case Operator(operands, build) => build(operands.map(rec(_, bindings)))
    }

    rec(e, Map.empty)
  }

  private def unfoldMathOperators(e: Expr)(using Symbols): Expr = exprOps.postMap {
    case FPAbs(a) =>
      a.getType match {
        case FPType(exponent, significand) =>
          val zero = FPLiteral.plusZero(exponent, significand)
          Some(named(a)(x => IfExpr(FPLessThan(x, zero), FPUMinus(x), x)))
        case _ => None
      }

    case FPMax(l, r) => Some(named(l)(a => named(r)(b => IfExpr(FPLessThan(a, b), b, a))))
    case FPMin(l, r) => Some(named(l)(a => named(r)(b => IfExpr(FPLessThan(a, b), a, b))))

    case _ => None
  }(e)

  /** Names an operand unless it already is one, so unfolding never repeats the work in it. */
  private def named(e: Expr)(build: Expr => Expr)(using Symbols): Expr = e match {
    case _: Variable => build(e)
    case FPLit(_) => build(e)
    case _ =>
      val vd = ValDef.fresh("t", e.getType)
      Let(vd, e, build(vd.toVariable))
  }



  /** Rewrites a body into a tree of conditionals over straight-line leaves.
    */
  private def hoistConditionals(e: Expr): Expr = e match {
    case Let(vd, value, body) =>
      val hoistedBody = hoistConditionals(body)
      nest(hoistConditionals(value))(Let(vd, _, hoistedBody))

    case IfExpr(condition, thenBranch, elseBranch) =>
      val liftedThen = hoistConditionals(thenBranch)
      val liftedElse = hoistConditionals(elseBranch)
      nest(hoistConditionals(condition))(IfExpr(_, liftedThen, liftedElse))

    case Operator(operands, build) => nest(operands.map(hoistConditionals))(build)
  }

  /** Moves the leftmost conditional among already hoisted operands above the node they belong
    * to, and repeats until none is left: `f(a, if (c) x else y)` becomes
    * `if (c) f(a, x) else f(a, y)`.
    */
  private def nest(operands: Seq[Expr])(build: Seq[Expr] => Expr): Expr = {
    // The whole node, built again with operand `i` standing for what was lifted off it.
    def nodeWith(i: Int, operand: Expr): Expr = nest(operands.updated(i, operand))(build)

    val lifted = operands.zipWithIndex.collectFirst {
      case (IfExpr(condition, thenBranch, elseBranch), i) =>
        IfExpr(condition, nodeWith(i, thenBranch), nodeWith(i, elseBranch))

      case (Let(vd, value, body), i) if isTopLevelConditional(body) =>
        Let(vd, value, nodeWith(i, body))
    }

    lifted.getOrElse(build(operands))
  }

  private def nest(operand: Expr)(build: Expr => Expr): Expr =
    nest(Seq(operand))(operands => build(operands.head))

  @tailrec
  private def isTopLevelConditional(e: Expr): Boolean = e match {
    case _: IfExpr => true
    case Let(_, _, body) => isTopLevelConditional(body)
    case _ => false
  }

  private def hasConditional(body: Expr): Boolean =
    exprOps.exists { case _: IfExpr => true; case _ => false }(body)

  /** Whether a conditional sits in a guard or a let binding */
  private def conditionalsNotHoisted(e: Expr): Boolean = e match {
    case Let(_, value, body) => hasConditional(value) || conditionalsNotHoisted(body)
    case IfExpr(condition, thenBranch, elseBranch) =>
      hasConditional(condition) ||
        conditionalsNotHoisted(thenBranch) || conditionalsNotHoisted(elseBranch)
    case other => hasConditional(other)
  }

  private def isUnsupported(body: Expr): Option[String] = {

    def isRNE(mode: Expr): Option[String] = mode match {
      case RoundNearestTiesToEven => None
      case _ => Some("an operation rounds in a mode other than to-nearest-ties-to-even")
    }

    def rec(e: Expr): Option[String] = e match {
      case FPLit(_) => None
      case _: Variable => None
      case _: BooleanLiteral => None

      case FPAdd(mode, l, r) => isRNE(mode) orElse rec(l) orElse rec(r)
      case FPSub(mode, l, r) => isRNE(mode) orElse rec(l) orElse rec(r)
      case FPMul(mode, l, r) => isRNE(mode) orElse rec(l) orElse rec(r)
      case FPDiv(mode, l, r) => isRNE(mode) orElse rec(l) orElse rec(r)
      case FPFMA(mode, a, b, c) => isRNE(mode) orElse rec(a) orElse rec(b) orElse rec(c)
      case FPUMinus(a) => rec(a)

      case Sqrt(mode, a) => isRNE(mode) orElse rec(a)

      // The library computes these in Scala, and the analysis reads them as exact instead.
      case TranscendentalFunctionCall(_, args) => args.view.flatMap(rec).headOption

      case Let(_, value, body) => rec(value) orElse rec(body)
      case IfExpr(condition, thenBranch, elseBranch) =>
        rec(condition) orElse rec(thenBranch) orElse rec(elseBranch)

      case FPLessThan(l, r) => rec(l) orElse rec(r)
      case FPLessEquals(l, r) => rec(l) orElse rec(r)
      case FPGreaterThan(l, r) => rec(l) orElse rec(r)
      case FPGreaterEquals(l, r) => rec(l) orElse rec(r)
      case FPEquals(l, r) => rec(l) orElse rec(r)

      case And(parts) => parts.view.flatMap(rec).headOption
      case Or(parts) => parts.view.flatMap(rec).headOption
      case Not(a) => rec(a)

      case fi: FunctionInvocation =>
        Some(s"a call to '${fi.id.name}' survived inlining")

      case other =>
        Some(s"${other.getClass.getSimpleName} has no floating-point meaning here")
    }

    rec(body)
  }
}

case class PointedAccessPath(root: Variable, path: AccessPath) {

  def name: String =
    if (path.steps.isEmpty) root.id.name else s"${root.id.name}_${path.displayName("_")}"

  /** The objects passed through on the way. */
  def enclosingObjects: Seq[Expr] =
    path.steps.inits.toSeq.drop(1).reverse.map(AccessPath(_).select(root))

  /** This path with one more step taken from where it ends. */
  def append(step: Selector): PointedAccessPath = PointedAccessPath(root, path.append(step))
}

/** Introduce additional parameters to represent ADT and Tuple selectors */
case class ADTParametersFlattening(accessPathVariables: Map[PointedAccessPath, Variable], parameters: Seq[ValDef]) {

  def substituteAccessPaths(e: Expr)(using Symbols): Expr =
    ADTParametersFlattening.replacePathsWithVariables(e, accessPathVariables)

  /** The objects every path passes through, each of which may carry an invariant of its own. */
  def enclosingObjects: Seq[Expr] =
    accessPathVariables.keys.flatMap(_.enclosingObjects).toSeq.distinct
}

object ADTParametersFlattening {

  def flatten(fd: FunDef, body: Expr)(using Symbols): Either[String, (Expr, ADTParametersFlattening)] = {
    val parameterIds = fd.params.map(_.id).toSet
    val accessPathVariables = scala.collection.mutable.LinkedHashMap.empty[PointedAccessPath, Variable]

    def accessPathVariable(path: PointedAccessPath, tpe: Type): Variable =
      accessPathVariables.getOrElseUpdate(path, Variable.fresh(path.name, tpe))

    def rec(e: Expr, bindings: Map[Identifier, PointedAccessPath]): Either[String, Expr] = e match {
      case selection if AccessPath.isCompound(selection) && TypeCheckerUtils.isFloatType(selection.getType) =>
        toPointedAccessPath(selection, bindings) match {
          case Some(path) if parameterIds(path.root.id) =>
            Right(accessPathVariable(path, selection.getType))
          case Some(path) =>
            Left(s"'${path.name}' is read off '${path.root.id.name}', which is not one " +
              s"of the values '${fd.id.name}' was given")
          case None =>
            Left("a field is read off something the analysis cannot follow back to a parameter")
        }

      case Let(vd, value, body) =>
        val updatedBindings = toPointedAccessPath(value, bindings)
          .map(path => bindings + (vd.id -> path)).getOrElse(bindings)

        rec(value, bindings).flatMap { flattenedValue =>
          rec(body, updatedBindings).map { flattenedBody =>
            if (TypeCheckerUtils.isFloatType(vd.tpe) || exprOps.variablesOf(flattenedBody).exists(_.id == vd.id))
              Let(vd, flattenedValue, flattenedBody)
            else flattenedBody
          }
        }

      case Operator(operands, build) => traverse(operands)(rec(_, bindings)).map(build)
    }

    rec(body, Map.empty).map { flattenedBody =>
      val parameters = fd.params.flatMap { parameter =>
        if (TypeCheckerUtils.isFloatType(parameter.tpe)) Seq(parameter)
        else
          accessPathVariables.collect {
            case (path, variable) if path.root.id == parameter.id => path.name -> variable
          }.toSeq.sortBy(_._1).map(_._2.toVal)
      }

      (flattenedBody, ADTParametersFlattening( accessPathVariables.toMap, parameters))
    }
  }

  private def toPointedAccessPath(e: Expr, bindings: Map[Identifier, PointedAccessPath]): Option[PointedAccessPath] =
    e match {
      case variable: Variable =>
        Some(bindings.getOrElse(variable.id, PointedAccessPath(variable, AccessPath.nil)))
      case ADTSelector(receiver, field) =>
        toPointedAccessPath(receiver, bindings).map(_.append(Selector.Field(field)))
      case TupleSelect(receiver, index) =>
        toPointedAccessPath(receiver, bindings).map(_.append(Selector.Index(index)))
      case _ => None
    }

  private def replacePathsWithVariables(e: Expr, variableOfPath: Map[PointedAccessPath, Variable])
                                       (using Symbols): Expr = {
    def rec(e: Expr, bindings: Map[Identifier, PointedAccessPath]): Expr = e match {
      case Operator(Seq(receiver), rebuild) if AccessPath.isCompound(e) =>
        toPointedAccessPath(e, bindings).flatMap(variableOfPath.get)
          .getOrElse(rebuild(Seq(rec(receiver, bindings))))

      case Let(vd, value, body) =>
        val inner = toPointedAccessPath(value, bindings)
          .map(path => bindings + (vd.id -> path)).getOrElse(bindings)
        Let(vd, rec(value, bindings), rec(body, inner))

      case Operator(operands, build) => build(operands.map(rec(_, bindings)))
    }

    rec(e, Map.empty)
  }

}

/** Selector type. */
enum Selector {
  case Index(at: Int)
  case Field(id: Identifier)

  def name: String = this match {
    case Index(at) => s"_$at"
    case Field(id) => id.name
  }

  def select(e: Expr): Expr = this match {
    case Index(at) => TupleSelect(e, at)
    case Field(id) => ADTSelector(e, id)
  }
}

/** Sequence of tuple projections or case class field selections */
case class AccessPath(steps: Seq[Selector]) {
  def displayName: String = displayName(".")
  def displayName(separator: String): String = steps.map(_.name).mkString(separator)
  def select(e: Expr): Expr = steps.foldLeft(e)((inner, step) => step.select(inner))
  def append(step: Selector): AccessPath = AccessPath(steps :+ step)

  /** `e` narrowed to a projection of the result it computes.
   */
  def project(e: Expr)(using Symbols): Expr =
    if (steps.isEmpty) e else Preprocessor.resolveADTSelections(select(e))
}

object AccessPath {

  val nil: AccessPath = AccessPath(Seq.empty)

  /** Every floating-point access path in a given type */
  def list(tpe: Type)(using symbols: Symbols): Seq[AccessPath] = {
    def rec(tpe: Type, pathBuilder: Seq[Selector], seen: Set[Identifier]): Seq[AccessPath] =
      tpe match {
        case FPType(_, _) => Seq(AccessPath(pathBuilder))

        case TupleType(bases) =>
          bases.zipWithIndex.flatMap { case (base, at) =>
            rec(base, pathBuilder :+ Selector.Index(at + 1), seen)
          }

        // Avoid infinite recursion
        case adt: ADTType if !seen(adt.id) =>
          adt.getSort.constructors match {
            case Seq(only) =>
              only.fields.flatMap(field =>
                rec(field.getType, pathBuilder :+ Selector.Field(field.id), seen + adt.id))
            case _ => Seq.empty
          }

        case _ => Seq.empty
      }
    rec(tpe, Seq.empty, Set.empty)
  }

  def errorMessage(tpe: Type)(using Symbols): String = tpe match {
    case adt: ADTType if adt.getSort.constructors.size > 1 =>
      s"the result is a '${adt.id.name}', which has more than one constructor, so which " +
      "fields a value of it has is not known from its type"
    case _ if isCompound(tpe) =>
      "nothing in the result of this function is a floating-point number"
    case _ =>
      "the result of this function is not a floating-point number"
  }

  /** Whether `tpe` is a result the analysis takes apart rather than one value. */
  def isCompound(tpe: Type): Boolean = tpe match {
    case TupleType(_) => true
    case _: ADTType => true
    case _ => false
  }

  def isCompound(e: Expr): Boolean = e match {
    case _: TupleSelect | _: ADTSelector => true
    case _ => false
  }
}