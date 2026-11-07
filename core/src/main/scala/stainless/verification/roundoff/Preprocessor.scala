/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification
package roundoff

import trees._
import scala.annotation.tailrec

/** One choice of constructor for every input, or field of an input, whose type has several,
  * such as `Option`. Both runs see the same constructor, so the error of a function is the
  * largest error of its variants.
  *
  * @param function           the function, taking the fields of the chosen constructors as inputs
  * @param description        the constructors chosen, such as `o = Some`; empty when there is none
  * @param sourceOfInput      for each input of `function`, the part of a parameter of the
  *                           original function it stands for, such as `o`, `Some`, `v`
  * @param chosenConstructors each part of a parameter with a choice of constructor, and the
  *                           constructor chosen for it
  */
case class InputVariant(function: FunDef, description: String,
                        sourceOfInput: Map[Identifier, FieldRead],
                        chosenConstructors: Seq[(FieldRead, Identifier)])

object InputVariants {

  /** The variants of `fd` its precondition does not rule out, at least one. Without a choice
    * of constructor in the inputs, the only variant is `fd` itself.
    */
  def allowedVariants(fd: FunDef)(using Symbols): Either[String, Seq[InputVariant]] =
    if (!fd.params.exists(p => holdsConstructorChoice(p.tpe)))
      Right(Seq(InputVariant(fd, "", fd.params.map(p => p.id -> FieldRead(p.toVariable, FieldPath.empty)).toMap,
                             Seq.empty)))
    else traverse(fd.params)(shapesOf).flatMap { perParameter =>
      cartesianProduct(perParameter).flatMap { shapes =>
        val substituted =
          exprOps.replaceFromSymbols(fd.params.zip(shapes.map(_.value)).toMap, fd.fullBody)
        val invariants = shapes.flatMap(_.built).flatMap(invariantOf)
        val precondition = andJoin(exprOps.preconditionOf(substituted).toSeq ++ invariants)

        Option.unless(Preprocessor.normalisedCondition(precondition) == BooleanLiteral(false)) {
          // The analysis reads only the precondition and the body.
          val body = exprOps.withoutSpecs(substituted).getOrElse(substituted)
          val function = fd.copy(params = shapes.flatMap(_.inputs),
                                 fullBody = Require(precondition, body))
          InputVariant(function, shapes.flatMap(_.chosen).mkString(", "),
                       shapes.flatMap(_.sourceOfInput).toMap, shapes.flatMap(_.chosenConstructors))
        }
      } match {
        case Seq() => Left("the precondition rules out every constructor of the inputs")
        case variants => Right(variants)
      }
    }

  /** One way to build a value: the value, the inputs it is built from, the objects built on
    * the way, the constructors chosen, such as `o = Some`, and, as in [[InputVariant]], where
    * each input and each choice is in the parameter.
    */
  private case class InputShape(value: Expr, inputs: Seq[ValDef], built: Seq[Expr],
                                chosen: Seq[String], sourceOfInput: Seq[(Identifier, FieldRead)],
                                chosenConstructors: Seq[(FieldRead, Identifier)])

  private def shapesOf(parameter: ValDef)(using Symbols): Either[String, Seq[InputShape]] = {
    val whole = FieldRead(parameter.toVariable, FieldPath.empty)
    if (holdsConstructorChoice(parameter.tpe))
      shapesOfType(parameter.id.name, parameter.id.name, whole, parameter.tpe, Set.empty)
    else Right(Seq(InputShape(parameter.toVariable, Seq(parameter), Seq.empty, Seq.empty,
                              Seq(parameter.id -> whole), Seq.empty)))
  }

  /** Every way to build a value of type `tpe`, called `name` inside the input `root`, and found
    * at `source` in it, from inputs without a choice of constructor. `seen` stops at a recursive
    * type.
    */
  private def shapesOfType(root: String, name: String, source: FieldRead, tpe: Type,
                           seen: Set[Identifier])
                          (using Symbols): Either[String, Seq[InputShape]] = tpe match {

    case adt: ADTType if holdsConstructorChoice(adt) && seen(adt.id) =>
      Left(s"the input '$root' holds a '${adt.id.name}', which can hold another one, so its " +
           "values have no bounded number of shapes")

    case adt: ADTType if holdsConstructorChoice(adt) =>
      val constructors = adt.getSort.constructors
      val hasChoice = constructors.size > 1
      traverse(constructors) { constructor =>
        val chosen = Option.when(hasChoice)(s"$name = ${constructor.id.name}")
        val inConstructor =
          if (hasChoice) source.append(FieldStep.Constructor(constructor.id)) else source
        traverse(constructor.fields) { field =>
          shapesOfType(root, s"$name.${field.id.name}", inConstructor.append(FieldStep.Field(field.id)),
                       field.getType, seen + adt.id)
        }.map(cartesianProduct(_).map { parts =>
          val value = ADT(constructor.id, adt.tps, parts.map(_.value))
          InputShape(value, parts.flatMap(_.inputs), value +: parts.flatMap(_.built),
                     chosen.toSeq ++ parts.flatMap(_.chosen), parts.flatMap(_.sourceOfInput),
                     Option.when(hasChoice)(source -> constructor.id).toSeq ++
                       parts.flatMap(_.chosenConstructors))
        })
      }.map(_.flatten)

    case TupleType(bases) if holdsConstructorChoice(tpe) =>
      traverse(bases.zipWithIndex) { case (base, i) =>
        shapesOfType(root, s"$name._${i + 1}", source.append(FieldStep.TupleElement(i + 1)), base, seen)
      }
        .map(cartesianProduct(_).map { parts =>
          InputShape(Tuple(parts.map(_.value)), parts.flatMap(_.inputs), parts.flatMap(_.built),
                     parts.flatMap(_.chosen), parts.flatMap(_.sourceOfInput),
                     parts.flatMap(_.chosenConstructors))
        })

    case _ =>
      val input = ValDef(FreshIdentifier(name.replace('.', '_')), tpe)
      Right(Seq(InputShape(input.toVariable, Seq(input), Seq.empty, Seq.empty,
                           Seq(input.id -> source), Seq.empty)))
  }

  /** Whether a value of type `tpe` holds a type with several constructors. */
  private def holdsConstructorChoice(tpe: Type)(using Symbols): Boolean = {
    def holdsChoiceWithin(tpe: Type, seen: Set[Identifier]): Boolean = tpe match {
      case adt: ADTType if !seen(adt.id) =>
        val constructors = adt.getSort.constructors
        constructors.size > 1 ||
          constructors.exists(_.fields.exists(field => holdsChoiceWithin(field.getType, seen + adt.id)))
      case TupleType(bases) => bases.exists(holdsChoiceWithin(_, seen))
      case _ => false
    }
    holdsChoiceWithin(tpe, Set.empty)
  }

  /** Every way to pick one element from each of `choices`. */
  private def cartesianProduct[A](choices: Seq[Seq[A]]): Seq[Seq[A]] =
    choices.foldRight(Seq(Seq.empty[A])) { (options, rest) =>
      for (option <- options; tail <- rest) yield option +: tail
    }
}

/** Rewrites a function body into a tree of conditionals over straight-line leaves. */
object Preprocessor {

  /** Rewrites a function body into a tree of conditionals over straight-line leaves.
   * Executes the following steps:
    *  1. inline every call, and write every `match` as nested conditionals;
    *  2. remove annotations, resolve what is read from objects built in the body, and keep
    *     only the branch of a conditional whose condition is then known;
    *  3. write `abs`, `min` and `max` as conditionals, and move every conditional to the top;
    *  4. write every object returned as it is (such as `this`) as a constructor of its fields;
    *  5. replace each field read from a parameter by a new parameter;
    *  6. check that what is left only uses supported operations.
    */
  def apply(fd: FunDef, limit: TimeLimit = TimeLimit.never)(using Symbols)
    : Either[String, (Expr, Seq[FieldPath], FlattenedParameters)] = {
    val fields = FieldPath.numberPathsOf(fd.returnType)

    for {
      _ <- Either.cond(fields.nonEmpty, (),
             "nothing in the result of this function is a floating-point number, an 'Int' or a " +
             "'Long'; a recursive class with several constructors is not taken apart")
      body <- exprOps.withoutSpecs(fd.fullBody).toRight("function has no body")
      inlined <- inlineFunctionCalls(body)
      normalised = normalisedAfterInlining(inlined, limit)
      hoisted = foldConstantConditions(resolveBuiltObjects(
                  hoistConditionals(absMinMaxAsConditionals(normalised), limit), limit))
      expanded = resolveBuiltObjects(expandReturnedObjects(hoisted), limit)
      (rewritten, flattening) <- FlattenedParameters.flatten(fd, expanded, limit)
      _ <- unsupportedReason(rewritten, fields).toLeft(())
    } yield (rewritten, fields, flattening)
  }

  /** `condition`, such as a precondition, normalised as a body is, except that a call that
    * cannot be inlined is kept.
    */
  def normalisedCondition(condition: Expr)(using Symbols): Expr =
    normalisedAfterInlining(inlineFunctionCalls(condition).getOrElse(condition))

  /** Step 2 of [[apply]]. */
  private def normalisedAfterInlining(inlined: Expr, limit: TimeLimit = TimeLimit.never)
                                     (using symbols: Symbols): Expr =
    foldConstantConditions(
      resolveBuiltObjects(stripAnnotations(symbols.matchToIfThenElse(inlined)), limit))

  /** `body` with every test that an input is an infinity or NaN answered `false`, which holds
    * for an input `ranges` bounds on both sides, and the branches this rules out dropped.
    */
  def withFiniteInputs(body: Expr, ranges: Map[Identifier, (Double, Double)]): Either[String, Expr] = {
    def boundedOnBothSides(v: Variable) =
      ranges.get(v.id).exists { case (low, high) => !low.isInfinite && !high.isInfinite }

    val answered = foldConstantConditions(exprOps.postMap {
      case FPIsInfinite(v: Variable) if boundedOnBothSides(v) => Some(BooleanLiteral(false))
      case FPIsNaN(v: Variable) if boundedOnBothSides(v) => Some(BooleanLiteral(false))
      case _ => None
    }(body))

    exprOps.collect[Variable] {
      case FPIsInfinite(v: Variable) => Set(v)
      case FPIsNaN(v: Variable) => Set(v)
      case _ => Set.empty
    }(answered).headOption match {
      case Some(v) =>
        Left(s"'isInfinity' and 'isNaN' are only read on an input bounded on both sides, and " +
             s"'${v.id.name}' is not")
      case None => Right(answered)
    }
  }

  def stripAnnotations(e: Expr): Expr = exprOps.postMap {
    case Assert(_, _, body) => Some(body)
    case Assume(_, body) => Some(body)
    case Annotated(body, _) => Some(body)
    case Decreases(_, body) => Some(body)
    case _ => None
  }(e)

  /** Replaces what is read from an object built in the body, also through bindings and
    * conditionals: `Point(a, b).x` becomes `a`, `Some(a) is None` becomes `false` and
    * `((v) => v < 1)(a)` becomes `a < 1`. What cannot be resolved is kept.
    */
  private[roundoff] def resolveBuiltObjects(e: Expr, limit: TimeLimit = TimeLimit.never,
                                           inScope: Map[Identifier, Expr] = Map.empty)
                                           (using symbols: Symbols): Expr = {

    def selectFrom(selection: Expr, expression: Expr, bindings: Map[Identifier, Expr])
      : Option[Expr] = expression match {
      case Let(vd, value, body) =>
        selectFrom(selection, body, bindings + (vd.id -> value)).map(Let(vd, value, _))

      case IfExpr(condition, thenBranch, elseBranch) =>
        selectFrom(selection, thenBranch, bindings).flatMap { fromThenBranch =>
          selectFrom(selection, elseBranch, bindings)
            .map(IfExpr(condition, fromThenBranch, _))
        }

      // Conditionals are not copied into every read.
      case variable: Variable =>
        bindings.get(variable.id).filterNot(isTopLevelConditional)
          .flatMap(selectFrom(selection, _, bindings))

      case reached =>
        (selection, reached) match {
          case (TupleSelect(_, index), Tuple(fields)) => Some(fields(index - 1))

          case (ADTSelector(_, field), ADT(id, _, fields)) =>
            val position = symbols.getConstructor(id).fields.indexWhere(_.id == field)
            Option.when(position >= 0)(fields(position))

          case (IsConstructor(_, tested), ADT(built, _, _)) => Some(BooleanLiteral(tested == built))

          case _ => None
        }
    }

    def lambdaOf(e: Expr, bindings: Map[Identifier, Expr]): Option[Lambda] = e match {
      case lambda: Lambda => Some(lambda)
      case variable: Variable => bindings.get(variable.id).flatMap(lambdaOf(_, bindings))
      case _ => None
    }

    def resolve(e: Expr, bindings: Map[Identifier, Expr]): Expr = e match {
      case Application(callee, arguments) if lambdaOf(callee, bindings).isDefined =>
        val Lambda(parameters, body) = lambdaOf(callee, bindings).get
        val (renamed, freshBody) = freshCopy(parameters, body)
        resolve(withLets(renamed.zip(arguments), freshBody), bindings)

      case Operator(Seq(receiver), rebuild)
          if FieldPath.isFieldSelection(e) || e.isInstanceOf[IsConstructor] =>
        val resolvedReceiver = resolve(receiver, bindings)

        selectFrom(e, resolvedReceiver, bindings)
          .map(resolve(_, bindings)).getOrElse(rebuild(Seq(resolvedReceiver)))

      case Let(vd, value, body) =>
        limit.check()
        val resolvedValue = resolve(value, bindings)
        val resolvedBody = resolve(body, bindings + (vd.id -> resolvedValue))

        if (exprOps.variablesOf(resolvedBody).exists(_.id == vd.id))
          Let(vd, resolvedValue, resolvedBody)
        else resolvedBody

      case Operator(operands, build) => build(operands.map(resolve(_, bindings)))
    }

    resolve(e, inScope)
  }

  /** `body` with every object it returns written as a constructor of
    * its fields, e.g, converts `this` into a new object
    */
  private def expandReturnedObjects(body: Expr)(using Symbols): Expr = body match {
    case Let(vd, value, rest) => Let(vd, value, expandReturnedObjects(rest))
    case IfExpr(condition, thenBranch, elseBranch) =>
      IfExpr(condition, expandReturnedObjects(thenBranch), expandReturnedObjects(elseBranch))
    case Tuple(parts) => Tuple(parts.map(expandReturnedObjects))
    case ADT(id, tps, args) => ADT(id, tps, args.map(expandReturnedObjects))
    // Only names and field reads, so that no computation is repeated.
    case _: Variable | _: ADTSelector | _: TupleSelect => asConstructor(body, body.getType, Set.empty)
    case other => other
  }

  /** `e` as a constructor of its fields, recursively, when its type has a single constructor.
    * `seen` stops at a recursive type.
    */
  private def asConstructor(e: Expr, tpe: Type, seen: Set[Identifier])(using Symbols): Expr =
    tpe match {
      case TupleType(bases) =>
        Tuple(bases.zipWithIndex.map { case (base, i) =>
          asConstructor(TupleSelect(e, i + 1), base, seen)
        })

      case adt: ADTType if !seen(adt.id) =>
        adt.getSort.constructors match {
          case Seq(only) =>
            ADT(only.id, adt.tps, only.fields.map { field =>
              asConstructor(ADTSelector(e, field.id), field.getType, seen + adt.id)
            })
          case _ => e
        }

      case _ => e
    }

  /** Why the analysis cannot handle some number of the result, if it cannot. */
  private def unsupportedReason(e: Expr, paths: Seq[FieldPath])(using Symbols): Option[String] =
    paths.view.map(_.extractFrom(e)).flatMap { body =>
      firstUnsupportedFeature(body)
        .orElse(Option.when(conditionalsNotHoisted(body))(
          "a conditional remains inside an expression"))
    }.headOption

  /** `e` with every condition that is `true` or `false`, also through a `val`, folded away:
    * `if (true) a else b` becomes `a`, `x && false` becomes `false`, `x || false` becomes `x`.
    */
  private def foldConstantConditions(e: Expr): Expr = {
    def simplifyConstantCondition(e: Expr): Expr = e match {
      case IfExpr(BooleanLiteral(holds), thenBranch, elseBranch) =>
        if (holds) thenBranch else elseBranch
      case Not(BooleanLiteral(holds)) => BooleanLiteral(!holds)
      case And(parts) if parts.contains(BooleanLiteral(false)) => BooleanLiteral(false)
      case And(parts) if parts.contains(BooleanLiteral(true)) =>
        andJoin(parts.filterNot(_ == BooleanLiteral(true)))
      case Or(parts) if parts.contains(BooleanLiteral(true)) => BooleanLiteral(true)
      case Or(parts) if parts.contains(BooleanLiteral(false)) =>
        orJoin(parts.filterNot(_ == BooleanLiteral(false)))
      case other => other
    }

    def substituteKnownConditions(e: Expr): Expr = e match {
      case Let(vd, value, body) =>
        substituteKnownConditions(value) match {
          case constant: BooleanLiteral =>
            substituteKnownConditions(exprOps.replaceFromSymbols(Map(vd -> constant), body))
          case resolved => Let(vd, resolved, substituteKnownConditions(body))
        }
      case Operator(operands, build) =>
        simplifyConstantCondition(build(operands.map(substituteKnownConditions)))
    }

    substituteKnownConditions(e)
  }


  private val inliningBudget = 4096

  private def inlineFunctionCalls(e: Expr)(using symbols: Symbols): Either[String, Expr] = {
    var callsLeftToInline = inliningBudget

    def inlineInOperands(e: Expr): Either[String, Expr] = e match {
      case Operator(operands, build) => traverse(operands)(inlineCalls).map(build)
    }

    def inlineCalls(e: Expr): Either[String, Expr] = e match {
      case TranscendentalFunctionCall(_, _) => inlineInOperands(e)
      case call: FunctionInvocation => inlinedCall(call)
      case other => inlineInOperands(other)
    }

    def inlinedCall(call: FunctionInvocation): Either[String, Expr] = {
      val name = call.id.name
      val hidden = call.tfd.fd.flags.collectFirst {
        case Extern => "extern"
        case Opaque => "opaque"
      }

      if (callsLeftToInline <= 0)
        Left(s"inlining passed $inliningBudget calls")
      else if (symbols.isRecursive(call.id))
        Left(s"'$name' is recursive, so inlining it reaches no finite body")
      else if (hidden.isDefined)
        Left(s"'$name' is @${hidden.get}, so its body is hidden from the analysis")
      else exprOps.withoutSpecs(call.tfd.fullBody) match {
        case None => Left(s"'$name' has no body")

        case Some(body) =>
          callsLeftToInline -= 1
          traverse(call.args)(inlineCalls).flatMap { arguments =>
            val (parameters, freshBody) = freshCopy(call.tfd.params, body)
            inlineCalls(freshBody).map(withLets(parameters.zip(arguments), _))
          }
      }
    }

    inlineCalls(e)
  }

  /** `body` with `parameters` and the names it binds renamed, so that two copies never clash. */
  private def freshCopy(parameters: Seq[ValDef], body: Expr): (Seq[ValDef], Expr) = {
    val renamed = parameters.map(_.freshen)
    val renamedBody = exprOps.freshenLocals(
      exprOps.replaceFromSymbols(parameters.zip(renamed.map(_.toVariable)).toMap, body))
    (renamed, renamedBody)
  }

  private def absMinMaxAsConditionals(e: Expr)(using Symbols): Expr = exprOps.postMap {
    case FPAbs(a) =>
      a.getType match {
        case FPType(exponent, significand) =>
          val zero = FPLiteral.plusZero(exponent, significand)
          Some(bindUnlessAtomic(a)(x => IfExpr(FPLessThan(x, zero), FPUMinus(x), x)))
        case _ => None
      }

    case FPMax(l, r) =>
      Some(bindUnlessAtomic(l)(a => bindUnlessAtomic(r)(b => IfExpr(FPLessThan(a, b), b, a))))
    case FPMin(l, r) =>
      Some(bindUnlessAtomic(l)(a => bindUnlessAtomic(r)(b => IfExpr(FPLessThan(a, b), a, b))))

    case _ => None
  }(e)

  /** Binds `e` to a fresh name unless it is a variable or a literal, so that it is never
    * computed twice.
    */
  private def bindUnlessAtomic(e: Expr)(build: Expr => Expr)(using Symbols): Expr = e match {
    case _: Variable => build(e)
    case FPLit(_) => build(e)
    case _ =>
      val vd = ValDef.fresh("t", e.getType)
      Let(vd, e, build(vd.toVariable))
  }

  private def hoistConditionals(e: Expr, limit: TimeLimit): Expr = e match {
    case Let(vd, value, body) =>
      val hoistedBody = hoistConditionals(body, limit)
      liftConditional(hoistConditionals(value, limit), limit)(Let(vd, _, hoistedBody))

    case IfExpr(condition, thenBranch, elseBranch) =>
      val liftedThen = hoistConditionals(thenBranch, limit)
      val liftedElse = hoistConditionals(elseBranch, limit)
      liftConditional(hoistConditionals(condition, limit), limit)(IfExpr(_, liftedThen, liftedElse))

    case Operator(operands, build) =>
      liftConditional(operands.map(hoistConditionals(_, limit)), limit)(build)
  }

  /** Moves the leftmost conditional among already hoisted operands above their node, until
    * none is left: `f(a, if (c) x else y)` becomes `if (c) f(a, x) else f(a, y)`.
    */
  private def liftConditional(operands: Seq[Expr], limit: TimeLimit)
                             (build: Seq[Expr] => Expr): Expr = {
    // Lifting copies the node into both branches, so this is where the body grows.
    limit.check()
    def rebuiltWithOperand(i: Int, operand: Expr): Expr =
      liftConditional(operands.updated(i, operand), limit)(build)

    val lifted = operands.zipWithIndex.collectFirst {
      case (IfExpr(condition, thenBranch, elseBranch), i) =>
        IfExpr(condition, rebuiltWithOperand(i, thenBranch), rebuiltWithOperand(i, elseBranch))

      case (Let(vd, value, body), i) if isTopLevelConditional(body) =>
        Let(vd, value, rebuiltWithOperand(i, body))
    }

    lifted.getOrElse(build(operands))
  }

  private def liftConditional(operand: Expr, limit: TimeLimit)(build: Expr => Expr): Expr =
    liftConditional(Seq(operand), limit)(operands => build(operands.head))

  @tailrec
  private def isTopLevelConditional(e: Expr): Boolean = e match {
    case _: IfExpr => true
    case Let(_, _, body) => isTopLevelConditional(body)
    case _ => false
  }

  private def hasConditional(body: Expr): Boolean =
    exprOps.exists { case _: IfExpr => true; case _ => false }(body)

  /** Whether a conditional is left inside a guard or a `let` value after hoisting. */
  private def conditionalsNotHoisted(e: Expr): Boolean = e match {
    case Let(_, value, body) => hasConditional(value) || conditionalsNotHoisted(body)
    case IfExpr(condition, thenBranch, elseBranch) =>
      hasConditional(condition) ||
        conditionalsNotHoisted(thenBranch) || conditionalsNotHoisted(elseBranch)
    case other => hasConditional(other)
  }

  /** Why `body` uses something the analysis cannot handle, if it does. */
  private def firstUnsupportedFeature(body: Expr)(using Symbols): Option[String] = {
    def notNearestEven(mode: Expr): Option[String] = mode match {
      case RoundNearestTiesToEven => None
      case _ => Some("an operation rounds in a mode other than to-nearest-ties-to-even")
    }

    def notIntOrLong(operand: Expr): Option[String] =
      if (isIntegerType(operand.getType)) None
      else Some(s"only 'Int' and 'Long' integers are supported, and this one is a " +
                s"'${operand.getType}'")

    def unsupportedInIntegerOperands(operands: Expr*): Option[String] =
      operands.view.flatMap(notIntOrLong).headOption orElse
        operands.view.flatMap(firstUnsupportedIn).headOption

    def firstUnsupportedIn(e: Expr): Option[String] = e match {
      case FPLit(_) => None
      case Int32Literal(_) | Int64Literal(_) => None
      case v: Variable => v.tpe match {
        case BVType(_, _) | IntegerType() => notIntOrLong(v)
        case _ => None
      }
      case _: BooleanLiteral => None

      case FPAdd(mode, l, r) => notNearestEven(mode) orElse firstUnsupportedIn(l) orElse firstUnsupportedIn(r)
      case FPSub(mode, l, r) => notNearestEven(mode) orElse firstUnsupportedIn(l) orElse firstUnsupportedIn(r)
      case FPMul(mode, l, r) => notNearestEven(mode) orElse firstUnsupportedIn(l) orElse firstUnsupportedIn(r)
      case FPDiv(mode, l, r) => notNearestEven(mode) orElse firstUnsupportedIn(l) orElse firstUnsupportedIn(r)
      case FPFMA(mode, a, b, c) =>
        notNearestEven(mode) orElse Seq(a, b, c).view.flatMap(firstUnsupportedIn).headOption
      case FPUMinus(a) => firstUnsupportedIn(a)

      case Sqrt(mode, a) => notNearestEven(mode) orElse firstUnsupportedIn(a)

      // Not inlined: the analysis reads them as the mathematical functions.
      case TranscendentalFunctionCall(_, args) => args.view.flatMap(firstUnsupportedIn).headOption

      case Let(_, value, body) => firstUnsupportedIn(value) orElse firstUnsupportedIn(body)
      case IfExpr(condition, thenBranch, elseBranch) =>
        Seq(condition, thenBranch, elseBranch).view.flatMap(firstUnsupportedIn).headOption

      case Inequality(Guard(l, r, _, integral)) =>
        if (integral) unsupportedInIntegerOperands(l, r)
        else firstUnsupportedIn(l) orElse firstUnsupportedIn(r)
      case FPEquals(l, r) => firstUnsupportedIn(l) orElse firstUnsupportedIn(r)
      case Equals(l, r) => unsupportedInIntegerOperands(l, r)

      case Plus(l, r) => unsupportedInIntegerOperands(l, r)
      case Minus(l, r) => unsupportedInIntegerOperands(l, r)
      case Times(l, r) => unsupportedInIntegerOperands(l, r)
      case UMinus(a) => unsupportedInIntegerOperands(a)
      case _: Division | _: Remainder | _: Modulo =>
        Some("integer division and '%' are not supported")
      case BVWideningCast(inner, Int64Type()) => unsupportedInIntegerOperands(inner)

      // Exact: a `Double` holds every integer up to 2^53, and a `Float` up to 2^24, which
      // [[InputRanges.inexactIntegerConversion]] checks.
      case FPCast(exponent, significand, _, inner) if inner.getType.isInstanceOf[BVType] &&
          FPPrecision.values.exists(p => p.exponent == exponent && p.significand == significand) =>
        unsupportedInIntegerOperands(inner)
      case FPCast(_, _, _, inner) if inner.getType.isInstanceOf[BVType] =>
        Some("only a conversion from 'Int' or 'Long' to 'Double' or 'Float' is supported")
      case _: FPCast => Some("a conversion between floating-point precisions is not supported")
      case _: FPToBVJVM | _: FPToBV =>
        Some("a conversion from floating point to an integer is not supported: the exact and " +
             "the rounded value can convert to different integers, a jump no guard shows")

      case And(parts) => parts.view.flatMap(firstUnsupportedIn).headOption
      case Or(parts) => parts.view.flatMap(firstUnsupportedIn).headOption
      case Not(a) => firstUnsupportedIn(a)

      // Answered once the ranges are known, by [[withFiniteInputs]].
      case FPIsInfinite(_: Variable) | FPIsNaN(_: Variable) => None
      case _: FPIsInfinite | _: FPIsNaN =>
        Some("'isInfinity' and 'isNaN' are only read on an input: the exact run computes no " +
             "infinity and no NaN, so the two runs could answer them differently")

      case fi: FunctionInvocation =>
        Some(s"a call to '${fi.id.name}' survived inlining")

      case other =>
        Some(s"'$other' has no floating-point meaning here")
    }

    firstUnsupportedIn(body)
  }
}

/** One step into a value: a tuple element, a field, or, for a type with several constructors,
  * the constructor the value is built with. A constructor step reads nothing: it says which
  * fields follow.
  */
enum FieldStep {
  case TupleElement(index: Int)
  case Field(id: Identifier)
  case Constructor(id: Identifier)

  def name: String = this match {
    case TupleElement(index) => s"_$index"
    case Field(id) => id.name
    case Constructor(id) => id.name
  }

  def readFrom(e: Expr): Expr = this match {
    case TupleElement(index) => TupleSelect(e, index)
    case Field(id) => ADTSelector(e, id)
    case Constructor(_) => e
  }

  def isConstructor: Boolean = this match {
    case Constructor(_) => true
    case _ => false
  }
}

/** The steps from a value to one number inside it. For a result of type `(Double, Point)`,
  * the numbers are at `_1`, `_2.x` and `_2.y`. For `Option[Double]`, the number is at
  * `Some.v`: the `Some` step says it only exists when the value is built with `Some`. No
  * steps for a value that is itself a number.
  */
case class FieldPath(steps: Seq[FieldStep]) {
  def displayName: String = joinedWith(".")
  def joinedWith(separator: String): String = steps.map(_.name).mkString(separator)
  def append(step: FieldStep): FieldPath = FieldPath(steps :+ step)

  /** `e` followed by these steps, such as `e._2.x`. */
  def readFrom(e: Expr): Expr = steps.foldLeft(e)((inner, step) => step.readFrom(inner))

  /** `body` with each leaf replaced by its number at this path: for `_2`,
    * `if (c) (a, b) else (d, e)` becomes `if (c) b else e`. A leaf built with another
    * constructor than the path's, such as `None` for `Some.v`, becomes zero.
    */
  def extractFrom(body: Expr)(using Symbols): Expr =
    if (steps.isEmpty) body
    else if (!steps.exists(_.isConstructor)) Preprocessor.resolveBuiltObjects(readFrom(body))
    else {
      def extractFromLeaves(e: Expr, bindings: Map[Identifier, Expr]): Expr = e match {
        case Let(vd, value, rest) =>
          Let(vd, value, extractFromLeaves(rest, bindings + (vd.id -> value)))
        case IfExpr(condition, thenBranch, elseBranch) =>
          IfExpr(condition, extractFromLeaves(thenBranch, bindings),
                 extractFromLeaves(elseBranch, bindings))
        case leaf if heldBy(leaf, bindings).contains(true) =>
          Preprocessor.resolveBuiltObjects(readFrom(leaf), inScope = bindings)
        case leaf => FieldPath.zero(typeIn(leaf.getType))
      }
      extractFromLeaves(body, Map.empty)
    }

  /** Whether `leaf` holds the number at this path: `Some(x)` holds `Some.v`, `None` does not.
    * An error when the constructor of `leaf` cannot be seen, as for a parameter.
    */
  def heldBy(leaf: Expr, bindings: Map[Identifier, Expr] = Map.empty)(using Symbols)
    : Either[String, Boolean] =
    constructorTests(leaf).foldLeft[Either[String, Boolean]](Right(true)) {
      case (Right(true), test) => Preprocessor.resolveBuiltObjects(test, inScope = bindings) match {
        case BooleanLiteral(holds) => Right(holds)
        case _ => Left(FieldPath.hiddenConstructorMessage)
      }
      case (decided, _) => decided
    }

  /** The tests that `e` is built with the constructors on this path, such as `e is Some`. */
  def constructorTests(e: Expr): Seq[Expr] =
    steps.inits.toSeq.reverse.collect {
      case before :+ FieldStep.Constructor(id) => IsConstructor(FieldPath(before).readFrom(e), id)
    }

  /** The type of the number at this path, in a value of type `valueType`. */
  def typeIn(valueType: Type)(using Symbols): Type =
    steps.foldLeft(valueType) {
      case (TupleType(bases), FieldStep.TupleElement(index)) => bases(index - 1)
      case (adt: ADTType, FieldStep.Field(field)) =>
        adt.getSort.constructors.flatMap(_.fields).find(_.id == field).map(_.getType)
          .getOrElse(Untyped)
      case (tpe, _) => tpe
    }
}

object FieldPath {

  val empty: FieldPath = FieldPath(Seq.empty)

  /** The path to every number inside a value of type `tpe`. For a type with several
    * constructors, the numbers of each, behind a constructor step. A recursive type is not
    * taken apart.
    */
  def numberPathsOf(tpe: Type)(using symbols: Symbols): Seq[FieldPath] = {
    def collectPaths(tpe: Type, prefix: Seq[FieldStep], seen: Set[Identifier]): Seq[FieldPath] =
      tpe match {
        case number if isNumberType(number) => Seq(FieldPath(prefix))

        case TupleType(bases) =>
          bases.zipWithIndex.flatMap { case (base, i) =>
            collectPaths(base, prefix :+ FieldStep.TupleElement(i + 1), seen)
          }

        case adt: ADTType if !seen(adt.id) =>
          adt.getSort.constructors match {
            case Seq(only) =>
              only.fields.flatMap(field =>
                collectPaths(field.getType, prefix :+ FieldStep.Field(field.id), seen + adt.id))
            case several if !isRecursive(adt) =>
              several.flatMap(constructor =>
                constructor.fields.flatMap(field =>
                  collectPaths(field.getType,
                               prefix :+ FieldStep.Constructor(constructor.id) :+
                                 FieldStep.Field(field.id),
                               seen + adt.id)))
            case _ => Seq.empty
          }

        case _ => Seq.empty
      }
    collectPaths(tpe, Seq.empty, Set.empty)
  }

  /** Whether a value of `adt` can hold another one of the same type. */
  private def isRecursive(adt: ADTType)(using Symbols): Boolean = {
    def mentions(tpe: Type): Boolean = tpe match {
      case other: ADTType => other.id == adt.id || other.tps.exists(mentions)
      case TupleType(bases) => bases.exists(mentions)
      case _ => false
    }
    adt.getSort.constructors.exists(_.fields.exists(field => mentions(field.getType)))
  }

  /** Whether a value of type `tpe` can be built with different constructors, also when they
    * hold no number, such as two case objects. A recursive type is not taken apart, unlike
    * in [[InputVariants]], which counts it as a choice.
    */
  def hasConstructorChoice(tpe: Type)(using symbols: Symbols): Boolean = {
    def hasChoiceWithin(tpe: Type, seen: Set[Identifier]): Boolean = tpe match {
      case TupleType(bases) => bases.exists(hasChoiceWithin(_, seen))
      case adt: ADTType if !seen(adt.id) =>
        adt.getSort.constructors match {
          case Seq(only) => only.fields.exists(field => hasChoiceWithin(field.getType, seen + adt.id))
          case _ => !isRecursive(adt)
        }
      case _ => false
    }
    hasChoiceWithin(tpe, Set.empty)
  }

  /** Whether `e` reads a tuple element or a field. */
  def isFieldSelection(e: Expr): Boolean = e match {
    case _: TupleSelect | _: ADTSelector => true
    case _ => false
  }

  private[roundoff] val hiddenConstructorMessage =
    "the constructor of the result is not visible on every path: each branch has to build " +
    "it, such as 'Some(x)', rather than return a value of its type"

  /** The constructor or tuple `e` evaluates to, following `let` bindings, with the bindings
    * in scope there.
    */
  private[roundoff] def builtValueOf(e: Expr, bindings: Map[Identifier, Expr])
    : Option[(Expr, Map[Identifier, Expr])] = e match {
    case Let(vd, value, body) => builtValueOf(body, bindings + (vd.id -> value))
    case v: Variable => bindings.get(v.id).flatMap(builtValueOf(_, bindings))
    case node @ (_: ADT | _: Tuple) => Some((node, bindings))
    case _ => None
  }

  /** The constructors `leaf`, of type `tpe`, is built with, wherever `tpe` has a choice, such
    * as `Seq(Some)` for `Some(x)`. Two leaves with the same constructors end in the same case.
    * An error when one of them cannot be seen.
    */
  def constructorsOf(leaf: Expr, tpe: Type, bindings: Map[Identifier, Expr] = Map.empty)
                    (using symbols: Symbols): Either[String, Seq[Identifier]] =
    if (!hasConstructorChoice(tpe)) Right(Seq.empty)
    else builtValueOf(leaf, bindings) match {
      case Some((ADT(id, _, args), inScope)) =>
        val adt = tpe.asInstanceOf[ADTType]
        val fieldTypes =
          adt.getSort.constructors.find(_.id == id).toSeq.flatMap(_.fields.map(_.getType))
        val here = if (adt.getSort.constructors.size > 1) Seq(id) else Seq.empty
        traverse(args.zip(fieldTypes)) { case (arg, t) => constructorsOf(arg, t, inScope) }
          .map(here ++ _.flatten)
      case Some((Tuple(args), inScope)) =>
        val TupleType(bases) = tpe: @unchecked
        traverse(args.zip(bases)) { case (arg, t) => constructorsOf(arg, t, inScope) }.map(_.flatten)
      case _ => Left(hiddenConstructorMessage)
    }

  private[roundoff] def zero(tpe: Type): Expr = tpe match {
    case FPType(8, 24) => Float32Literal(0.0f)
    case FPType(_, _) => Float64Literal(0.0)
    case Int64Type() => Int64Literal(0)
    case _ => Int32Literal(0)
  }
}

/** A field read off a variable, such as `p.x`: the variable and the path from it. */
case class FieldRead(variable: Variable, path: FieldPath) {

  /** The name of the parameter that replaces it, such as `p_x`. */
  def flatName: String = joinedWith("_")

  /** As it is written in the source, such as `p.x`. */
  def dottedName: String = joinedWith(".")

  private def joinedWith(separator: String): String =
    (variable.id.name +: path.steps.map(_.name)).mkString(separator)

  /** The objects read on the way, such as `p` and `p.a` for `p.a.x`. */
  def enclosingObjects: Seq[Expr] =
    path.steps.inits.toSeq.drop(1).reverse.map(FieldPath(_).readFrom(variable))

  def append(step: FieldStep): FieldRead = FieldRead(variable, path.append(step))
}

/** The parameters of a function once every number field it reads off a parameter is a
  * parameter of its own: the analyzers only take numbers, so `p.x` becomes `p_x`.
  *
  * @param parameterOfFieldRead the new parameter for each field read, such as `p_x` for `p.x`
  * @param parameters           the new parameter list, in declaration order
  */
case class FlattenedParameters(parameterOfFieldRead: Map[FieldRead, Variable],
                               parameters: Seq[ValDef]) {

  /** The field read `parameter` replaces, such as `p.x`, or its own name if it was declared. */
  def sourceNameOf(parameter: ValDef): String =
    parameterOfFieldRead.collectFirst {
      case (read, variable) if variable.id == parameter.id => read.dottedName
    }.getOrElse(parameter.id.name)

  /** `e` with every field read replaced by its new parameter. */
  def withFieldReadsReplaced(e: Expr)(using Symbols): Expr = {
    def replaceFieldReads(e: Expr, bindings: Map[Identifier, FieldRead]): Expr = e match {
      case Operator(Seq(receiver), rebuild) if FieldPath.isFieldSelection(e) =>
        FlattenedParameters.fieldReadOf(e, bindings).flatMap(parameterOfFieldRead.get)
          .getOrElse(rebuild(Seq(replaceFieldReads(receiver, bindings))))

      case Let(vd, value, body) =>
        val innerBindings = FlattenedParameters.fieldReadOf(value, bindings)
          .map(read => bindings + (vd.id -> read)).getOrElse(bindings)
        Let(vd, replaceFieldReads(value, bindings), replaceFieldReads(body, innerBindings))

      case Operator(operands, build) => build(operands.map(replaceFieldReads(_, bindings)))
    }

    replaceFieldReads(e, Map.empty)
  }

  /** Every object on the way to a replaced field. Each may have an invariant of its own. */
  def enclosingObjects: Seq[Expr] =
    parameterOfFieldRead.keys.flatMap(_.enclosingObjects).toSeq.distinct
}

object FlattenedParameters {

  /** `body` with every number field read off a parameter replaced by a new parameter. */
  def flatten(fd: FunDef, body: Expr, limit: TimeLimit = TimeLimit.never)(using Symbols)
    : Either[String, (Expr, FlattenedParameters)] = {
    val parameterIds = fd.params.map(_.id).toSet
    val parameterOfFieldRead = scala.collection.mutable.LinkedHashMap.empty[FieldRead, Variable]

    def flattenFieldReads(e: Expr, bindings: Map[Identifier, FieldRead]): Either[String, Expr] =
      e match {
        case selection
            if FieldPath.isFieldSelection(selection) && isNumberType(selection.getType) =>
          fieldReadOf(selection, bindings) match {
            case Some(read) if parameterIds(read.variable.id) =>
              Right(parameterOfFieldRead.getOrElseUpdate(read,
                Variable.fresh(read.flatName, selection.getType)))
            case Some(read) =>
              Left(s"'${read.dottedName}' is read off '${read.variable.id.name}', which is not one " +
                s"of the values '${fd.id.name}' was given")
            case None =>
              Left("a field is read off something the analysis cannot follow back to a parameter")
          }

        case Let(vd, value, body) =>
          limit.check()
          val innerBindings = fieldReadOf(value, bindings)
            .map(read => bindings + (vd.id -> read)).getOrElse(bindings)

          for {
            flattenedValue <- flattenFieldReads(value, bindings)
            flattenedBody <- flattenFieldReads(body, innerBindings)
          } yield {
            val stillUsed = exprOps.variablesOf(flattenedBody).exists(_.id == vd.id)
            if (isNumberType(vd.tpe) || stillUsed)
              Let(vd, flattenedValue, flattenedBody)
            else flattenedBody
          }

        case Operator(operands, build) => traverse(operands)(flattenFieldReads(_, bindings)).map(build)
      }

    flattenFieldReads(body, Map.empty).map { flattenedBody =>
      val parameters = fd.params.flatMap { parameter =>
        if (isNumberType(parameter.tpe)) Seq(parameter)
        else
          parameterOfFieldRead.collect {
            case (read, variable) if read.variable.id == parameter.id => read.flatName -> variable
          }.toSeq.sortBy(_._1).map(_._2.toVal)
      }

      (flattenedBody, FlattenedParameters(parameterOfFieldRead.toMap, parameters))
    }
  }

  /** The variable and the fields `e` reads, also through `val`s, if `e` is a field read. */
  private def fieldReadOf(e: Expr, bindings: Map[Identifier, FieldRead]): Option[FieldRead] =
    e match {
      case variable: Variable =>
        Some(bindings.getOrElse(variable.id, FieldRead(variable, FieldPath.empty)))
      case ADTSelector(receiver, field) =>
        fieldReadOf(receiver, bindings).map(_.append(FieldStep.Field(field)))
      case TupleSelect(receiver, index) =>
        fieldReadOf(receiver, bindings).map(_.append(FieldStep.TupleElement(index)))
      case _ => None
    }
}
