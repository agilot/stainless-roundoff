/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification
package roundoff

import trees.*

object Preprocessor {

  /** The body as the analysis reads it, one expression per number in the result.
    *
    * Everything up to the projection is done once: the paths of a result are read off the same
    * computation however it is taken apart, so inlining, flattening and lifting are shared and
    * only the last step differs. Projecting is the fold again, on a selector at the root, which
    * pushes it down the bindings and branches until it meets the constructors at the leaves.
    */
  def apply(fd: FunDef)(using Symbols)
    : Either[String, (Expr, Seq[AccessPath], Flattening)] =
    for {
      raw <- exprOps.withoutSpecs(fd.fullBody).toRight("function has no body")
      // Calls come out first, so that a conditional or a selection arriving from a
      // callee meets the same rewrites as one written here.
      called <- inlineCalls(raw)
      // A thing built and taken apart again is what it was built from. Done before the fields,
      // so that one read off a constructor is followed to whatever the constructor was given.
      built = foldConstructors(stripAnnotations(called))
      // Then the fields, so that what follows only ever sees values. After inlining, since a
      // callee reads its own name for an object; before the rest, since they know no fields.
      read <- Flattening.of(fd, built)
      (fields, flattening) = read
      // And again once conditionals are lifted: a selector that sat on a branch now sits on each
      // of its sides, where each side is a constructor of its own.
      whole = foldConstructors(liftConditionals(unfoldSelections(fields)))

      paths = AccessPath.list(fd.returnType)
      _ <- Either.cond(paths.nonEmpty, (), AccessPath.errorMessage(fd.returnType))

      // Checked one field at a time, since what the analysis can read is a number's own
      // computation and the constructor holding it is not part of that.
      _ <- traverse(paths) { path =>
             val body = project(whole, path)
             for {
               _ <- isUnsupported(body).toLeft(())
               // Lifting leaves none behind, and one left behind would be measured as
               // rounding alone, which understates the error.
               _ <- Either.cond(!branchesInsideExpression(body), (),
                      "a conditional remains inside an expression")
             } yield ()
           }
    } yield (whole, paths, flattening)

  /** `e` narrowed to one number of the result it computes.
    *
    * The selector is pushed down the bindings and the branches until it meets the constructors
    * at the leaves, which is the fold that already reads a field off an object built and taken
    * apart again — here with the taking apart supplied rather than written.
    */
  def project(e: Expr, path: AccessPath)(using Symbols): Expr =
    if (path.steps.isEmpty) e else foldConstructors(path.select(e))

  private def traverse[A, B](xs: Seq[A])(f: A => Either[String, B]): Either[String, Seq[B]] =
    xs.foldLeft(Right(Vector.empty): Either[String, Vector[B]]) { (acc, x) =>
      for { done <- acc; next <- f(x) } yield done :+ next
    }

  def stripAnnotations(e: Expr): Expr = exprOps.postMap {
    case Assert(_, _, body) => Some(body)
    case Assume(_, body) => Some(body)
    case Annotated(body, _) => Some(body)
    case Decreases(_, body) => Some(body)
    case _ => None
  }(e)

  /** How many calls one body may absorb before its paths stop being worth enumerating. */
  private val inliningBudget = 256

  /** Replaces every call the analysis holds no meaning of its own for by the body behind
    * it, so that a computation written across several definitions is measured as the one
    * it stands for.
    */
  private def inlineCalls(e: Expr)(using symbols: Symbols): Either[String, Expr] = {
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

      for {
        _ <- Either.cond(remaining > 0, (),
               s"inlining passed $inliningBudget calls, which is more than the analysis " +
                 "can enumerate paths through")
        _ <- Either.cond(!symbols.isRecursive(call.id), (),
               s"'$name' is recursive, so inlining it reaches no finite body")
        _ <- hidden.map(flag => s"'$name' is @$flag, so its body is hidden from the analysis")
               .toLeft(())
        // The callee's own precondition is dropped along with the rest of its specs: it
        // is checked as its own obligation, and the range each parameter really takes
        // follows from the argument bound to it.
        body <- exprOps.withoutSpecs(call.tfd.fullBody).toRight(s"'$name' has no body")
        _ = remaining -= 1

        arguments <- traverse(call.args)(rec)
        parameters = call.tfd.params.map(_.freshen)
        renamed = exprOps.freshenLocals(
                    exprOps.replaceFromSymbols(
                      call.tfd.params.zip(parameters.map(_.toVariable)).toMap, body))
        result <- rec(renamed)
      } yield
        // Parameters become bindings rather than substitutions, so an argument is
        // computed once however often the body reads it, and two leaves that compute the
        // same thing stay equal as trees.
        parameters.zip(arguments).foldRight(result) {
          case ((parameter, argument), kept) => Let(parameter, argument, kept)
        }
    }

    rec(e)
  }

  /** Reads a thing written and immediately taken apart again as what it was written from.
    *
    * Imperative code arrives in this shape. Assigning to a variable on both sides of a conditional
    * is encoded as the two sides handing back what changed, read off by position, and a callee
    * returning several values does the same. Neither is a computation of its own: the value asked
    * for is one of the operands the constructor was given.
    */
  private def foldConstructors(e: Expr)(using symbols: Symbols): Expr = {

    def rec(e: Expr, built: Map[Identifier, Expr]): Expr = {
      // What is read arrives under whatever the bindings and branches on the way to it left
      // there, so the reading is carried inside until it meets what it reads. The bindings it
      // passes on the way are added to the ones it knows, since a value written down a line
      // above and named on the next is reached through its own name.
      def through(e: Expr, known: Map[Identifier, Expr])
                 (read: Expr => Option[Expr]): Option[Expr] = e match {
        case Let(vd, value, body) =>
          through(body, known + (vd.id -> value))(read).map(Let(vd, value, _))
        case IfExpr(condition, thenBranch, elseBranch) =>
          for {
            taken <- through(thenBranch, known)(read)
            untaken <- through(elseBranch, known)(read)
          } yield IfExpr(condition, taken, untaken)
        case v: Variable => known.get(v.id).flatMap(through(_, known)(read))
        case other => read(other)
      }

      /** What a reading found, tidied: the bindings it made unnecessary are gone.
        *
        * Going round again is what drops them, and it terminates because a reading that found
        * something returns a smaller tree than it was given.
        */
      def folded(found: Option[Expr], otherwise: => Expr): Expr =
        found.map(rec(_, built)).getOrElse(otherwise)

      e match {
        case TupleSelect(receiver, index) =>
          val target = rec(receiver, built)
          folded(through(target, built) {
            case Tuple(fields) => Some(fields(index - 1))
            case _ => None
          }, TupleSelect(target, index))

        case ADTSelector(receiver, field) =>
          val target = rec(receiver, built)
          folded(through(target, built) {
            case ADT(id, _, fields) =>
              Option.when(symbols.getConstructor(id).fields.exists(_.id == field))(
                fields(symbols.getConstructor(id).fields.indexWhere(_.id == field)))
            case _ => None
          }, ADTSelector(target, field))

        case Let(vd, value, body) =>
          val bound = rec(value, built)
          // Every binding is remembered, and carrying a reading inside one is what decides
          // whether it meets anything: where it does not, the reading stays where it was.
          val rest = rec(body, built + (vd.id -> bound))
          // Whatever was written is now in the places that read it, so the name it was given
          // has nothing left needing it.
          if (exprOps.variablesOf(rest).exists(_.id == vd.id)) Let(vd, bound, rest) else rest

        case Operator(operands, build) => build(operands.map(rec(_, built)))
      }
    }

    rec(e, Map.empty)
  }

  /** Rewrites the operations that pick a value by comparing into the conditional they
    * stand for, since neither Daisy nor the path enumeration knows them by name.
    */
  private def unfoldSelections(e: Expr)(using Symbols): Expr = exprOps.postMap {
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

  private def hasConditional(body: Expr): Boolean =
    exprOps.exists { case _: IfExpr => true; case _ => false }(body)

  /** Rewrites a body into a tree of conditionals over straight-line leaves, so that no
    * branch is left inside an expression where the path enumeration would miss its jump.
    */
  def liftConditionals(e: Expr): Expr = e match {
    case Let(vd, value, body) =>
      val liftedBody = liftConditionals(body)
      distribute(Seq(liftConditionals(value)))(vs => Let(vd, vs.head, liftedBody))

    case IfExpr(condition, thenBranch, elseBranch) =>
      val liftedThen = liftConditionals(thenBranch)
      val liftedElse = liftConditionals(elseBranch)
      distribute(Seq(liftConditionals(condition)))(cs => IfExpr(cs.head, liftedThen, liftedElse))

    case Operator(operands, build) => distribute(operands.map(liftConditionals))(build)
  }

  /** Moves the leftmost conditional among already lifted operands above the node they
    * belong to, and repeats until none is left.
    */
  private def distribute(operands: Seq[Expr])(build: Seq[Expr] => Expr): Expr = {
    def above(i: Int): Option[Expr] = operands(i) match {
      case IfExpr(condition, thenBranch, elseBranch) =>
        Some(IfExpr(condition,
                    distribute(operands.updated(i, thenBranch))(build),
                    distribute(operands.updated(i, elseBranch))(build)))

      // The branches mention what the binding binds, so it has to come out with them.
      case Let(vd, value, body) if branchesAtTop(body) =>
        Some(Let(vd, value, distribute(operands.updated(i, body))(build)))

      case _ => None
    }

    operands.indices.view.flatMap(above).headOption.getOrElse(build(operands))
  }

  private def branchesAtTop(e: Expr): Boolean = e match {
    case _: IfExpr => true
    case Let(_, _, body) => branchesAtTop(body)
    case _ => false
  }

  /** Whether a conditional sits anywhere other than on the spine of bindings and branches. */
  private def branchesInsideExpression(e: Expr): Boolean = e match {
    case Let(_, value, body) => hasConditional(value) || branchesInsideExpression(body)
    case IfExpr(condition, thenBranch, elseBranch) =>
      hasConditional(condition) ||
        branchesInsideExpression(thenBranch) || branchesInsideExpression(elseBranch)
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
  def displayName: String = steps.map(_.name).mkString(".")
  def select(e: Expr): Expr = steps.foldLeft(e)((inner, step) => step.select(inner))
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
}