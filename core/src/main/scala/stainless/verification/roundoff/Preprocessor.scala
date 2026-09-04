/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification
package roundoff

import trees._

object Preprocessor {

  def apply(fd: FunDef)(using Symbols): Either[String, Expr] =
    for {
      raw <- exprOps.withoutSpecs(fd.fullBody).toRight("function has no body")
      // Calls come out first, so that a conditional or a selection arriving from a
      // callee meets the same rewrites as one written here.
      called <- inlineCalls(raw)
      body = liftConditionals(unfoldSelections(stripAnnotations(called)))
      _ <- isUnsupported(body).toLeft(())
      // Lifting leaves none behind, and one left behind would be measured as rounding
      // alone, which understates the error.
      _ <- Either.cond(!branchesInsideExpression(body), (),
             "a conditional remains inside an expression")
    } yield body

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
      // The library implements these itself, and the analysis reads each as the exact
      // function it approximates, so only the arguments are followed.
      case MathCall(_, _) => descend(e)
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
      case MathCall(_, args) => args.view.flatMap(rec).headOption

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