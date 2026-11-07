/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification
package roundoff

import org.scalatest.funsuite.AnyFunSuite
import stainless.roundoff.Unwrapping
import stainless.trees._

/** Covers inputs whose type has several constructors: one variant of the function per
  * constructor, in which every constructor test is answered. Nothing here needs a solver.
  */
class InputVariantsSuite extends AnyFunSuite with Unwrapping {

  private val f64 = FPType(11, 53)
  private val rm = RoundNearestTiesToEven

  private val x = Variable.fresh("x", f64)

  /** `sealed abstract class Answer` with `Known(known: Double)` and `Absent()`. */
  private val known = ValDef.fresh("known", f64)
  private val answerId = FreshIdentifier("Answer")
  private val knownId = FreshIdentifier("Known")
  private val absentId = FreshIdentifier("Absent")
  private val answer =
    new ADTSort(answerId, Seq(),
                Seq(new ADTConstructor(knownId, answerId, Seq(known)),
                    new ADTConstructor(absentId, answerId, Seq())),
                Seq())
  private val a = Variable.fresh("a", ADTType(answerId, Seq()))

  /** `sealed abstract class Chain` with `Link(rest: Chain)` and `End()`. */
  private val chainId = FreshIdentifier("Chain")
  private val chain =
    new ADTSort(chainId, Seq(),
                Seq(new ADTConstructor(FreshIdentifier("Link"), chainId,
                                       Seq(ValDef.fresh("rest", ADTType(chainId, Seq())))),
                    new ADTConstructor(FreshIdentifier("End"), chainId, Seq())),
                Seq())

  private given Symbols = NoSymbols.withSorts(Seq(answer, chain))

  private def between(low: Double, e: Expr, high: Double): Expr =
    And(FPLessEquals(Float64Literal(low), e), FPLessEquals(e, Float64Literal(high)))

  private val isKnown = IsConstructor(a, knownId)
  private val knownValue = ADTSelector(a, known.id)

  /** `if (a is Known) a.known * x else x`, with `x` and a known value in `[0, 1]`. */
  private def function(precondition: Expr = Or(Not(isKnown), between(0, knownValue, 1))) =
    new FunDef(FreshIdentifier("f"), Seq.empty, Seq(a.toVal, x.toVal), f64,
               Require(And(between(0, x, 1), precondition),
                       IfExpr(isKnown, FPMul(rm, knownValue, x), x)),
               Seq.empty)

  test("an input with several constructors gives one variant per constructor") {
    val variants = InputVariants.allowedVariants(function()).orFail
    assert(variants.map(_.description) == Seq("a = Known", "a = Absent"))
    // Each variant takes the fields of its own constructor as inputs.
    assert(variants.map(_.function.params.map(_.id.name)) == Seq(Seq("a_known", "x"), Seq("x")))
  }

  test("a variant says where in the parameters each input is, and which constructor it chose") {
    val Seq(knownVariant, absentVariant) = InputVariants.allowedVariants(function()).orFail: @unchecked
    val Seq(field, input) = knownVariant.function.params: @unchecked
    val whole = FieldRead(a, FieldPath.empty)
    assert(knownVariant.sourceOfInput(field.id) ==
             FieldRead(a, FieldPath(Seq(FieldStep.Constructor(knownId), FieldStep.Field(known.id)))))
    assert(knownVariant.sourceOfInput(input.id) == FieldRead(x, FieldPath.empty))
    assert(knownVariant.chosenConstructors == Seq(whole -> knownId))
    assert(absentVariant.chosenConstructors == Seq(whole -> absentId))
  }

  test("in a variant, constructor tests are answered and the fields have their ranges") {
    val knownVariant = InputVariants.allowedVariants(function()).orFail.head.function
    val (body, _, flattening) = Preprocessor(knownVariant).orFail
    assert(!exprOps.exists { case _: IfExpr | _: IsConstructor => true; case _ => false }(body))

    val spec = InputRanges.inputSpecOf(knownVariant, body, flattening).orFail
    val field = knownVariant.params.head.id
    assert(spec.ranges(field) == (0.0, 1.0))
  }

  test("a variant the precondition rules out is left out") {
    val variants = InputVariants.allowedVariants(function(precondition = And(isKnown,
                                                                between(0, knownValue, 1))))
    assert(variants.orFail.map(_.description) == Seq("a = Known"))
  }

  test("an input of a type that can hold itself is refused") {
    val c = Variable.fresh("c", ADTType(chainId, Seq()))
    val fd = new FunDef(FreshIdentifier("g"), Seq.empty, Seq(c.toVal, x.toVal), f64,
                        Require(between(0, x, 1), x), Seq.empty)
    InputVariants.allowedVariants(fd) match {
      case Left(why) => assert(why.contains("no bounded number of shapes"))
      case Right(_) => fail("an input of a recursive type was split into variants")
    }
  }

  test("a function applied where it is known is replaced by its body") {
    val v = ValDef.fresh("v", f64)
    val applied = Application(Lambda(Seq(v), FPMul(rm, v.toVariable, v.toVariable)), Seq(x))
    Preprocessor.resolveBuiltObjects(applied) match {
      case Let(bound, `x`, FPMul(_, left, right)) =>
        assert(left == bound.toVariable && right == bound.toVariable)
      case other => fail(s"the function was not applied: $other")
    }
  }

  test("a condition with a false part is false, wherever the part is") {
    val built = ADT(absentId, Seq(), Seq())
    val condition = And(between(0, x, 1), IsConstructor(built, knownId))
    assert(Preprocessor.normalisedCondition(condition) == BooleanLiteral(false))
  }
}
