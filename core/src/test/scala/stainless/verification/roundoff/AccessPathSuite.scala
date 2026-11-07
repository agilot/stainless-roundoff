/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification
package roundoff

import org.scalatest.funsuite.AnyFunSuite
import stainless.trees._

/** Covers which numbers a result holds, and how the body is narrowed to one of them.
  *
  * The error of several numbers is several errors, so a result is taken apart before anything
  * is measured. Nothing here needs a solver.
  */
class AccessPathSuite extends AnyFunSuite {

  private val f64 = FPType(11, 53)
  private val rm = RoundNearestTiesToEven

  private val x = Variable.fresh("x", f64)
  private val y = Variable.fresh("y", f64)

  /** `case class Reading(value: Double, tag: Boolean)` */
  private val tag = ValDef.fresh("tag", BooleanType())
  private val value = ValDef.fresh("value", f64)
  private val readingId = FreshIdentifier("Reading")
  private val reading =
    new ADTSort(readingId, Seq(), Seq(new ADTConstructor(readingId, readingId,
                                       Seq(value, tag))), Seq())

  /** `case class Span(near: Reading, far: Double)` */
  private val near = ValDef.fresh("near", ADTType(readingId, Seq()))
  private val far = ValDef.fresh("far", f64)
  private val spanId = FreshIdentifier("Span")
  private val span =
    new ADTSort(spanId, Seq(), Seq(new ADTConstructor(spanId, spanId, Seq(near, far))), Seq())

  /** `sealed abstract class Answer` with two cases, one of them carrying a number. */
  private val known = ValDef.fresh("known", f64)
  private val answerId = FreshIdentifier("Answer")
  private val knownId = FreshIdentifier("Known")
  private val absentId = FreshIdentifier("Absent")
  private val answer =
    new ADTSort(answerId, Seq(),
                Seq(new ADTConstructor(knownId, answerId, Seq(known)),
                    new ADTConstructor(absentId, answerId, Seq())),
                Seq())

  /** `sealed trait Conclusion` with two case objects, which hold no number. */
  private val conclusionId = FreshIdentifier("Conclusion")
  private val continueId = FreshIdentifier("Continue")
  private val finishedId = FreshIdentifier("Finished")
  private val conclusion =
    new ADTSort(conclusionId, Seq(),
                Seq(new ADTConstructor(continueId, conclusionId, Seq()),
                    new ADTConstructor(finishedId, conclusionId, Seq())),
                Seq())

  private given Symbols = NoSymbols.withSorts(Seq(reading, span, answer, conclusion))

  private def labels(tpe: Type): Seq[String] = FieldPath.numberPathsOf(tpe).map(_.displayName)

  test("a result that is one number is one path, with nothing to say about it") {
    assert(FieldPath.numberPathsOf(f64) == Seq(FieldPath.empty))
    assert(FieldPath.numberPathsOf(f64).map(_.displayName) == Seq(""))
  }

  test("a tuple is taken apart by position, one-based as a selector reads it") {
    assert(labels(TupleType(Seq(f64, f64, f64))) == Seq("_1", "_2", "_3"))
  }

  test("a case class is taken apart by field, and a field that is not a number is passed over") {
    assert(labels(ADTType(readingId, Seq())) == Seq("value"))
  }

  test("taking apart goes as deep as the type does") {
    assert(labels(ADTType(spanId, Seq())) == Seq("near.value", "far"))
  }

  test("a tuple of case classes composes both ways of stepping") {
    assert(labels(TupleType(Seq(ADTType(spanId, Seq()), f64))) ==
             Seq("_1.near.value", "_1.far", "_2"))
  }

  private val answerType = ADTType(answerId, Seq())
  private val knownValue = FieldPath(Seq(FieldStep.Constructor(knownId), FieldStep.Field(known.id)))

  test("a class with several constructors gives the numbers of each, behind its constructor") {
    assert(FieldPath.numberPathsOf(answerType) == Seq(knownValue))
    assert(labels(answerType) == Seq("Known.known"))
    assert(FieldPath.hasConstructorChoice(answerType))
    assert(!FieldPath.hasConstructorChoice(ADTType(spanId, Seq())))
  }

  test("a leaf holds a number behind a constructor only when it is built with it") {
    assert(knownValue.heldBy(ADT(knownId, Seq(), Seq(x))) == Right(true))
    assert(knownValue.heldBy(ADT(absentId, Seq(), Seq())) == Right(false))
    // Through the binding it was given, as a leaf closes over the values it reads.
    val bound = ValDef.fresh("a", answerType)
    assert(knownValue.heldBy(Let(bound, ADT(knownId, Seq(), Seq(x)), bound.toVariable)) ==
             Right(true))
    // A value whose constructor the body does not show cannot be placed.
    assert(knownValue.heldBy(Variable.fresh("p", answerType)).isLeft)
  }

  test("a choice between constructors that hold no number is still a choice of case") {
    val tpe = TupleType(Seq(ADTType(conclusionId, Seq()), f64))
    assert(labels(tpe) == Seq("_2"))
    assert(FieldPath.hasConstructorChoice(tpe))
    assert(FieldPath.constructorsOf(Tuple(Seq(ADT(finishedId, Seq(), Seq()), x)), tpe) ==
             Right(Seq(finishedId)))
    // Constructors without a choice between them are no case.
    assert(!FieldPath.hasConstructorChoice(TupleType(Seq(ADTType(spanId, Seq()), f64))))
  }

  test("the case of a leaf is the constructors it is built with") {
    assert(FieldPath.constructorsOf(ADT(knownId, Seq(), Seq(x)), answerType) == Right(Seq(knownId)))
    assert(FieldPath.constructorsOf(ADT(absentId, Seq(), Seq()), answerType) == Right(Seq(absentId)))
    assert(FieldPath.constructorsOf(x, f64) == Right(Seq()))
  }

  test("projecting through a constructor keeps the leaves built with it, the others are zero") {
    val body = IfExpr(FPLessThan(x, y), ADT(knownId, Seq(), Seq(x)), ADT(absentId, Seq(), Seq()))
    assert(knownValue.extractFrom(body) == IfExpr(FPLessThan(x, y), x, Float64Literal(0.0)))
  }

  test("a number behind a constructor is reached after testing for it") {
    val res = Variable.fresh("res", answerType)
    assert(knownValue.constructorTests(res) == Seq(IsConstructor(res, knownId)))
    assert(knownValue.readFrom(res) == ADTSelector(res, known.id))
  }

  test("a recursive class with several constructors is not taken apart") {
    val chainId = FreshIdentifier("Chain")
    val linkId = FreshIdentifier("Link")
    val endId = FreshIdentifier("End")
    val chain = new ADTSort(chainId, Seq(),
      Seq(new ADTConstructor(linkId, chainId,
                             Seq(ValDef.fresh("head", f64),
                                 ValDef.fresh("next", ADTType(chainId, Seq())))),
          new ADTConstructor(endId, chainId, Seq())),
      Seq())
    given Symbols = NoSymbols.withSorts(Seq(chain))
    assert(FieldPath.numberPathsOf(ADTType(chainId, Seq())).isEmpty)
  }

  test("a result holding no number at all yields nothing") {
    assert(FieldPath.numberPathsOf(BooleanType()).isEmpty)
    assert(FieldPath.numberPathsOf(TupleType(Seq(BooleanType(), IntegerType()))).isEmpty)
  }

  test("projecting reads the field off a constructor on every branch") {
    // if (x < y) Reading(x + y, true) else Reading(x * y, false)
    def built(e: Expr, flag: Boolean) =
      ADT(reading.constructors.head.id, Seq(), Seq(e, BooleanLiteral(flag)))
    val body = IfExpr(FPLessThan(x, y), built(FPAdd(rm, x, y), true), built(FPMul(rm, x, y), false))

    val path = FieldPath.numberPathsOf(ADTType(readingId, Seq())).head
    assert(path.extractFrom(body) ==
             IfExpr(FPLessThan(x, y), FPAdd(rm, x, y), FPMul(rm, x, y)))
  }

  test("projecting follows a constructor through the binding it was given") {
    val held = ValDef.fresh("held", TupleType(Seq(f64, f64)))
    val body = Let(held, Tuple(Seq(FPAdd(rm, x, y), FPSub(rm, x, y))), held.toVariable)

    val second = FieldPath.numberPathsOf(TupleType(Seq(f64, f64)))(1)
    assert(second.extractFrom(body) == FPSub(rm, x, y))
  }

  test("the empty path is the body itself, untouched") {
    val body = FPAdd(rm, x, y)
    assert(FieldPath.empty.extractFrom(body) == body)
  }

  test("a selection meeting a constructor that holds no such field is left alone") {
    // The same selection against the constructor that does hold the field, so that what
    // follows tells the guard apart from the selection never reaching a constructor at all.
    val held = ADT(knownId, Seq(), Seq(FPAdd(rm, x, y)))
    assert(Preprocessor.resolveBuiltObjects(ADTSelector(held, known.id)) == FPAdd(rm, x, y))

    // `Absent` carries nothing, so selecting `Known`'s field meets no field to take.
    val absent = ADT(absentId, Seq(), Seq())
    val fromAbsent = ADTSelector(absent, known.id)
    assert(Preprocessor.resolveBuiltObjects(fromAbsent) == fromAbsent)

    // One side of the branch holds the field and the other does not, so neither is selected:
    // what is left has to be an expression, not a selection sitting on one branch.
    val either = IfExpr(FPLessThan(x, y), ADT(knownId, Seq(), Seq(FPAdd(rm, x, y))), absent)
    val fromEither = ADTSelector(either, known.id)
    assert(Preprocessor.resolveBuiltObjects(fromEither) == fromEither)
  }
}
