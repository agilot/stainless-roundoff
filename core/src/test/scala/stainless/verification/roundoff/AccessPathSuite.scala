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
  private val answer =
    new ADTSort(answerId, Seq(),
                Seq(new ADTConstructor(FreshIdentifier("Known"), answerId, Seq(known)),
                    new ADTConstructor(FreshIdentifier("Absent"), answerId, Seq())),
                Seq())

  private given Symbols = NoSymbols.withSorts(Seq(reading, span, answer))

  private def labels(tpe: Type): Seq[String] = AccessPath.of(tpe).map(_.displayName)

  test("a result that is one number is one path, with nothing to say about it") {
    assert(AccessPath.of(f64) == Seq(AccessPath.nil))
    assert(AccessPath.of(f64).map(_.displayName) == Seq(""))
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

  test("a class with more than one constructor is not taken apart") {
    assert(AccessPath.of(ADTType(answerId, Seq())).isEmpty)
    assert(AccessPath.refusal(ADTType(answerId, Seq())).contains("more than one constructor"))
  }

  test("a result holding no number at all yields nothing") {
    assert(AccessPath.of(BooleanType()).isEmpty)
    assert(AccessPath.of(TupleType(Seq(BooleanType(), IntegerType()))).isEmpty)
  }

  test("projecting reads the field off a constructor on every branch") {
    // if (x < y) Reading(x + y, true) else Reading(x * y, false)
    def built(e: Expr, flag: Boolean) =
      ADT(reading.constructors.head.id, Seq(), Seq(e, BooleanLiteral(flag)))
    val body = IfExpr(FPLessThan(x, y), built(FPAdd(rm, x, y), true), built(FPMul(rm, x, y), false))

    val path = AccessPath.of(ADTType(readingId, Seq())).head
    assert(Preprocessor.project(body, path) ==
             IfExpr(FPLessThan(x, y), FPAdd(rm, x, y), FPMul(rm, x, y)))
  }

  test("projecting follows a constructor through the binding it was given") {
    val held = ValDef.fresh("held", TupleType(Seq(f64, f64)))
    val body = Let(held, Tuple(Seq(FPAdd(rm, x, y), FPSub(rm, x, y))), held.toVariable)

    val second = AccessPath.of(TupleType(Seq(f64, f64)))(1)
    assert(Preprocessor.project(body, second) == FPSub(rm, x, y))
  }

  test("the empty path is the body itself, untouched") {
    val body = FPAdd(rm, x, y)
    assert(Preprocessor.project(body, AccessPath.nil) == body)
  }
}
