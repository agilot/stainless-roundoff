/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package roundoff

import org.scalatest.funsuite.AnyFunSuite
import stainless.trees._
import stainless.verification.roundoff._

/** Covers reading a floating-point field as a value of its own.
  *
  * No solver and no analyzer: what is being checked is which readings become which values, and in
  * particular that two ways of reaching the same field come back to one value.
  */
class FlatteningSuite extends AnyFunSuite with Unwrapping {

  private val f64 = FPType(11, 53)
  private val rm = RoundNearestTiesToEven

  private val offset = FreshIdentifier("offset")
  private val calSort = new ADTSort(FreshIdentifier("Calibration"), Seq.empty,
    Seq(new ADTConstructor(FreshIdentifier("Calibration"), FreshIdentifier("Calibration"),
                           Seq(ValDef(offset, f64)))), Seq.empty)
  private val calType = ADTType(calSort.id, Seq.empty)

  private val raw = FreshIdentifier("raw")
  private val cal = FreshIdentifier("cal")
  private val sensorSort = new ADTSort(FreshIdentifier("Sensor"), Seq.empty,
    Seq(new ADTConstructor(FreshIdentifier("Sensor"), FreshIdentifier("Sensor"),
                           Seq(ValDef(raw, f64), ValDef(cal, calType)))), Seq.empty)
  private val sensorType = ADTType(sensorSort.id, Seq.empty)

  // The constructors above name their own sort, which is what `getSort` follows.
  private val sorts = Seq(
    new ADTSort(calSort.id, Seq.empty,
      Seq(new ADTConstructor(calSort.constructors.head.id, calSort.id, Seq(ValDef(offset, f64)))),
      Seq.empty),
    new ADTSort(sensorSort.id, Seq.empty,
      Seq(new ADTConstructor(sensorSort.constructors.head.id, sensorSort.id,
                             Seq(ValDef(raw, f64), ValDef(cal, calType)))),
      Seq.empty))

  private val s = Variable.fresh("s", sensorType)

  private def flatten(body: Expr, params: Seq[ValDef] = Seq(s.toVal))
    : Either[String, (Expr, ParameterFlattening)] = {
    val fd = new FunDef(FreshIdentifier("f"), Seq.empty, params, f64, body, Seq.empty)
    given Symbols = NoSymbols.withSorts(sorts).withFunctions(Seq(fd))
    ParameterFlattening.flatten(fd, body)
  }

  private def value(body: Expr): (Expr, ParameterFlattening) =
    flatten(body).orFail

  test("a field of a parameter becomes a value of its own") {
    val (rewritten, flattening) = value(ADTSelector(s, raw))
    assert(flattening.accessPathVariables.size == 1)
    assert(rewritten.isInstanceOf[Variable])
    assert(rewritten.asInstanceOf[Variable].id.name == "s_raw")
  }

  test("a field of a field is reached through both, and named after the way there") {
    val (rewritten, flattening) = value(ADTSelector(ADTSelector(s, cal), offset))
    assert(flattening.accessPathVariables.size == 1)
    assert(rewritten.asInstanceOf[Variable].id.name == "s_cal_offset")
  }

  test("two readings of one field are one value, since they cannot differ") {
    val read = ADTSelector(s, raw)
    val (rewritten, flattening) = value(FPAdd(rm, read, read))
    assert(flattening.accessPathVariables.size == 1)
    val FPAdd(_, l, r) = rewritten: @unchecked
    assert(l == r)
  }

  test("two different fields are two values") {
    val (_, flattening) = value(FPAdd(rm, ADTSelector(s, raw), ADTSelector(ADTSelector(s, cal), offset)))
    assert(flattening.accessPathVariables.size == 2)
    assert(flattening.parameters.map(_.id.name).sorted == Seq("s_cal_offset", "s_raw"))
  }

  test("a field read through a binding is the same value as one read directly") {
    // What inlining a helper leaves behind: the callee reads its own name for the object.
    val inner = ValDef.fresh("p", sensorType)
    val body = FPAdd(rm, ADTSelector(s, raw),
                     Let(inner, s, ADTSelector(inner.toVariable, raw)))
    val (rewritten, flattening) = value(body)

    assert(flattening.accessPathVariables.size == 1, "the two readings came back to one value")
    val FPAdd(_, l, r) = rewritten: @unchecked
    assert(l == r)
  }

  test("the binding that passed the object around is left out, having nothing reading it") {
    val inner = ValDef.fresh("p", sensorType)
    val (rewritten, _) = value(Let(inner, s, ADTSelector(inner.toVariable, raw)))
    assert(!rewritten.isInstanceOf[Let], s"a dead binding survived in $rewritten")
  }

  test("a field of something the function was not given is refused") {
    val other = Variable.fresh("built", sensorType)
    val outcome = flatten(Let(other.toVal, s, ADTSelector(other, raw)), params = Seq.empty)
    assert(outcome.isLeft)
  }

  test("an object-valued field is not a value, so it is left as it was") {
    val (rewritten, flattening) = value(ADTSelector(s, cal))
    assert(flattening.accessPathVariables.isEmpty)
    assert(rewritten == ADTSelector(s, cal))
  }

  test("a tuple parameter is taken apart by position, the same way a class is by field") {
    val pair = Variable.fresh("p", TupleType(Seq(f64, f64)))
    val body = FPAdd(rm, TupleSelect(pair, 1), TupleSelect(pair, 2))
    val (rewritten, flattening) = flatten(body, params = Seq(pair.toVal))
      .orFail

    assert(flattening.accessPathVariables.size == 2)
    assert(flattening.parameters.map(_.id.name).sorted == Seq("p__1", "p__2"))

    // The tuple is gone from the body: what is left adds two plain variables.
    val FPAdd(_, l, r) = rewritten: @unchecked
    assert(l.isInstanceOf[Variable] && r.isInstanceOf[Variable])
    assert(l != r, "the two positions are two values")
  }

  test("a position read through a binding is the same value as one read directly") {
    val pair = Variable.fresh("p", TupleType(Seq(f64, f64)))
    val inner = ValDef.fresh("q", TupleType(Seq(f64, f64)))
    val body = FPAdd(rm, TupleSelect(pair, 1),
                     Let(inner, pair, TupleSelect(inner.toVariable, 1)))
    val (rewritten, flattening) = flatten(body, params = Seq(pair.toVal))
      .orFail

    assert(flattening.accessPathVariables.size == 1, "the two readings came back to one value")
    val FPAdd(_, l, r) = rewritten: @unchecked
    assert(l == r)
  }

  test("a plain parameter is carried through untouched") {
    val x = Variable.fresh("x", f64)
    val (rewritten, flattening) = flatten(FPAdd(rm, x, x), params = Seq(x.toVal))
      .orFail
    assert(flattening.accessPathVariables.isEmpty)
    assert(flattening.parameters.map(_.id.name) == Seq("x"))
    assert(rewritten == FPAdd(rm, x, x))
  }
}
