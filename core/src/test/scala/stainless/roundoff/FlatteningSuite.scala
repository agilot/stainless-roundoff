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
    : Either[String, (Expr, FlattenedParameters)] = {
    val fd = new FunDef(FreshIdentifier("f"), Seq.empty, params, f64, body, Seq.empty)
    given Symbols = NoSymbols.withSorts(sorts).withFunctions(Seq(fd))
    FlattenedParameters.flatten(fd, body)
  }

  private def value(body: Expr): (Expr, FlattenedParameters) =
    flatten(body).orFail

  test("a field of a parameter becomes a value of its own") {
    val (rewritten, flattening) = value(ADTSelector(s, raw))
    assert(flattening.parameterOfFieldRead.size == 1)
    assert(rewritten.isInstanceOf[Variable])
    assert(rewritten.asInstanceOf[Variable].id.name == "s_raw")
  }

  test("a field of a field is reached through both, and named after the way there") {
    val (rewritten, flattening) = value(ADTSelector(ADTSelector(s, cal), offset))
    assert(flattening.parameterOfFieldRead.size == 1)
    assert(rewritten.asInstanceOf[Variable].id.name == "s_cal_offset")
  }

  test("two readings of one field are one value, since they cannot differ") {
    val read = ADTSelector(s, raw)
    val (rewritten, flattening) = value(FPAdd(rm, read, read))
    assert(flattening.parameterOfFieldRead.size == 1)
    val FPAdd(_, l, r) = rewritten: @unchecked
    assert(l == r)
  }

  test("two different fields are two values") {
    val (_, flattening) = value(FPAdd(rm, ADTSelector(s, raw), ADTSelector(ADTSelector(s, cal), offset)))
    assert(flattening.parameterOfFieldRead.size == 2)
    assert(flattening.parameters.map(_.id.name).sorted == Seq("s_cal_offset", "s_raw"))
  }

  test("a field read through a binding is the same value as one read directly") {
    // What inlining a helper leaves behind: the callee reads its own name for the object.
    val inner = ValDef.fresh("p", sensorType)
    val body = FPAdd(rm, ADTSelector(s, raw),
                     Let(inner, s, ADTSelector(inner.toVariable, raw)))
    val (rewritten, flattening) = value(body)

    assert(flattening.parameterOfFieldRead.size == 1, "the two readings came back to one value")
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
    assert(flattening.parameterOfFieldRead.isEmpty)
    assert(rewritten == ADTSelector(s, cal))
  }

  test("a tuple parameter is taken apart by position, the same way a class is by field") {
    val pair = Variable.fresh("p", TupleType(Seq(f64, f64)))
    val body = FPAdd(rm, TupleSelect(pair, 1), TupleSelect(pair, 2))
    val (rewritten, flattening) = flatten(body, params = Seq(pair.toVal))
      .orFail

    assert(flattening.parameterOfFieldRead.size == 2)
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

    assert(flattening.parameterOfFieldRead.size == 1, "the two readings came back to one value")
    val FPAdd(_, l, r) = rewritten: @unchecked
    assert(l == r)
  }

  test("an object returned as it is is taken apart like one built in the body") {
    // `if (d < 0) s.cal else Calibration(s.cal.offset + d)`
    val d = Variable.fresh("d", f64)
    val built = ADT(calSort.constructors.head.id, Seq.empty,
                    Seq(FPAdd(rm, ADTSelector(ADTSelector(s, cal), offset), d)))
    val body = IfExpr(FPLessThan(d, Float64Literal(0.0)), ADTSelector(s, cal), built)
    val fd = new FunDef(FreshIdentifier("g"), Seq.empty, Seq(s.toVal, d.toVal), calType, body,
                        Seq.empty)
    given Symbols = NoSymbols.withSorts(sorts).withFunctions(Seq(fd))

    val (_, fields, flattening) = Preprocessor(fd).orFail
    assert(fields.map(_.displayName) == Seq("offset"))
    assert(flattening.parameters.map(_.id.name) == Seq("s_cal_offset", "d"))
  }

  test("a match that cannot fail, as from `val (a, b) = pair`, becomes plain bindings") {
    // `val p = (x, y) match { case q @ (a, b) => q }; p._1 + p._2`
    val x = Variable.fresh("x", f64)
    val y = Variable.fresh("y", f64)
    val pairType = TupleType(Seq(f64, f64))
    val q = ValDef.fresh("q", pairType)
    val p = ValDef.fresh("p", pairType)
    val pattern = TuplePattern(Some(q), Seq(WildcardPattern(Some(ValDef.fresh("a", f64))),
                                            WildcardPattern(Some(ValDef.fresh("b", f64)))))
    val body = Let(p, MatchExpr(Tuple(Seq(x, y)), Seq(MatchCase(pattern, None, q.toVariable))),
                   FPAdd(rm, TupleSelect(p.toVariable, 1), TupleSelect(p.toVariable, 2)))
    val fd = new FunDef(FreshIdentifier("h"), Seq.empty, Seq(x.toVal, y.toVal), f64, body,
                        Seq.empty)
    given Symbols = NoSymbols.withSorts(sorts).withFunctions(Seq(fd))

    val (rewritten, _, _) = Preprocessor(fd).orFail
    assert(!exprOps.exists { case _: MatchExpr | _: TupleSelect => true; case _ => false }(rewritten))
  }

  test("a plain parameter is carried through untouched") {
    val x = Variable.fresh("x", f64)
    val (rewritten, flattening) = flatten(FPAdd(rm, x, x), params = Seq(x.toVal))
      .orFail
    assert(flattening.parameterOfFieldRead.isEmpty)
    assert(flattening.parameters.map(_.id.name) == Seq("x"))
    assert(rewritten == FPAdd(rm, x, x))
  }
}
