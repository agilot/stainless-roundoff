/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package roundoff

import org.scalatest.funsuite.AnyFunSuite
import stainless.trees._
import stainless.verification.roundoff._

/** Covers the task FPTaylor is handed: what it is told about the inputs, and how the
  * expression is written once every binding has been lifted out of it.
  */
class FPTaylorEmitterSuite extends AnyFunSuite with Unwrapping {

  private val f64 = FPType(11, 53)
  private val f32 = FPType(8, 24)
  private val rm = RoundNearestTiesToEven

  private val a = Variable.fresh("a", f64)
  private val b = Variable.fresh("b", f64)

  private val spec = InputSpec(FPPrecision.Binary64,
                               Map(a.id -> (0.1, 10.0), b.id -> (0.5, 2.0)))

  private given Symbols = NoSymbols

  private def emit(body: Expr, using: InputSpec = spec): Either[String, String] =
    FPTaylorEmitter.emit("f_1_leaf0", "denoise (leaf 1)", body, using)

  private def name(v: Variable): String = s"v_${v.id.globalId}"

  test("an input is declared real, so that it is rounded on entry as Daisy rounds it") {
    val task = emit(FPMul(rm, a, b)).orFail
    assert(task.contains(s"real ${name(a)} in ["), s"a is not a real input in\n$task")
  }

  test("a range is written as the exact rational the double stands for") {
    val task = emit(FPMul(rm, a, b)).orFail
    // 0.1 is not a tenth, and writing it as one would ask about a different interval.
    assert(task.contains("3602879701896397/36028797018963968"),
           s"0.1 was not written exactly in\n$task")
    assert(task.contains("1/2"), s"0.5 was not written exactly in\n$task")
  }

  test("the rounding operator follows the precision of the expression") {
    assert(emit(FPMul(rm, a, b)).orFail.contains("f_1_leaf0 rnd64="))

    val x = Variable.fresh("x", f32)
    val single = InputSpec(FPPrecision.Binary32, Map(x.id -> (0.0, 1.0)))
    assert(emit(FPMul(rm, x, x), single).orFail.contains("f_1_leaf0 rnd32="))
  }

  test("a binding becomes a definition of its own rather than a nested expression") {
    val t = ValDef.fresh("t", f64)
    val body = Let(t, FPMul(rm, a, a), FPAdd(rm, t.toVariable, b))
    val task = emit(body).orFail

    assert(task.contains("Definitions"), s"no definitions section in\n$task")
    assert(task.contains(s"v_${t.id.globalId} rnd64= (${name(a)} * ${name(a)});"),
           s"the binding was not lifted out in\n$task")
    assert(task.contains(s"f_1_leaf0 rnd64= (v_${t.id.globalId} + ${name(b)});"),
           s"the body does not read the definition in\n$task")
  }

  test("nested bindings are defined before the ones that read them") {
    val inner = ValDef.fresh("inner", f64)
    val outer = ValDef.fresh("outer", f64)
    val body = Let(outer, Let(inner, FPMul(rm, a, a), FPAdd(rm, inner.toVariable, b)),
                   FPMul(rm, outer.toVariable, b))

    val task = emit(body).orFail
    val innerAt = task.indexOf(s"v_${inner.id.globalId} rnd64=")
    val outerAt = task.indexOf(s"v_${outer.id.globalId} rnd64=")

    assert(innerAt >= 0 && outerAt >= 0, s"a definition is missing from\n$task")
    assert(innerAt < outerAt, s"the inner definition comes second in\n$task")
  }

  test("an expression with no bindings has no definitions section") {
    assert(!emit(FPMul(rm, a, b)).orFail.contains("Definitions"))
  }

  test("a fused multiply-add stays one operation, so it is charged one rounding") {
    val task = emit(FPFMA(rm, a, b, a)).orFail
    assert(task.contains(s"fma(${name(a)}, ${name(b)}, ${name(a)})"), s"in\n$task")
  }

  test("a square root is written as a call, since the interval library implements it") {
    assert(emit(Sqrt(rm, a)).orFail.contains(s"sqrt(${name(a)})"))
  }

  test("an input with no range is refused, naming the input and what to write") {
    val loose = InputSpec(FPPrecision.Binary64, Map(a.id -> (0.1, 10.0)))
    val why = emit(FPMul(rm, a, b), loose).left.getOrElse(fail("a loose input was accepted"))
    assert(why.contains(b.id.name))
    assert(why.contains("lo <= x && x <= hi"))
  }

  test("an expression with no inputs is refused, since there is nothing to range over") {
    val why = emit(FPMul(rm, Float64Literal(2.0), Float64Literal(3.0)))
      .left.getOrElse(fail("a constant expression was accepted"))
    assert(why.contains("no floating-point inputs"))
  }

  test("a rounding mode other than to-nearest is refused, naming the mode") {
    val why = emit(FPMul(RoundTowardZero, a, b))
      .left.getOrElse(fail("a non-default rounding mode was accepted"))
    assert(why.contains("toward zero"))
    assert(why.contains("rnd64"))
  }

}
