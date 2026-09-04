/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package roundoff

import org.scalatest.funsuite.AnyFunSuite
import stainless.trees._
import stainless.verification.roundoff._

/** Covers what the fuzzer is handed: the program written for it, and the configuration
  * that says where to look.
  */
class FuzzEmitterSuite extends AnyFunSuite {

  private val f64 = FPType(11, 53)
  private val rm = RoundNearestTiesToEven

  private val a = Variable.fresh("a", f64)
  private val b = Variable.fresh("b", f64)

  private def between(low: Double, v: Variable, high: Double): Expr =
    And(Seq(FPLessEquals(Float64Literal(low), v), FPLessEquals(v, Float64Literal(high))))

  private val precondition = And(Seq(between(0.1, a, 10.0), between(0.5, b, 2.0)))

  private val spec = InputSpec(FPPrecision.Binary64,
                               Map(a.id -> (0.1, 10.0), b.id -> (0.5, 2.0)))

  /** Two bindings of the same source name, as inlining the same helper twice leaves. */
  private val shared = {
    val one = ValDef.fresh("t", f64)
    val other = ValDef.fresh("t", f64)
    Let(one, FPMul(rm, a, a),
        Let(other, FPAdd(rm, one.toVariable, b),
            IfExpr(FPLessThan(other.toVariable, b), one.toVariable, other.toVariable)))
  }

  private def emit(body: Expr): Either[String, String] = {
    val fd = new FunDef(FreshIdentifier("denoise"), Seq(), Seq(a.toVal, b.toVal), f64,
                        Require(precondition, body), Seq())
    given Symbols = NoSymbols.withFunctions(Seq(fd))
    FuzzProgramEmitter.emit(fd, "denoise", spec, body)
  }

  test("a program is marked, and takes its parameters in the order they are declared") {
    val source = emit(shared).fold(fail(_), identity)
    assert(source.startsWith("@fuzz\n"))
    assert("""def denoise\(a_\d+: Double, b_\d+: Double\): Double""".r.findFirstIn(source).isDefined)
  }

  test("the precondition travels with the program") {
    val source = emit(shared).fold(fail(_), identity)
    assert("""require\(\(0\.1 <= a_\d+ && a_\d+ <= 10\.0\)""".r.findFirstIn(source).isDefined)
  }

  test("bindings of the same source name are named apart") {
    val source = emit(shared).fold(fail(_), identity)
    val bound = """val (t_\d+):""".r.findAllMatchIn(source).map(_.group(1)).toList
    assert(bound.size == 2, s"expected two bindings in\n$source")
    assert(bound.distinct.size == 2, s"the two bindings share a name in\n$source")
  }

  test("floating-point arithmetic keeps the shape it was written in") {
    // a - (a - b) is not (a - a) - b, so the inner subtraction has to stay parenthesised.
    val nested = FPSub(rm, a, FPSub(rm, a, b))
    val source = emit(nested).fold(fail(_), identity)
    assert("""a_\d+ - \(a_\d+ - b_\d+\)""".r.findFirstIn(source).isDefined, source)
  }

  test("a call the fuzzer cannot promote is refused by name") {
    assert(emit(Sqrt(rm, a)) == Left("'sqrt' has no counterpart in the fuzzer's MPFR build"))
    assert(emit(FPFMA(rm, a, b, a)) ==
      Left("a fused multiply-add has no counterpart in the fuzzer's MPFR build"))
  }

  test("a function that is not in double precision is refused") {
    val single = FPType(8, 24)
    val x = Variable.fresh("x", single)
    val fd = new FunDef(FreshIdentifier("f"), Seq(), Seq(x.toVal), single, x, Seq())
    given Symbols = NoSymbols.withFunctions(Seq(fd))
    val narrower = InputSpec(FPPrecision.Binary32, Map(x.id -> (0.0, 1.0)))
    assert(FuzzProgramEmitter.emit(fd, "f", narrower, x).isLeft)
  }

  private val subject = FuzzSubject("denoise", Seq("a", "b"), Seq((0.1, 10.0), (0.5, 2.0)))

  private def witness(box: Box): Witness =
    Witness.bounded(Site("denoise", 0), other = 2, maximizing = true, box = box,
                    against = Some(1), scheme = DiscontinuityMode.Merged)

  test("a configuration names its intervals by position, and the domain comes from the ranges") {
    val box: Box = Map("a" -> (Some(BigDecimal(1)), Some(BigDecimal(2))),
                       "b" -> (Some(BigDecimal(3)), Some(BigDecimal(4))))
    val conf = FuzzConfEmitter.emit(Seq(subject -> Seq(witness(box))))

    assert(conf.contains("denoise.rounding.domain"))
    assert(conf.contains("[0.1, 10.0], [0.5, 2.0]"))
    assert(conf.contains("denoise.divergence.g0_u2_t1_max"))
    assert(conf.contains("[1, 2], [3, 4]"))
  }

  test("an open end, and an input the query never narrowed, are left for the domain to fill") {
    val box: Box = Map("a" -> (None, Some(BigDecimal(2))))
    val conf = FuzzConfEmitter.emit(Seq(subject -> Seq(witness(box))))
    assert(conf.contains("[*, 2], [*, *]"))
  }

  test("a divergence with no box of its own is not made into a configuration") {
    val refused = Witness.infeasible(Site("denoise", 0), other = 2, against = Some(1),
                                     scheme = DiscontinuityMode.Merged)
    val conf = FuzzConfEmitter.emit(Seq(subject -> Seq(refused)))
    assert(!conf.contains("divergence"))
    assert(conf.contains("denoise.rounding.domain"))
  }
}

/** The fuzzer is read through its own output, so what that output looks like is pinned
  * here rather than left to be noticed when a lower bound quietly stops appearing.
  */
class FuzzRunnerSuite extends AnyFunSuite {

  private val runner = new FuzzRunner(inox.Context.empty)

  private val output =
    """|Compiling /tmp/witness.scala...
       |done. Fuzzing denoise, twice with 10000 inputs in each configuration.
       |
       |denoise: divergences
       |------------------------------------------------------------------------------
       |  g0_u2_t0_max  [0.707, 0.708] × [0.403, 0.404] × [0.5, 0.6]
       |    diverged      354 of 10000 (3,54%)
       |    max abs error 1.36396094219933949e-01 at 0.707, 0.403, 0.5
       |    max rel error 1.22806322112226159e+00 at 0.707, 0.403, 0.5
       |  g0_u3_t0_min  [1.414, 1.415] × [1.414, 1.415] × [1.999, 2.0]
       |    diverged      332 of 10000 (3,32%)
       |    max abs error 7.27161034360573784e-01 at 1.414, 1.414, 1.999
       |    max rel error 1.63655888572798590e+00 at 1.414, 1.414, 1.999
       |
       |denoise: rounding error
       |------------------------------------------------------------------------------
       |  domain  [0.1, 10.0] × [0.1, 10.0] × [0.5, 2.0]
       |    diverged      0 of 10000 (0,00%)
       |    max abs error 3.33066907387546962e-15 at 9.997, 9.124, 0.713
       |    max rel error 3.73910945900159338e-16 at 1.443, 0.320, 1.469
       |
       |twice: rounding error
       |------------------------------------------------------------------------------
       |  domain  [-10.0, 10.0]
       |    diverged      0 of 10000 (0,00%)
       |    max abs error 1.25000000000000000e-16 at 3.5
       |    max rel error 1.00000000000000000e-16 at 3.5
       |    outside the domain of the program: 12 inputs
       |""".stripMargin

  test("the widest error under a function is read across all of its configurations") {
    val found = runner.parse(output)
    assert(found("denoise") == BigDecimal("7.27161034360573784e-01"))
    assert(found("twice") == BigDecimal("1.25000000000000000e-16"))
    assert(found.keySet == Set("denoise", "twice"))
  }

  test("a run that reported nothing is read as nothing, not as zero") {
    assert(runner.parse("").isEmpty)
    assert(runner.parse("no program given\n").isEmpty)
  }

  test("a figure outside any heading belongs to no function") {
    assert(runner.parse("    max abs error 1.0e-01 at 3.0\n").isEmpty)
  }
}
