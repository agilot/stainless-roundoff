/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package roundoff

import org.scalatest.funsuite.AnyFunSuite
import stainless.trees._
import stainless.verification.roundoff._

/** Covers `Int` and `Long` values: which integer code is accepted, what ranges it gets, and
  * how it is written for Daisy and Ibex.
  *
  * No solver and no analyzer is run.
  */
class IntegerSuite extends AnyFunSuite with Unwrapping {

  private val f64 = FPType(11, 53)
  private val f32 = FPType(8, 24)
  private val rm = RoundNearestTiesToEven

  private val x = Variable.fresh("x", f64)
  private val n = Variable.fresh("n", Int32Type())

  private def int(i: Int): Expr = Int32Literal(i)

  /** `0 <= x <= 10 && 0 <= n <= 9`, the last bound written as `n < 10`. */
  private val ranged = And(Seq(
    FPLessEquals(Float64Literal(0.0), x), FPLessEquals(x, Float64Literal(10.0)),
    LessEquals(int(0), n), LessThan(n, int(10))))

  private def function(body: Expr, result: Type = f64, params: Seq[ValDef] = Seq(x.toVal, n.toVal))
    : (FunDef, Symbols) = {
    val fd = new FunDef(FreshIdentifier("f"), Seq.empty, params, result,
                        Require(ranged, body), Seq.empty)
    (fd, NoSymbols.withFunctions(Seq(fd)))
  }

  private def preprocess(body: Expr, result: Type = f64): Either[String, (Expr, Seq[FieldPath])] = {
    val (fd, symbols) = function(body, result)
    given Symbols = symbols
    Preprocessor(fd).map { case (rewritten, fields, _) => (rewritten, fields) }
  }

  private def specOf(body: Expr): InputSpec = {
    val (fd, symbols) = function(body)
    given Symbols = symbols
    val (rewritten, _, flattening) = Preprocessor(fd).orFail
    InputRanges.inputSpecOf(fd, rewritten, flattening).orFail
  }

  private val scaled = FPMul(rm, x, FPCast(11, 53, rm, n))

  test("an Int parameter converted to a double is accepted, and kept as a parameter") {
    val (fd, symbols) = function(scaled)
    given Symbols = symbols
    val (_, _, flattening) = Preprocessor(fd).orFail
    assert(flattening.parameters.map(_.id) == Seq(x.id, n.id))
  }

  test("a function returning an Int has its result analysed") {
    val (_, fields) = preprocess(IfExpr(FPLessThan(x, Float64Literal(0.5)), int(1), int(2)),
                                 result = Int32Type()).orFail
    assert(fields == Seq(FieldPath.empty))
  }

  test("a conversion from floating point to an integer is refused") {
    val truncated = FPToBVJVM(11, 53, 32, x)
    preprocess(truncated, result = Int32Type()) match {
      case Left(why) => assert(why.contains("floating point to an integer"))
      case Right(_) => fail("toInt was accepted")
    }
  }

  test("integer division is refused") {
    preprocess(FPCast(11, 53, rm, Division(n, int(2)))) match {
      case Left(why) => assert(why.contains("integer division"))
      case Right(_) => fail("an integer division was accepted")
    }
  }

  private val m = Variable.fresh("m", Int64Type())

  test("a Long is accepted like an Int") {
    val (fd, symbols) = function(FPCast(11, 53, rm, Plus(m, Int64Literal(1))),
                                 params = Seq(x.toVal, n.toVal, m.toVal))
    given Symbols = symbols
    assert(Preprocessor(fd).isRight)
  }

  test("an integer other than Int and Long is refused") {
    val s = Variable.fresh("s", Int16Type())
    val (fd, symbols) = function(FPCast(11, 53, rm, s), params = Seq(x.toVal, n.toVal, s.toVal))
    given Symbols = symbols
    Preprocessor(fd) match {
      case Left(why) => assert(why.contains("only 'Int' and 'Long'"))
      case Right(_) => fail("a Short was accepted")
    }
  }

  /** Why `val k = m * factor; x * k.toDouble` is refused, for `m` in `[0, 10^9]`. */
  private def conversionOf(factor: Long): Option[String] = {
    val k = Variable.fresh("k", Int64Type())
    val body = Let(k.toVal, Times(m, Int64Literal(factor)), FPMul(rm, x, FPCast(11, 53, rm, k)))
    val bounded = And(Seq(ranged, LessEquals(Int64Literal(0), m),
                          LessEquals(m, Int64Literal(1000000000L))))
    val fd = new FunDef(FreshIdentifier("f"), Seq.empty, Seq(x.toVal, n.toVal, m.toVal), f64,
                        Require(bounded, body), Seq.empty)
    given Symbols = NoSymbols.withFunctions(Seq(fd))
    val (rewritten, _, flattening) = Preprocessor(fd).orFail
    InputRanges.inexactIntegerConversion(rewritten,
                                         InputRanges.inputSpecOf(fd, rewritten, flattening).orFail)
  }

  test("a Long converted to Double is accepted only while it stays within 2^53") {
    // 10^12 is a Double exactly, but 10^16 is beyond 2^53 (about 9.0e15).
    assert(conversionOf(1000L).isEmpty)
    assert(conversionOf(10000000L).exists(_.contains("2^53")))
  }

  test("an integer bound is read from the precondition, a strict one as the next integer in") {
    assert(specOf(scaled).ranges(n.id) == (0.0, 9.0))
  }

  test("an integer comparison is a guard marked as integral") {
    val (guards, _) = PathExtractor(IfExpr(GreaterThan(n, int(5)), x, Float64Literal(0.0))).orFail
    assert(guards == Seq(Guard(int(5), n, strict = true, integral = true)))
  }

  test("an integral guard narrows its input exactly, on both sides") {
    val spec = specOf(scaled)
    val guards = Seq(Guard(n, int(5), strict = true, integral = true))
    def along(taken: Boolean) =
      InputRanges.rangesAlongPath(spec, guards, exactInputs = false)(Seq(BranchChoice(0, taken)))
        .get.ranges(n.id)
    assert(along(taken = true) == (0.0, 4.0))
    assert(along(taken = false) == (5.0, 9.0))
  }

  /** Why `y * k.toFloat` is refused, for a `Float` `y` and `k` in `[0, high]`. */
  private def floatConversionOf(high: Int): Option[String] = {
    val y = Variable.fresh("y", f32)
    val k = Variable.fresh("k", Int32Type())
    val bounded = And(Seq(FPLessEquals(Float32Literal(0f), y), FPLessEquals(y, Float32Literal(1f)),
                          LessEquals(int(0), k), LessEquals(k, int(high))))
    val fd = new FunDef(FreshIdentifier("g"), Seq.empty, Seq(y.toVal, k.toVal), f32,
                        Require(bounded, FPMul(rm, y, FPCast(8, 24, rm, k))), Seq.empty)
    given Symbols = NoSymbols.withFunctions(Seq(fd))
    val (rewritten, _, flattening) = Preprocessor(fd).orFail
    InputRanges.inexactIntegerConversion(rewritten,
                                         InputRanges.inputSpecOf(fd, rewritten, flattening).orFail)
  }

  test("an Int converted to Float is accepted only while it stays within 2^24") {
    // 80 is a Float exactly, as in `github/giant_HotSpots_standardRemapping.scala`, but 10^8 is
    // beyond 2^24 (about 1.7e7).
    assert(floatConversionOf(80).isEmpty)
    assert(floatConversionOf(100000000).exists(_.contains("2^24")))
  }

  test("an unranged Int is refused like an unranged float") {
    val unranged = Variable.fresh("k", Int32Type())
    val guards = Seq(Guard(unranged, int(5), strict = true, integral = true))
    val paths = Seq(ProgramPath(Seq(BranchChoice(0, true)), x),
                    ProgramPath(Seq(BranchChoice(0, false)), Float64Literal(0.0)))
    GuardRegions.encode(guards, paths, specOf(scaled), DiscontinuityMode.Pairs) match {
      case Left(why) => assert(why.contains("no range in the precondition for 'k'"))
      case Right(_) => fail("an unranged Int was accepted")
    }
  }

  test("Daisy is told which inputs and subexpressions are integers") {
    val (fd, symbols) = function(scaled)
    given Symbols = symbols
    val source = FPCoreEmitter.emit("q", "f", FPMul(rm, x, FPCast(11, 53, rm, Plus(n, int(1)))),
                                    specOf(scaled)).orFail
    // The emitter names inputs `v_0`, `v_1`, ... in the order it finds them.
    assert("""\(FPCore q \(v_\d+ \(! :precision integer v_\d+\)\)""".r.findFirstIn(source).isDefined,
           source)
    assert("""\(! :precision integer \(\+ v_\d+ 1\)\)""".r.findFirstIn(source).isDefined, source)
  }

  test("FPTaylor refuses integers") {
    val (_, symbols) = function(scaled)
    given Symbols = symbols
    FPTaylorEmitter.emit("q", "f", scaled, specOf(scaled)) match {
      case Left(why) => assert(why.contains("FPTaylor reads no integers"))
      case Right(_) => fail("FPTaylor was given an Int")
    }
  }

  test("a strict integral guard becomes a non-strict one, one below, for Ibex") {
    val guards = Seq(Guard(n, int(5), strict = true, integral = true),
                     Guard(x, Float64Literal(1.0), strict = false))
    val paths = Seq(
      ProgramPath(Seq(BranchChoice(0, true), BranchChoice(1, true)), Float64Literal(1.0)),
      ProgramPath(Seq(BranchChoice(0, true), BranchChoice(1, false)), Float64Literal(2.0)),
      ProgramPath(Seq(BranchChoice(0, false)), Float64Literal(3.0)))
    val regions =
      GuardRegions.encode(guards, paths, specOf(scaled), DiscontinuityMode.Pairs).orFail.regions

    // The region of guard 1 lies below `n < 5` taken, which Ibex reads as `n <= 5 - 1`.
    val below = regions.find(_.guard == 1).get.shared
    assert(below.exists {
      case inox.trees.LessEquals(_, inox.trees.Minus(_, inox.trees.FractionLiteral(one, _))) =>
        one == 1
      case _ => false
    })
  }
}
