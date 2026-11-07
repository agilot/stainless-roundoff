/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package roundoff

import org.scalatest.funsuite.AnyFunSuite
import stainless.trees._
import stainless.verification.roundoff._

/** Covers what the fuzzer is handed: the program written for it, and the configuration
  * that says where to look.
  */
class FuzzEmitterSuite extends AnyFunSuite with Unwrapping {

  /** A benchmark as it is written for Stainless. */
  private val source =
    """|package benchmarks.clamp
       |
       |import stainless.annotation.*
       |import stainless.math.sqrt
       |import scala.annotation.tailrec
       |
       |object Clamp {
       |  case class Point(x: Double, y: Double)
       |
       |  @roundoff
       |  @fuzz
       |  def net(p: Point): Double = {
       |    require(0 <= p.x && p.x <= 1)
       |    stainless.math.sqrt(p.x) + sqrt(p.y)
       |  }
       |}
       |""".stripMargin

  test("a program is the source as written, made plain Scala") {
    assert(FuzzProgramEmitter.asPlainScala(source) ==
      """|
         |import scala.math.sqrt
         |import scala.annotation.tailrec
         |
         |object Clamp {
         |  case class Point(x: Double, y: Double)
         |
         |  @fuzz
         |  def net(p: Point): Double = {
         |    require(0 <= p.x && p.x <= 1)
         |    scala.math.sqrt(p.x) + sqrt(p.y)
         |  }
         |}
         |""".stripMargin)
  }

  test("a function is named after the objects around it, without its package") {
    val net = new FunDef(ast.SymbolIdentifier("benchmarks.clamp.Clamp.net"), Seq(), Seq(),
                         FPType(11, 53), Float64Literal(0.0), Seq())
    assert(FuzzProgramEmitter.fuzzerNameOf(net, source) == "Clamp.net")
  }

  test("a top-level function is named without the object Scala puts it in") {
    val net = new FunDef(ast.SymbolIdentifier("benchmarks.clamp.Clamp$package.net"), Seq(), Seq(),
                         FPType(11, 53), Float64Literal(0.0), Seq())
    assert(FuzzProgramEmitter.fuzzerNameOf(net, source) == "net")
  }

  test("a function the fuzzer is not given loses its annotation, on its line or above it") {
    val written = FuzzProgramEmitter.withoutFuzzAt(
      """|@fuzz def kept(x: Double): Double = x
         |@roundoff
         |@ fuzz
         |def above(x: Double): Double = x
         |@roundoff @fuzz def same(x: Double): Double = x
         |""".stripMargin, Set(4, 5))
    assert(written ==
      """|@fuzz def kept(x: Double): Double = x
         |@roundoff
         |
         |def above(x: Double): Double = x
         |@roundoff def same(x: Double): Double = x
         |""".stripMargin)
  }

  test("the library's None, built or matched, is Scala's") {
    val written = FuzzProgramEmitter.asPlainScala(
      """|o match {
         |  case Some(v) => if (v > 5.0) Some(v) else None[Double]()
         |  case None() => None[Option[Double]]()
         |}
         |""".stripMargin)
    assert(written ==
      """|o match {
         |  case Some(v) => if (v > 5.0) Some(v) else None
         |  case None => None
         |}
         |""".stripMargin)
  }

  /** Two package blocks, as in `github/sclera_SeqRegrR2Aggregate_valueExprs.scala`. */
  private val blocks =
    """|package com.example.types {
       |  case class Scale(k: Double)
       |}
       |
       |package com.example.calc {
       |  import stainless.annotation.*
       |  object Calc {
       |    @fuzz def scaled(x: Double): Double = x
       |  }
       |}
       |""".stripMargin

  test("a package block is kept, since its braces hold the rest") {
    assert(FuzzProgramEmitter.asPlainScala(blocks) ==
      """|package com.example.types {
         |  case class Scale(k: Double)
         |}
         |
         |package com.example.calc {
         |  object Calc {
         |    @fuzz def scaled(x: Double): Double = x
         |  }
         |}
         |""".stripMargin)
  }

  test("a function in a package block is named without its package") {
    val scaled = new FunDef(ast.SymbolIdentifier("com.example.calc.Calc.scaled"), Seq(), Seq(),
                            FPType(11, 53), Float64Literal(0.0), Seq())
    assert(FuzzProgramEmitter.fuzzerNameOf(scaled, blocks) == "Calc.scaled")
  }

  test("qualified access is dropped, since it can name a package that is") {
    assert(FuzzProgramEmitter.asPlainScala("private[regression] class Tweedie(val p: Double)\n") ==
             "class Tweedie(val p: Double)\n")
  }

  test("a function handed to the fuzzer is made public, and no other") {
    val written = FuzzProgramEmitter.madePublicAt(
      """|private def fuzzed(x: Double): Double = x
         |private def helper(x: Double): Double = x
         |  protected final def method(x: Double): Double = x
         |""".stripMargin, Set(1, 3))
    assert(written ==
      """|def fuzzed(x: Double): Double = x
         |private def helper(x: Double): Double = x
         |  final def method(x: Double): Double = x
         |""".stripMargin)
  }

  test("a source holding several functions is written once") {
    assert(FuzzProgramEmitter.plainScalaProgram(Seq(source, source)) ==
             FuzzProgramEmitter.asPlainScala(source))
  }

  private val subject = FuzzSubject("Clamp.net",
    Seq(FuzzInput("p.x", 0.1, 10.0), FuzzInput("p.y", 0.5, 2.0)),
    Seq(FuzzVariant("", Seq.empty, Seq("p.x" -> "p_x", "p.y" -> "p_y"))))

  private val site = DivergenceSite("net", guard = 0, pair = Some((1, 2)))

  private def witness(box: Box): Witness =
    Witness(site, DivergenceStatus.Bounded, maximizing = Some(true), box = Some(box))

  private def emit(subjects: Seq[(FuzzSubject, Seq[Witness])]): String =
    FuzzConfEmitter.emit(subjects, seconds = 60)

  private def settings(conf: String): Map[String, String] =
    conf.linesIterator.collect { case s"$key = $value" => key.trim -> value }.toMap

  test("a configuration gives each input by its path, and the domain comes from the ranges") {
    val box: Box = Map("p_x" -> (Some(BigDecimal(1)), Some(BigDecimal(2))),
                       "p_y" -> (Some(BigDecimal(3)), Some(BigDecimal(4))))
    val conf = settings(emit(Seq(subject -> Seq(witness(box)))))

    assert(conf("Clamp.net.rounding.domain.p.x") == "[0.1, 10.0]")
    assert(conf("Clamp.net.rounding.domain.p.y") == "[0.5, 2.0]")
    assert(conf("Clamp.net.divergence.g0_u2_t1_max.p.x") == "[1, 2]")
    assert(conf("Clamp.net.divergence.g0_u2_t1_max.p.y") == "[3, 4]")
  }

  test("a divergence box is searched as Ibex certified it, and grows only where nothing diverges") {
    val conf = settings(emit(Seq(subject -> Seq())))
    assert(conf("widen") == "1")
    assert(conf("adaptive-widen") == "true")
    assert(conf("widen-factor") == "10")
  }

  test("a divergence box is explored by bisection, then mutated around what it finds") {
    val conf = settings(emit(Seq(subject -> Seq())))
    assert(conf("explore") == "bisection")
    assert(conf("mutate") == "true")
    assert(conf("explore-share") == "0.9")
  }

  test("the fuzzer searches for as long as the timeout, with no limit on the inputs") {
    val conf = settings(emit(Seq(subject -> Seq())))
    assert(conf("time") == "60")
    assert(!conf.contains("n"))
    assert(settings(FuzzConfEmitter.emit(Seq(subject -> Seq()), seconds = 1.5))("time") == "1.5")
  }

  test("identical boxes are searched once, and the domain is searched for divergences too") {
    val conf = settings(emit(Seq(subject -> Seq())))
    assert(conf("unique-boxes") == "true")
    assert(conf("divergence-in-domains") == "true")
  }

  test("a box of a single point gets one ulp on each side, so that the fuzzer can widen it") {
    val box: Box = Map("p_x" -> (Some(BigDecimal(1)), Some(BigDecimal(1))),
                       "p_y" -> (Some(BigDecimal(3)), Some(BigDecimal(4))))
    val conf = settings(emit(Seq(subject -> Seq(witness(box)))))
    assert(conf("Clamp.net.divergence.g0_u2_t1_max.p.x") ==
             s"[${Math.nextDown(1.0)}, ${Math.nextUp(1.0)}]")
    assert(conf("Clamp.net.divergence.g0_u2_t1_max.p.y") == "[3, 4]")
  }

  test("an open end, and an input the query never narrowed, are left for the domain to fill") {
    val box: Box = Map("p_x" -> (None, Some(BigDecimal(2))))
    val conf = settings(emit(Seq(subject -> Seq(witness(box)))))
    assert(conf("Clamp.net.divergence.g0_u2_t1_max.p.x") == "[*, 2]")
    assert(conf("Clamp.net.divergence.g0_u2_t1_max.p.y") == "[*, *]")
  }

  test("a divergence with no box of its own is not made into a configuration") {
    val refused = Witness(site, DivergenceStatus.Infeasible)
    val conf = emit(Seq(subject -> Seq(refused)))
    assert(!conf.contains(".divergence."))
    assert(conf.contains("Clamp.net.rounding.domain.p.x"))
  }

  test("a box that narrows no input is not made into a configuration, being the whole domain") {
    val nothingFound = witness(Map.empty)
    val unbounded = witness(Map("p_x" -> (None, None), "p_y" -> (None, None)))
    val conf = emit(Seq(subject -> Seq(nothingFound, unbounded)))
    assert(!conf.contains(".divergence."))
  }

  test("a witness of one number of the result, or of one variant, belongs to its function") {
    def found(function: String) = witness(Map.empty).copy(site = site.copy(function = function))
    assert(FuzzConfEmitter.isFoundFor(found("net"), "net"))
    assert(FuzzConfEmitter.isFoundFor(found("net.centre._1"), "net"))
    assert(FuzzConfEmitter.isFoundFor(found("net [Some]"), "net"))
    assert(!FuzzConfEmitter.isFoundFor(found("network"), "net"))
  }

  test("a box found for one number of the result, or one variant, is named after it") {
    val box: Box = Map("p_x" -> (Some(BigDecimal(1)), Some(BigDecimal(2))))
    def found(function: String) = witness(box).copy(site = site.copy(function = function))
    val withVariant = subject.copy(variants = subject.variants :+ subject.variants.head.copy(description = "Some"))
    val names = settings(emit(Seq(withVariant -> Seq(
      found("net.centre._1"), found("net [Some]"), found("net.radius [Some]")))))
      .keySet.collect { case s"Clamp.net.divergence.$name.p.x" => name }

    assert(names == Set("centre__1_g0_u2_t1_max", "Some_g0_u2_t1_max", "radius_Some_g0_u2_t1_max"))
  }

  /** `area(s: Shape, flag: Boolean)`, with `Circle(r)`, `Rect(w, h)` and `Empty`. */
  private val shapes = FuzzSubject("area",
    Seq(FuzzInput("s.Circle.r", 0.0, 1.0), FuzzInput("s.Rect.w", 0.0, 2.0), FuzzInput("s.Rect.h", 0.0, 3.0)),
    Seq(FuzzVariant("s = Circle", Seq("s" -> Some("Circle"), "flag" -> None), Seq("s.Circle.r" -> "s_r")),
        FuzzVariant("s = Rect", Seq("s" -> Some("Rect"), "flag" -> None), Seq("s.Rect.w" -> "s_w", "s.Rect.h" -> "s_h")),
        FuzzVariant("s = Empty", Seq("s" -> Some("Empty"), "flag" -> None), Seq.empty)))

  test("a domain gives every field of every case, and names no case") {
    val conf = settings(emit(Seq(shapes -> Seq())))
    assert(conf("area.rounding.domain.s.Circle.r") == "[0.0, 1.0]")
    assert(conf("area.rounding.domain.s.Rect.h") == "[0.0, 3.0]")
    assert(!conf.contains("area.rounding.domain.s") && !conf.contains("area.rounding.domain.flag"))
  }

  test("a box names the case of its variant, and gives the fields of that case only") {
    val box: Box = Map("s_w" -> (Some(BigDecimal(1)), Some(BigDecimal(2))))
    val found = witness(box).copy(site = site.copy(function = "area [s = Rect]"))
    val conf = settings(emit(Seq(shapes -> Seq(found))))
    assert(conf("area.divergence.s_Rect_g0_u2_t1_max.s") == "Rect")
    assert(conf("area.divergence.s_Rect_g0_u2_t1_max.s.Rect.w") == "[1, 2]")
    assert(conf("area.divergence.s_Rect_g0_u2_t1_max.s.Rect.h") == "[*, *]")
    assert(!conf.contains("area.divergence.s_Rect_g0_u2_t1_max.s.Circle.r"))
  }

  test("a case the analysis leaves open, as for a Boolean, is any case without fields") {
    val box: Box = Map("s_r" -> (Some(BigDecimal(0.25)), Some(BigDecimal(0.5))))
    val found = witness(box).copy(site = site.copy(function = "area [s = Circle]"))
    assert(settings(emit(Seq(shapes -> Seq(found))))("area.divergence.s_Circle_g0_u2_t1_max.flag") == "empty")
  }

  test("a witness of no variant the subject knows is not made into a configuration") {
    val box: Box = Map("s_r" -> (Some(BigDecimal(0.25)), Some(BigDecimal(0.5))))
    val found = witness(box).copy(site = site.copy(function = "area [s = Triangle]"))
    assert(!emit(Seq(shapes -> Seq(found))).contains(".divergence."))
  }

  test("a name recorded twice, as by the two terms of an extrema query, is numbered apart") {
    val box: Box = Map("p_x" -> (Some(BigDecimal(1)), Some(BigDecimal(2))))
    val all = DivergenceSite("net", guard = 3, pair = None)
    val half = Witness(all, DivergenceStatus.Bounded, maximizing = Some(true), box = Some(box))
    val names = settings(emit(Seq(subject -> Seq(half, half, half)))).keySet
      .collect { case s"Clamp.net.divergence.$name.p.x" => name }

    assert(names == Set("g3_all_max", "g3_all_max_2", "g3_all_max_3"))
  }
}

/** The fuzzer is read through its JSON report, so what that report looks like is pinned
  * here rather than left to be noticed when a lower bound quietly stops appearing.
  */
class FuzzRunnerSuite extends AnyFunSuite {

  private val runner = new FuzzRunner(inox.Context.empty, RoundoffSettings.from(inox.Context.empty))

  private def fields(errors: Seq[(String, String)]): String =
    errors.map { case (field, error) =>
      s""""$field": {"maxAbsErr": "$error", "maxAbsErrAt": [0.5]}""" }.mkString(", ")

  /** A divergence box gives errors only for the runs that diverged, so with none it has none. */
  private def configuration(name: String, divergent: Int, errors: (String, String)*): String =
    s"""{"name": "$name", "inputs": ["x"], "box": [[0.0, 1.0]], "tested": 5000,
       | "uniqueTested": 5000, "failed": 0, "divergent": $divergent,
       | "uniqueDivergent": $divergent, "divergencePoints": ${divergent min 1},
       | "pathPairs": ${divergent min 1}, "fields": {${fields(errors)}}}""".stripMargin

  private def totals(divergent: Int, errors: (String, String)*): String =
    s"""{"divergent": $divergent, "uniqueDivergent": $divergent,
       | "divergencePoints": ${divergent min 1}, "pathPairs": ${divergent min 1},
       | "fields": {${fields(errors)}}}""".stripMargin

  private val report =
    s"""|{"source": "Clamp.scala", "n": 10000, "widen": 1000.0, "seed": 0,
        | "explore": "sampling", "mutate": true, "exploreShare": 0.9, "mutationsPerInput": 10,
        | "stopOnDivergence": false, "divergenceErrors": true, "verbose": false,
        | "functions": {
        |  "Clamp.net": {
        |    "divergenceTotals": ${totals(5, "" -> "7.27161034360573784e-01")},
        |    "divergence": [${configuration("g0_u2_t0_max", 2, "" -> "1.36396094219933949e-01")},
        |                   ${configuration("g0_u3_t0_min", 3, "" -> "7.27161034360573784e-01")}],
        |    "rounding": [${configuration("domain", 0, "" -> "3.33066907387546962e-15")}]
        |  },
        |  "steady": {
        |    "divergenceTotals": ${totals(0)},
        |    "divergence": [${configuration("g0_u1_t0_any", 0)}],
        |    "rounding": [${configuration("domain", 0, "" -> "2.22044604925031308e-16")}]
        |  },
        |  "twice": {
        |    "divergenceTotals": ${totals(0)},
        |    "divergence": [],
        |    "rounding": [${configuration("domain", 0, "" -> "1.25000000000000000e-16")}]
        |  }
        |}}""".stripMargin

  test("the widest error of a function is read across all of its configurations") {
    val found = runner.read(report)
    assert(found("Clamp.net").widestErrors == Map("" -> BigDecimal("7.27161034360573784e-01")))
    assert(found("twice").widestErrors("") == BigDecimal("1.25000000000000000e-16"))
    assert(found.keySet == Set("Clamp.net", "steady", "twice"))
  }

  test("a divergence box where nothing diverged leaves the error to the rounding domain") {
    assert(runner.read(report)("steady").widestErrors("") == BigDecimal("2.22044604925031308e-16"))
  }

  test("each number of a result has its own widest error") {
    val tuple = s"""{"functions": {"f": {"divergence": [${configuration("g0_all_max", 1, "_1" -> "0.5")}],
                   | "rounding": [${configuration("domain", 0, "_1" -> "0.25", "Some.value" -> "0.125")}]}}}""".stripMargin
    assert(runner.read(tuple)("f").widestErrors ==
             Map("_1" -> BigDecimal("0.5"), "Some.value" -> BigDecimal("0.125")))
  }

  /** `update(stepBy, reset)` returns `(Conclusion, Double)`, and `shape` picks a `Circle(r)` or an `Empty`. */
  private def withCases(name: String, crashed: Int, firstCrash: String, divergences: String): String =
    s"""{"name": "$name", "inputs": ["stepBy", "shape", "shape.Circle.r", "reset"],
       | "box": [[0.0, 1.0], [0.0, 1.0], [0.0, 1.0], [0.0, 1.0]], "fields": {},
       | "crashed": $crashed, "firstCrash": $firstCrash,
       | "caseDivergent": 1, "caseDivergences": [$divergences]}""".stripMargin

  private val differing =
    """{"cases": [{"path": "_1", "float": "Continue", "mpfr": "Finished"}], "divergent": 67,
      | "uniqueDivergent": 67, "example": [0.5, 1.0, 0.0, 1.0]}""".stripMargin

  private val crash =
    """{"input": [0.25, 0.0, 0.5, 0.0], "float": "java.lang.ArithmeticException: x", "mpfr": null}"""

  private val withCasesReport =
    s"""{"functions": {"update": {"cases": {"shape": ["Circle", "Empty"], "reset": ["false", "true"]},
       | "divergence": [${withCases("g0_all_max", 0, "null", differing)}],
       | "rounding": [${withCases("domain", 3, crash, differing)}]}}}""".stripMargin

  test("runs that returned different cases are added up over the configurations") {
    val Seq(divergence) = runner.read(withCasesReport)("update").caseDivergences: @unchecked
    assert(divergence.cases == Seq(("_1", "Continue", "Finished")))
    assert(divergence.runs == 134)
  }

  test("an input is written with its cases by name, without the fields of the cases not picked") {
    val Seq(divergence) = runner.read(withCasesReport)("update").caseDivergences: @unchecked
    assert(divergence.example == "stepBy = 0.5, shape = Empty, reset = true")
  }

  test("the runs that threw are counted, and the first one is kept with what each version threw") {
    val found = runner.read(withCasesReport)("update")
    assert(found.crashes == 3)
    assert(found.firstCrash == Some(FuzzCrash("stepBy = 0.25, shape = Circle, shape.Circle.r = 0.5, reset = false",
                                              Some("java.lang.ArithmeticException: x"), None)))
  }

  test("a function no input could run is read as nothing, not as zero") {
    val none = """{"functions": {"f": {"divergence": [], "rounding": [{"name": "domain", "fields": {}}]}}}"""
    assert(runner.read(none)("f").widestErrors.isEmpty)
  }

  test("a report that is not JSON is read as nothing") {
    assert(runner.read("").isEmpty)
    assert(runner.read("no program given\n").isEmpty)
  }
}
