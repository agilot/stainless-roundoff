/* Scratch harness: exercises FPCoreEmitter + DaisyRunner against a real Daisy binary. */

package stainless
package roundoff

import stainless.trees._
import stainless.verification.roundoff._

object DaisyProbe {

  def main(args: Array[String]): Unit = {
    val f64 = FPType(11, 53)
    val rm = RoundNearestTiesToEven

    // def poly(x: Double) = { require(1.0 <= x && x <= 3.0); x*x - 2.0*x }
    val x = Variable.fresh("x", f64)
    val polyBody = FPSub(rm, FPMul(rm, x, x), FPMul(rm, Float64Literal(2.0), x))
    val polyPre = And(Seq(
      FPLessEquals(Float64Literal(1.0), x),
      FPLessEquals(x, Float64Literal(3.0))))
    val poly = new FunDef(
      FreshIdentifier("poly"), Seq(), Seq(x.toVal), f64,
      Require(polyPre, polyBody), Seq())

    // def sum(a: Double, b: Double) = { require(...); (a + b) * a }
    val a = Variable.fresh("a", f64)
    val b = Variable.fresh("b", f64)
    val sumBody = FPMul(rm, FPAdd(rm, a, b), a)
    val sumPre = And(Seq(
      FPLessEquals(Float64Literal(0.5), a), FPLessEquals(a, Float64Literal(2.0)),
      FPLessEquals(Float64Literal(0.0), b), FPLessEquals(b, Float64Literal(1.0))))
    val sum = new FunDef(
      FreshIdentifier("sum"), Seq(), Seq(a.toVal, b.toVal), f64,
      Require(sumPre, sumBody), Seq())

    // Deliberately unanalyzable: the denominator's range straddles zero.
    val c = Variable.fresh("c", f64)
    val d = Variable.fresh("d", f64)
    val badBody = FPDiv(rm, FPAdd(rm, c, d), FPSub(rm, c, d))
    val badPre = And(Seq(
      FPLessEquals(Float64Literal(0.5), c), FPLessEquals(c, Float64Literal(2.0)),
      FPLessEquals(Float64Literal(0.0), d), FPLessEquals(d, Float64Literal(1.0))))
    val bad = new FunDef(
      FreshIdentifier("bad"), Seq(), Seq(c.toVal, d.toVal), f64,
      Require(badPre, badBody), Seq())

    // No range for the input: must be rejected before Daisy ever sees it.
    val e = Variable.fresh("e", f64)
    val unbounded = new FunDef(
      FreshIdentifier("unbounded"), Seq(), Seq(e.toVal), f64,
      FPMul(rm, e, e), Seq())

    // Non-default rounding mode: must be rejected.
    val g = Variable.fresh("g", f64)
    val badRm = new FunDef(
      FreshIdentifier("badRounding"), Seq(), Seq(g.toVal), f64,
      Require(
        And(Seq(FPLessEquals(Float64Literal(1.0), g), FPLessEquals(g, Float64Literal(2.0)))),
        FPMul(RoundTowardZero, g, g)),
      Seq())

    val fds = Seq(poly, sum, bad, unbounded, badRm)
    given Symbols = NoSymbols.withFunctions(fds)

    println("=" * 70)
    val queries = fds.flatMap { fd =>
      val built = for {
        read <- Preprocessor(fd)
        (whole, fields, flattening) = read
        body = Preprocessor.project(whole, fields.head)
        spec <- FPCoreEmitter.specOf(fd, body, flattening)
        source <- FPCoreEmitter.emit(fd.id.name, fd.id.name, body, spec)
      } yield RoundingQuery(fd.id, fd.id.name, spec.precision, source)

      built match {
        case Right(q) =>
          println(s"[emit ok]   ${fd.id.name} -> ${q.name} (${q.precision})")
          println(q.fpcoreSource.linesIterator.map("    " + _).mkString("\n"))
          Some(q)
        case Left(why) =>
          println(s"[emit skip] ${fd.id.name}: $why")
          None
      }
    }

    println("=" * 70)
    val ctx = inox.Context.empty.withOpts(
      optDaisy(args.headOption.getOrElse("daisy")))
    val runner = new DaisyRunner(ctx)

    for ((name, res) <- runner.analyze(queries).toSeq.sortBy(_._1)) {
      res match {
        case Right(r) => println(s"[result]  $name: error <= ${r.absError}")
        case Left(why) => println(s"[no result] $name: $why")
      }
    }
    println("=" * 70)
  }
}
