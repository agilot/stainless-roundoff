/* Scratch harness: exercises FPTaylorEmitter + FPTaylorRunner against a real FPTaylor binary.
 *
 * The shapes are the ones DaisyProbe uses, so the two probes can be read side by side, plus a
 * square root, which is the transcendental the portable interval library does implement.
 */

package stainless
package roundoff

import stainless.trees._
import stainless.verification.roundoff._

object FPTaylorProbe {

  def main(args: Array[String]): Unit = {
    val f64 = FPType(11, 53)
    val rm = RoundNearestTiesToEven

    def bounded(v: Variable, low: Double, high: Double): Expr =
      And(Seq(FPLessEquals(Float64Literal(low), v), FPLessEquals(v, Float64Literal(high))))

    // def poly(x: Double) = { require(1.0 <= x && x <= 3.0); x*x - 2.0*x }
    val x = Variable.fresh("x", f64)
    val poly = new FunDef(
      FreshIdentifier("poly"), Seq(), Seq(x.toVal), f64,
      Require(bounded(x, 1.0, 3.0),
        FPSub(rm, FPMul(rm, x, x), FPMul(rm, Float64Literal(2.0), x))), Seq())

    // def sum(a: Double, b: Double) = { require(...); (a + b) * a }
    val a = Variable.fresh("a", f64)
    val b = Variable.fresh("b", f64)
    val sum = new FunDef(
      FreshIdentifier("sum"), Seq(), Seq(a.toVal, b.toVal), f64,
      Require(And(Seq(bounded(a, 0.5, 2.0), bounded(b, 0.0, 1.0))),
        FPMul(rm, FPAdd(rm, a, b), a)), Seq())

    // A binding, which becomes a definition of its own rather than a nested expression.
    val n = Variable.fresh("n", f64)
    val shared = ValDef.fresh("shared", f64)
    val lets = new FunDef(
      FreshIdentifier("lets"), Seq(), Seq(n.toVal), f64,
      Require(bounded(n, 1.0, 2.0),
        Let(shared, FPMul(rm, n, n), FPAdd(rm, shared.toVariable, shared.toVariable))), Seq())

    // A square root: implemented by the portable interval library, unlike the trigonometry.
    val r = Variable.fresh("r", f64)
    val root = new FunDef(
      FreshIdentifier("root"), Seq(), Seq(r.toVal), f64,
      Require(bounded(r, 1.0, 4.0),
        Sqrt(rm, FPAdd(rm, r, Float64Literal(1.0)))), Seq())

    // Deliberately hard: the denominator's range straddles zero.
    val c = Variable.fresh("c", f64)
    val d = Variable.fresh("d", f64)
    val bad = new FunDef(
      FreshIdentifier("bad"), Seq(), Seq(c.toVal, d.toVal), f64,
      Require(And(Seq(bounded(c, 0.5, 2.0), bounded(d, 0.0, 1.0))),
        FPDiv(rm, FPAdd(rm, c, d), FPSub(rm, c, d))), Seq())

    // No range for the input: must be rejected before FPTaylor ever sees it.
    val e = Variable.fresh("e", f64)
    val unbounded = new FunDef(
      FreshIdentifier("unbounded"), Seq(), Seq(e.toVal), f64,
      FPMul(rm, e, e), Seq())

    // Non-default rounding mode: must be rejected.
    val g = Variable.fresh("g", f64)
    val badRm = new FunDef(
      FreshIdentifier("badRounding"), Seq(), Seq(g.toVal), f64,
      Require(bounded(g, 1.0, 2.0), FPMul(RoundTowardZero, g, g)), Seq())

    val fds = Seq(poly, sum, lets, root, bad, unbounded, badRm)
    given Symbols = NoSymbols.withFunctions(fds)

    println("=" * 70)
    val queries = fds.flatMap { fd =>
      val built = for {
        read <- Preprocessor(fd)
        (whole, fields, flattening) = read
        body = fields.head.project(whole)
        spec <- FPCoreEmitter.specOf(fd, body, flattening)
        source <- FPTaylorEmitter.emit(fd.id.name, fd.id.name, body, spec)
      } yield RoundingQuery(fd.id, fd.id.name, spec.precision, source)

      built match {
        case Right(q) =>
          println(s"[emit ok]   ${fd.id.name} -> ${q.name} (${q.precision})")
          println(q.source.linesIterator.map("    " + _).mkString("\n"))
          Some(q)
        case Left(why) =>
          println(s"[emit skip] ${fd.id.name}: $why")
          None
      }
    }

    println("=" * 70)
    val ctx = inox.Context.empty.withOpts(
      optFPTaylor(args.headOption.getOrElse("fptaylor")))
    val runner = new FPTaylorRunner(ctx)

    for ((name, res) <- runner.analyze(queries).toSeq.sortBy(_._1)) {
      res match {
        case Right(res) => println(s"[result]  $name: error <= ${res.absError}")
        case Left(why) => println(s"[no result] $name: $why")
      }
    }
    println("=" * 70)
  }
}
