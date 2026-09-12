/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification
package roundoff

import org.scalatest.funsuite.AnyFunSuite
import inox.trees.{Expr => RExpr, _}

/** Covers which guard an objective is a multiple of, and what is left over when it is taken out.
  *
  * That question decides two things at once: how an objective is written, and which guards are
  * worth naming at all. A guard nothing is a multiple of costs a variable and an equation in
  * every region of the function, so answering `None` has to mean nothing is added.
  */
class NormalisationSuite extends AnyFunSuite {

  private val x = Variable.fresh("x", RealType())
  private val y = Variable.fresh("y", RealType())
  private val z = Variable.fresh("z", RealType())

  private def real(n: Int): RExpr = FractionLiteral(n, 1)

  private def sameValue(one: RExpr, other: RExpr): Boolean =
    Poly.of(Minus(one, other)).exists(_.isZero)

  test("an objective that is a guard doubled is that guard, doubled") {
    val guard = Minus(x, y)
    val Some((which, quotient)) = Normalisation.divisor(Times(real(2), guard), Seq(guard)): @unchecked

    assert(which == 0)
    assert(sameValue(quotient, real(2)))
  }

  test("the guard need not appear in the objective as it is written") {
    // 0.5x - 0.5y is the guard halved, spread over two terms, which no common subexpression
    // is shared between.
    val guard = Minus(y, x)
    val objective = Minus(Times(FractionLiteral(1, 2), x), Times(FractionLiteral(1, 2), y))
    val Some((which, quotient)) = Normalisation.divisor(objective, Seq(guard)): @unchecked

    assert(which == 0)
    assert(sameValue(quotient, FractionLiteral(-1, 2)))
  }

  test("a quotient may itself be an expression over the inputs") {
    val guard = Minus(x, y)
    val objective = Minus(Times(x, x), Times(y, y))
    val Some((_, quotient)) = Normalisation.divisor(objective, Seq(guard)): @unchecked

    assert(sameValue(quotient, Plus(x, y)))
  }

  test("a division that leaves a remainder is refused") {
    // x - y + 1 is the guard plus a constant, which the rewrite may not take: the two halves
    // are each larger than the sum and the solver holds no relation between them.
    assert(Normalisation.divisor(Plus(Minus(x, y), real(1)), Seq(Minus(x, y))).isEmpty)
  }

  test("an objective in an unrelated variable is refused") {
    assert(Normalisation.divisor(z, Seq(Minus(x, y))).isEmpty)
  }

  test("a constant objective is refused, since a guard does not divide it") {
    assert(Normalisation.divisor(real(3), Seq(Minus(x, y))).isEmpty)
  }

  test("an objective that is nothing is refused rather than named") {
    assert(Normalisation.divisor(Minus(x, x), Seq(Minus(x, y))).isEmpty)
  }

  test("a guard that is nothing divides nothing") {
    assert(Normalisation.divisor(Minus(x, y), Seq(Minus(x, x))).isEmpty)
  }

  test("the guard that is reported is the one that divides") {
    val guards = Seq(Minus(x, x), Minus(y, z), Minus(x, y))
    val Some((which, _)) = Normalisation.divisor(Times(real(3), Minus(x, y)), guards): @unchecked

    assert(which == 2)
  }

  test("no guard divides an objective that mixes two of them") {
    val guards = Seq(Minus(x, y), Minus(y, z))
    assert(Normalisation.divisor(Plus(Minus(x, y), Minus(y, z)), guards).isEmpty)
  }
}
