/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification
package roundoff

import inox.trees.{Expr => RExpr}

/** An exact rational, so that rearranging a sum never moves a coefficient. */
private[roundoff] final case class Rat(num: BigInt, den: BigInt) {
  def +(o: Rat): Rat = Rat.of(num * o.den + o.num * den, den * o.den)
  def -(o: Rat): Rat = this + -o
  def *(o: Rat): Rat = Rat.of(num * o.num, den * o.den)
  def /(o: Rat): Rat = Rat.of(num * o.den, den * o.num)
  def unary_- : Rat = Rat(-num, den)
  def isZero: Boolean = num == 0
  def isOne: Boolean = num == 1 && den == 1
}

private[roundoff] object Rat {
  val zero: Rat = Rat(0, 1)
  val one: Rat = Rat(1, 1)

  def of(n: BigInt, d: BigInt): Rat = {
    require(d != 0)
    val sign = if (d < 0) BigInt(-1) else BigInt(1)
    val g = n.gcd(d)
    Rat(sign * (n / g), sign * (d / g))
  }
}

/** A sum of monomials with rational coefficients, over terms nothing further is known about.
  *
  * Two expressions that compute the same thing in different words become the same map here,
  * which is what lets a guard be recognised inside a leaf that never mentions it literally:
  * `setpoint - temperature` and `temperature - setpoint` differ only in a sign, and
  * `0.95 * limit - 0.95 * apparent` is a multiple of `apparent - limit` spread over two terms.
  *
  * Anything the arithmetic does not reach — a root, a call, a division — is one opaque term,
  * so nothing cancels through it but everything around it still normalises.
  */
private[roundoff] final case class Poly(terms: Map[Poly.Mono, Rat]) {
  def isZero: Boolean = terms.isEmpty

  def +(o: Poly): Poly = Poly.merge(terms, o.terms)
  def -(o: Poly): Poly = this + -o
  def unary_- : Poly = Poly(terms.view.mapValues(-_).toMap)

  def *(o: Poly): Poly =
    terms.foldLeft(Poly.zero) { case (outer, (m1, c1)) =>
      o.terms.foldLeft(outer) { case (inner, (m2, c2)) =>
        inner + Poly(Map(Poly.ordered(m1 ++ m2) -> (c1 * c2)))
      }
    }
}

private[roundoff] object Poly {

  /** One product of opaque terms, kept in a fixed order so that equal products compare equal. */
  type Mono = Seq[RExpr]

  /** How large a polynomial may grow before the whole attempt is abandoned.
    *
    * Multiplying two sums multiplies their lengths, and inlining a binding repeats whatever it
    * held, so a body written with shared values can expand a long way. Past this the expression
    * goes to the solver as it was written.
    */
  private val limit = 512

  val zero: Poly = Poly(Map.empty)

  def constant(r: Rat): Poly = if (r.isZero) zero else Poly(Map(Seq.empty[RExpr] -> r))
  def opaque(e: RExpr): Poly = Poly(Map(Seq(e) -> Rat.one))

  private def key(a: RExpr): String = a.toString
  private[roundoff] def ordered(m: Mono): Mono = m.sortBy(key)

  private def merge(a: Map[Mono, Rat], b: Map[Mono, Rat]): Poly =
    Poly((a.keySet ++ b.keySet).view
      .map(m => m -> (a.getOrElse(m, Rat.zero) + b.getOrElse(m, Rat.zero)))
      .filterNot(_._2.isZero)
      .toMap)

  /** Reads an expression as a polynomial, or nothing where it grows past what is worth it. */
  def of(e: RExpr): Option[Poly] = {
    import inox.trees.*

    def capped(p: Poly): Option[Poly] = Option.when(p.terms.size <= limit)(p)

    def rec(e: RExpr): Option[Poly] = e match {
      case Plus(a, b) => for { x <- rec(a); y <- rec(b); r <- capped(x + y) } yield r
      case Minus(a, b) => for { x <- rec(a); y <- rec(b); r <- capped(x - y) } yield r
      case Times(a, b) => for { x <- rec(a); y <- rec(b); r <- capped(x * y) } yield r
      case UMinus(a) => rec(a).map(-_)
      case FractionLiteral(n, d) => Some(constant(Rat.of(n, d)))

      // A binding is written out, since the same value reached through one is the same term.
      case Let(vd, value, body) =>
        rec(inox.trees.exprOps.replaceFromSymbols(Map(vd -> value), body))

      case other => Some(opaque(other))
    }

    rec(e)
  }

  /** Degree first, then the terms of the product, so that every pair of monomials compares. */
  private def compare(a: Mono, b: Mono): Int =
    if (a.size != b.size) a.size.compare(b.size)
    else a.map(key).zip(b.map(key)).collectFirst { case (x, y) if x != y => x.compare(y) }.getOrElse(0)

  private def leading(p: Poly): Option[(Mono, Rat)] =
    p.terms.keys.reduceOption((x, y) => if (compare(x, y) >= 0) x else y).map(m => m -> p.terms(m))

  /** `a` with one of each term of `b` taken out, where `b` divides it. */
  private def without(a: Mono, b: Mono): Option[Mono] =
    b.foldLeft(Option(a)) { (left, x) =>
      left.flatMap { rest =>
        val at = rest.indexWhere(_ == x)
        Option.when(at >= 0)(rest.patch(at, Nil, 1))
      }
    }

  /** `p` written as `quotient * g + remainder`.
    *
    * A remainder of zero says `g` divides `p`, which is the case worth having: the whole of the
    * objective is then a multiple of the guard, and the solver reads it off the band.
    */
  def divide(p: Poly, g: Poly): (Poly, Poly) = leading(g) match {
    case None => (zero, p)
    case Some((gm, gc)) =>
      var rest = p
      var quotient = zero
      var remainder = zero
      var steps = 0

      while (!rest.isZero && steps < limit) {
        steps += 1
        val (m, c) = leading(rest).get
        without(m, gm) match {
          case Some(q) =>
            val step = Poly(Map(ordered(q) -> (c / gc)))
            quotient = quotient + step
            rest = rest - (step * g)
          case None =>
            remainder = remainder + Poly(Map(m -> c))
            rest = Poly(rest.terms - m)
        }
      }

      (quotient, remainder + rest)
  }

  /** The expression a polynomial stands for, with the terms in a settled order. */
  def toExpr(p: Poly): RExpr = {
    import inox.trees.*

    if (p.isZero) FractionLiteral(0, 1)
    else p.terms.toSeq
      .sortWith { case ((m1, _), (m2, _)) => compare(m1, m2) > 0 }
      .map { case (m, c) =>
        val coefficient: RExpr = FractionLiteral(c.num, c.den)
        if (m.isEmpty) coefficient
        else if (c.isOne) m.reduce(Times(_, _))
        else Times(coefficient, m.reduce(Times(_, _)))
      }
      .reduce(Plus(_, _))
  }
}

/** Writes an objective over the guards it turns out to be made of.
  *
  * The solver searches a box, one interval per variable, and a box cannot hold the fact that two
  * variables are nearly equal. So a band saying `|temperature - setpoint| <= e` is invisible when
  * the objective is read: `setpoint` and `temperature` go in over their whole ranges and the
  * result comes out far too wide, and the only way back is to bisect both until their intervals
  * are as narrow as the band, which takes about fifty bisections each.
  *
  * Naming the difference makes it a variable of its own, whose interval is the band. The
  * objective is then read off in one step and nothing has to be bisected at all.
  */
private[roundoff] object Normalisation {

  /** Which guard divides `objective`, and what is left when it is taken out.
    *
    * Only a guard dividing the whole objective counts, which is the case worth having: the
    * objective is then one product with the band on one side of it, and the solver reads it off.
    * A guard that divides nothing is never named, since a variable and an equation carried by
    * every region of a function is paid for whether or not anything reads them.
    *
    * A division that leaves a remainder is refused even though `q * name + r` is just as true.
    * The two halves of it are each far larger than what they add up to, and a box holds no
    * relation between them, so the solver would widen a bound it had been reading correctly.
    * `Clamp` is the case that says so: rewriting on a remainder took its bound from 1.7e-13 to
    * 1.2, seven hundred thousand times worse for a rewrite that changes nothing about the value.
    */
  def divisor(objective: RExpr, differences: Seq[RExpr]): Option[(Int, RExpr)] = {
    val exact = for {
      whole <- Poly.of(objective).toSeq
      (difference, k) <- differences.zipWithIndex
      guard <- Poly.of(difference).filterNot(_.isZero).toSeq
      (quotient, remainder) = Poly.divide(whole, guard)
      if remainder.isZero && !quotient.isZero
    } yield (k, Poly.toExpr(quotient))

    exact.headOption
  }
}
