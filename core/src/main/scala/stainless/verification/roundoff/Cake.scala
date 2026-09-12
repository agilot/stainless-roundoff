/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification
package roundoff

/** A stretch of time divided among a known number of queries, where what one saves the rest get.
  *
  * The share is worked out again before every query, from the clock rather than from a plan, so
  * a query that settles at once leaves what it did not use to the queries after it and a query
  * that settles slowly takes only its own. Both halves of a function's budget are cut this way:
  * the reachability questions asked while its paths are enumerated, and the divergence queries
  * asked once they are.
  *
  * The count may be an over-estimate, which is what makes it usable where the queries are
  * discovered as they are asked. A query never taken still counts against the divisor, so the
  * shares come out smaller than they need be rather than larger, and the budget holds.
  */
private[roundoff] final class Cake(seconds: Double, queries: Int) {

  private val deadline: Long = System.nanoTime() + (seconds.max(0.0) * 1e9).toLong
  private var pending: Int = queries

  /** How long there is before the whole of it is gone. */
  def left: Double = ((deadline - System.nanoTime()) / 1e9).max(0.0)

  /** What the next query may spend: the time left over the queries left. */
  def slice(): Double = left / pending.max(1)

  /** Records that one query has had its turn, whatever it spent. */
  def taken(): Unit = pending -= 1
}
