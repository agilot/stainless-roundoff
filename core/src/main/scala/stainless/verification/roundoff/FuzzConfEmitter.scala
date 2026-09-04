/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification
package roundoff

/** One function handed to the fuzzer, as the configuration writer sees it.
  *
  * `domain` holds one range per parameter, in the order they are declared, because a
  * configuration names its intervals by position rather than by variable.
  */
case class FuzzSubject(name: String, parameters: Seq[String], domain: Seq[(Double, Double)])

/** Writes what the analysis established as a configuration the fuzzer can search.
  *
  * Each bounded divergence becomes a box to sample, and the precondition becomes the
  * domain, which is both what the rounding search covers and what an end the analysis left
  * open falls back to.
  */
object FuzzConfEmitter {

  /** How many inputs the fuzzer tries in each configuration. */
  private val samples = 10000

  /** How far a certified box is widened before it is searched.
    *
    * Ibex narrows a box to a couple of ulps, and the fuzzer clamps its mutations back into
    * the box it was given, so searching one as certified never looks around the witness.
    */
  private val widening = 1000

  def emit(subjects: Seq[(FuzzSubject, Seq[Witness])]): String = {
    val entries = subjects.flatMap { case (subject, witnesses) => configurations(subject, witnesses) }
    val column = entries.map(_._1.length).maxOption.getOrElse(0)

    val settings = Seq(s"n = $samples", s"widen = $widening")
    val body = entries.map { case (key, value) => s"${key.padTo(column, ' ')} = $value" }

    (settings ++ Seq("") ++ body).mkString("", "\n", "\n")
  }

  private def configurations(subject: FuzzSubject, witnesses: Seq[Witness])
    : Seq[(String, String)] = {
    val domain = (s"${subject.name}.rounding.domain",
                  subject.domain.map { case (low, high) => s"[$low, $high]" }.mkString(", "))

    // Only a bounded divergence carries a box, and only the merged scheme is read back for
    // now, so anything else is left out rather than named without a region to search.
    val divergences = witnesses.collect {
      case w if w.scheme == DiscontinuityMode.Merged && w.box.isDefined =>
        (s"${subject.name}.divergence.${nameOf(w)}", box(w.box.get, subject.parameters))
    }

    domain +: divergences
  }

  private def nameOf(w: Witness): String = {
    val objective = if (w.maximizing.getOrElse(true)) "max" else "min"
    val taken = w.against.map(against => s"_t$against").getOrElse("")
    s"g${w.region}_u${w.other}${taken}_$objective"
  }

  /** One interval per parameter, in declaration order.
    *
    * A parameter the query never narrowed, and an end it left open, are written `*`, which
    * the fuzzer reads as the matching end of the domain.
    */
  private def box(bounds: Box, parameters: Seq[String]): String =
    parameters.map { parameter =>
      bounds.get(parameter) match {
        case Some((low, high)) => s"[${end(low)}, ${end(high)}]"
        case None => "[*, *]"
      }
    }.mkString(", ")

  private def end(d: Option[BigDecimal]): String = d.fold("*")(_.toString)
}
