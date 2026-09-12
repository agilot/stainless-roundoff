/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification

import stainless.trees._

package object roundoff {

  /** What the analysis was asked to do, and what it found to do it to.
    *
    * Kept apart from `verification`, which carries a line per obligation, because this is a
    * line per function about how the work was shaped rather than about whether it passed.
    */
  object DebugSectionRoundoff extends inox.DebugSection("roundoff")

  /** `n` written with the name of what was counted, plural unless there was one of it. */
  private[roundoff] def counted(n: Int, thing: String, plural: String = ""): String =
    s"$n ${if (n == 1) thing else if (plural.nonEmpty) plural else thing + "s"}"

  /** Path to the Daisy executable */
  object optDaisy extends inox.OptionDef[String] {
    import inox.OptionParsers._
    val name = "daisy"
    val default = "daisy"
    val parser = stringParser
    val usageRhs = "PATH"
  }

  /** Path to the fuzzer, empty for not fuzzing at all.
    *
    * The analysis bounds an error from above; the fuzzer looks for one from below, in the
    * very regions the analysis proved a divergence possible in. Given both, an obligation
    * reports the true worst case as an interval rather than a ceiling.
    */
  object optFuzz extends inox.OptionDef[String] {
    import inox.OptionParsers._
    val name = "fuzz"
    val default = ""
    val parser = stringParser
    val usageRhs = "PATH"
  }

  /** An external tool, as given or as found on `PATH`. */
  private[roundoff] def findExecutable(configured: String): Option[java.io.File] = {
    val direct = new java.io.File(configured)
    if (direct.isFile && direct.canExecute) Some(direct.getAbsoluteFile)
    else if (configured.contains(java.io.File.separator)) None
    else Option(System.getenv("PATH")).flatMap { path =>
      path.split(java.io.File.pathSeparatorChar).iterator
        .map(dir => new java.io.File(dir, configured))
        .find(f => f.isFile && f.canExecute)
        .map(_.getAbsoluteFile)
    }
  }

  /** Whether an input holds an exact real, rather than a value already rounded on entry.
    *
    * Daisy assumes the second and charges every input half an ulp of its range, which makes
    * a guard between an input and a constant able to diverge; under the first it cannot.
    */
  object optRoundoffExactInputs extends inox.FlagOptionDef("roundoff-exact-inputs", false)

  /** Whether a branch is asked about before it is enumerated.
    *
    * A path no input takes is not one a run can round, so leaving it out is what keeps a leaf
    * behind a condition the precondition already decides from setting the error of the whole
    * function. Turning this off enumerates every path the body spells out, which is what the
    * analysis did before it asked.
    */
  object optRoundoffPruning extends inox.FlagOptionDef("roundoff-pruning", true)

  /** Whether a divergence that cannot be the widest one is bounded anyway.
    *
    * The error of a function is the widest of its divergences, so a query that cannot reach as
    * far as one already answered needs no figure of its own. Asking whether it can is a plain
    * satisfiability question and is settled quickly where the answer is no, which saves the two
    * searches that would otherwise bracket it.
    */
  object optRoundoffIncumbent extends inox.FlagOptionDef("roundoff-incumbent", true)

  /** Whether a leaf is bounded over the inputs that reach it rather than over every input.
    *
    * A guard between an input and a literal holds that input to one side of it, so a leaf below
    * the guard never runs anywhere else and the analyzer can be told so. It only ever narrows a
    * box, so it can only tighten what comes back.
    */
  object optRoundoffPathRanges extends inox.FlagOptionDef("roundoff-path-ranges", true)

  /** Whether an objective is rewritten over the guards it turns out to be made of.
    *
    * Ibex searches a box, and a box cannot hold the fact that two variables are nearly equal, so
    * the band a divergence lives in is invisible while the objective is being read. Naming each
    * guard difference and rewriting the objective over those names puts the band where the
    * solver can see it. Where nothing matches, the objective goes over as it was written.
    */
  object optRoundoffNormalisation extends inox.FlagOptionDef("roundoff-normalisation", true)

  /** How long the divergence queries of one function may take, all told.
    *
    * A budget rather than an allowance per query, because the queries of one function differ
    * enormously in what they need: most settle in a millisecond or two and a few never settle
    * at all. Whatever a query leaves unspent is divided among the ones after it, so a function
    * whose regions are all easy finishes in a fraction of this and a function with one hard
    * region spends it all there.
    *
    * The phases before the queries are subtracted from it, so this bounds the analysis of a
    * function rather than only its search. Work shared by every function is not, since there
    * is no honest way to charge one function for a batch that answered for all of them.
    */
  object optRoundoffTimeout extends inox.OptionDef[Double] {
    import inox.OptionParsers._
    val name = "roundoff-timeout"
    val default = 1.0
    val parser = doubleParser
    val usageRhs = "SECONDS"
  }

  /** What fraction of a function's budget the reachability questions may take together.
    *
    * They are cut like the divergence queries that follow them, each offered the time left over
    * the questions left, so a question settled at once leaves its share to the ones after it.
    * What the whole phase does not use is not lost either: the queries are given whatever is
    * left of the budget when they start, so this is a ceiling on pruning rather than a portion
    * set aside for it.
    *
    * A question that runs out of time keeps its branch, which is what an unanswered question
    * means anyway, so the only thing a small share costs is the refutations that needed longer.
    */
  object optRoundoffPruningShare extends inox.OptionDef[Double] {
    import inox.OptionParsers._
    val name = "roundoff-pruning-share"
    val default = 0.2
    val parser = doubleParser
    val usageRhs = "0..1"
  }

  /** What fraction of a query's share goes on asking whether its region holds any point.
    *
    * The rest is split between the two ends of the enclosure. Deciding a region is empty is
    * the cheapest useful thing the search does and usually takes a millisecond, so it is given
    * a small slice; raise it where regions are being searched that a longer look would have
    * refuted outright.
    */
  object optRoundoffFeasibilityShare extends inox.OptionDef[Double] {
    import inox.OptionParsers._
    val name = "roundoff-feasibility-share"
    val default = 0.1
    val parser = doubleParser
    val usageRhs = "0..1"
  }

  /** Where to write what each branch-divergence query established, empty for nowhere.
    *
    * A `@fuzz` function also gets a program and a configuration for the fuzzer, written
    * beside this file under the same name, since the fuzzer finds a program from its
    * configuration by exactly that rule.
    */
  object optRoundoffWitnesses extends inox.OptionDef[String] {
    import inox.OptionParsers._
    val name = "roundoff-witnesses"
    val default = ""
    val parser = stringParser
    val usageRhs = "FILE"
  }

  /** How a discontinuity is bounded. */
  enum DiscontinuityMode {
    /** Every ordered pair of paths, each side of the guard asked about separately, which
      * is exact and costs two queries per pair of leaves.
      */
    case Pairwise

    /** The same pairs, but both sides of the guard asked about at once. Half the queries,
      * and over-estimates only where the paths carry guards below the one they part at,
      * whose conditions both have to be relaxed to fit in one region.
      */
    case Merged

    /** Every leaf below a guard against one of them, which costs a query per leaf and
      * over-estimates by the spread within a side.
      */
    case Reference
  }

  object DiscontinuityMode {
    def tryFromString(s: String): Option[DiscontinuityMode] = s.toLowerCase match {
      case "pairwise" => Some(Pairwise)
      case "merged" => Some(Merged)
      case "reference" => Some(Reference)
      case _ => None
    }
  }

  /** Which of the three discontinuity bounds to compute. */
  object optRoundoffDiscontinuity extends inox.OptionDef[DiscontinuityMode] {
    val name = "roundoff-discontinuity"
    val default = DiscontinuityMode.Pairwise
    val parser = DiscontinuityMode.tryFromString
    val usageRhs = "pairwise|merged|reference"
  }

  /** How a bound is shortened when it does not fit in the digits a report carries.
    *
    * Rounded away from zero, so that a shortened figure is still an upper bound, and to
    * the width `BigDecimal` uses by default, so that arithmetic on a shortened figure does
    * not shorten it again with a rounding of its own choosing.
    */
  private[roundoff] val reportedPrecision =
    new java.math.MathContext(34, java.math.RoundingMode.CEILING)

  /** Which function, and which region of it, a divergence query belongs to.
    *
    * A region is one path of the function under the pairwise scheme, and one guard under
    * the reference scheme.
    */
  case class Site(function: String, region: Int)

  /** The box one Ibex query narrowed its variables to, with `None` at an end left open. */
  type Box = Map[String, (Option[BigDecimal], Option[BigDecimal])]

  /** What became of one divergence, which is why a box is there or missing. */
  enum DivergenceStatus(val label: String) {
    /** A guard it needs rounds exactly, so the rounded program never reads it the other
      * way; Ibex is not asked about it at all.
      */
    case Unreachable extends DivergenceStatus("unreachable")

    /** Ibex found no point of the region where it can be taken. */
    case Infeasible extends DivergenceStatus("infeasible")

    /** Ibex bracketed how far it moves the result, narrowing a box on the way. */
    case Bounded extends DivergenceStatus("bounded")

    /** Ibex found a point of the region, which is all that was asked of it there. */
    case Feasible extends DivergenceStatus("feasible")

    /** Ibex showed it cannot reach as far as a divergence already found, so how far it does
      * reach was never worked out. The error of a function is the widest of its divergences,
      * so one that cannot be the widest needs no figure of its own.
      */
    case Dominated extends DivergenceStatus("dominated")
  }

  /** What one divergence query established.
    *
    * Every divergence considered is recorded, refused ones included, so that an empty
    * report means nothing was asked rather than everything was refused.
    */
  case class Witness(
    function: String,
    region: Int,
    other: Int,
    against: Option[Int],
    scheme: DiscontinuityMode,
    status: DivergenceStatus,
    maximizing: Option[Boolean],
    box: Option[Box]
  )

  object Witness {
    import io.circe.Json

    def unreachable(site: Site, other: Int, against: Option[Int] = None,
                    scheme: DiscontinuityMode = DiscontinuityMode.Pairwise): Witness =
      Witness(site.function, site.region, other, against, scheme,
              DivergenceStatus.Unreachable, None, None)

    def infeasible(site: Site, other: Int, against: Option[Int] = None,
                   scheme: DiscontinuityMode = DiscontinuityMode.Pairwise): Witness =
      Witness(site.function, site.region, other, against, scheme,
              DivergenceStatus.Infeasible, None, None)

    def dominated(site: Site, other: Int, against: Option[Int] = None,
                  scheme: DiscontinuityMode = DiscontinuityMode.Pairwise): Witness =
      Witness(site.function, site.region, other, against, scheme,
              DivergenceStatus.Dominated, None, None)

    /** A point of the region, found by asking whether it holds one rather than how far a
      * difference reaches inside it.
      *
      * It carries no direction because none was asked for, and it sits nearer the boundary than
      * either end does: an optimum is pulled to the outer face of the band, since the difference
      * between two leaves grows with the guard difference the band is drawn around, while a
      * satisfying point has nothing pulling it anywhere.
      */
    def feasible(site: Site, other: Int, box: Box, against: Option[Int] = None,
                 scheme: DiscontinuityMode = DiscontinuityMode.Pairwise): Witness =
      Witness(site.function, site.region, other, against, scheme,
              DivergenceStatus.Feasible, None, Some(box))

    def bounded(site: Site, other: Int, maximizing: Boolean, box: Box,
                against: Option[Int] = None,
                scheme: DiscontinuityMode = DiscontinuityMode.Pairwise): Witness =
      Witness(site.function, site.region, other, against, scheme, DivergenceStatus.Bounded,
              Some(maximizing), Some(box))

    /** Every divergence considered, grouped by the function it belongs to.
      *
      * `parametersOf` names a function's inputs in declaration order, which is the order a
      * box is written in, so that the report reads alongside the configuration the fuzzer
      * is given, whose intervals are positional.
      */
    def report(witnesses: Seq[Witness], parametersOf: String => Seq[String]): Json = {
      def end(d: Option[BigDecimal]): Json = d.fold(Json.Null)(Json.fromBigDecimal)

      def bounds(box: Box, parameters: Seq[String]): Json = {
        // A name the function does not declare cannot be placed among the ones it does,
        // so it goes last rather than somewhere misleading.
        def position(name: String): (Int, String) =
          (parameters.indexOf(name) match { case -1 => parameters.size; case i => i }, name)

        Json.obj(box.toSeq.sortBy { case (name, _) => position(name) }.map {
          case (name, (low, high)) => name -> Json.obj("lo" -> end(low), "hi" -> end(high))
        }*)
      }

      // Each scheme names what it compared in its own terms, so an entry says which one
      // wrote it as well as what it found.
      def where(w: Witness): Seq[(String, Json)] = w.scheme match {
        case DiscontinuityMode.Pairwise =>
          Seq("path" -> Json.fromInt(w.region),
              "divergentPath" -> Json.fromInt(w.other))

        case DiscontinuityMode.Merged =>
          Seq("guard" -> Json.fromInt(w.region),
              "untaken" -> Json.fromInt(w.other)) ++
            w.against.map(taken => "taken" -> Json.fromInt(taken))

        case DiscontinuityMode.Reference =>
          Seq("guard" -> Json.fromInt(w.region),
              "leaf" -> Json.fromInt(w.other)) ++
            w.against.map(reference => "reference" -> Json.fromInt(reference))
      }

      def one(w: Witness): Json = Json.obj(
        where(w) ++
        Seq("status" -> Json.fromString(w.status.label)) ++
        w.maximizing.map(m => "objective" -> Json.fromString(if (m) "maximum" else "minimum")) ++
        w.box.map(b => "box" -> bounds(b, parametersOf(w.function)))*
      )

      Json.obj(witnesses.groupBy(_.function).toSeq.sortBy(_._1).map {
        case (function, found) => function -> Json.arr(found.map(one)*)
      }*)
    }
  }

  enum FPPrecision(val exponent: Int, val significand: Int, val daisyName: String) {
    case Binary32 extends FPPrecision(8, 24, "Float32")
    case Binary64 extends FPPrecision(11, 53, "Float64")
  }

  object FPPrecision {
    def fromType(tpe: Type): Option[FPPrecision] = tpe match {
      case FPType(8, 24)  => Some(FPPrecision.Binary32)
      case FPType(11, 53) => Some(FPPrecision.Binary64)
      case _ => None
    }
  }

  /** The precision a function runs at, and the range its precondition gives each input. */
  case class InputSpec(precision: FPPrecision, ranges: Map[Identifier, (Double, Double)])

  /** One straight-line expression to analyze, as a self-contained FPCore definition. */
  case class RoundingQuery(fid: Identifier, name: String, precision: FPPrecision, fpcoreSource: String)

  case class RoundingResult(absError: BigDecimal)

  /** A tool that bounds errors introduced by floating-point rounding along one straight-line expression. */
  trait RoundingAnalyzer {
    val name: String

    /** Answers every query in one batch */
    def analyze(queries: Seq[RoundingQuery]): Map[String, Either[String, RoundingResult]]
  }

  private[roundoff] def traverse[A, B](as: Seq[A])(f: A => Either[String, B])
    : Either[String, Seq[B]] =
    as.foldLeft[Either[String, Seq[B]]](Right(Seq.empty)) {
      case (acc, a) => for { bs <- acc; b <- f(a) } yield bs :+ b
    }
}