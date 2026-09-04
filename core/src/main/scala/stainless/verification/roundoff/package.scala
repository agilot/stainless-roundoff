/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification

import stainless.trees._

package object roundoff {

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