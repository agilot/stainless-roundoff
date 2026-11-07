/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification
package roundoff

// What each option does is described for `--help` in `MainHelpers`.

object optDaisy extends inox.StringOptionDef("daisy", "daisy", "PATH")
object optFPTaylor extends inox.StringOptionDef("fptaylor", "fptaylor", "PATH")
object optFuzz extends inox.StringOptionDef("fuzz", "", "PATH")
object optRoundoffWitnesses extends inox.StringOptionDef("roundoff-witnesses", "", "FILE")

/** `bb` compiles every objective with `ocamlopt`, which is slow on many small leaves (36.4 s
  * against 0.3 s for `bb-eval` on forty leaves, with the same bounds). But `bb-eval` does not
  * scale: on `Algebird` and `OrientationIndexFilter` it gives nothing within five minutes,
  * where `auto` takes 56 s and 90 s.
  */
object optFPTaylorOptimizer extends inox.StringOptionDef("fptaylor-optimizer", "auto", "auto|bb|bb-eval")
object optFPTaylorOptTimeout extends inox.IntOptionDef("fptaylor-opt-timeout", 10000, "MILLISECONDS")

object optRoundoffExactInputs extends inox.FlagOptionDef("roundoff-exact-inputs", false)
object optRoundoffIncumbent extends inox.FlagOptionDef("roundoff-incumbent", true)
object optRoundoffPathRanges extends inox.FlagOptionDef("roundoff-path-ranges", true)
object optRoundoffOnly extends inox.FlagOptionDef("roundoff-only", false)

object optRoundoffFeasibilityShare extends inox.DoubleOptionDef("roundoff-feasibility-share", 0.1, "0..1")
object optRoundoffRefineShare extends inox.DoubleOptionDef("roundoff-refine-share", 0.5, "0..1")

/** On `TrainedMlp2` to `TrainedMlp4` the refinement stopped by itself after 12, 28 and 64
  * queries, far below the 324, 2,916 and 26,244 this default allows.
  */
object optRoundoffRefineBudget extends inox.DoubleOptionDef("roundoff-refine-budget", 4.0, "QUERIES")

/** Which tool bounds the rounding error of a leaf. Both treat an input as an exact real that
  * is rounded on entry; they differ only in how tight their bounds are.
  */
enum AnalyzerChoice {
  case Daisy
  case FPTaylor
}

object optRoundoffAnalyzer extends inox.OptionDef[AnalyzerChoice] {
  val name = "roundoff-analyzer"
  val default = AnalyzerChoice.Daisy
  val parser = (s: String) => AnalyzerChoice.values.find(_.toString.equalsIgnoreCase(s))
  val usageRhs = "daisy|fptaylor"
}

/** How the divergences across one guard are bounded. */
enum DiscontinuityMode(val label: String) {
  /** One Ibex query per pair of leaves across the guard: tight, but quadratic in the paths. */
  case Pairs extends DiscontinuityMode("pairs")

  /** One extrema query per guard bounds every pair at once, then the block with the largest
    * bound is split along its subtrees, within `--roundoff-refine-budget` queries per path.
    * Falls back to `pairs` when a leaf may be undefined somewhere on the input box.
    */
  case LinearRefine extends DiscontinuityMode("linear-refine")
}

object DiscontinuityMode {
  def tryFromString(s: String): Option[DiscontinuityMode] =
    values.find(_.label.equalsIgnoreCase(s))
}

object optRoundoffDiscontinuity extends inox.OptionDef[DiscontinuityMode] {
  val name = "roundoff-discontinuity"
  val default = DiscontinuityMode.LinearRefine
  val parser = DiscontinuityMode.tryFromString
  val usageRhs = "pairs|linear-refine"
}

case class RoundoffSettings(
  analyzer: AnalyzerChoice,
  daisy: String,
  fptaylor: String,
  fptaylorOptimizer: String,
  fptaylorOptTimeout: Int,
  fuzzer: String,
  exactInputs: Boolean,
  incumbent: Boolean,
  pathRanges: Boolean,
  roundoffOnly: Boolean,
  timeout: Option[Double],
  feasibilityShare: Double,
  witnessFile: Option[java.io.File],
  discontinuity: DiscontinuityMode,
  refineBudget: Double,
  refineShare: Double
) {

  def fuzzingEnabled: Boolean = fuzzer.nonEmpty
}

object RoundoffSettings {
  def from(ctx: inox.Context): RoundoffSettings = {
    def get[A: scala.reflect.ClassTag](option: inox.OptionDef[A]): A = ctx.options.findOptionOrDefault(option)
    def share(option: inox.OptionDef[Double]): Double = get(option).max(0.0).min(1.0)

    RoundoffSettings(
      analyzer = get(optRoundoffAnalyzer),
      daisy = get(optDaisy),
      fptaylor = get(optFPTaylor),
      fptaylorOptimizer = get(optFPTaylorOptimizer),
      fptaylorOptTimeout = get(optFPTaylorOptTimeout),
      fuzzer = get(optFuzz),
      exactInputs = get(optRoundoffExactInputs),
      incumbent = get(optRoundoffIncumbent),
      pathRanges = get(optRoundoffPathRanges),
      roundoffOnly = get(optRoundoffOnly),
      timeout = ctx.options.findOption(inox.optTimeout).map(_.toNanos / 1e9).filter(_ > 0),
      feasibilityShare = share(optRoundoffFeasibilityShare),
      witnessFile = Some(get(optRoundoffWitnesses)).filter(_.nonEmpty).map(new java.io.File(_)),
      discontinuity = get(optRoundoffDiscontinuity),
      refineBudget = get(optRoundoffRefineBudget).max(0.0),
      refineShare = share(optRoundoffRefineShare)
    )
  }
}

