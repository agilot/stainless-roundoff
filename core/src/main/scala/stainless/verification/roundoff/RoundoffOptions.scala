/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification
package roundoff

/** Path to the Daisy executable. */
object optDaisy extends inox.OptionDef[String] {
  import inox.OptionParsers._
  val name = "daisy"
  val default = "daisy"
  val parser = stringParser
  val usageRhs = "PATH"
}

/** Which tool bounds the rounding error of a leaf.
  *
  * Both answer the same question (an input is an exact real, rounded on entry); they differ
  * only in how tight their bounds are.
  */
enum AnalyzerChoice {
  case Daisy
  case FPTaylor
}

object AnalyzerChoice {
  def tryFromString(s: String): Option[AnalyzerChoice] =
    values.find(_.toString.equalsIgnoreCase(s))
}

object optRoundoffAnalyzer extends inox.OptionDef[AnalyzerChoice] {
  val name = "roundoff-analyzer"
  val default = AnalyzerChoice.Daisy
  val parser = AnalyzerChoice.tryFromString
  val usageRhs = "daisy|fptaylor"
}

/** Path to the FPTaylor executable. */
object optFPTaylor extends inox.OptionDef[String] {
  import inox.OptionParsers._
  val name = "fptaylor"
  val default = "fptaylor"
  val parser = stringParser
  val usageRhs = "PATH"
}

/** Seconds one FPTaylor run (all leaves together) may take.
  *
  * FPTaylor limits each of its optimisation problems, but not a whole run, and a hard leaf can
  * raise many problems.
  */
object optFPTaylorTimeout extends inox.OptionDef[Double] {
  import inox.OptionParsers._
  val name = "fptaylor-timeout"
  val default = 300.0
  val parser = doubleParser
  val usageRhs = "SECONDS"
}

/** Which FPTaylor optimizer bounds a Taylor form.
  *
  * `bb` compiles every objective with `ocamlopt`, which is slow on many small leaves (36.4 s
  * against 0.3 s for `bb-eval` on forty leaves, with identical bounds). But `bb-eval` does not
  * scale to large leaves: on `Algebird` and `OrientationIndexFilter` it returns nothing within
  * five minutes, where `auto` takes 56 s and 90 s. So `auto` is the default, and `bb-eval` is
  * only worth using when every leaf is small.
  */
object optFPTaylorOptimizer extends inox.OptionDef[String] {
  import inox.OptionParsers._
  val name = "fptaylor-optimizer"
  val default = "auto"
  val parser = stringParser
  val usageRhs = "auto|bb|bb-eval"
}

/** Milliseconds FPTaylor may spend on one optimisation problem. */
object optFPTaylorOptTimeout extends inox.OptionDef[Int] {
  import inox.OptionParsers._
  val name = "fptaylor-opt-timeout"
  val default = 10000
  val parser = intParser
  val usageRhs = "MILLISECONDS"
}

/** Path to the fuzzer; empty for no fuzzing.
  *
  * The analysis bounds the error from above. The fuzzer searches the regions Ibex found for a
  * large error, which bounds it from below, so each obligation reports an interval.
  */
object optFuzz extends inox.OptionDef[String] {
  import inox.OptionParsers._
  val name = "fuzz"
  val default = ""
  val parser = stringParser
  val usageRhs = "PATH"
}

/** Whether inputs are exact reals, rather than values already rounded on entry.
  *
  * With rounded inputs, Daisy charges every input half an ulp, so even a guard comparing an
  * input with a constant can be read the wrong way. With exact inputs it cannot.
  */
object optRoundoffExactInputs extends inox.FlagOptionDef("roundoff-exact-inputs", false)

/** Whether the solver is asked which branches no input can take, so that their leaves are
  * left out of the bound.
  */
object optRoundoffPruning extends inox.FlagOptionDef("roundoff-pruning", true)

/** Whether to skip bounding a divergence that cannot exceed the largest one found so far.
  *
  * The function's error only depends on the largest divergence. Checking whether a divergence
  * can exceed it is a yes-or-no question, usually much faster than bounding it.
  */
object optRoundoffIncumbent extends inox.FlagOptionDef("roundoff-incumbent", true)

/** Whether a leaf is analysed only over the inputs that reach it.
  *
  * A guard between an input and a literal restricts that input on each side. Using this only
  * narrows ranges, so it can only make bounds tighter.
  */
object optRoundoffPathRanges extends inox.FlagOptionDef("roundoff-path-ranges", true)

/** Whether objectives are rewritten over named guard differences (see [[Normalisation]]).
  *
  * Ibex searches a box, which cannot express that two variables are nearly equal. Naming the
  * guard difference makes the band an interval Ibex can use directly.
  */
object optRoundoffNormalisation extends inox.FlagOptionDef("roundoff-normalisation", true)

/** Seconds the analysis of one function may take, divergence queries included.
  *
  * It is a budget for all queries of a function, not a limit per query, because most queries
  * finish in a few milliseconds while a few never do. Time a query does not use goes to the
  * queries after it. Time spent before the queries (reading the function, pruning) is
  * subtracted. Work shared by all functions, such as the analyzer run, is not.
  */
object optRoundoffTimeout extends inox.OptionDef[Double] {
  import inox.OptionParsers._
  val name = "roundoff-timeout"
  val default = 1.0
  val parser = doubleParser
  val usageRhs = "SECONDS"
}

/** The largest fraction of a function's budget the branch questions may use together.
  *
  * Time they do not use goes to the divergence queries. A question that runs out of time keeps
  * its branch, so a small share can only cost refutations, never soundness.
  */
object optRoundoffPruningShare extends inox.OptionDef[Double] {
  import inox.OptionParsers._
  val name = "roundoff-pruning-share"
  val default = 0.2
  val parser = doubleParser
  val usageRhs = "0..1"
}

/** The fraction of a query's time spent checking whether its region contains any point.
  *
  * The rest is split between the upper and the lower bound. The check is cheap and usually
  * takes about a millisecond.
  */
object optRoundoffFeasibilityShare extends inox.OptionDef[Double] {
  import inox.OptionParsers._
  val name = "roundoff-feasibility-share"
  val default = 0.1
  val parser = doubleParser
  val usageRhs = "0..1"
}

/** Where to write what each divergence query found, as JSON; empty for nowhere.
  *
  * For `@fuzz` functions, the fuzzer program (`.scala`) and configuration (`.conf`) are written
  * next to it with the same base name, which is how the fuzzer finds them.
  */
object optRoundoffWitnesses extends inox.OptionDef[String] {
  import inox.OptionParsers._
  val name = "roundoff-witnesses"
  val default = ""
  val parser = stringParser
  val usageRhs = "FILE"
}

/** Every roundoff option, read once from the context. */
case class RoundoffSettings(
  analyzer: AnalyzerChoice,
  daisy: String,
  fptaylor: String,
  fptaylorTimeout: Double,
  fptaylorOptimizer: String,
  fptaylorOptTimeout: Int,
  fuzzer: String,
  exactInputs: Boolean,
  pruning: Boolean,
  incumbent: Boolean,
  pathRanges: Boolean,
  normalisation: Boolean,
  budget: Double,
  pruningShare: Double,
  feasibilityShare: Double,
  witnessFile: Option[java.io.File]
) {
  def fuzzingEnabled: Boolean = fuzzer.nonEmpty

  /** One line for `--debug=roundoff`. */
  def describe: String = {
    def flag(name: String, on: Boolean) = if (on) name else s"no $name"
    s"${budget}s per function of which ${(pruningShare * 100).toInt}% for the branch questions, " +
    s"${(feasibilityShare * 100).toInt}% of a search for feasibility, " +
    Seq(flag("pruning", pruning), flag("normalisation", normalisation),
        flag("path ranges", pathRanges), flag("incumbent", incumbent),
        if (exactInputs) "exact inputs" else "rounded inputs").mkString(", ")
  }
}

object RoundoffSettings {
  def from(ctx: inox.Context): RoundoffSettings = {
    def get[A: scala.reflect.ClassTag](option: inox.OptionDef[A]): A = ctx.options.findOptionOrDefault(option)
    def share(option: inox.OptionDef[Double]): Double = get(option).max(0.0).min(1.0)

    RoundoffSettings(
      analyzer = get(optRoundoffAnalyzer),
      daisy = get(optDaisy),
      fptaylor = get(optFPTaylor),
      fptaylorTimeout = get(optFPTaylorTimeout),
      fptaylorOptimizer = get(optFPTaylorOptimizer),
      fptaylorOptTimeout = get(optFPTaylorOptTimeout),
      fuzzer = get(optFuzz),
      exactInputs = get(optRoundoffExactInputs),
      pruning = get(optRoundoffPruning),
      incumbent = get(optRoundoffIncumbent),
      pathRanges = get(optRoundoffPathRanges),
      normalisation = get(optRoundoffNormalisation),
      budget = get(optRoundoffTimeout),
      pruningShare = share(optRoundoffPruningShare),
      feasibilityShare = share(optRoundoffFeasibilityShare),
      witnessFile = Some(get(optRoundoffWitnesses)).filter(_.nonEmpty).map(new java.io.File(_))
    )
  }
}
