/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification
package roundoff

import trees._
import java.io.File
import java.nio.file.Files
import scala.util.Try

/* The fuzzer searches the regions Ibex found for a large error, which gives a lower bound on
 * the worst-case error to set against the upper bound:
 *  - [[FuzzDriver]]: hands the `@fuzz` functions to the fuzzer and reads back their bounds;
 *  - [[FuzzRunner]]: runs the fuzzer;
 *  - [[FuzzConfEmitter]] and [[FuzzProgramEmitter]]: what the fuzzer is given.
 */

/** Runs the fuzzer on a configuration and reads back what it found. */
class FuzzRunner(ctx: inox.Context, settings: RoundoffSettings) {
  val name = "gavdos"

  val enabled: Boolean = settings.fuzzingEnabled

  /** What the fuzzer found for each function, by the name it gives the function, or why it
    * found nothing.
    */
  def run(conf: File): Either[String, Map[String, FuzzedFunction]] =
    ExternalTool.findExecutable(settings.fuzzer) match {
      case None => Left(ExternalTool.notFoundMessage("fuzzer", settings.fuzzer, "fuzz"))

      case Some(executable) =>
        val report = File.createTempFile("gavdos", ".json")
        report.deleteOnExit()
        val command = Seq(executable.getAbsolutePath, conf.getAbsolutePath,
                          "--output", report.getAbsolutePath)
        ExternalTool.run("the fuzzer", command, conf.getAbsoluteFile.getParentFile, ctx.reporter)
          .flatMap { run =>
            val found = Try(Files.readString(report.toPath)).toOption.map(read).getOrElse(Map.empty)
            // A run that found nothing has failed at something.
            if (found.nonEmpty) Right(found)
            else Left(s"the fuzzer ${failureOf(run.exitCode)} (exit code ${run.exitCode})" +
              run.output.linesIterator.map(_.trim).filter(_.nonEmpty).toSeq.lastOption
                .map(line => s": $line").getOrElse(""))
          }
    }

  /** What the fuzzer's exit code says went wrong. */
  private def failureOf(exitCode: Int): String = exitCode match {
    case 1 => "could not compile the program, compare its results or write its report"
    case 2 => "refused the configuration"
    // Above 128, a signal stopped it, such as SIGABRT after a crash of its native code.
    case code if code > 128 => "crashed"
    case _ => "reported nothing"
  }

  /** What the JSON report says about each function, across all of its configurations. Errors
    * are strings, to keep every digit.
    *
    * A divergence box reports the errors of the runs that diverged and no others, so a box
    * where nothing diverged adds nothing, and the rounding domain still gives a figure.
    */
  def read(report: String): Map[String, FuzzedFunction] = {
    import io.circe.Json

    def findingsOf(results: Json): FuzzedFunction = {
      val cases = results.hcursor.downField("cases").as[Map[String, Seq[String]]].getOrElse(Map.empty)
      val configurations = Seq("divergence", "rounding").flatMap(goal =>
        results.hcursor.downField(goal).focus.flatMap(_.asArray).getOrElse(Vector.empty))

      def inputsOf(configuration: Json): Seq[String] =
        configuration.hcursor.downField("inputs").as[Seq[String]].getOrElse(Seq.empty)

      val errors = configurations.flatMap { configuration =>
        configuration.hcursor.downField("fields").focus.flatMap(_.asObject).toSeq.flatMap(_.toList)
          .flatMap { case (number, found) =>
            // Stripped, so that a zero written with 35 digits reads as 0.
            found.hcursor.downField("maxAbsErr").as[String].toOption
              .flatMap(error => Try(BigDecimal(new java.math.BigDecimal(error).stripTrailingZeros)).toOption)
              .map(number -> _)
          }
      }

      val caseDivergences = configurations.flatMap { configuration =>
        configuration.hcursor.downField("caseDivergences").focus.flatMap(_.asArray).toSeq.flatten
          .map { divergence =>
            val returned = divergence.hcursor.downField("cases").focus.flatMap(_.asArray).toSeq.flatten
              .map { place =>
                def text(key: String) = place.hcursor.downField(key).as[String].getOrElse("")
                (text("path"), text("float"), text("mpfr"))
              }
            val example = divergence.hcursor.downField("example").as[Seq[Json]].getOrElse(Seq.empty)
            CaseDivergence(returned, divergence.hcursor.downField("divergent").as[Long].getOrElse(0L),
                           inputText(inputsOf(configuration), example, cases))
          }
      }

      val firstCrash = configurations.iterator.flatMap { configuration =>
        configuration.hcursor.downField("firstCrash").focus.filterNot(_.isNull).map { crash =>
          def thrown(version: String) = crash.hcursor.downField(version).as[String].toOption
          FuzzCrash(inputText(inputsOf(configuration),
                              crash.hcursor.downField("input").as[Seq[Json]].getOrElse(Seq.empty), cases),
                    thrown("float"), thrown("mpfr"))
        }
      }.nextOption()

      FuzzedFunction(
        errors.groupMapReduce(_._1)(_._2)(_ max _),
        // The same cases can differ in several configurations.
        caseDivergences.groupBy(_.cases).values.map(same => same.head.copy(runs = same.map(_.runs).sum))
          .toSeq.sortBy(-_.runs),
        configurations.map(_.hcursor.downField("crashed").as[Long].getOrElse(0L)).sum,
        firstCrash)
    }

    io.circe.parser.parse(report).toOption
      .flatMap(_.hcursor.downField("functions").focus.flatMap(_.asObject))
      .map(_.toMap.map { case (function, results) => function -> findingsOf(results) })
      .getOrElse(Map.empty)
  }

  /** An input of the report as `name = value`. A case input is written as its case, and the
    * fields of the cases it did not pick, which hold 0, are left out.
    */
  private def inputText(names: Seq[String], values: Seq[io.circe.Json],
                        cases: Map[String, Seq[String]]): String = {
    val namedValues = names.zip(values)
    val picked: Map[String, String] = namedValues.flatMap { case (name, value) =>
      cases.get(name).flatMap(names => value.asNumber.flatMap(_.toInt).flatMap(names.lift)).map(name -> _)
    }.toMap
    def isFieldOfAnotherCase(name: String): Boolean = picked.exists { case (input, chosen) =>
      name.startsWith(s"$input.") && name.stripPrefix(s"$input.").takeWhile(_ != '.') != chosen
    }
    namedValues.collect {
      case (name, value) if !isFieldOfAnotherCase(name) =>
        s"$name = ${picked.getOrElse(name, value.noSpaces)}"
    }.mkString(", ")
  }
}

/** What the fuzzer found for one function, across all of its configurations.
  *
  * @param widestErrors    the widest error of each number of the result, by the name the fuzzer
  *                        gives it, such as `_1` or `Some.value`; empty for a result that is
  *                        one number
  * @param caseDivergences the runs in which the floating-point and the precise version
  *                        returned different cases, the most frequent first
  * @param crashes         how many runs threw something other than a failed `require`
  * @param firstCrash      the first of them
  */
case class FuzzedFunction(widestErrors: Map[String, BigDecimal], caseDivergences: Seq[CaseDivergence],
                          crashes: Long, firstCrash: Option[FuzzCrash])

/** Runs that returned different cases.
  *
  * @param cases   where in the result they differ, and what each version returned there, such
  *                as `_1`, `Continue` (floating point) and `Finished` (precise)
  * @param runs    how many runs did
  * @param example an input that did, as `name = value`
  */
case class CaseDivergence(cases: Seq[(String, String, String)], runs: Long, example: String)

/** A run that threw: its input, and what each version threw, `None` for one that did not. */
case class FuzzCrash(input: String, floatThrew: Option[String], preciseThrew: Option[String])

/** A number the fuzzer gives a function, named as the fuzzer names it, such as `p.x` or
  * `s.Circle.r`, and the range it takes over the function's domain.
  */
case class FuzzInput(path: String, low: Double, high: Double)

/** One variant of a function's inputs ([[InputVariant]]), as its divergence boxes build it.
  *
  * @param description the variant's description, as in the names of its witnesses
  * @param cases       each input that picks a case, such as `s` for a trait or a `Boolean`, and
  *                    the case the variant builds, or `None` where it may build any case without
  *                    fields
  * @param variables   each number the variant builds, as the fuzzer names it, and the variable
  *                    that stands for it in Ibex's boxes, such as `s.Circle.r` and `s_r`
  */
case class FuzzVariant(description: String, cases: Seq[(String, Option[String])],
                       variables: Seq[(String, String)])

/** One function handed to the fuzzer, called by the name the fuzzer gives it. */
case class FuzzSubject(name: String, inputs: Seq[FuzzInput], variants: Seq[FuzzVariant])

/** Writes the fuzzer configuration: each function's input domain and the regions Ibex found. */
object FuzzConfEmitter {

  /** How far a certified box is widened before it is searched: not at all, since adaptive
    * widening grows it only where it holds no divergence.
    */
  private val initialWidening = 1

  /** Whether a box grows about its centre each time bisection finds no divergence in it, until
    * one turns up or the box fills the domain.
    */
  private val adaptiveWidening = true

  /** How much a box grows each time, with adaptive widening. */
  private val wideningFactor = 10

  /** How a divergence box is explored. Bisection finds the inputs a few ulps from a branch
    * boundary, which sampling almost never hits.
    */
  private val exploration = "bisection"

  /** Whether the inputs left after exploring go on mutating around the divergences found. */
  private val mutatesAfterExploring = true

  /** The share of a box's inputs spent exploring before mutation starts. */
  private val explorationShare = 0.9

  /** Whether identical divergence boxes are searched once, so that a copy, such as the box of
    * each term of an extrema query, takes no share of the inputs.
    */
  private val uniqueBoxes = true

  /** Whether the rounding domain is also searched as a divergence box, which can find a
    * divergence where Ibex gave no box.
    */
  private val divergenceInDomains = true

  /** The configuration for `subjects`, each with the witnesses Ibex found for it: the
    * settings, then one `key = value` line per input of each domain and each box.
    *
    * The fuzzer searches each rounding domain for `seconds`, and each function's divergence
    * boxes for as long together, evenly, once identical ones are merged; the rounding domain
    * searched for divergences counts as one of them. It tries as many inputs as fit.
    */
  def emit(subjects: Seq[(FuzzSubject, Seq[Witness])], seconds: Double): String = {
    val entries = subjects.flatMap { case (subject, witnesses) => configurationEntries(subject, witnesses) }
    val keyWidth = entries.map { case (key, _) => key.length }.maxOption.getOrElse(0)

    val time = BigDecimal(seconds).bigDecimal.stripTrailingZeros.toPlainString
    val settings = Seq(s"time = $time", s"widen = $initialWidening",
                       s"adaptive-widen = $adaptiveWidening", s"widen-factor = $wideningFactor",
                       s"explore = $exploration",
                       s"mutate = $mutatesAfterExploring", s"explore-share = $explorationShare",
                       s"unique-boxes = $uniqueBoxes", s"divergence-in-domains = $divergenceInDomains")
    val entryLines = entries.map { case (key, value) => s"${key.padTo(keyWidth, ' ')} = $value" }

    (settings ++ Seq("") ++ entryLines).mkString("", "\n", "\n")
  }

  /** The `(key, value)` entries of one function: the range of each number over its rounding
    * domain, then, for each box Ibex found, the cases its variant builds and the range of each
    * number it builds. A domain covers every case, so it names none.
    */
  private def configurationEntries(subject: FuzzSubject, witnesses: Seq[Witness])
  : Seq[(String, String)] = {
    val domain = subject.inputs.map(input =>
      (s"${subject.name}.rounding.domain.${input.path}", s"[${input.low}, ${input.high}]"))

    // A divergence without a box has no region to search, and one whose box narrows no input,
    // as when Ibex found no point, would only search the whole domain again.
    val searched = witnesses.flatMap { w =>
      w.box.zip(subject.variants.find(_.description == variantOf(w)))
        .filter { case (box, variant) =>
          variant.variables.exists { case (_, variable) => narrows(box, variable) }
        }
        .map { case (box, variant) => (w, box, variant) }
    }
    // An extrema query records one box per term of its distance under the same name, so a
    // repeated name gets the number of its repetition.
    val names = searched.map { case (w, _, _) => configurationName(w) }
    val uniqueNames = names.zipWithIndex.map { case (name, i) =>
      names.take(i).count(_ == name) match {
        case 0 => name
        case seen => s"${name}_${seen + 1}"
      }
    }
    val divergences = searched.zip(uniqueNames).flatMap { case ((_, box, variant), name) =>
      val prefix = s"${subject.name}.divergence.$name"
      variant.cases.map { case (input, chosen) => (s"$prefix.$input", chosen.getOrElse("empty")) } ++
        variant.variables.map { case (path, variable) => (s"$prefix.$path", intervalOf(box, variable)) }
    }

    domain ++ divergences
  }

  /** A witness is named after the obligation it was found for: the function, then the number
    * of its result after a dot and the variant of its inputs in brackets, where it has several.
    */
  def isFoundFor(w: Witness, function: String): Boolean =
    w.function == function || w.function.startsWith(s"$function.") ||
      w.function.startsWith(s"$function [")

  /** The description of the variant `w` was found for, empty without a choice of constructor. */
  private def variantOf(w: Witness): String = w.function match {
    case s"$_ [$variant]" => variant
    case _ => ""
  }

  /** The name of the configuration searching the box of `w`, such as `g2_u3_t1_max`: its
    * guard, its leaves, and the end of the distance it bounded.
    */
  private def configurationName(w: Witness): String = {
    val objective = w.maximizing.map(if (_) "max" else "min").getOrElse("any")
    val leaves = w.site.pair match {
      case Some((taken, untaken)) => s"u${untaken}_t$taken"
      case None => "all"
    }
    val obligation = numberAndVariantOf(w)
    val prefix = if (obligation.isEmpty) "" else s"${obligation}_"
    s"${prefix}g${w.site.guard}_${leaves}_$objective"
  }

  /** The number and variant a witness was found for, as one word, since the fuzzer reads the
    * name of a configuration up to the next dot.
    */
  private def numberAndVariantOf(w: Witness): String =
    w.function.dropWhile(c => c != '.' && c != ' ')
      .replaceAll("\\W+", "_").stripPrefix("_").stripSuffix("_")

  private def narrows(box: Box, variable: String): Boolean =
    box.get(variable).exists { case (low, high) => low.isDefined || high.isDefined }

  /** The interval of `variable` in `box`, `[*, *]` when Ibex left it open. A single point gets
    * one ulp on each side: the fuzzer widens a box by scaling its width, which leaves a point as
    * it is.
    */
  private def intervalOf(box: Box, variable: String): String =
    box.get(variable) match {
      case Some((Some(low), Some(high))) if low == high =>
        s"[${Math.nextDown(low.toDouble)}, ${Math.nextUp(high.toDouble)}]"
      case Some((low, high)) => s"[${boundOrWildcard(low)}, ${boundOrWildcard(high)}]"
      case None => "[*, *]"
    }

  /** A missing bound is written `*`, which the fuzzer replaces by the bound of the domain. */
  private def boundOrWildcard(bound: Option[BigDecimal]): String =
    bound.map(_.toString).getOrElse("*")
}

/** Writes the program the fuzzer runs: each source file holding a `@fuzz` function, made plain
  * Scala.
  *
  * Stainless imports are dropped, except `stainless.math`, which becomes `scala.math`, and so
  * are annotations other than `@fuzz` and package clauses, such as `package a.b`, so that several
  * files can share one program. Package blocks, `package a.b { ... }`, are kept, since their
  * braces hold the rest. Qualified access, such as `private[regression]`, is dropped, since what
  * it names may be a package that is. The library's `Option` becomes Scala's, whose `None` is an object: `None()` and
  * `None[Double]()` become `None`. What else only Stainless knows, such as `Real` or
  * `decreases`, is left as it is, and the fuzzer refuses it.
  */
object FuzzProgramEmitter {

  def plainScalaProgram(sources: Seq[String]): String =
    sources.distinct.map(asPlainScala).mkString("\n")

  def asPlainScala(source: String): String = {
    val keptLines = source.linesIterator.flatMap { line =>
      val code = line.trim
      if (code.startsWith("import stainless.math"))
        Some(line.replace("import stainless.math", "import scala.math"))
      else if (code.startsWith("import stainless") || isPackageClause(code)) None
      else Some(line)
    }
    val withoutAnnotations = nonFuzzAnnotation.replaceAllIn(keptLines.mkString("", "\n", "\n"), "")
    val withScalaNone = stainlessNone.replaceAllIn(withoutAnnotations, "None")
    qualifiedAccess.replaceAllIn(withScalaNone, "").replace("stainless.math.", "scala.math.")
  }

  /** `private[a]` or `protected[a]`, and the space after it. */
  private val qualifiedAccess = """\b(?:private|protected)\[[^\]]*\]\s*""".r

  /** `source` with the functions declared on `lines`, counted from 1, made public: the fuzzer
    * only calls public functions, and being public changes nothing about what one computes.
    */
  def madePublicAt(source: String, lines: Set[Int]): String =
    if (lines.isEmpty) source
    else source.linesIterator.zipWithIndex.map { case (text, i) =>
      if (lines(i + 1)) accessBeforeDef.replaceFirstIn(text, "") else text
    }.mkString("", "\n", "\n")

  /** `private` or `protected` before a `def`, maybe with other modifiers in between. */
  private val accessBeforeDef = """\b(?:private|protected)\s+(?=(?:[a-z]+\s+)*def\b)""".r

  /** `source` without the `@fuzz` of the functions declared on `lines`, counted from 1, so that
    * the fuzzer does not try a function it was not given a configuration for. The annotation is
    * on the line of its function, or on the lines just above it that hold only annotations.
    */
  def withoutFuzzAt(source: String, lines: Set[Int]): String =
    if (lines.isEmpty) source
    else {
      val sourceLines = source.linesIterator.toVector
      val annotated = lines.flatMap { line =>
        Iterator.iterate(line - 1)(_ - 1)
          .takeWhile(above => above >= 1 && onlyAnnotations.matches(sourceLines(above - 1).trim))
          .toSet + line
      }
      sourceLines.zipWithIndex.map { case (text, i) =>
        if (annotated(i + 1)) fuzzAnnotation.replaceAllIn(text, "") else text
      }.mkString("", "\n", "\n")
    }

  /** A line holding annotations and nothing else, such as `@roundoff @ fuzz`. */
  private val onlyAnnotations = """(?:@\s*[A-Za-z_][\w.]*(?:\([^()]*\))?\s*)+""".r

  /** `@fuzz`, also written `@ fuzz`, and the space after it. */
  private val fuzzAnnotation = """@\s*fuzz\b\s*""".r

  /** The library's `None`, built or matched, with its type argument if it is given one. */
  private val stainlessNone = """\bNone(?:\[(?:[^\[\]]|\[[^\[\]]*\])*\])?\(\)""".r

  /** A package clause, such as `package a.b`, rather than a package block, `package a.b {`. */
  private def isPackageClause(code: String): Boolean =
    code.startsWith("package ") && !code.endsWith("{")

  /** What the fuzzer calls `fd`: its name after the objects around it, without its package.
    * A top-level function is in an object Scala names after the file, such as `Clamp$package`,
    * which the source does not show, so it is left out.
    */
  def fuzzerNameOf(fd: FunDef, source: String): String = {
    val path = (fd.id match {
      case id: SymbolIdentifier => id.symbol.path
      case id => Seq(id.name)
    }).filterNot(_.endsWith("$package"))
    val inPackage = packagesDeclaredIn(source).filter(name => path.startsWith(name)).maxByOption(_.size)
    path.drop(inPackage.map(_.size).getOrElse(0)).mkString(".")
  }

  /** The packages `source` declares, each as the names it is made of. Clauses add up, so
    * `package a` then `package b` declare `a.b`, and each block, `package c { ... }`, declares
    * one under them.
    */
  private def packagesDeclaredIn(source: String): Seq[Seq[String]] =
    source.linesIterator.map(_.trim).filter(_.startsWith("package "))
      .foldLeft((Seq.empty[String], Seq.empty[Seq[String]])) { case ((clauses, declared), line) =>
        val inside = clauses ++ line.stripPrefix("package ").stripSuffix("{").trim.split('.').toSeq
        if (isPackageClause(line)) (inside, declared :+ inside) else (clauses, declared :+ inside)
      }._2

  /** An annotation other than `@fuzz`, with its arguments and the space after it. */
  private val nonFuzzAnnotation = """@(?!fuzz\b)[A-Za-z_][\w.]*(?:\([^()]*\))?\s*""".r
}

/** Hands the `@fuzz` functions to the fuzzer and reads back what it found for each.
  *
  * @param functions  the `@roundoff` functions, in declaration order
  * @param variantsOf the decomposition of each variant of a function's inputs, any number of its
  *                   result
  * @param witnesses  the regions Ibex found, read once the search is over
  */
private[roundoff] final class FuzzDriver(
  ctx: inox.Context,
  settings: RoundoffSettings,
  fuzzer: FuzzRunner,
  functions: Seq[FunDef],
  variantsOf: FunDef => Either[String, Seq[RoundoffErrorDecomposition]],
  witnesses: () => Seq[Witness],
  timers: inox.utils.TimerStorage
)(using symbols: Symbols) {

  import ctx.reporter

  private given PrinterOptions = PrinterOptions.fromSymbols(symbols, ctx)

  /** Runs the fuzzer over every subject, once, and warns of the runs that threw. */
  def run(): Unit = {
    val _ = fuzzedFunctions
    subjects.foreach { subject =>
      findingsFor(subject.fd)
        .flatMap(found => found.firstCrash.filter(_ => found.crashes > 0).map(found -> _))
        .foreach { case (found, crash) =>
          val thrown = Seq("the floating-point version" -> crash.floatThrew,
                           "the precise version" -> crash.preciseThrew)
            .collect { case (version, Some(exception)) => s"$version threw $exception" }
          reporter.warning(subject.fd.getPos,
            s"${found.crashes} runs of ${subject.fd.id.asString} by the fuzzer threw, first at " +
              s"${crash.input}: ${thrown.mkString(" and ")}")
        }
    }
  }

  /** The widest error the fuzzer found for the number of `fd`'s result labelled `field`
    * ([[VCKind.RoundoffError]]), or why it found none. Nothing when the fuzzer was not asked
    * for, or `fd` is not marked `@fuzz`.
    */
  def lowerBound(fd: FunDef, field: Option[String]): Option[Either[String, BigDecimal]] =
    subjectsByFunction.collectFirst { case (`fd`, subject) => subject }.filter(_ => fuzzer.enabled).map {
      case Left(why) => Left(s"no fuzzer program: $why")
      case Right(subject) =>
        val number = fuzzerNameOfResultNumber(fd, field)
        val obligation = (fd.id.asString +: field.toSeq).mkString(".")
        val found = fuzzedFunctions
          .flatMap(_.get(subject.fuzzed.name).toRight("the fuzzer reported nothing for it"))
          .flatMap(found => found.widestErrors.get(number).toRight(noErrorMessage(found)))
        found.left.foreach(why => reporter.warning(fd.getPos, s"No fuzzed error for $obligation: $why"))
        found
    }

  /** Why the fuzzer gave no error for a number of the result: the names it did report, when
    * none matches, since they show what it named the numbers instead.
    */
  private def noErrorMessage(found: FuzzedFunction): String =
    found.widestErrors.keys.toSeq.sorted match {
      case Seq() => "the fuzzer reported no error for it"
      case reported => s"the fuzzer reported errors only for ${reported.map(n => s"'$n'").mkString(", ")}"
    }

  /** The runs in which the fuzzer saw the two versions of `fd` return different cases, if it
    * was run on it.
    */
  def caseDivergences(fd: FunDef): Option[Seq[CaseDivergence]] =
    findingsFor(fd).map(_.caseDivergences)

  private def findingsFor(fd: FunDef): Option[FuzzedFunction] =
    subjects.find(_.fd == fd).filter(_ => fuzzer.enabled)
      .flatMap(subject => fuzzedFunctions.toOption.flatMap(_.get(subject.fuzzed.name)))

  /** Writes the program and the configuration beside `base`, if there are subjects. The
    * fuzzer finds its program from the configuration's name, so both share it.
    */
  def writeFuzzerInputs(base: File): Unit =
    if (subjects.nonEmpty) { val _ = writeProgramAndConfiguration(base) }

  /** The files the program was read from that writing `base` and its siblings would replace. */
  def sourcesReplacedBy(base: File): Seq[File] = {
    val written =
      if (subjects.isEmpty) Seq(base) else Seq(base, withExtension(base, "conf"), withExtension(base, "scala"))
    written.map(_.getCanonicalFile).distinct.filter(sourceFiles)
  }

  private lazy val sourceFiles: Set[File] =
    (symbols.functions.values ++ symbols.sorts.values).map(_.getPos).collect {
      case pos: inox.utils.DefinedPosition => pos.file.getCanonicalFile
    }.toSet

  /** A `@fuzz` function, as the fuzzer is given it, and the source file it is written in. */
  private case class Subject(fd: FunDef, fuzzed: FuzzSubject, source: String)

  /** Each `@fuzz` function, as the fuzzer is given it, or why it is not. */
  private lazy val subjectsByFunction: Seq[(FunDef, Either[String, Subject])] =
    functions.filter(_.flags.contains(Fuzz)).foldLeft(Seq.empty[(FunDef, Either[String, Subject])]) {
      (done, fd) =>
        val subject = subjectOf(fd, done.collect { case (_, Right(written)) => written.fd.id.name })
        subject.left.foreach(why => reporter.warning(fd.getPos, s"No fuzzer program for ${fd.id.asString}: $why"))
        done :+ (fd -> subject)
    }

  private lazy val subjects: Seq[Subject] = subjectsByFunction.collect { case (_, Right(subject)) => subject }

  private def subjectOf(fd: FunDef, takenNames: Seq[String]): Either[String, Subject] =
    if (takenNames.contains(fd.id.name))
      Left(s"another annotated function is called '${fd.id.name}', and a witness names only " +
           "the function it belongs to, so the two cannot be told apart")
    else
      sourceOf(fd).flatMap { source =>
        variantsOf(fd).flatMap { variants =>
          inputPartsOf(fd).flatMap(parts =>
            fuzzSubjectOf(fd, FuzzProgramEmitter.fuzzerNameOf(fd, source), parts, variants))
        }.map(Subject(fd, _, source))
      }

  /** A part of a parameter the fuzzer builds: a number, or the choice of a case, as for a trait
    * or a `Boolean`, with the names of its cases.
    */
  private enum InputPart {
    case Number(source: FieldRead, tpe: Type)
    case CaseChoice(source: FieldRead, cases: Seq[String])
  }

  /** Every part of `fd`'s parameters the fuzzer builds, the fields of every case included, or
    * why it cannot build one.
    */
  private def inputPartsOf(fd: FunDef): Either[String, Seq[InputPart]] = {
    def partsOfType(source: FieldRead, tpe: Type, seen: Set[Identifier]): Either[String, Seq[InputPart]] =
      tpe match {
        case number if isNumberType(number) => Right(Seq(InputPart.Number(source, number)))
        case BooleanType() => Right(Seq(InputPart.CaseChoice(source, Seq("false", "true"))))
        case TupleType(bases) =>
          traverse(bases.zipWithIndex) { case (base, i) =>
            partsOfType(source.append(FieldStep.TupleElement(i + 1)), base, seen)
          }.map(_.flatten)
        case adt: ADTType if seen(adt.id) =>
          Left(s"the fuzzer cannot build '${fuzzerNameOf(source)}', a '${adt.id.name}' that can " +
               "hold another one")
        case adt: ADTType if !isDefinedBeside(adt, fd) =>
          Left(s"the fuzzer only builds types defined in the file of the function, and " +
               s"'${fuzzerNameOf(source)}' is a '${adt.id.name}' defined elsewhere")
        case adt: ADTType =>
          def fieldsOf(constructor: TypedADTConstructor, inConstructor: FieldRead) =
            traverse(constructor.fields) { field =>
              partsOfType(inConstructor.append(FieldStep.Field(field.id)), field.getType, seen + adt.id)
            }.map(_.flatten)
          adt.getSort.constructors match {
            case Seq(only) => fieldsOf(only, source)
            case several =>
              traverse(several)(c => fieldsOf(c, source.append(FieldStep.Constructor(c.id))))
                .map(fields => InputPart.CaseChoice(source, several.map(_.id.name)) +: fields.flatten)
          }
        case other => Left(s"the fuzzer cannot build '${fuzzerNameOf(source)}', of type '$other'")
      }

    traverse(fd.params) { p =>
      partsOfType(FieldRead(p.toVariable, FieldPath.empty), p.tpe, Set.empty)
    }.map(_.flatten)
  }

  /** Whether `adt` is defined in the file of `fd`, as the fuzzer needs of a type it builds. The
    * library's, such as `Option`, are not.
    */
  private def isDefinedBeside(adt: ADTType, fd: FunDef): Boolean = {
    val sort = symbols.getSort(adt.id)
    (sort.getPos, fd.getPos) match {
      case (sortPos: inox.utils.DefinedPosition, fdPos: inox.utils.DefinedPosition) =>
        !sort.flags.contains(Library) && sortPos.file.getCanonicalFile == fdPos.file.getCanonicalFile
      case _ => false
    }
  }

  /** What the fuzzer is given for `fd`: the domain of each number, from the ranges its variants
    * give it, and what each variant builds.
    *
    * A number without a range is one the computation never reads, since the analysis needs the
    * range of every number it reads. Its range is then read off the precondition, where it has
    * one. Otherwise, it is in a case the precondition rules out, which the `require` turns away
    * whatever its fields hold, or nothing reads it, so it can hold anything. The fuzzer still
    * needs a range, so it gets `[0, 0]`. One that the precondition or a class invariant mentions
    * without bounding it is refused: `[0, 0]` could fail them.
    */
  private def fuzzSubjectOf(fd: FunDef, name: String, parts: Seq[InputPart],
                            variants: Seq[RoundoffErrorDecomposition]): Either[String, FuzzSubject] = {
    val fuzzVariants = variants.map(fuzzVariantOf(parts, _))
    lazy val preconditionRanges = rangesInPrecondition(fd)
    traverse(parts.collect { case number: InputPart.Number => number }) { number =>
      val path = fuzzerNameOf(number.source)
      val analysed = fuzzVariants.flatMap { case (_, rangeOf) => rangeOf.get(path) }
      val ranges = if (analysed.nonEmpty) analysed else preconditionRanges.get(path).toSeq
      val built = fuzzVariants.exists { case (variant, _) => builds(variant, number.source) }
      if (ranges.isEmpty && built && isMentionedByConditions(fd, number.source))
        Left(s"'$path' has no range: the precondition or a class invariant mentions it without " +
             "bounding it on both sides")
      else {
        val (low, high) = if (ranges.isEmpty) (0.0, 0.0) else (ranges.map(_._1).min, ranges.map(_._2).max)
        if (number.tpe == Int64Type() && (low < -maxExactLong || high > maxExactLong))
          Left(s"the fuzzer takes a 'Long' only within ±2^53, and the precondition lets '$path' " +
               s"range over [$low, $high]")
        else Right(FuzzInput(path, low, high))
      }
    }.map(inputs => FuzzSubject(name, inputs, fuzzVariants.map(_._1)))
  }

  /** The ranges the precondition of `fd` gives the numbers of its parameters it reads, by the
    * names the fuzzer gives them, read as the analysis reads them off the numbers its
    * computation reads.
    */
  private def rangesInPrecondition(fd: FunDef): Map[String, (Double, Double)] =
    exprOps.preconditionOf(fd.fullBody).map(Preprocessor.normalisedCondition)
      .flatMap(precondition => FlattenedParameters.flatten(fd, precondition).toOption)
      .flatMap { case (_, flattening) =>
        InputRanges.inputSpecOf(fd, fd.fullBody, flattening).toOption.map { spec =>
          flattening.parameters.flatMap { p =>
            spec.ranges.get(p.id).map(fuzzerNameOf(fieldReadReplacedBy(flattening, p)) -> _)
          }.toMap
        }
      }
      .getOrElse(Map.empty)

  /** The field read that the parameter `p` of `flattening` replaces, or `p` itself. */
  private def fieldReadReplacedBy(flattening: FlattenedParameters, p: ValDef): FieldRead =
    flattening.parameterOfFieldRead.collectFirst { case (read, v) if v.id == p.id => read }
      .getOrElse(FieldRead(p.toVariable, FieldPath.empty))

  /** Whether the precondition of `fd`, or the invariant of the class a field is in, mentions
    * the part at `source`.
    */
  private def isMentionedByConditions(fd: FunDef, source: FieldRead): Boolean = {
    val field = source.path.steps.lastOption.collect { case FieldStep.Field(id) => id }
    def mentions(condition: Expr): Boolean = exprOps.exists {
      case v: Variable => field.isEmpty && v.id == source.variable.id
      case ADTSelector(_, selected) => field.contains(selected)
      case _ => false
    }(condition)
    val precondition = exprOps.preconditionOf(fd.fullBody).map(Preprocessor.normalisedCondition)
    val invariants = field.toSeq.flatMap { id =>
      symbols.sorts.values.filter(_.constructors.exists(_.fields.exists(_.id == id)))
        .flatMap(_.invariant).map(_.fullBody)
    }
    (precondition.toSeq ++ invariants).exists(mentions)
  }

  /** The largest whole number a `Double` holds exactly, beyond which the fuzzer refuses a
    * `Long`.
    */
  private val maxExactLong = 9007199254740992.0

  /** What one variant builds, and the range of each number it builds that has one. */
  private def fuzzVariantOf(parts: Seq[InputPart], decomposition: RoundoffErrorDecomposition)
    : (FuzzVariant, Map[String, (Double, Double)]) = {
    val variant = decomposition.variant
    val flattening = decomposition.flattening
    val chosen = variant.chosenConstructors.map { case (read, c) => fuzzerNameOf(read) -> c.name }.toMap

    val numbers = flattening.parameters.map { p =>
      // The field read `p` replaces in the variant, then where that is in the parameter.
      val read = fieldReadReplacedBy(flattening, p)
      val source = variant.sourceOfInput.get(read.variable.id)
        .map(inParameter =>
          FieldRead(inParameter.variable, FieldPath(inParameter.path.steps ++ read.path.steps)))
        .getOrElse(read)
      (fuzzerNameOf(source), p.id.name, decomposition.spec.ranges.get(p.id))
    }
    val cases = parts.collect {
      case InputPart.CaseChoice(source, _) if isBuiltWith(chosen, source) =>
        fuzzerNameOf(source) -> chosen.get(fuzzerNameOf(source))
    }
    (FuzzVariant(variant.description, cases, numbers.map { case (path, variable, _) => path -> variable }),
     numbers.collect { case (path, _, Some(range)) => path -> range }.toMap)
  }

  /** Whether `variant` builds the part at `source`: it picks every case on the way to it. */
  private def builds(variant: FuzzVariant, source: FieldRead): Boolean =
    isBuiltWith(variant.cases.collect { case (input, Some(chosen)) => input -> chosen }.toMap, source)

  /** Whether the part at `source` is built when each input in `chosenCases` picks its case. */
  private def isBuiltWith(chosenCases: Map[String, String], source: FieldRead): Boolean =
    source.path.steps.zipWithIndex.forall {
      case (FieldStep.Constructor(c), i) =>
        val caseInput = FieldRead(source.variable, FieldPath(source.path.steps.take(i)))
        chosenCases.get(fuzzerNameOf(caseInput)).contains(c.name)
      case _ => true
    }

  /** The name the fuzzer gives the number of `fd`'s result labelled `field`: empty for a result
    * that is one number.
    */
  private def fuzzerNameOfResultNumber(fd: FunDef, field: Option[String]): String = {
    val numbers = FieldPath.numberPathsOf(fd.returnType)
    val path = field.flatMap(label => numbers.find(_.displayName == label)).orElse(numbers.headOption)
    fuzzerNamesOf(path.map(_.steps).getOrElse(Seq.empty)).mkString(".")
  }

  /** A part of a parameter as the fuzzer names it, such as `s.Circle.r`. */
  private def fuzzerNameOf(read: FieldRead): String =
    (read.variable.id.name +: fuzzerNamesOf(read.path.steps)).mkString(".")

  /** The names of `steps` in the plain Scala the fuzzer runs, where the library's `Option` is
    * Scala's, whose `Some` calls its field `value` rather than `v`.
    */
  private def fuzzerNamesOf(steps: Seq[FieldStep]): Seq[String] =
    steps.zipWithIndex.map {
      case (FieldStep.Field(_), i) if steps.lift(i - 1).exists(isLibrarySome) => "value"
      case (step, _) => step.name
    }

  private def isLibrarySome(step: FieldStep): Boolean = step match {
    case FieldStep.Constructor(id) =>
      id.name == "Some" && symbols.getSort(symbols.getConstructor(id).sort).flags.contains(Library)
    case _ => false
  }

  private def sourceOf(fd: FunDef): Either[String, String] =
    fd.getPos match {
      case pos: inox.utils.DefinedPosition =>
        Try(Files.readString(pos.file.toPath)).toEither.left.map(e =>
          s"its source file cannot be read: ${e.getMessage}")
      case _ => Left("it has no source file")
    }

  /** What the fuzzer found for each subject, from one run over all of them. */
  private lazy val fuzzedFunctions: Either[String, Map[String, FuzzedFunction]] =
    if (!fuzzer.enabled || subjects.isEmpty) Left("the fuzzer was not run")
    else
      scala.util.Try(
        timers.fuzzing.run(fuzzer.run(writeProgramAndConfiguration(
          settings.witnessFile.filter(sourcesReplacedBy(_).isEmpty).getOrElse(scratchWitnessFile))))
      ) match {
        case scala.util.Success(found) => found
        case scala.util.Failure(e) => Left(s"the fuzzer could not be run: ${e.getMessage}")
      }

  /** Writes the program and the configuration, and returns the configuration. */
  private def writeProgramAndConfiguration(base: File): File = {
    val allWitnesses = witnesses()
    val conf = withExtension(base, "conf")

    Files.writeString(withExtension(base, "scala").toPath,
      FuzzProgramEmitter.plainScalaProgram(subjects.map(s =>
        FuzzProgramEmitter.madePublicAt(
          FuzzProgramEmitter.withoutFuzzAt(s.source, linesOfFuzzFunctionsLeftOutBeside(s.fd)),
          subjects.filter(other => fileOf(other.fd) == fileOf(s.fd)).map(_.fd.getPos.line).toSet))))
    // The rounding domain and the divergence boxes each get half, so that fuzzing a function
    // takes about one `--timeout`.
    Files.writeString(conf.toPath, FuzzConfEmitter.emit(subjects.map(s =>
      s.fuzzed -> allWitnesses.filter(w => FuzzConfEmitter.isFoundFor(w, s.fd.id.name))),
      seconds = settings.timeout.get / 2))
    conf
  }

  /** The lines of the `@fuzz` functions in the file of `fd` that are not handed to the fuzzer. */
  private def linesOfFuzzFunctionsLeftOutBeside(fd: FunDef): Set[Int] =
    functions.filter(f => f.flags.contains(Fuzz) && !subjects.exists(_.fd == f) && fileOf(f) == fileOf(fd))
      .map(_.getPos.line).toSet

  private def fileOf(fd: FunDef): Option[File] = fd.getPos match {
    case pos: inox.utils.DefinedPosition => Some(pos.file.getCanonicalFile)
    case _ => None
  }

  /** Where the fuzzer's input goes when no witness file was asked for. */
  private lazy val scratchWitnessFile: File = {
    val directory = Files.createTempDirectory("stainless-roundoff").toFile
    directory.deleteOnExit()
    new File(directory, "roundoff.json")
  }

  /** `file` with its extension, if any, replaced by `extension`. */
  private def withExtension(file: File, extension: String): File = {
    val name = file.getName
    val base = name.lastIndexOf('.') match { case -1 => name; case dot => name.take(dot) }
    new File(file.getParentFile, s"$base.$extension")
  }
}