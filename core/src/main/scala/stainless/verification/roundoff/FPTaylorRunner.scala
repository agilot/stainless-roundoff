/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification
package roundoff

import java.io.File
import java.nio.file.Files
import java.util.concurrent.TimeUnit
import scala.jdk.CollectionConverters._
import scala.util.Try

/** Drives FPTaylor as an external process, sending one task per query and reading its summary.
  *
  * Every query goes into a single file: FPTaylor reads a sequence of brace-delimited tasks that
  * share nothing, so one run answers the whole batch and a leaf still gets the ranges of the
  * path that reaches it. A task whose expression FPTaylor cannot evaluate reports an error and
  * leaves the rest of the run alone, so a refusal costs one query rather than all of them.
  */
class FPTaylorRunner(ctx: inox.Context) extends RoundingAnalyzer {
  import ctx.reporter

  val name = "fptaylor"

  val emitter = FPTaylorEmitter

  private val configured = ctx.options.findOptionOrDefault(optFPTaylor)
  private val timeout = ctx.options.findOptionOrDefault(optFPTaylorTimeout)
  private val optTimeout = ctx.options.findOptionOrDefault(optFPTaylorOptTimeout)
  private val optimizer = ctx.options.findOptionOrDefault(optFPTaylorOptimizer)

  /** The executable, either as given or found on `PATH`. */
  private lazy val executable: Option[File] = findExecutable(configured)

  /** FPTaylor's own directory, where `default.cfg` and the optimizer's sources live.
    *
    * It is both the working directory and `FPTAYLOR_BASE`, because the branch-and-bound
    * optimizer compiles each objective against sources it finds under its own installation.
    * What the run writes goes elsewhere, to the scratch directory `invoke` makes for it.
    */
  private def installDir: Option[File] = executable.map(_.getParentFile)

  def analyze(queries: Seq[RoundingQuery]): Map[String, Either[String, RoundingResult]] =
    executable match {
      case None =>
        val why = s"FPTaylor executable '$configured' not found; " +
          "set --fptaylor=<path> or put it on your PATH"
        queries.map(q => q.name -> Left(why)).toMap

      case Some(_) =>
        if (queries.isEmpty) Map.empty
        else invoke(queries) match {
          case Left(why) => queries.map(q => q.name -> Left(why)).toMap
          case Right(rows) => queries.map { q =>
            q.name -> rows.getOrElse(q.name, Left("FPTaylor reported nothing for this function"))
          }.toMap
        }
    }

  /** One FPTaylor run: a bound per task, or why the run as a whole produced nothing. */
  private def invoke(queries: Seq[RoundingQuery])
    : Either[String, Map[String, Either[String, RoundingResult]]] = {

    val exe = executable.get
    val dir = installDir.get

    val source = File.createTempFile("stainless-", ".fptaylor")
    val transcript = File.createTempFile("stainless-", ".fptaylor-out")
    // FPTaylor compiles each objective under its temporary directory and writes a log beside
    // it, both named after the input file, so two runs sharing one installation would write
    // over each other. A run of our own gets a scratch directory of its own.
    val scratch = Files.createTempDirectory("stainless-fptaylor-").toFile

    try {
      Files.write(source.toPath, queries.map(_.source).mkString("\n").getBytes("UTF-8"))

      val cmd = List(
        exe.getAbsolutePath,
        "--abs-error", "true",
        "--rel-error", "false",
        "--find-bounds", "false",
        "--print-hex-floats", "false",
        "--print-precision", "17",
        "--opt", optimizer,
        "--opt-timeout", optTimeout.toString,
        "--tmp-base-dir", new File(scratch, "tmp").getAbsolutePath,
        "--log-base-dir", new File(scratch, "log").getAbsolutePath,
        "--verbosity", "1",
        source.getAbsolutePath
      )

      reporter.debug(s"Invoking ${cmd.mkString(" ")}")(using DebugSectionVerification)

      val pb = new ProcessBuilder(cmd.asJava)
      pb.directory(dir)
      pb.environment().put("FPTAYLOR_BASE", dir.getAbsolutePath)
      pb.redirectErrorStream(true)
      // Written to a file rather than read from a pipe, because reading the pipe to its end
      // would block for as long as the run takes and leave the timeout below nothing to do.
      pb.redirectOutput(transcript)

      val proc = pb.start()
      proc.getOutputStream.close()

      if (!proc.waitFor((timeout * 1000).toLong, TimeUnit.MILLISECONDS)) {
        proc.destroyForcibly()
        Left(s"FPTaylor did not finish within $timeout seconds; raise --fptaylor-timeout")
      } else {
        val output = new String(Files.readAllBytes(transcript.toPath), "UTF-8")
        val rows = parseSummary(output)
        // A run that parsed nothing said nothing about any one task, so the whole batch is
        // told why rather than each query being told it was left out.
        if (rows.isEmpty) Left("FPTaylor reported no results" +
          firstError(output).map(": " + _).getOrElse(""))
        else Right(rows)
      }
    } catch {
      case e: java.io.IOException => Left(s"could not run FPTaylor: ${e.getMessage}")
      case e: InterruptedException =>
        Thread.currentThread().interrupt()
        Left("interrupted while waiting for FPTaylor")
    } finally {
      source.delete()
      transcript.delete()
      remove(scratch)
    }
  }

  /** Deletes a scratch directory and whatever the run left in it. */
  private def remove(file: File): Unit = {
    Option(file.listFiles).foreach(_.foreach(remove))
    file.delete()
  }

  /** The most informative line of a failed run. */
  private def firstError(output: String): Option[String] =
    output.linesIterator
      .find(_.startsWith("**ERROR**"))
      .map(_.stripPrefix("**ERROR**:").trim)
      .filter(_.nonEmpty)

  /** Reads the summary, which gives `Problem: name` and then the bounds computed for it.
    *
    * A task FPTaylor could not finish still gets its `Problem` line but no error bound, which
    * is how a refused function is told apart from one that was never asked about.
    */
  private def parseSummary(output: String): Map[String, Either[String, RoundingResult]] = {
    val problem = "Problem: (.+)".r
    val absolute = raw"Absolute error \([^)]*\): *([0-9eE.+-]+).*".r

    val (rows, _) = output.linesIterator.map(_.trim).foldLeft(
      (Map.empty[String, Either[String, RoundingResult]], Option.empty[String])) {
      case ((found, _), problem(task)) =>
        (found + (task -> Left("FPTaylor computed no bound for this function")), Some(task))

      case ((found, Some(task)), absolute(value)) =>
        val bound = Try(BigDecimal(value)).toOption
          .map(RoundingResult(_))
          .toRight("FPTaylor printed an absolute error this reader could not parse")
        // Several bounds may be printed for one task; the tightest of them is still sound.
        val kept = (found.get(task).flatMap(_.toOption), bound.toOption) match {
          case (Some(had), Some(now)) => Right(RoundingResult(had.absError min now.absError))
          case _ => bound
        }
        (found + (task -> kept), Some(task))

      case (state, _) => state
    }

    rows
  }
}
