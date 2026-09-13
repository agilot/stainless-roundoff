/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification
package roundoff

import java.io.File
import java.nio.file.Files
import scala.jdk.CollectionConverters._
import scala.util.Try

/** Drives Daisy as an external process, sending FPCore and reading back a CSV. */
class DaisyRunner(ctx: inox.Context) extends RoundingAnalyzer {
  import ctx.reporter

  val name = "daisy"

  private val configured = ctx.options.findOptionOrDefault(optDaisy)

  /** The executable, either as given or found on `PATH`. */
  private lazy val executable: Option[File] = findExecutable(configured)

  /** Daisy's working directory: where its `lib/` and `output/` live. */
  private def installDir: Option[File] = executable.map(_.getParentFile)

  def analyze(queries: Seq[RoundingQuery]): Map[String, Either[String, RoundingResult]] =
    executable match {
      case None =>
        val why = s"Daisy executable '$configured' not found; " +
          "set --daisy=<path> or put it on your PATH"
        queries.map(q => q.name -> Left(why)).toMap

      case Some(_) =>
        // --precision is global to an invocation, so each precision is its own batch.
        queries.groupBy(_.precision).flatMap { case (precision, batch) =>
          invoke(precision, batch) match {
            case Left(why) => batch.map(q => q.name -> Left(why)).toMap
            case Right(rows) => batch.map { q =>
              q.name -> rows.getOrElse(q.name, Left("Daisy reported nothing for this function"))
            }.toMap
          }
        }
    }

  /** One Daisy run: a row per function, or why the run as a whole produced nothing. */
  private def invoke(precision: FPPrecision, batch: Seq[RoundingQuery])
    : Either[String, Map[String, Either[String, RoundingResult]]] = {

    val exe = executable.get
    val dir = installDir.get

    val stamp = java.util.UUID.randomUUID().toString.take(12)
    val source = File.createTempFile(s"stainless-$stamp-", ".fpcore")
    val csvName = s"stainless-$stamp.csv"
    val outputDir = new File(dir, "output")
    val csv = new File(outputDir, csvName)

    try {
      // Daisy writes into output/ without creating it, and appends if the file is
      // already there, so each run gets a fresh name in a directory we make ourselves.
      outputDir.mkdirs()
      Files.write(source.toPath, batch.map(_.fpcoreSource).mkString("\n").getBytes("UTF-8"))

      val cmd = List(
        exe.getAbsolutePath,
        "--treesitter",
        s"--precision=${precision.daisyName}",
        s"--results-csv=$csvName",
        "--no-stdout-print",
        source.getAbsolutePath
      )

      reporter.debug(s"Invoking ${cmd.mkString(" ")}")(using DebugSectionVerification)

      val pb = new ProcessBuilder(cmd.asJava)
      pb.directory(dir)
      pb.redirectErrorStream(true)

      val proc = pb.start()
      proc.getOutputStream.close()
      val output = new String(proc.getInputStream.readAllBytes(), "UTF-8")
      val exit = proc.waitFor()

      // Daisy exits non-zero when any function failed, yet still reports the others, so
      // the results file and not the exit code says whether the run produced anything.
      if (csv.isFile) Right(parseCsv(Files.readAllLines(csv.toPath).asScala.toSeq))
      else Left(s"Daisy exited with code $exit" + firstError(output).map(": " + _).getOrElse(""))
    } catch {
      case e: java.io.IOException => Left(s"could not run Daisy: ${e.getMessage}")
      case e: InterruptedException =>
        Thread.currentThread().interrupt()
        Left("interrupted while waiting for Daisy")
    } finally {
      source.delete()
      csv.delete()
    }
  }

  /** The most informative line of a failed run. */
  private def firstError(output: String): Option[String] =
    output.linesIterator
      .map(stripAnsi)
      .find(l => l.contains("Fatal") || l.contains("Exception"))
      .map(_.trim)
      .filter(_.nonEmpty)

  private def stripAnsi(s: String): String = s.replaceAll("\\[[;\\d]*m", "")

  /** Reads rows of `name; abs error; rel error; range; time; failure`.
    *
    * The failure column comes last in every mode Daisy writes, and is absent altogether
    * in a version that gives up on the whole run rather than reporting one function.
    */
  private def parseCsv(lines: Seq[String]): Map[String, Either[String, RoundingResult]] =
    lines.flatMap { line =>
      val fields = line.split(";", -1).map(_.trim)
      val failure = if (fields.length >= 6) fields.last else ""

      if (fields.length < 2 || fields.head == "Function name") None
      else if (failure.nonEmpty) Some(fields.head -> Left(failure))
      else Some(fields.head -> Try(BigDecimal(fields(1))).toOption
        .map(RoundingResult(_))
        .toRight("Daisy reported no absolute error for this function"))
    }.toMap
}