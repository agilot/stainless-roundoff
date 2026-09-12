/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification
package roundoff

import java.io.File
import scala.jdk.CollectionConverters._
import scala.util.Try

/** Drives a fuzzer as an external process to compute a lower bound for the worst-case
 * roundoff error.
  */
class FuzzRunner(ctx: inox.Context) {
  import ctx.reporter

  val name = "gavdos"

  private val configured = ctx.options.findOptionOrDefault(optFuzz)

  val enabled: Boolean = configured.nonEmpty

  private lazy val executable: Option[File] = findExecutable(configured)

  /** Runs the fuzzer of each function using a given configuration path and outputs the result
   * of the fuzzer for each function or an error.
   */
  def run(conf: File): Either[String, Map[String, BigDecimal]] =
    executable match {
      case None =>
        Left(s"fuzzer executable '$configured' not found; " +
          "set --fuzz=<path> or put it on your PATH")

      case Some(exe) =>
        val cmd = List(exe.getAbsolutePath, conf.getAbsolutePath)
        reporter.debug(s"Invoking ${cmd.mkString(" ")}")(using DebugSectionVerification)

        try {
          val pb = new ProcessBuilder(cmd.asJava)
          pb.directory(conf.getAbsoluteFile.getParentFile)
          pb.redirectErrorStream(true)

          val proc = pb.start()
          proc.getOutputStream.close()
          val output = new String(proc.getInputStream.readAllBytes(), "UTF-8")
          val exit = proc.waitFor()

          val observed = parse(output)
          // A run that found nothing has failed at something.
          if (observed.nonEmpty) Right(observed)
          else Left(s"the fuzzer exited with code $exit and reported no error" +
            lastLine(output).fold("")(l => s": $l"))
        } catch {
          case e: java.io.IOException => Left(s"could not run the fuzzer: ${e.getMessage}")
          case e: InterruptedException =>
            Thread.currentThread().interrupt()
            Left("interrupted while waiting for the fuzzer")
        }
    }

  /** The heading the fuzzer prints above each function's configurations. */
  private val heading = """(\S+): (?:divergences|rounding error)\s*$""".r.unanchored

  /** What one configuration's widest disagreement was reported as. */
  private val observation = """max abs error\s+(\S+)""".r.unanchored

  /** The widest error reported under each function, across all of its configurations.
    */
  def parse(output: String): Map[String, BigDecimal] =
    output.linesIterator.foldLeft((Option.empty[String], Map.empty[String, BigDecimal])) {
      case ((_, found), heading(function)) => (Some(function), found)

      case ((Some(function), found), observation(value)) =>
        val widest = Try(BigDecimal(value)).toOption.map { error =>
          function -> found.get(function).fold(error)(_ max error)
        }
        (Some(function), found ++ widest)

      case (state, _) => state
    }._2

  private def lastLine(output: String): Option[String] =
    output.linesIterator.map(_.trim).filter(_.nonEmpty).toSeq.lastOption
}
