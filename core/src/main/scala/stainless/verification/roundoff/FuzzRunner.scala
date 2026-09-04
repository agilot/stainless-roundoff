/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification
package roundoff

import java.io.File
import scala.jdk.CollectionConverters._
import scala.util.Try

/** Drives the fuzzer as an external process, and reads back the error it observed.
  *
  * What comes back is a lower bound: an error the program really made on an input the
  * fuzzer tried, against the upper bound the analysis proves. The two together bracket the
  * worst case rather than only capping it.
  */
class FuzzRunner(ctx: inox.Context) {
  import ctx.reporter

  val name = "fuzz"

  private val configured = ctx.options.findOptionOrDefault(optFuzz)

  /** Whether a lower bound was asked for at all. */
  val enabled: Boolean = configured.nonEmpty

  private lazy val executable: Option[File] = findExecutable(configured)

  /** The widest error the fuzzer saw for each function, or why the run gave nothing.
    *
    * @param conf the configuration to search, beside the program it belongs to
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
          // A run that found nothing has failed at something, and its own last words say
          // more about what than an exit code does.
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
    *
    * The fuzzer writes a heading per function and then a block per configuration, so the
    * heading last seen says which function a figure belongs to. Public because reading
    * another tool's output is the brittle half of driving it, and is worth a test.
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
