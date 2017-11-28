scalaVersion := "2.11.8"

lazy val ourRun = taskKey[Unit]("A custom run task for our-plugin.")

fork in ourRun := true

ourRun := {
  val r: ScalaRun = (runner in Compile).value
  val cp: Classpath = (fullClasspath in Compile).value
  println(s"SBT's ClassPath: ${cp}")
  val opts = Seq(
    "--plugin=viper.silver.plugin.OuroborosPlugin",
    "--z3Exe=/usr/local/Viper/z3/bin/z3",
    "--boogieExe=/usr/local/Viper/boogie/Binaries/Boogie",
    "src/test/resources/our_types.vpr")
  val res = r.run("viper.carbon.Carbon", cp.map(_.data), opts, streams.value.log)
  val ExitCode = "Nonzero exit code: (-?\\d+)".r
  val code = res match {
    case Some(ExitCode(c)) => c.toInt
    case _ => 0
  }
  println(s"ourRun returned with $code")
  if (code != 0) sys.exit(code)
}