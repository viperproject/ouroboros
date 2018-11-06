
name := "ouroboros"

lazy val baseSettings = Seq(
    organization := "viper",
    version := "1.0-SNAPSHOT"
)

def isBuildServer = sys.env.contains("BUILD_TAG")

lazy val jenkins = taskKey[Unit]("Informs the builder whether Jenkins-specific build setting have been activated.")

def printWhetherIsJenkins = {
  if (isBuildServer)
    println("[Arshavir] Using Jenkins-specific build settings.")
  else
    println("[Arshavir] Using local build settings. This might not work in Jenkins.")
}

//def internalDep = if (isBuildServer) Nil else Seq(
//    dependencies.silSrc % "compile->compile;test->test"
//)

def externalDep =
    if (isBuildServer) {
        Seq("viper" %% "silver" %  "0.1-SNAPSHOT" from "file:///lib/silver.jar",
            "viper" %% "carbon" % "0.1-SNAPSHOT" from "file:///lib/carbon.jar")
    } else {
        Nil
    }

lazy val carbon = RootProject(new java.io.File("../carbon"))
lazy val silver = RootProject(new java.io.File("../silver"))

lazy val ouroboros = {
    var p = (project in file("."))

    if (!isBuildServer) {
      p = p.dependsOn(silver)
      p = p.dependsOn(carbon)
    }

    p = p.settings(
      jenkins := { printWhetherIsJenkins },
      (Compile / compile) := ((Compile / compile) dependsOn jenkins).value,
      baseSettings,
      name := "Ouroboros",
      libraryDependencies ++= externalDep,
      assembly / assemblyJarName := "carbon-ouroboros.jar",
      assembly / test := {},
      testOptions in Test += Tests.Setup(classLoader =>
          classLoader
              .loadClass("org.slf4j.LoggerFactory")
              .getMethod("getLogger", classLoader.loadClass("java.lang.String"))
              .invoke(null, "ROOT"))
    )
    p
}

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

    //val res =
    r.run("viper.carbon.Carbon", cp.map(_.data), opts, streams.value.log)

    // The API has changed since SBT 1.0.0
    // SBT now uses sbt.util.Logger to output exit codes.
    // See https://github.com/sbt/sbt/blob/8af7a5acaef783b69d0f4c88d348ac3d90c753ad/run/src/main/scala/sbt/Run.scala
    // val ExitCode = "Nonzero exit code: (-?\\d+)".r
    // val code = res match {
    //  case ExitCode(c) => c.toInt
    //  case _ => 0
    //}
    //println(s"ourRun returned with $code")
    //if (code != 0) sys.exit(code)
}
