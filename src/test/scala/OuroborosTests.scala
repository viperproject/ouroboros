import java.nio.file.Path

import org.scalatest.{Args, Status}
import viper.carbon.CarbonVerifier
import viper.silver.frontend.Frontend
import viper.silver.logger.{SilentLogger, ViperStdOutLogger}
import viper.silver.plugin.{OuroborosPlugin, SilverPlugin}
import viper.silver.reporter.StdIOReporter
import viper.silver.testing.SilSuite
import viper.silver.verifier.Verifier

class OuroborosTests extends SilSuite {
  val fe = new CarbonWithOuroborosFrontend(new StdIOReporter("OuroborosTest"), ViperStdOutLogger.apply("OuroborosTest", "INFO").get)

  override def testDirectories: Seq[String] = Vector(/*"local", "fails",*/"succeeds"
  )
  override def frontend(verifier: Verifier, files: Seq[Path]): Frontend = {
    require(files.length == 1, "tests should consist of exactly one file")
    fe.init(verifier)
    fe.reset(files.head)
    fe
  }

  protected override def runTest (testName: String, args : Args) : Status = {
    var fileName  : String = testName.split("/").last
    fe.currentFileName = testName.split("/").last.split("\\.")(0) + ".vpr"
    super.runTest(testName, args)
  }

  lazy val verifiers = List(CarbonVerifier())

}
