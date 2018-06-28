import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Path, Paths}

import ch.qos.logback.classic.Logger
import viper.carbon.{CarbonFrontend, CarbonVerifier}
import viper.silver.frontend.{Frontend, Phase, SilFrontend}
import viper.silver.logger.SilentLogger
import viper.silver.plugin.{OuroborosPlugin, SilverPluginManager}
import viper.silver.reporter.{NoopReporter, Reporter}
import viper.silver.verifier.Verifier

class CarbonWithOuroborosFrontend(override val reporter: Reporter,
                                  override val logger: Logger) extends CarbonFrontend(reporter, logger){
  var currentFileName = ""

  override def verify(): Unit = {
    super.verify()
    Files.write(Paths.get("src/test/resources/output/" + currentFileName), _plugins.plugins(0).asInstanceOf[OuroborosPlugin].translatedCode.toString().getBytes(StandardCharsets.UTF_8))
  }

  override def reset(input: Path): Unit = {
    super.reset(input)
    _plugins = new SilverPluginManager(SilverPluginManager.resolveAll("viper.silver.plugin.OuroborosPlugin")(reporter, logger, _config))
  }
}

