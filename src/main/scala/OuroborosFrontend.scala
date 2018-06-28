/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.plugin

import java.nio.file.Path

import viper.silver.ast.Program
import viper.silver.frontend.{SilFrontend, SilFrontendConfig, TranslatorState}
import viper.silver.parser.PProgram
import viper.silver.verifier.{Failure, Success, Verifier}

/** Minimal SilFrontend to load a file and translate it into an AST
  * Will probably break if it is used for something else than loadFile.
  */


class OuroborosFrontend extends SilFrontend {

  override def createVerifier(fullCmd: String): Verifier = ???

  override def configureVerifier(args: Seq[String]): SilFrontendConfig = ???

  def loadFile(path: Path): Option[Program] = {
    _plugins = SilverPluginManager()
    _state = TranslatorState.Initialized
    reset(path)
    translate()

    if (_errors.nonEmpty) {
      logger.info(s"Could not load ${path.getFileName}:")
      _errors.foreach(e => logger.info(s"  ${e.readableMessage}"))
    }
    _program
  }

  def preLoadFile(path: Path): Option[PProgram] = {
    _plugins = SilverPluginManager()
    _state = TranslatorState.Initialized
    reset(path)
    parse()

    if (_errors.nonEmpty) {
      logger.info(s"Could not pre-load ${path.getFileName}:")
      _errors.foreach(e => logger.info(s"  ${e.readableMessage}"))
    }
    _parseResult
  }
}
