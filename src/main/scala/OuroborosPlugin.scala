/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.plugin

import java.io.{File, FileOutputStream, InputStream}
import java.net.URL
import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Path, Paths}

import viper.silver.ast._
import viper.silver.ast.utility.Rewriter.{Strategy, StrategyBuilder, Traverse}
import viper.silver.parser._
import viper.silver.verifier._

import scala.io.{BufferedSource, Codec}

class OuroborosPlugin extends SilverPlugin {

  val our_frontend = new OuroborosFrontend

  val graph_handler = new OuroborosGraphDefinition(this)
  val graphAST_handler = new OuroborosGraphHandler()

  var translatedCode = ""

  override def beforeResolve(input: PProgram): PProgram = {

    println(">>> beforeResolve " + Thread.currentThread().getId)


    //val pprog = addPreamble(input, "/viper/silver/plugin/TrCloDomain.sil")

    val pprog: PProgram =
      addPreamble(
        addPreamble(
          addPreamble(input,
            "/viper/silver/plugin/TrCloDomain.sil"),
            "/viper/silver/plugin/TrCloTypes.sil"),
            "/viper/silver/plugin/TrCloOperations.sil")

    //val methodRewriter = new Strategy[PNode, String](
    //  {
    //    case (m: PMethod, _) if m.idndef.name == "link_$field$" => m
    //  }
    //)
    //val ppprog = methodRewriter

    val ourRewriter = StrategyBuilder.Slim[PNode](
      {
        case p: PProgram => graph_handler.synthesizeParametricEntities(pprog)
        case m: PMethod => graph_handler.handlePMethod(pprog, m)
        case m: PCall => graph_handler.handlePCall(pprog, m)
        case m: PField => graph_handler.handlePField(pprog, m) //TODO Fields, Domains
      }
    )

    val newProg = ourRewriter.execute[PProgram](pprog)

    // Construct the parent relation for the overall PAST:
    newProg.initProperties()

    println(newProg)

    newProg
  }

  override def beforeVerify(input: Program): Program = {

    println(">>> beforeVerify")

    val graph_defs = graph_handler.graph_definitions

    val ourRewriter = StrategyBuilder.Context[Node, String](
      {
        case (m: Method, ctx) if graph_defs.contains(m.name) => graphAST_handler.handleMethod(input, m, graph_defs.get(m.name), ctx)
        case (fa: FieldAssign, ctx) => graph_handler.handleAssignments(input, fa, ctx)
      },
      "", // default context
      {
        case _ => ""
      }
    )

    val inputPrime = ourRewriter.execute[Program](input)

    translatedCode = inputPrime.toString()
    //println(inputPrime)
    inputPrime
  }

  private def readResourceIntoTmpFile(resource: String): Path = {

    implicit val c: Codec = scala.io.Codec.UTF8

    val istream = getClass.getResourceAsStream(resource)
    val byte_array = Stream.continually(istream.read).takeWhile(_ != -1).map(_.toByte).toArray

    val tmp_file = java.io.File.createTempFile(resource, "tmp")
    val ostream = new java.io.FileOutputStream(tmp_file)

    ostream.write(byte_array)

    tmp_file.toPath
  }

  def preLoadSilFile(file: String): Option[PProgram] = {

    val loaded_sil_file = readResourceIntoTmpFile(file)

    our_frontend.preLoadFile(loaded_sil_file)
  }

  def loadSilFile(file: String): Program = {

    val loaded_sil_file = readResourceIntoTmpFile(file)

    our_frontend.loadFile(loaded_sil_file) match {
      case Some(program) => program
      case None => Program(Seq(), Seq(), Seq(), Seq(), Seq())() // TODO: Probably not the best way to do it
    }
  }

  // Adds the graph operations as method declarations.
  def addPreamble(input: PProgram, global_resource: String): PProgram = preLoadSilFile(global_resource) match {
    case Some(pprog) =>
      PProgram(
        input.imports ++ pprog.imports,
        input.macros ++ pprog.macros,
        input.domains ++ pprog.domains,
        input.fields ++ pprog.fields,
        input.functions ++ pprog.functions,
        input.predicates ++ pprog.predicates,
        input.methods ++ pprog.methods,
        input.errors ++ pprog.errors
      )
    case None => input
  }

  /*
  // Adds a generic preamble (could be an arbitrary Viper program).
  def addTrCloPreamble(input: PProgram): Program = {
    val ourPreamble = preLoadSilFile("/viper/silver/plugin/TrCloDomain.sil")

    PProgram(
      input.domains ++ ourPreamble.domains,
      input.fields ++ ourPreamble.fields,
      input.functions ++ ourPreamble.functions,
      input.predicates ++ ourPreamble.predicates,
      input.methods ++ ourPreamble.methods
    )(input.pos, input.info, input.errT + NodeTrafo(input))
  }*/
}
