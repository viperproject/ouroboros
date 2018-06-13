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

import viper.silver.{FastMessaging}
import viper.silver.ast._
import viper.silver.ast.utility.Rewriter.{Strategy, StrategyBuilder, Traverse}
import viper.silver.parser._
import viper.silver.verifier._

import scala.collection.mutable
import scala.io.{BufferedSource, Codec}

class OuroborosPlugin extends SilverPlugin {

  val our_frontend = new OuroborosFrontend

  val graph_handler = new OuroborosGraphDefinition(this)
  val graphAST_handler = new OuroborosGraphHandler()
  val graph_names_handler = new OuroborosNamesHandler()
  var translatedCode = ""
  var methodKeyWords : Set[String] = Set()
  var keywords: mutable.Map[String, String] = mutable.Map.empty[String, String]

  override def beforeResolve(input: PProgram): PProgram = {

    println(">>> beforeResolve " + Thread.currentThread().getId)

    def getErrors(nodes: Set[PIdnDef]) = {
      var newErrors: Set[AbstractError] = Set()
      nodes.map(x => {
        val message = FastMessaging.message(x, "Cannot use identifier " + x.name)
        for (m <- message) {
          newErrors += OuroborosInvalidIdentifierError( m.label,
            m.pos match {
              case fp: FilePosition =>
                SourcePosition(fp.file, m.pos.line, m.pos.column)
              case _ =>
                //SourcePosition(_inputFile.get, m.pos.line, m.pos.column)
                NoPosition //TODO find position
            }
          )
        }
        x
      })

      _errors ++= newErrors

    }


    //val pprog = addPreamble(input, "/viper/silver/plugin/TrCloDomain.sil")

    //Collect identifiers
    var names: Set[String] = Set()
    var invalidIdentifier: Option[Set[PIdnDef]] = None
    invalidIdentifier = graph_names_handler.collectNames(input)
    names = graph_names_handler.used_names
    //println("NAMES: " + names)

    //If one identifier is "Graph" or "Node", stop
    invalidIdentifier match {
      case None =>
      case Some(nodes) => {
        getErrors(nodes)
        return input
      }
    }

    //Get Ref Fields
    val ref_fields: Seq[String] = input.fields.collect {
      case PField(f, t) if t == TypeHelper.Ref => f.name
      case x:PField => x.typ match {
        case d: PDomainType if d.domain.name == "Node" => x.idndef.name
      }
    }
    //println("REF_FIELDS: " + ref_fields)

    var preamble: PProgram =
      addPreamble(
        addPreamble(
          addPreamble(
            PProgram(Seq(), Seq(), Seq(), Seq(), Seq(), Seq(), Seq(), Seq()),
            "/viper/silver/plugin/TrCloDomain.sil"),
          "/viper/silver/plugin/TrCloTypes.sil"),
        "/viper/silver/plugin/TrCloOperations.sil")


    //synthesize parametric entities
    val synthesizeResult = OuroborosSynthesize.synthesize(preamble, ref_fields)
    preamble = synthesizeResult._1
    methodKeyWords = synthesizeResult._2
    println("MethodKeyWords: " + methodKeyWords)


    //Fresh Name Generation
    preamble = graph_names_handler.getNewNames(preamble, names, ref_fields)
    keywords = graph_names_handler.graph_keywords
    graph_handler.graph_keywords = keywords

    val pprog: PProgram =
      PProgram(
        preamble.imports ++ input.imports,
        preamble.macros ++ input.macros,
        preamble.domains ++ input.domains,
        preamble.fields ++ input.fields,
        preamble.functions ++ input.functions,
        preamble.predicates ++ input.predicates,
        preamble.methods ++ input.methods,
        preamble.errors ++ input.errors
      )

    /*addPreamble(
        addPreamble(
          addPreamble(input,
            "/viper/silver/plugin/TrCloDomain.sil"),
            "/viper/silver/plugin/TrCloTypes.sil"),
            "/viper/silver/plugin/TrCloOperations.sil")*/

    //val methodRewriter = new Strategy[PNode, String](
    //  {
    //    case (m: PMethod, _) if m.idndef.name == "link_$field$" => m
    //  }
    //)
    //val ppprog = methodRewriter

    val ourRewriter = StrategyBuilder.Slim[PNode](
      {
        //case p: PProgram => graph_handler.synthesizeParametricEntities(pprog)
        case m: PMethod => graph_handler.handlePMethod(pprog, m)
        case m: PCall => graph_handler.handlePCall(pprog, m)
        case m: PField => graph_handler.handlePField(pprog, m) //TODO Fields, Domains
      }
    )

    val newProg = ourRewriter.execute[PProgram](pprog)

    // Construct the parent relation for the overall PAST:
    newProg.initProperties()

    //println(newProg)

    newProg
  }

  override def beforeVerify(input: Program): Program = {

    println(">>> beforeVerify")

    val graph_defs = graph_handler.graph_definitions
    var containsAssignment = false

    val ourRewriter = StrategyBuilder.Context[Node, String](
      {
        case (m: Method, ctx) if graph_defs.contains(m.name) => graphAST_handler.handleMethod(input, m, graph_defs.get(m.name), ctx)
        case (fa: FieldAssign, ctx) => {
          containsAssignment = true
          graph_handler.handleAssignments(input, fa, ctx)
        }
      },
      "", // default context
      {
        case _ => ""
      }
    )

    var inputPrime = ourRewriter.execute[Program](input)

    inputPrime = Program(inputPrime.domains, inputPrime.fields, inputPrime.functions, inputPrime.predicates,
      if(containsAssignment) inputPrime.methods else inputPrime.methods.filter(method => !method.name.contains("link_")) //TODO user cannot use identifiers containing "link_"
    )(inputPrime.pos, inputPrime.info, inputPrime.errT)

/*    inputPrime = Program(inputPrime.domains, inputPrime.fields, inputPrime.functions, inputPrime.predicates,
          if(containsAssignment) inputPrime.methods else inputPrime.methods.filter(method => !methodKeyWords.contains(method.name)) //TODO user cannot use identifiers containing "link_"
        )(inputPrime.pos, inputPrime.info, inputPrime.errT)*/

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
