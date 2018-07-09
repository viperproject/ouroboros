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

import ch.qos.logback.classic.Logger
import viper.silver.reporter.Reporter
import viper.silver.FastMessaging
import viper.silver.ast._
import viper.silver.ast.utility.Rewriter.{Strategy, StrategyBuilder, Traverse}
import viper.silver.frontend.SilFrontendConfig
import viper.silver.parser._
import viper.silver.verifier._

import scala.collection.mutable
import scala.io.{BufferedSource, Codec}

class OuroborosPlugin(val reporter: Reporter, val logger: Logger, val cmdArgs: SilFrontendConfig)
  extends SilverPlugin with IOAwarePlugin {

  val our_frontend = new OuroborosFrontend

  val graph_handler = new OuroborosGraphDefinition(this)
  val graphAST_handler = new OuroborosGraphHandler()
  val graph_names_handler = new OuroborosNamesHandler()
  var translatedCode = ""

  def reset(): Unit = {
    OuroborosNames reset()
  }

  override def beforeResolve(input: PProgram): PProgram = {
    reset()

    logger.debug(">>> beforeResolve ")

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
    var invalidIdentifier: Option[Set[PIdnDef]] = None
    invalidIdentifier = graph_names_handler.collectNames(input)
    //logger.debug("NAMES: " + names)

    //If one identifier is "Graph" or "Node", stop
    invalidIdentifier match {
      case None =>
      case Some(nodes) =>
        getErrors(nodes)
        return input
    }

    //Get Ref Fields
    val ref_fields: Seq[String] = input.fields.collect {
      case PField(f, t) if t == TypeHelper.Ref => f.name
      case x:PField => x.typ match {
        case d: PDomainType if d.domain.name == "Node" => x.idndef.name
      }
    }
    //logger.debug("REF_FIELDS: " + ref_fields)

    var preamble: PProgram =
      addPreamble(
        addPreamble(
          addPreamble(
            PProgram(Seq(), Seq(), Seq(), Seq(), Seq(), Seq(), Seq(), Seq()),
            "/viper/silver/plugin/TrCloDomain.sil"),
          "/viper/silver/plugin/TrCloTypes.sil"),
        "/viper/silver/plugin/TrCloOperations.sil")

    val macroFile : PProgram = preLoadSilFile("/viper/silver/plugin/TrCloMacros.sil") match {
      case None => PProgram(Seq(), Seq(), Seq(), Seq(), Seq(), Seq(), Seq(), Seq())
      case Some(pProgram) => pProgram
    }

    /*  val synthesized = OuroborosSynthesize.synthesize(macros, ref_fields)
      var synthesizedMacros : PProgram= synthesized._1
    */  //TODO synthesize methods and get mapping


    //synthesize parametric entities
    preamble = OuroborosSynthesize.synthesize(preamble, ref_fields)
    //logger.debug("MethodKeyWords: " + methodKeyWords)

    val macroSynthesizedFile = OuroborosSynthesize.synthesize(macroFile, ref_fields)


    //Fresh Name Generation
    preamble = graph_names_handler.getNewNames(preamble, OuroborosNames.used_names, ref_fields)

    val macroDefinitivePAST: PProgram = graph_names_handler.getNewNames(macroSynthesizedFile, OuroborosNames.used_names, ref_fields)

    preamble = PProgram(
      preamble.imports ++ macroDefinitivePAST.imports,
      preamble.macros ++ macroDefinitivePAST.macros,
      preamble.domains ++ macroDefinitivePAST.domains,
      preamble.fields ++ macroDefinitivePAST.fields,
      preamble.functions ++ macroDefinitivePAST.functions,
      preamble.predicates ++ macroDefinitivePAST.predicates,
      preamble.methods ++ macroDefinitivePAST.methods,
      preamble.errors ++ macroDefinitivePAST.errors
    )


    val macros : Seq[PGlobalDeclaration] = macroSynthesizedFile.methods ++ macroSynthesizedFile.functions

    macros.map {
      case function: PFunction =>
        OuroborosNames.macroNames put (function.idndef.name, None) //put(function.idndef.name, function.formalArgs.map(arg => arg.idndef.name))
        function
      case method: PMethod =>
        OuroborosNames.macroNames put (method.idndef.name, None) //put(method.idndef.name, method.formalArgs.map(arg => arg.idndef.name))
        method

      case mac => mac
    }
//    synthesizedMacros = graph_names_handler.getNewNames(synthesizedMacros, names ++ keywords.values, ref_fields)


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
        case m: PMethodCall => graph_handler.handlePMethodCall(pprog, m)
        case m: PField => graph_handler.handlePField(pprog, m) //TODO Fields, Domains
        case f: PFormalArgDecl => graph_handler.handlePFormalArgDecl(pprog, f) //TODO maybe register graphs?
        //case l: PLocalVarDecl => graph_handler.handlePLocalVarDecl(pprog, l) //
      }
    )

    val newProg = ourRewriter.execute[PProgram](pprog)

    // Construct the parent relation for the overall PAST:
    newProg.initProperties()

    //logger.debug(newProg)

    newProg
  }

  override def beforeVerify(input: Program): Program = {

    logger.debug(">>> beforeVerify")

    val stmtHandler = new OuroborosStmtHandler
    val graph_defs = graph_handler.graph_definitions

    val ourRewriter = StrategyBuilder.Context[Node, String](
      {
        case (m: Method, ctx) if graph_defs.contains(m.name) =>
          stmtHandler.handleMethod(graphAST_handler.handleMethod(input, m, graph_defs.get(m.name), ctx), graph_defs.get(m.name), input)
//        case (fa: FieldAssign, ctx) =>
//          graph_handler.handleAssignments(input, fa, ctx)
        case (fc : FuncApp, ctx) if OuroborosNames.macroNames.contains(fc.funcname) => OuroborosMemberInliner.inlineFunction(fc, input, fc.pos, fc.info, fc.errT)

        case (mc: MethodCall, ctx) if OuroborosNames.macroNames.contains(mc.methodName) => OuroborosMemberInliner.inlineMethod(mc, input, mc.pos, mc.info, mc.errT)

        case (inhale: Inhale, ctx) => inhale.exp match {
          case fc: FuncApp if OuroborosNames.macroNames.contains(fc.funcname) => OuroborosMemberInliner.inlineInhaleFunction(inhale, fc, input, inhale.pos, inhale.info, inhale.errT)
          case _ => inhale
        }
      },
      "", // default context
      {
        case _ => ""
      }
    )

    var inputPrime = ourRewriter.execute[Program](input)

    inputPrime = Program(inputPrime.domains, inputPrime.fields,
      inputPrime.functions.filter(function => !OuroborosNames.macroNames.contains(function.name)),
      inputPrime.predicates,
      inputPrime.methods.filter(method => !OuroborosNames.macroNames.contains(method.name))
    )(inputPrime.pos, inputPrime.info, inputPrime.errT)

/*    inputPrime = Program(inputPrime.domains, inputPrime.fields, inputPrime.functions, inputPrime.predicates,
          if(containsAssignment) inputPrime.methods else inputPrime.methods.filter(method => !methodKeyWords.contains(method.name)) //TODO user cannot use identifiers containing "link_"
        )(inputPrime.pos, inputPrime.info, inputPrime.errT)*/

    translatedCode = inputPrime.toString()
    logger.debug(s"Complete Viper program:\n${inputPrime.toString()}")
    inputPrime
  }

  override def mapVerificationResult(input: VerificationResult): VerificationResult = input match {
    case Success => Success
    case Failure(errors) => Failure(errors.map {
      case x: AbstractVerificationError => x.transformedError()
      case x => x
    })
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
