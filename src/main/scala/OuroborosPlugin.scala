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
  val graph_state_checker = new OuroborosReachingDefinition()
  var translatedCode = ""
  var zOPGdomainNames : Seq[String] = Seq()

  def reset(): Unit = {
    OuroborosNames reset()
    OuroborosConfig reset()
  }

  override def beforeParse(input: String, isImported: Boolean): String = {
    //input.split("\\n", 1)
    super.beforeParse(input, isImported)
  }

  override def beforeResolve(input: PProgram): PProgram = {
    reset()

    logger.debug(">>> beforeResolve ")
    var inline: Boolean = false
    var wisdoms: Boolean = false
    var update_invariants: Boolean = false
    var type_check: Boolean = false
    input.fields.foreach(field => {
      field.idndef.name match {
        case "__CONFIG_OUROBOROS_INLINE" => inline = true
        case "__CONFIG_OUROBOROS_WISDOMS" => wisdoms = true
        case "__CONFIG_OUROBOROS_UPDATE_INVARIANTS" => update_invariants = true
        case "__CONFIG_OUROBOROS_TYPE_CHECK" => type_check = true
        case _ =>
      }
    })

    OuroborosConfig.set(inline, wisdoms, update_invariants, type_check)

    val inputWithoutConfigFields = PProgram(
      input.imports,
      input.macros,
      input.domains,
      input.fields.filter(field => !OuroborosNames.magic_fields.contains(field.idndef.name)),
      input.functions,
      input.predicates,
      input.methods,
      input.errors
    )

//    input.methods.foreach(method => {
//
//      val message = FastMessaging.message(method, "Test warning")
//      for (m <- message) {
//        val error: AbstractError = ParseWarning(m.label, m.pos match {
//          case fp: FilePosition =>
//            SourcePosition(fp.file, m.pos.line, m.pos.column)
//          case _ =>
//            NoPosition
//        })
//
//        reportError(error)
//      }
//    })

    def getErrors(nodes: Set[PIdnDef]) = {
      nodes.foreach(x => {
        val message = FastMessaging.message(x, "Cannot use identifier " + x.name)
        for (m <- message) {
          val error: AbstractError = OuroborosInvalidIdentifierError( m.label,
            m.pos match {
              case fp: FilePosition =>
                SourcePosition(fp.file, m.pos.line, m.pos.column)
              case _ =>
                //SourcePosition(_inputFile.get, m.pos.line, m.pos.column)
                NoPosition //TODO find position
            }
          )
          reportError(error)
        }
      })

    }


    //val pprog = addPreamble(input, "/viper/silver/plugin/TrCloDomain.sil")

    //Collect identifiers
    var invalidIdentifier: Option[Set[PIdnDef]] = None
    invalidIdentifier = OuroborosNames.collectNames(inputWithoutConfigFields)
    //logger.debug("NAMES: " + names)

    //If one identifier is "Graph" or "Node", stop
    invalidIdentifier match {
      case None =>
      case Some(nodes) =>
        getErrors(nodes)
        return inputWithoutConfigFields
    }

    //Get Ref Fields
    val ref_fields: Seq[String] = inputWithoutConfigFields.fields.collect {
      case PField(f, t) if t == TypeHelper.Ref => Seq(f.name)
      case x:PField => x.typ match {
        case d: PDomainType if d.domain.name == "Node" => Seq(x.idndef.name)
        case _ => Seq()
      }
    }.flatten
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
      case Some(p) => PProgram(p.imports, Seq(), p.domains, p.fields, p.functions, p.predicates, p.methods, p.errors)
    }

    val persistentMacroFile : PProgram = preLoadSilFile("/viper/silver/plugin/TrCloPersistentMacros.sil") match {
      case None => PProgram(Seq(), Seq(), Seq(), Seq(), Seq(), Seq(), Seq(), Seq())
      case Some(p) => PProgram(p.imports, Seq(), p.domains, p.fields, p.functions, p.predicates, p.methods, p.errors)
    }

    val zOPGDomain: PProgram  = preLoadSilFile("/viper/silver/plugin/TrCloZOPGDomain.sil") match {
      case None => PProgram(Seq(), Seq(), Seq(), Seq(), Seq(), Seq(), Seq(), Seq())
      case Some(p) => PProgram(p.imports, Seq(), p.domains, p.fields, p.functions, p.predicates, p.methods, p.errors)
    }

    /*  val synthesized = OuroborosSynthesize.synthesize(macros, ref_fields)
      var synthesizedMacros : PProgram= synthesized._1
    */  //TODO synthesize methods and get mapping


    //synthesize parametric entities
    preamble = OuroborosSynthesize.synthesize(preamble, ref_fields)
    //logger.debug("MethodKeyWords: " + methodKeyWords)

    val macroSynthesizedFile = OuroborosSynthesize.synthesize(macroFile, ref_fields)
    val persistentMacroSynthesizedFile = OuroborosSynthesize.synthesize(persistentMacroFile, ref_fields)
    val zOPGDomainSynthesized = OuroborosSynthesize.synthesize(zOPGDomain, ref_fields)

    //Fresh Name Generation
    preamble = OuroborosNames.getNewNames(preamble, ref_fields)
    val macroDefinitivePAST: PProgram = OuroborosNames.getNewNames(macroSynthesizedFile, ref_fields)
    val persistentMacroDefinitivePAST: PProgram = OuroborosNames.getNewNames(persistentMacroSynthesizedFile, ref_fields)
    val zOPGDomainDefinitive = OuroborosNames.getNewNames(zOPGDomainSynthesized, ref_fields)

    zOPGdomainNames ++= (zOPGDomainDefinitive.domains ++ zOPGDomainDefinitive.methods ++ zOPGDomainDefinitive.functions).map(d => d.idndef.name)

    preamble = PProgram(
      preamble.imports ++ macroDefinitivePAST.imports ++ persistentMacroDefinitivePAST.imports,
      Seq(),//preamble.macros ++ macroDefinitivePAST.macros,
      preamble.domains ++ macroDefinitivePAST.domains ++ persistentMacroDefinitivePAST.domains ++ zOPGDomainDefinitive.domains,
      preamble.fields ++ macroDefinitivePAST.fields ++ persistentMacroDefinitivePAST.fields,
      preamble.functions ++ macroDefinitivePAST.functions ++ persistentMacroDefinitivePAST.functions ++ zOPGDomainDefinitive.functions,
      preamble.predicates ++ macroDefinitivePAST.predicates ++ persistentMacroDefinitivePAST.predicates,
      preamble.methods ++ macroDefinitivePAST.methods ++ persistentMacroDefinitivePAST.methods ++ zOPGDomainDefinitive.methods,
      preamble.errors ++ macroDefinitivePAST.errors ++ persistentMacroDefinitivePAST.errors
    )


    val macros : Seq[PGlobalDeclaration] = macroSynthesizedFile.methods ++ macroSynthesizedFile.functions

    macros.foreach {
      case function: PFunction =>
        OuroborosNames.macroNames put (function.idndef.name, None) //put(function.idndef.name, function.formalArgs.map(arg => arg.idndef.name))
      case method: PMethod =>
        OuroborosNames.macroNames put (method.idndef.name, None) //put(method.idndef.name, method.formalArgs.map(arg => arg.idndef.name))

      case _ =>
    }


    val pprog: PProgram =
      PProgram(
        preamble.imports ++ inputWithoutConfigFields.imports,
        Seq(),//preamble.macros ++ input.macros,
        preamble.domains ++ inputWithoutConfigFields.domains,
        preamble.fields ++ inputWithoutConfigFields.fields,
        preamble.functions ++ inputWithoutConfigFields.functions,
        preamble.predicates ++ inputWithoutConfigFields.predicates,
        preamble.methods ++ inputWithoutConfigFields.methods,
        preamble.errors ++ inputWithoutConfigFields.errors
      )

    val ourRewriter = StrategyBuilder.Slim[PNode](
      {
        //case p: PProgram => graph_handler.synthesizeParametricEntities(pprog)
        case i: PProgram => OuroborosNames.ref_fields = graph_handler.ref_fields(i); i
        case m: PMethod =>
          val methodAndErrors = graph_handler.handlePMethod(pprog, m)
          methodAndErrors._2.foreach(reportError)
          methodAndErrors._1
        case m: PCall => graph_handler.handlePCall(pprog, m, None)
        case m: PMethodCall => graph_handler.handlePMethodCall(pprog, m)
        case m: PField =>
          val res = graph_handler.handlePField(pprog, m)
          res._2.foreach(reportError)
          res._1
        case f: PFormalArgDecl =>
          val declRes = graph_handler.handlePFormalArgDecl(pprog, f, false)
          declRes._2.foreach(reportError)
          declRes._1
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

    val usedMacroCalls: mutable.Buffer[String] = mutable.Buffer.empty[String]
    val ourRewriter = StrategyBuilder.Context[Node, String](
      {
        case (m: Method, ctx) if graph_defs.contains(m.name) =>
          val first = graphAST_handler.handleMethod(input, m, graph_defs.get(m.name), ctx)
          stmtHandler.handleMethod(first, graph_defs.get(m.name), input)
        case (f:FuncApp, ctx) if !OuroborosConfig.type_check =>
          usedMacroCalls += f.funcname
          f
        case (mc: MethodCall, ctx) if !OuroborosConfig.type_check =>
          usedMacroCalls += mc.methodName
          mc
      },
      "", // default context
      {
        case _ => ""
      }
    )


    lazy val ourStateChecker = StrategyBuilder.Slim[Node](
      {
        case m: Method if graph_defs.contains(m.name) =>
          val tuple = graph_state_checker.handleMethod(m, graph_defs, input)
          tuple._2.foreach(err => reportError(err))
          tuple._1
        case f:FuncApp =>
          usedMacroCalls += f.funcname
          f
        case mc: MethodCall =>
          usedMacroCalls += mc.methodName
          mc
      }
    )

    lazy val ourInliner = StrategyBuilder.Context[Node, mutable.Set[Declaration]]({
      case (fc : FuncApp, ctx) if OuroborosNames.macroNames.contains(fc.funcname) || zOPGdomainNames.contains(fc.funcname) =>
        OuroborosMemberInliner.inlineFunctionApp(fc, input, fc.pos, fc.info, fc.errT)

      case (mc: MethodCall, ctx) if OuroborosNames.macroNames.contains(mc.methodName) || zOPGdomainNames.contains(mc.methodName) =>
        OuroborosMemberInliner.inlineMethodCall(mc, input, mc.pos, mc.info, mc.errT)

      case (inhale: Inhale, ctx) => inhale.exp match {
        case fc: FuncApp if OuroborosNames.macroNames.contains(fc.funcname) => OuroborosMemberInliner.inlineFunctionAppInhale(inhale, fc, input, inhale.pos, inhale.info, inhale.errT)
        case _ => inhale
      }
    }, mutable.Set.empty[Declaration])

    var inputPrime = input

    inputPrime = ourRewriter.execute[Program](input)

    if(OuroborosConfig.type_check) {
      inputPrime = ourStateChecker.execute[Program](inputPrime)
    }

    inputPrime = Program(
      if(OuroborosConfig.zopgUsed) inputPrime.domains else inputPrime.domains.filter(domain => !zOPGdomainNames.contains(domain.name)),
      inputPrime.fields,
      inputPrime.functions.filter(function => !(OuroborosNames.macroNames.keySet ++ zOPGdomainNames).contains(function.name) || usedMacroCalls.contains(function.name)),
      inputPrime.predicates,
      inputPrime.methods.filter(method => !(OuroborosNames.macroNames.keySet ++ zOPGdomainNames).contains(method.name) || usedMacroCalls.contains(method.name))
    )(inputPrime.pos, inputPrime.info, inputPrime.errT)

    if(OuroborosConfig.inline) {
      inputPrime = ourInliner.execute[Program](inputPrime)
      inputPrime = Program(
        if (OuroborosConfig.zopgUsed) inputPrime.domains else inputPrime.domains.filter(domain => !zOPGdomainNames.contains(domain.name)),
        inputPrime.fields,
        inputPrime.functions.filter(function => !OuroborosNames.macroNames.contains(function.name) && !zOPGdomainNames.contains(function.name)),
        inputPrime.predicates,
        inputPrime.methods.filter(method => !OuroborosNames.macroNames.contains(method.name) && !zOPGdomainNames.contains(method.name))
      )(inputPrime.pos, inputPrime.info, inputPrime.errT)
    }

    OuroborosConfig.zopgUsed = false
    translatedCode = inputPrime.toString()
    logger.debug(s"Complete Viper program:\n${inputPrime.toString()}")
    this.input = Some(inputPrime)
    inputPrime
  }

  var input: Option[Program] = None

  override def mapVerificationResult(input: VerificationResult): VerificationResult = {
    if(OuroborosNames.ref_fields.isEmpty) {
      val noRefFields = ParseWarning("There are no fields of type Node or Ref.", this.input match {
        case None => NoPosition
        case Some(x) => x.pos
      })
      input match {
        case Success => Failure(Seq(noRefFields))
        case Failure(errors) => Failure(errors.map {
          case x: AbstractVerificationError => x.transformedError()
          case x => x
        } :+ noRefFields)
      }
    } else {
      input match {
        case Success => Success
        case Failure(errors) => Failure(errors.map {
          case x: AbstractVerificationError => x.transformedError()
          case x => x
        })
      }
    }
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

object OuroborosConfig {
  var inline: Boolean = false
  var wisdoms: Boolean = false
  var update_invariants: Boolean = false
  var type_check: Boolean = false

  def set(inline: Boolean, wisdoms: Boolean, update_invariants: Boolean, type_check: Boolean) = {
    this.inline = inline
    this.wisdoms = wisdoms
    this.update_invariants = update_invariants
    this.type_check = type_check
  }

  def reset() = {
    inline = false
    wisdoms = false
    update_invariants = false
    type_check = false
  }

  var zopgUsed: Boolean = false
}
