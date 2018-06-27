package viper.silver.plugin

import viper.silver.ast._
import viper.silver.ast.utility.Rewriter.{ContextC, StrategyBuilder}
import viper.silver.plugin.errors.{OuroborosGraphSpecificactionError, OuroborosInternalEncodingError}
import viper.silver.plugin.reasons.{InsufficientGraphPermission, NullInGraphReason, OpenGraphReason}
import viper.silver.verifier.AbstractVerificationError
import viper.silver.verifier.errors.PostconditionViolated
import viper.silver.verifier.reasons.{AssertionFalse, InsufficientPermission, InternalReason}

import scala.collection.mutable

class OuroborosGraphHandler {

  //var graph_keywords: mutable.Map[String, String] = mutable.Map.empty[String, String]

  def handleMethod(input: Program, m: Method, s: Option[OurGraphSpec], ctx: ContextC[Node, String]): Method = s match {
    case None => m
    case Some(ss) => {
      val inputObjects: Seq[(OurObject, Seq[LocalVarDecl])] = ss.inputs.map(obj => (obj,m.formalArgs.filter(arg => arg.name == obj.name)))
      val outputObjects: Seq[(OurObject, Seq[LocalVarDecl])] = ss.outputs.map(obj => (obj,m.formalReturns.filter(arg => arg.name == obj.name)))
      val inputGraphs = {
        m.formalArgs.filter(x => ss.inputs.map(y => y.name).contains(x.name))
      }
      val outputGraphs = m.formalReturns.filter(x => ss.outputs.map(y => y.name).contains(x.name))
      Method(
        m.name,
        m.formalArgs,
        m.formalReturns,
        disjointGraphs(inputGraphs, input) ++ inputTypesAndClosed(inputObjects, input.fields, input, m) ++ m.pres,
        outputTypes(outputObjects ++ inputObjects, input.fields, input, m) ++ m.posts,
        handleMethodBody(input, m.body, inputGraphs, outputGraphs) /* ++ TCFraming*/
      ) (m.pos, m.info, m.errT)
    }
  }

/*  def handleFuncApp(input: Program, fc: FuncApp, args: Seq[String], ctx: ContextC[Node, String]): Exp = {
    val calledFunction = input.findFunction(fc.funcname)
    val funcArgs = calledFunction.formalArgs.map(arg => arg.name)
    val callArgs = fc.getArgs

    if(callArgs.size != funcArgs.size) return fc

    //fc.getArgs.

    val partialFunction : PartialFunction[String, Exp] = {
      case s if funcArgs.contains(s) => {
        callArgs(funcArgs.indexOf(s))
      }

      case s => LocalVar(s)(Ref)
    }

    calledFunction.body match {
      case None => fc
      case Some(body) => body.deepCopyWithLocalVarSubstitution(partialFunction, fc.pos, fc.info, fc.errT)
    }
  }*/


  def inputTypesAndClosed(objects: Seq[(OurObject, Seq[LocalVarDecl])], fields: Seq[Field], input: Program, method: Method): Seq[Exp] = {
    var allGraphs : Option[Exp] = None
    var toReturn : Seq[Exp] = objects.flatMap(
      mapping => {
        val obj = mapping._1
        val decls = mapping._2
        decls.size match {
          case 1 =>
            val decl = decls.head
            obj.typ match {
              case OurClosedGraph => {
                allGraphs match {
                  case None => allGraphs = Some(
                    LocalVar(
                      decl.name
                    )(decl.typ, decl.pos, decl.info, OuroborosErrorTransformers.graphErrTrafo)
                  )
                  case Some(prev) => allGraphs = Some(
                    AnySetUnion(
                      prev,
                      LocalVar(
                        decl.name
                      )(decl.typ, decl.pos, decl.info, OuroborosErrorTransformers.graphErrTrafo)
                    )(decl.pos, decl.info, OuroborosErrorTransformers.graphErrTrafo)
                  )
                }

                Seq(GRAPH(decl, fields, input, method, true))
              }
              case OurGraph => {
                allGraphs match {
                  case None => allGraphs = Some(
                    LocalVar(
                      decl.name
                    )(decl.typ, decl.pos, decl.info, OuroborosErrorTransformers.graphErrTrafo)
                  )
                  case Some(prev) => allGraphs = Some(
                    AnySetUnion(
                      prev,
                      LocalVar(
                        decl.name
                      )(decl.typ, decl.pos, decl.info, OuroborosErrorTransformers.graphErrTrafo)
                    )(decl.pos, decl.info, OuroborosErrorTransformers.graphErrTrafo)
                  )
                }

                Seq(GRAPH(decl, fields, input, method, false))
              }
              //case OurList => //TODO
              case _ => Seq()
            }
          case 0 => Seq()
        }

      }
    )

    allGraphs match {
      case None => toReturn
      case Some(graphs) => {
        toReturn :+ CLOSED(graphs, input)
      }
    }
  }

  def outputTypes(objects: Seq[(OurObject, Seq[LocalVarDecl])], fields: Seq[Field], input: Program, method: Method): Seq[Exp] =
    {
      val noNullInGraph = input.findFunction(OuroborosNames.getIdentifier("NoNullInGraph"))
      var additionalPostConditions : Seq[Exp] = Seq()
      var allGraphs : Option[Exp] = None
      objects.map(
        mapping => {
          val obj = mapping._1
          val decls = mapping._2
          decls.size match {
            case 1 => {
              val decl = decls.head
              obj.typ match {
                case OurClosedGraph =>
                  allGraphs match {
                    case None => allGraphs = Some(
                      LocalVar(
                        decl.name
                      )(decl.typ, decl.pos, decl.info, OuroborosErrorTransformers.graphErrTrafo)
                    )
                    case Some(prev) => allGraphs = Some(
                      AnySetUnion(
                        prev,
                        LocalVar(
                          decl.name
                        )(decl.typ, decl.pos, decl.info, OuroborosErrorTransformers.graphErrTrafo)
                      )(decl.pos, decl.info, OuroborosErrorTransformers.graphErrTrafo) //TODO other position?
                    )
                  }
                  val postConditions : Seq[Exp] =
                    Seq(
                      NO_NULL(decl, input),
                      CLOSED(LocalVar(decl.name)(decl.typ, decl.pos, decl.info, decl.errT), input))

                  additionalPostConditions = additionalPostConditions :+ postConditions.foldRight[Exp](TrueLit()())((exp, foldedExp) => And(foldedExp, exp)(exp.pos, exp.info, OuroborosErrorTransformers.graphErrTrafo))
                case OurGraph => {
                  allGraphs match {
                    case None => allGraphs = Some(
                      LocalVar(
                        decl.name
                      )(decl.typ, decl.pos, decl.info, OuroborosErrorTransformers.graphErrTrafo)
                    )
                    case Some(prev) => allGraphs = Some(
                      AnySetUnion(
                        prev,
                        LocalVar(
                          decl.name
                        )(decl.typ, decl.pos, decl.info, OuroborosErrorTransformers.graphErrTrafo)
                      )(decl.pos, decl.info, OuroborosErrorTransformers.graphErrTrafo)
                    )
                  }
                  additionalPostConditions = additionalPostConditions :+ FuncApp(noNullInGraph, Seq(LocalVar(decl.name)(decl.typ, decl.pos, decl.info, OuroborosErrorTransformers.graphErrTrafo)))(decl.pos, decl.info, OuroborosErrorTransformers.graphErrTrafo)
                }
                //case OurList => //TODO
              }
            }
            case 0 => Seq()
          }
          mapping
        }
      )
      allGraphs match {
        case Some(graphs) => {
          val qps: Seq[Exp] = collectQPsForRefFields(fields, graphs, FullPerm()())
          val qp: Exp = qps.foldRight[Exp](BoolLit(true)())((exp, foldedExps) => And(foldedExps, exp)(exp.pos, exp.info, OuroborosErrorTransformers.qpsForRefFieldErrTrafo))
          val test : Position = method.formalArgs(0).pos
          qp +: additionalPostConditions
        }
        case None => Seq()
      }
    }

def NO_NULL(decl: LocalVarDecl, input: Program)= {
  val noNullInGraph = input.findFunction("NoNullInGraph")
  val noNullErrTrafo = OuroborosErrorTransformers.NullInGraphErrTrafo(Seq(decl))
  val noNullCall = FuncApp(noNullInGraph, Seq(LocalVar(decl.name)(decl.typ, decl.pos, decl.info, decl.errT)))(decl.pos, decl.info, noNullErrTrafo)
  if (OuroborosNames.macroNames.contains(noNullCall.funcname))
    OuroborosMemberInliner.inlineFunction(noNullCall, input, noNullCall.pos, noNullCall.info, noNullCall.errT)
  else
    noNullCall
}

def GRAPH(graph: LocalVarDecl, fields: Seq[Field], input: Program, method: Method, closed: Boolean): Exp = {
    val unExp : Exp = NO_NULL(graph, input)
    val QPForRefFields : Seq[Exp] = collectQPsForRefFields(fields, LocalVar(graph.name)(graph.typ, graph.pos, graph.info, OuroborosErrorTransformers.qpsForRefFieldErrTrafo), FullPerm()(graph.pos, graph.info, OuroborosErrorTransformers.qpsForRefFieldErrTrafo))
    val InGraphForallsForRefFields = if(closed)
      Seq(
        CLOSED(LocalVar(graph.name)(graph.typ, graph.pos, graph.info, graph.errT), input)
      )//TODO (graph.pos, graph.info, OuroborosErrorTransformers.graphErrTrafo)
    else Seq()
    ((unExp +: QPForRefFields) ++ InGraphForallsForRefFields)
      .foldRight[Exp](TrueLit()(graph.pos, graph.info, OuroborosErrorTransformers.graphErrTrafo))(
        (x, y) => And(x, y)(graph.pos, graph.info, OuroborosErrorTransformers.graphErrTrafo)) //TODO If there is an error, then there is an error in the encoding => OuroborosInternalEncodingError
}

  private def collectQPsForRefFields(fields : Seq[Field], graph : Exp, perm_exp: Exp = FullPerm()(NoPosition, NoInfo, OuroborosErrorTransformers.qpsForRefFieldErrTrafo)): Seq[Exp] =
    fields.map(f => getQPForGraphNodes(graph, f, perm_exp))

  private def getQPForGraphNodes(graph: Exp, field: Field, perm: Exp): Exp = {
    Forall(
      Seq(LocalVarDecl(OuroborosNames.getIdentifier("n"), Ref)(graph.pos, graph.info, OuroborosErrorTransformers.qpsForRefFieldErrTrafo)),
      Seq(Trigger(Seq(FieldAccess(LocalVar(OuroborosNames.getIdentifier("n"))(Ref, graph.pos, graph.info, OuroborosErrorTransformers.qpsForRefFieldErrTrafo), field)(graph.pos, graph.info, OuroborosErrorTransformers.qpsForRefFieldErrTrafo)))(graph.pos, graph.info, OuroborosErrorTransformers.qpsForRefFieldErrTrafo)),
      Implies(AnySetContains(LocalVar(OuroborosNames.getIdentifier("n"))(Ref, graph.pos, graph.info, OuroborosErrorTransformers.qpsForRefFieldErrTrafo), graph)(graph.pos, graph.info, OuroborosErrorTransformers.qpsForRefFieldErrTrafo),
        FieldAccessPredicate(FieldAccess(LocalVar(OuroborosNames.getIdentifier("n"))(Ref, graph.pos, graph.info, OuroborosErrorTransformers.qpsForRefFieldErrTrafo), field)(graph.pos, graph.info, OuroborosErrorTransformers.qpsForRefFieldErrTrafo), perm)(graph.pos, graph.info, OuroborosErrorTransformers.qpsForRefFieldErrTrafo))(graph.pos, graph.info, OuroborosErrorTransformers.qpsForRefFieldErrTrafo)
    )(graph.pos, graph.info, OuroborosErrorTransformers.qpsForRefFieldErrTrafo)
  }

  private def CLOSED( decl: Exp, input: Program): Exp ={
    val closed = input.findFunction(OuroborosNames.getIdentifier("CLOSED"))
    val closedCallErrTrafo = OuroborosErrorTransformers.closedGraphErrTrafo(Seq(decl))
    val closedCall = FuncApp(closed, Seq(decl))(decl.pos, decl.info, closedCallErrTrafo)
    if (OuroborosNames.macroNames.contains(closedCall.funcname))
      OuroborosMemberInliner.inlineFunction(closedCall, input, closedCall.pos, closedCall.info, closedCallErrTrafo)
    else
      closedCall

  }

  private def disjointGraphs(graphs: Seq[LocalVarDecl], input: Program): Seq[Exp] = {
    graphs.flatMap(x => DISJOINT(x, graphs.filter(y => graphs.indexOf(y) > graphs.indexOf(x)), input))
  }

  private def DISJOINT(g0 : LocalVarDecl, g1: Seq[LocalVarDecl], input: Program): Seq[Exp] = {
    g1.map(x => {
      val disjoint = input.findFunction(OuroborosNames.getIdentifier("DISJOINT"))
      val disjointErrTrafo = OuroborosErrorTransformers.disjointGraphsErrTrafo(Seq(g0, x))
      val disjointCall = FuncApp(disjoint, Seq(
        LocalVar(g0.name)(g0.typ, g0.pos, g0.info, g0.errT),
        LocalVar(x.name)(x.typ, x.pos, x.info, x.errT)
      ))(g0.pos, g0.info, disjointErrTrafo)
      if (OuroborosNames.macroNames.contains(disjointCall.funcname)) OuroborosMemberInliner.inlineFunction(disjointCall, input, g0.pos, g0.info, disjointErrTrafo) else
      disjointCall
    })
  }

  private def handleMethodBody(input: Program, maybeBody: Option[Seqn], inputGraphs: Seq[LocalVarDecl], outputGraphs: Seq[LocalVarDecl]): Option[Seqn] = maybeBody match{
    case None => maybeBody
    case Some(body) => {
      inputGraphs.size match {
        case a if a > 1 => Some(Seqn(getFramingAxioms(input, inputGraphs) ++ body.ss, body.scopedDecls)(
          body.pos, body.info, body.errT
        ))
        case _ => Some(body)
      }
    }
  }

  private def getFramingAxioms(input: Program, inputGraphs: Seq[LocalVarDecl]): Seq[Stmt] = {
    inputGraphs.size match {
      case a if a <= 1 => Seq()
      case _ => inputGraphs.flatMap(a =>
        inputGraphs.filter(b => inputGraphs.indexOf(b) > inputGraphs.indexOf(a)).map(b => assumeApplyTCFraming(input, a,b)))
    }
  }

  private def assumeApplyTCFraming(input: Program, graph1: LocalVarDecl, graph2: LocalVarDecl): Stmt = {
    val errTrafo: ErrTrafo = { //This error is only for the case that the program inserts apply TCFraming automatically
      ErrTrafo({
        case x => OuroborosInternalEncodingError(x.offendingNode,
          InternalReason(x.offendingNode, "internal framing error: " + x.reason.readableMessage),
          x.cached)
      })
    }
    val apply_TCFraming = OuroborosNames.getIdentifier("apply_TCFraming")
    val TCFraming = input.findFunction(apply_TCFraming)
    val apply_TCFramingCall = FuncApp(
      apply_TCFraming,
      Seq(
        LocalVar(graph1.name)(graph1.typ, graph1.pos, graph1.info, errTrafo),
        LocalVar(graph2.name)(graph2.typ, graph2.pos, graph2.info, errTrafo)
      )
    )(graph1.pos, graph1.info, TCFraming.typ, TCFraming.formalArgs, errTrafo)
    val inhaleCall = Inhale(
      apply_TCFramingCall
    )(graph1.pos, graph1.info, errTrafo)

    if(OuroborosNames.macroNames.contains(apply_TCFramingCall.funcname))
      OuroborosMemberInliner.inlineInhaleFunction(inhaleCall, apply_TCFramingCall, input, inhaleCall.pos, inhaleCall.info, inhaleCall.errT)
    else
      inhaleCall
  }
}
