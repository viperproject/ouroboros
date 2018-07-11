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
    def foldFunction(graphName: String, pos: Infoed with Positioned): (Exp, Exp) => Exp = {
      val graphErrTrafo = OuroborosErrorTransformers.graphErrTrafo(graphName)
      (foldedExp, exp) => And(foldedExp, exp)(pos.pos, pos.info, graphErrTrafo)
    }

    var allGraphs : Option[Exp] = None
    val toReturn : Seq[Exp] = objects.flatMap(
      mapping => {
        val obj = mapping._1
        val decls = mapping._2
        decls.size match {
          case 1 =>
            val decl = decls.head
            val graphErrTrafo = OuroborosErrorTransformers.graphErrTrafo(decl.name)
            obj.typ match {
              case OurClosedGraph => {
                allGraphs match {
                  case None => allGraphs = Some(
                    LocalVar(
                      decl.name
                    )(decl.typ, decl.pos, decl.info, graphErrTrafo)
                  )
                  case Some(prev) => allGraphs = Some(
                    AnySetUnion(
                      prev,
                      LocalVar(
                        decl.name
                      )(decl.typ, decl.pos, decl.info, graphErrTrafo)
                    )(decl.pos, decl.info, graphErrTrafo)
                  )
                }

                val localVar = LocalVar(decl.name)(decl.typ, decl.pos, decl.info, decl.errT)
                Seq(fold_GRAPH(localVar, fields, input, true, true, TrueLit()(), foldFunction(decl.name, localVar)))
              }
              case OurGraph => {
                allGraphs match {
                  case None => allGraphs = Some(
                    LocalVar(
                      decl.name
                    )(decl.typ, decl.pos, decl.info, graphErrTrafo)
                  )
                  case Some(prev) => allGraphs = Some(
                    AnySetUnion(
                      prev,
                      LocalVar(
                        decl.name
                      )(decl.typ, decl.pos, decl.info, graphErrTrafo)
                    )(decl.pos, decl.info, graphErrTrafo)
                  )
                }

                val localVar = LocalVar(decl.name)(decl.typ, decl.pos, decl.info, decl.errT)
                Seq(fold_GRAPH(localVar, fields, input, false, true, TrueLit()(), foldFunction(decl.name, localVar)))
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
              val graphErrTrafo = OuroborosErrorTransformers.graphErrTrafo(decl.name)
              obj.typ match {
                case OurClosedGraph =>
                  allGraphs match {
                    case None => allGraphs = Some(
                      LocalVar(
                        decl.name
                      )(decl.typ, decl.pos, decl.info, graphErrTrafo)
                    )
                    case Some(prev) => allGraphs = Some(
                      AnySetUnion(
                        prev,
                        LocalVar(
                          decl.name
                        )(decl.typ, decl.pos, decl.info, graphErrTrafo)
                      )(decl.pos, decl.info, graphErrTrafo) //TODO other position?
                    )
                  }
                  val postConditions : Seq[Exp] =
                    /*Seq(
                      NO_NULL(LocalVar(decl.name)(decl.typ, decl.pos, decl.info, decl.errT), input),
                      CLOSED(LocalVar(decl.name)(decl.typ, decl.pos, decl.info, decl.errT), input))*/
                  GRAPH(LocalVar(decl.name)(decl.typ, decl.pos, decl.info, decl.errT), fields, input, true, false)

                  additionalPostConditions = additionalPostConditions :+ postConditions.foldLeft[Exp](TrueLit()())(
                    (foldedExp, exp) => And(foldedExp, exp)(exp.pos, exp.info, graphErrTrafo))
                case OurGraph => {
                  allGraphs match {
                    case None => allGraphs = Some(
                      LocalVar(
                        decl.name
                      )(decl.typ, decl.pos, decl.info, graphErrTrafo)
                    )
                    case Some(prev) => allGraphs = Some(
                      AnySetUnion(
                        prev,
                        LocalVar(
                          decl.name
                        )(decl.typ, decl.pos, decl.info, graphErrTrafo)
                      )(decl.pos, decl.info, graphErrTrafo)
                    )
                  }
                  additionalPostConditions = additionalPostConditions :+ FuncApp(noNullInGraph, Seq(LocalVar(decl.name)(decl.typ, decl.pos, decl.info, graphErrTrafo)))(decl.pos, decl.info, graphErrTrafo)
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
          val qp: Exp = qps.foldLeft[Exp](BoolLit(true)())((foldedExps, exp) => And(foldedExps, exp)(exp.pos, exp.info, OuroborosErrorTransformers.qpsForRefFieldErrTrafo(exp.toString())))
          qp +: additionalPostConditions
        }
        case None => Seq()
      }
    }

def NO_NULL(decl: Exp, input: Program)= {
  val noNullInGraph = input.findFunction("NoNullInGraph")
  val noNullErrTrafo = OuroborosErrorTransformers.NullInGraphErrTrafo(Seq(decl))
  val noNullCall = FuncApp(noNullInGraph, Seq(decl))(decl.pos, decl.info, noNullErrTrafo)
//  if (OuroborosNames.macroNames.contains(noNullCall.funcname))
//    OuroborosMemberInliner.inlineFunction(noNullCall, input, noNullCall.pos, noNullCall.info, noNullCall.errT)
//  else
    noNullCall
}
def fold_GRAPH[B](graph: Exp, fields: Seq[Field], input: Program, closed: Boolean, qpsNeeded: Boolean, initialValue: B, foldFunction: ((B, Exp) => B)): B = {
    GRAPH(graph, fields, input, closed, qpsNeeded).foldLeft[B](initialValue)(
      (x, y) => foldFunction(x, y))
}

def GRAPH(graph: Exp, fields: Seq[Field], input: Program, closed: Boolean, qpsNeeded: Boolean): Seq[Exp] = {
  val qpsForRefFieldErrTrafo = OuroborosErrorTransformers.qpsForRefFieldErrTrafo(graph.toString())
  val unExp : Exp = NO_NULL(graph, input)
  val QPForRefFields : Seq[Exp] = if(qpsNeeded)
    collectQPsForRefFields(fields, graph.duplicateMeta(graph.pos, graph.info, qpsForRefFieldErrTrafo).asInstanceOf[Exp], FullPerm()(graph.pos, graph.info, qpsForRefFieldErrTrafo))
  else Seq()
  val InGraphForallsForRefFields = if(closed)
    Seq(
      CLOSED(graph, input)
    )
  else Seq()

  (unExp +: QPForRefFields) ++ InGraphForallsForRefFields
}
/*def GRAPH[B](graph: Exp, fields: Seq[Field], input: Program, closed: Boolean, initialValue: B, foldFunction: ((B, Exp) => B)): B = {
  val graphErrTrafo = OuroborosErrorTransformers.graphErrTrafo(graph.toString())
  val qpsForRefFieldErrTrafo = OuroborosErrorTransformers.qpsForRefFieldErrTrafo(graph.toString())
  val unExp : Exp = NO_NULL(graph, input)
  val QPForRefFields : Seq[Exp] = collectQPsForRefFields(fields, graph.duplicateMeta(graph.pos, graph.info, qpsForRefFieldErrTrafo).asInstanceOf[Exp], FullPerm()(graph.pos, graph.info, qpsForRefFieldErrTrafo))
  val InGraphForallsForRefFields = if(closed)
    Seq(
      CLOSED(graph, input)
    )//TODO (graph.pos, graph.info, OuroborosErrorTransformers.graphErrTrafo)
  else Seq()
  ((unExp +: QPForRefFields) ++ InGraphForallsForRefFields)
    .foldLeft[B](initialValue)(
      (x, y) => foldFunction(x, y)/*(graph.pos, graph.info, graphErrTrafo)*/) //TODO If there is an error, then there is an error in the encoding => OuroborosInternalEncodingError
}*/



  private def collectQPsForRefFields(fields : Seq[Field], graph : Exp, perm_exp: Exp = FullPerm()(NoPosition, NoInfo, NoTrafos)): Seq[Exp] =
    fields.map(f => getQPForGraphNodes(graph, f, perm_exp))

  private def getQPForGraphNodes(graph: Exp, field: Field, perm: Exp): Exp = {
    val qpsForRefFieldErrTrafo = OuroborosErrorTransformers.qpsForRefFieldErrTrafo(graph.toString())
    Forall(
      Seq(LocalVarDecl(OuroborosNames.getIdentifier("n"), Ref)(graph.pos, graph.info, qpsForRefFieldErrTrafo)),
      Seq(Trigger(Seq(FieldAccess(LocalVar(OuroborosNames.getIdentifier("n"))(Ref, graph.pos, graph.info, qpsForRefFieldErrTrafo), field)(graph.pos, graph.info, qpsForRefFieldErrTrafo)))(graph.pos, graph.info, qpsForRefFieldErrTrafo)),
      Implies(AnySetContains(LocalVar(OuroborosNames.getIdentifier("n"))(Ref, graph.pos, graph.info, qpsForRefFieldErrTrafo), graph)(graph.pos, graph.info, qpsForRefFieldErrTrafo),
        FieldAccessPredicate(FieldAccess(LocalVar(OuroborosNames.getIdentifier("n"))(Ref, graph.pos, graph.info, qpsForRefFieldErrTrafo), field)(graph.pos, graph.info, qpsForRefFieldErrTrafo), perm)(graph.pos, graph.info, qpsForRefFieldErrTrafo))(graph.pos, graph.info, qpsForRefFieldErrTrafo)
    )(graph.pos, graph.info, qpsForRefFieldErrTrafo)
  }

  private def CLOSED( decl: Exp, input: Program): Exp ={
    val closed = input.findFunction(OuroborosNames.getIdentifier("CLOSED"))
    val closedCallErrTrafo = OuroborosErrorTransformers.closedGraphErrTrafo(Seq(decl))
    val closedCall = FuncApp(closed, Seq(decl))(decl.pos, decl.info, closedCallErrTrafo)
//    if (OuroborosNames.macroNames.contains(closedCall.funcname))
//      OuroborosMemberInliner.inlineFunction(closedCall, input, closedCall.pos, closedCall.info, closedCallErrTrafo)
//    else
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
//      if (OuroborosNames.macroNames.contains(disjointCall.funcname)) OuroborosMemberInliner.inlineFunction(disjointCall, input, g0.pos, g0.info, disjointErrTrafo) else
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

//    if(OuroborosNames.macroNames.contains(apply_TCFramingCall.funcname))
//      OuroborosMemberInliner.inlineInhaleFunction(inhaleCall, apply_TCFramingCall, input, inhaleCall.pos, inhaleCall.info, inhaleCall.errT)
//    else
      inhaleCall
  }
}
