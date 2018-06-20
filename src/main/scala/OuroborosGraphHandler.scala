package viper.silver.plugin

import viper.silver.ast._
import viper.silver.ast.utility.Rewriter.ContextC
import viper.silver.plugin.errors.{OuroborosGraphSpecificactionError, OuroborosInternalEncodingError}
import viper.silver.plugin.reasons.{InsufficientGraphPermission, NullInGraphReason, OpenGraphReason}
import viper.silver.verifier.AbstractVerificationError
import viper.silver.verifier.errors.PostconditionViolated
import viper.silver.verifier.reasons.{AssertionFalse, InsufficientPermission, InternalReason}

import scala.collection.mutable

class OuroborosGraphHandler {

  var graph_keywords: mutable.Map[String, String] = mutable.Map.empty[String, String]

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


  def inputTypesAndClosed(objects: Seq[(OurObject, Seq[LocalVarDecl])], fields: Seq[Field], input: Program, method: Method): Seq[Exp] = {
    var allGraphs : Option[Exp] = None
    var toReturn : Seq[Exp] = objects.flatMap(
      mapping => {
        val obj = mapping._1
        val decls = mapping._2
        decls.size match {
          case 1 => {
            val decl = decls.head
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

                Seq(GRAPH(decl, fields, input, method, true))
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

                Seq(GRAPH(decl, fields, input, method, false))
              }
              //case OurList => //TODO
              case _ => Seq()
            }
          }
          case 0 => Seq()
        }

      }
    )

    allGraphs match {
      case None => toReturn
      case Some(graphs) => {
        toReturn :+ collectInGraphForallsForRefFields(fields, graphs)
      }
    }
  }

  def outputTypes(objects: Seq[(OurObject, Seq[LocalVarDecl])], fields: Seq[Field], input: Program, method: Method): Seq[Exp] =
    {
      val noNullInGraph = input.findFunction(getIdentifier("NoNullInGraph"))
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
                  var postConditions : Seq[Exp] =
                    Seq(FuncApp(
                      noNullInGraph,
                      Seq(
                        LocalVar(decl.name)(decl.typ, decl.pos, decl.info, graphErrTrafo)
                      )
                    )(decl.pos, decl.info, graphErrTrafo),
                    collectInGraphForallsForRefFields(fields, LocalVar(decl.name)(decl.typ, decl.pos, decl.info, closedGraphErrTrafo)))

                  additionalPostConditions = additionalPostConditions :+ postConditions.foldRight[Exp](TrueLit()())((exp, foldedExp) => And(foldedExp, exp)(exp.pos, exp.info, graphErrTrafo))
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
          val qp: Exp = qps.foldRight[Exp](BoolLit(true)())((exp, foldedExps) => And(foldedExps, exp)(exp.pos, exp.info, qpsForRefFieldErrTrafo))

          qp +: additionalPostConditions
        }
        case None => Seq()
      }
    }
  val qpsForRefFieldErrTrafo : ErrTrafo = ErrTrafo({
    case x => OuroborosGraphSpecificactionError(
      x.offendingNode,
      InsufficientGraphPermission(
        x.offendingNode,
        s"might have insufficient permissions in the graph"
      ),
      x.cached
    )
  })

  val closedGraphErrTrafo : ErrTrafo = ErrTrafo({
    case x => OuroborosGraphSpecificactionError(
      x.offendingNode,
      OpenGraphReason(
        x.offendingNode,
        s"Graph might not be closed"
      ),
      x.cached
    )
  })

  val graphErrTrafo: ErrTrafo = ErrTrafo(
    {
      case err: PostconditionViolated => err.reason match {
        case r : InsufficientPermission => { //TODO maybe find out, for which field, we don't have enough permissions
          OuroborosGraphSpecificactionError(
            err.offendingNode,
            InsufficientGraphPermission(
              err.offendingNode,
              "There might be insufficient permission to access all fields of nodes inside the graph."
            ),
            err.cached
          )
        }
        case r : AssertionFalse if r.readableMessage.contains(s"${getIdentifier("closed")}(")=> {
          OuroborosGraphSpecificactionError(
            err.offendingNode,
            OpenGraphReason(
              err.offendingNode,
              "This graph might not be closed."
            ),
            err.cached
          )
        }

        case r : AssertionFalse if r.readableMessage.contains(s"${getIdentifier("NoNullInGraph")}(") => {
          OuroborosGraphSpecificactionError(
            err.offendingNode,
            NullInGraphReason(
              err.offendingNode,
              "Null might be in this graph."
            ),
            err.cached
          )
        }

        case _ => err
      }
      case err => err
    }
  )

def GRAPH(graph: LocalVarDecl, fields: Seq[Field], input: Program, method: Method, closed: Boolean): Exp = {
  //print("Decls: " + decls + " ")
    val noNullInGraph = input.findFunction(getIdentifier("NoNullInGraph"))
    val closedFunction = input.findDomainFunction(getIdentifier("closed"))
    //val closed = input.findFunction(getIdentifier("CLOSED"))
    val unExp : FuncApp = FuncApp(
      noNullInGraph,
      Seq(
        LocalVar(graph.name)(graph.typ, graph.pos, graph.info, graphErrTrafo)
      )
    )(graph.pos, graph.info, graphErrTrafo)
    val QPForRefFields : Seq[Exp] = collectQPsForRefFields(fields, LocalVar(graph.name)(graph.typ, graph.pos, graph.info, qpsForRefFieldErrTrafo), FullPerm()(graph.pos, graph.info, qpsForRefFieldErrTrafo))
    val InGraphForallsForRefFields = if(closed)
      Seq(
        DomainFuncApp(
          input.findDomainFunction(getIdentifier("closed")),
          Seq(collectInGraphForallsForRefFields(fields, LocalVar(graph.name)(graph.typ, graph.pos, graph.info, closedGraphErrTrafo))),
          Map.empty[TypeVar, Type])(graph.pos, graph.info, graphErrTrafo)
      )
    else Seq()
    ((unExp +: QPForRefFields) ++ InGraphForallsForRefFields)
      .foldRight[Exp](TrueLit()(graph.pos, graph.info, graphErrTrafo))(
        (x, y) => And(x, y)(graph.pos, graph.info, graphErrTrafo)) //TODO If there is an error, then there is an error in the encoding => OuroborosInternalEncodingError
}

  private def collectQPsForRefFields(fields : Seq[Field], graph : Exp, perm_exp: Exp = FullPerm()(NoPosition, NoInfo, qpsForRefFieldErrTrafo)): Seq[Exp] =
    fields.map(f => getQPForGraphNodes(graph, f, perm_exp))

  private def getQPForGraphNodes(graph: Exp, field: Field, perm: Exp): Exp = {
    Forall(
      Seq(LocalVarDecl(getIdentifier("n"), Ref)(graph.pos, graph.info, qpsForRefFieldErrTrafo)),
      Seq(Trigger(Seq(FieldAccess(LocalVar(getIdentifier("n"))(Ref, graph.pos, graph.info, qpsForRefFieldErrTrafo), field)(graph.pos, graph.info, qpsForRefFieldErrTrafo)))(graph.pos, graph.info, qpsForRefFieldErrTrafo)),
      Implies(AnySetContains(LocalVar(getIdentifier("n"))(Ref, graph.pos, graph.info, qpsForRefFieldErrTrafo), graph)(graph.pos, graph.info, qpsForRefFieldErrTrafo),
        FieldAccessPredicate(FieldAccess(LocalVar(getIdentifier("n"))(Ref, graph.pos, graph.info, qpsForRefFieldErrTrafo), field)(graph.pos, graph.info, qpsForRefFieldErrTrafo), perm)(graph.pos, graph.info, qpsForRefFieldErrTrafo))(graph.pos, graph.info, qpsForRefFieldErrTrafo)
    )(graph.pos, graph.info, qpsForRefFieldErrTrafo)
  }

  private def collectInGraphForallsForRefFields(fields: Seq[Field], decl: Exp): Exp =
    fields.map(f => getInGraphForallForField(decl, f)).foldRight[Exp](TrueLit()())((exp, foldedExp) => And(foldedExp, exp)(exp.pos, exp.info, graphErrTrafo))

  private def getInGraphForallForField(graph: Exp, field: Field): Exp = {
    Forall(
      Seq(LocalVarDecl(getIdentifier("n"), Ref)(graph.pos, graph.info, closedGraphErrTrafo)),
      Seq(
        Trigger(Seq(AnySetContains(FieldAccess(LocalVar(getIdentifier("n"))(Ref, graph.pos, graph.info, closedGraphErrTrafo), field)(graph.pos, graph.info, closedGraphErrTrafo),
          graph)(graph.pos, graph.info, closedGraphErrTrafo))
        )(graph.pos, graph.info, closedGraphErrTrafo),
        Trigger(Seq(AnySetContains(LocalVar(getIdentifier("n"))(Ref, graph.pos, graph.info, closedGraphErrTrafo), graph)(graph.pos, graph.info, closedGraphErrTrafo),
          FieldAccess(LocalVar(getIdentifier("n"))(Ref, graph.pos, graph.info, closedGraphErrTrafo), field)(graph.pos, graph.info, closedGraphErrTrafo)))(graph.pos, graph.info, closedGraphErrTrafo)
      ),
      Implies(
        And(
          AnySetContains(
            LocalVar(getIdentifier("n"))(Ref, graph.pos, graph.info, closedGraphErrTrafo),
            graph
          )(graph.pos, graph.info, closedGraphErrTrafo),
          NeCmp(
            FieldAccess(LocalVar(getIdentifier("n"))(Ref, graph.pos, graph.info, closedGraphErrTrafo), field)(graph.pos, graph.info, closedGraphErrTrafo),
            NullLit()(graph.pos, graph.info, closedGraphErrTrafo)
          )(graph.pos, graph.info, closedGraphErrTrafo)
        )(graph.pos, graph.info, closedGraphErrTrafo),
        AnySetContains(
          FieldAccess(LocalVar(getIdentifier("n"))(Ref, graph.pos, graph.info, closedGraphErrTrafo), field)(graph.pos, graph.info, closedGraphErrTrafo),
          graph
        )(graph.pos, graph.info, closedGraphErrTrafo)
      )(graph.pos, graph.info, closedGraphErrTrafo)
    )(graph.pos, graph.info, closedGraphErrTrafo) //TODO If there is an error, then there is an error in the encoding => OuroborosInternalEncodingError
  }

  private def disjointGraphs(graphs: Seq[LocalVarDecl], input: Program): Seq[Exp] = {
    graphs.flatMap(x => DISJOINT(x, graphs.filter(y => graphs.indexOf(y) > graphs.indexOf(x)), input))
  }

  private def DISJOINT(g0 : LocalVarDecl, g1: Seq[LocalVarDecl], input: Program): Seq[Exp] = {
    g1.map(x => DISJOINT(g0, x, input))
  }

  private def DISJOINT(g0: LocalVarDecl, g1: LocalVarDecl, input: Program): Exp = {
    val disjoint = input.findFunction(getIdentifier("DISJOINT"))
    FuncApp(
      disjoint,
      Seq(
        LocalVar(g0.name)(g0.typ, g0.pos, g0.info, g0.errT),
        LocalVar(g1.name)(g1.typ, g1.pos, g1.info, g1.errT)
      )
    )(g0.pos, g0.info, g0.errT)
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
    val errTrafo: ErrTrafo = {
      ErrTrafo({
        case x => OuroborosInternalEncodingError(x.offendingNode,
          InternalReason(x.offendingNode, "internal framing error: " + x.reason.readableMessage),
          x.cached)
      })
    }
    val apply_TCFraming = getIdentifier("apply_TCFraming")
    val TCFraming = input.findFunction(apply_TCFraming)
    Inhale(
      FuncApp(
        apply_TCFraming,
        Seq(
          LocalVar(graph1.name)(graph1.typ, graph1.pos, graph1.info, errTrafo),
          LocalVar(graph2.name)(graph2.typ, graph2.pos, graph2.info, errTrafo)
        )
      )(graph1.pos, graph1.info, TCFraming.typ, TCFraming.formalArgs, errTrafo)
    )(graph1.pos, graph1.info, errTrafo)
  }

  def getIdentifier(name : String): String = graph_keywords.get(name) match{
    case None => name //TODO maybe throw error
    case Some(newName) => newName
  }
}
