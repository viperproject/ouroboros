/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.plugin

import java.util

import scala.language.postfixOps
import scala.collection.{immutable, mutable}
import viper.silver.{FastMessaging, ast, parser, plugin}
import viper.silver.ast.utility.Rewriter.{ContextC, Rewritable, StrategyBuilder}
import viper.silver.ast._
import viper.silver.ast.utility.Rewriter
import viper.silver.parser.{PBinExp, PFormalArgDecl, _}
import viper.silver.plugin.GraphState.GraphState
import viper.silver.plugin.errors.{OuroborosAssignmentError, OuroborosNodeCheckError}
import viper.silver.plugin.reasons.{InsufficientGraphPermission, NotInGraphReason}
import viper.silver.verifier.AbstractError
import viper.silver.verifier.errors.PreconditionInCallFalse
import viper.silver.verifier.reasons.{AssertionFalse, InsufficientPermission, InternalReason}


//sealed trait OurType //extends PDomainType
////case object OurNode extends OurType
//case object OurGraph extends OurType
//case object OurClosedGraph extends OurType
//case object OurDAG extends OurType
//case object OurClosedDAG extends OurType
//case object OurZOPG extends OurType
//case object OurClosedZOPG extends OurType
//case object OurForest extends OurType
//case object OurClosedForest extends OurType

sealed trait Topology
sealed trait DAG extends Topology
sealed trait ZOPG extends Topology
sealed trait Forest extends DAG with ZOPG

sealed trait Closedness
sealed trait Closed extends Closedness

case class OurGraphType(topo: Topology, clos: Closedness)

case object OurGraph extends Topology with Closedness
case object OurClosedGraph extends Topology with Closed
case object OurDAG extends DAG with Closedness
case object OurClosedDAG extends DAG with Closed
case object OurZOPG extends ZOPG with Closedness
case object OurClosedZOPG extends ZOPG with Closed
case object OurForest extends Forest with Closedness
case object OurClosedForest extends Forest with Closed

case class GraphType[T <: Topology, C <: Closedness]()




case class OurObject(name: String, typ: Topology with Closedness)
case class OurNode(name: String, graphs: Set[String])

object OurNode {

  //optimize is only used for reaching definitions analysis, when we are sure that we have all reaching definitions
  def getGraphExp(graphs: Set[String], localGraphs: mutable.Map[String, (LocalVarDecl, GraphState)], optimize: Boolean = false): Exp = OuroborosHelper.transformAndFold[String, Exp](
    graphs.toSeq,
    EmptySet(SetType(Ref))(),
    (exp1, exp2) => AnySetUnion(exp1, exp2)(),
    graphName => {
      val graph = LocalVar(graphName)(SetType(Ref))
      val graphExp: Exp = localGraphs.get(graphName) match {
        case None =>
          graph
        case Some(tuple) => tuple._2 match {
          case GraphState.ALWAYS_INITIALIZED if optimize =>
            graph
          case GraphState.NEVER_INITIALIZED if optimize =>
            EmptySet(Ref)()
          case _ =>
            val decl = tuple._1
            val initVar: LocalVar = LocalVar(decl.name)(decl.typ)
            val cond: Exp = decl.typ match {
              case Int =>
                NeCmp(initVar, IntLit(0)())()
              case Bool =>
                initVar
            }

            CondExp(cond, graph, EmptySet(Ref)())()
        }
      }


      graphExp
    }
  )

  def getGraphs(graphExp: Exp): Set[String] = graphExp match {
    case AnySetUnion(l, r) => getGraphs(l) ++ getGraphs(r)
    case LocalVar(n) => Set(n)
  }
}

object GraphState extends Enumeration {
  type GraphState = Value
  val ALWAYS_INITIALIZED, NEVER_INITIALIZED, UNKNOWN = Value
}

trait OurOperation
//case class OurLink(name: String) extends OurOperation
//case class OurUnlink(name: String) extends OurOperation
case class OurOperPair(name: String) extends OurOperation
case class OurGraphSpec(inputGraphs: Seq[OurObject], outputGraphs: Seq[OurObject], inputNodes: Seq[OurNode], outputNodes: Seq[OurNode])

class OuroborosGraphDefinition(plugin: OuroborosPlugin) {

  val graph_definitions: mutable.Map[String, OurGraphSpec] = mutable.Map.empty[String, OurGraphSpec]

  def handlePFormalArgDecl(input: PProgram, decl: PFormalArgDecl, isMethodSpec: Boolean): (PFormalArgDecl, Seq[AbstractError]) =
    //PFormalArgDecl(decl.idndef, getSilverType(decl.typ)).setPos(decl) //TODO Only duplicate if needed, PDEFINE cannot be duplicated
  decl.typ match {
    case d: PDomainType =>
      d.domain.name match {
        case "Node" =>
          val error = if(!isMethodSpec && d.typeArguments.nonEmpty)
            OurTypes.getError("Nodes can only have type arguments in the method parameters, and in the local declarations of the method bodies.", d)
          else
            Seq()
          (PFormalArgDecl(decl.idndef, TypeHelper.Ref).setPos(decl), error)
        case "Graph" =>
          val error = if(!isMethodSpec && d.typeArguments.nonEmpty)
            OurTypes.getError("Graphs can only have type arguments in the method parameters, and in the local declarations of the method bodies.", d)
          else
            Seq()

          (PFormalArgDecl(decl.idndef, PSetType(TypeHelper.Ref)).setPos(decl), error)
        case _ => (decl, Seq())
      }
    case d: PSetType =>
      val handledRes = handlePFormalArgDecl(input, PFormalArgDecl(decl.idndef, d.elementType), isMethodSpec)
      val handledDecl = handledRes._1
      val errors = handledRes._2
      (PFormalArgDecl(decl.idndef, PSetType(handledDecl.typ)).setPos(decl), errors)
    case _ => (decl, Seq())
  }

/*  def handlePLocalVarDecl(input: PProgram, decl: PLocalVarDecl): PLocalVarDecl =
    PLocalVarDecl(decl.idndef, getSilverType(decl.typ), decl.init).setPos(decl)

  def getSilverType(oldType: PType): PType = oldType match {
    case d: PDomainType =>
      d.domain.name match {
        case "Node" => TypeHelper.Ref
        case "Graph" | "ClosedGraph" | "List" => PSetType(TypeHelper.Ref)
        case _ => oldType
      }
    case s: PSetType =>
      PSetType(getSilverType(s.elementType))
    case _ => oldType
  }*/

  private def seqOfPExpToPExp(exp_seq: Seq[PExp], binary_oper: String, neutral_element: PExp): PExp = exp_seq.toList match {
    case e :: Nil => e
    case e :: tail => PBinExp(e, binary_oper, seqOfPExpToPExp(tail, binary_oper, neutral_element))
    case Nil =>
      neutral_element
  }

  private def seqOfExpToUnionExp(exp_seq: Seq[Exp])(pos: Position = NoPosition, info: Info = NoInfo, errT: ErrorTrafo = NoTrafos): Exp = exp_seq.toList match {
    case e :: Nil => e
    case e :: tail => AnySetUnion(e, seqOfExpToUnionExp(tail)(pos, info, errT))(pos, info, errT)
    case Nil => EmptySet(Ref)(pos, info, errT)//TrueLit()(pos, info, errT)
  }

  lazy val n_Identifier: String = getIdentifier("n")

  // forall n:Ref :: {n.field_i} n in nodes ==> acc(n.field_i,perm_exp)
  private def getQPForGraphNodes(graph_exp: PExp, field: String, perm_exp: PExp = PFullPerm()): PExp = PForall(
    Seq(PFormalArgDecl(PIdnDef(n_Identifier), TypeHelper.Ref)),
    Seq(PTrigger( Seq( PFieldAccess(PIdnUse(n_Identifier),PIdnUse(field))))),
    PBinExp( PBinExp(PIdnUse(n_Identifier), "in", graph_exp.deepCopyAll[PExp]), "==>", PAccPred(PFieldAccess(PIdnUse(n_Identifier), PIdnUse(field)), perm_exp.deepCopyAll[PExp])))

  // ( forall n:Ref :: {n.field_i} n in nodes && n != mutable_node ==> acc(n.field_i,1/2) )
  private def getQPForGraphNodesExcept(graph_exp: PExp, field: String, perm_exp: PExp = PFullPerm(), except_node: PExp): PExp = PForall(
    Seq(PFormalArgDecl(PIdnDef(n_Identifier), TypeHelper.Ref)),
    Seq(PTrigger( Seq( PFieldAccess(PIdnUse(n_Identifier),PIdnUse(field))))),
    PBinExp( PBinExp( PBinExp(PIdnUse(n_Identifier), "in", graph_exp.deepCopyAll[PExp]), "&&", PBinExp(PIdnUse(n_Identifier), "!=", except_node.deepCopyAll[PExp])), "==>", PAccPred(PFieldAccess(PIdnUse(n_Identifier), PIdnUse(field)), perm_exp.deepCopyAll[PExp])))

  // forall n:Ref ::{n.field_i in nodes}{n in nodes, n.field_i} n in nodes && n.field_i != null ==> n.field_i in nodes
  private def getInGraphForallForField(graph_exp: PExp, field: String): PExp = PForall(
    Seq(PFormalArgDecl(PIdnDef(n_Identifier), TypeHelper.Ref)),
    Seq(
      PTrigger( Seq(PBinExp(PFieldAccess(PIdnUse(n_Identifier), PIdnUse(field)), "in", graph_exp.deepCopyAll[PExp])) ),
      PTrigger( Seq(PBinExp(PIdnUse(n_Identifier), "in", graph_exp.deepCopyAll[PExp]), PFieldAccess(PIdnUse(n_Identifier), PIdnUse(field))))),
    PBinExp( PBinExp(PBinExp(PIdnUse(n_Identifier), "in", graph_exp.deepCopyAll[PExp]), "&&", PBinExp(PFieldAccess(PIdnUse(n_Identifier), PIdnUse(field)), "!=", PNullLit())), "==>", PBinExp(PFieldAccess(PIdnUse(n_Identifier), PIdnUse(field)), "in", graph_exp.deepCopyAll[PExp])))


  private def collectQPsForRefFields(fields: Seq[String], graph_exp: PExp, perm_exp: PExp = PFullPerm()): Seq[PExp] =
    fields.map(f => getQPForGraphNodes(graph_exp, f, perm_exp))

  private def collectQPsForRefFieldsProtected(fields: Seq[String], mutable_node_exp: PExp, graph_exp: PExp): Seq[PExp] =
    fields.map(f => getQPForGraphNodesExcept(graph_exp, f, PBinExp(PIntLit(1), "/", PIntLit(2)), mutable_node_exp))

  private def collectInGraphForallsForRefFields(fields: Seq[String], graph_exp: PExp): Seq[PExp] =
    fields.map(f => getInGraphForallForField(graph_exp, f))


  /*
  private def GRAPH(prog: PProgram, graph_exp: PExp) = PBinExp(
    // !(null in nodes)
    PUnExp("!", PBinExp(PNullLit(), "in", graph_exp.deepCopyAll[PExp])),
    "&&", PBinExp(
      seqOfPExpToPExp(getQPsForRefFields(prog.fields, graph_exp.deepCopyAll[PExp]), "&&"), "&&",
      concatInGraphForallsForRefFields(prog.fields, graph_exp.deepCopyAll[PExp])))
  */

  private def GRAPH(prog: PProgram, graph_exp: PExp, fields: Seq[String], c: PCall, closed: Boolean) = OuroborosHelper.ourFold[PExp](
    (PUnExp("!", PBinExp(PNullLit(), "in", graph_exp.deepCopyAll[PExp])) +:
      collectQPsForRefFields(fields, graph_exp, PFullPerm())) ++
      (if (closed) Seq(OuroborosHelper.ourFold[PExp](
        collectInGraphForallsForRefFields(fields, graph_exp)
        ,PBoolLit(true), (exp1, exp2) => PBinExp(exp1, "&&", exp2)))
      else Seq()), PBoolLit(true), (exp1, exp2) => PBinExp(exp1, "&&", exp2)).setPos(c)

  private def PROTECTED_GRAPH(prog: PProgram, graph_exp: PExp, fields: Seq[String], mutable_node_exp: PExp, mutable_field: String, c: PCall) = seqOfPExpToPExp(Seq(
    PUnExp("!", PBinExp(PNullLit(), "in", graph_exp.deepCopyAll[PExp])),
    PBinExp(mutable_node_exp.deepCopyAll[PExp], "in", graph_exp.deepCopyAll[PExp])
  ) ++ fields.map(f =>
      if (f == mutable_field)
        PAccPred(PFieldAccess(mutable_node_exp.deepCopyAll[PExp], PIdnUse(f)), PFullPerm())
      else
        PAccPred(PFieldAccess(mutable_node_exp.deepCopyAll[PExp], PIdnUse(f)), PBinExp(PIntLit(1), "/", PIntLit(2)))) ++
    collectQPsForRefFieldsProtected(fields, mutable_node_exp, graph_exp) /*:+
    OuroborosHelper.ourFold[PExp](
      collectInGraphForallsForRefFields(fields, graph_exp)
      ,PBoolLit(true), (exp1, exp2) => PBinExp(exp1, "&&", exp2))*/, "&&", PBoolLit(true)).setPos(c)


   /*
    PBinExp(
    PUnExp("!", PBinExp(PNullLit(), "in", graph_exp.deepCopyAll[PExp])),
    "&&", PBinExp( PBinExp(mutable_node_exp.deepCopyAll[PExp], "in", graph_exp.deepCopyAll[PExp]),
      "&&", PBinExp(


            PAccPred(PFieldAccess(mutable_node_exp.deepCopyAll[PExp], PIdnUse(f_name)), PFullPerm()),
            PAccPred(PFieldAccess(mutable_node_exp.deepCopyAll[PExp], PIdnUse(f_name)), PBinExp(PIntLit(1), "/", PIntLit(2)))

        "&&", PBinExp(
          seqOfPExpToPExp(getQPsForRefFieldsProtected(prog.fields, mutable_node_exp, graph_exp.deepCopyAll[PExp]), "&&"), "&&",
          concatInGraphForallsForRefFields(prog.fields, graph_exp.deepCopyAll[PExp])))))
  */

  /* FIXME decided to use old(EXISTS_PATH(...)) for now.
  private def evalEdgeRelationInCorrectState(prog: PProgram, graph_exp: PExp): PExp = {
    prog.methods.collect { case m: PMethod =>
      m.deepCollect({
        case some_exp: PExp if some_exp == graph_exp =>
          val graph_defs: OurGraphSpec = graph_definitions(m.idndef.name)
          graph_defs.inputs
      })
    }
    graph_exp match {
      case PIdnUse(graph_name) if graph_definitions.find(_._1 == graph_name)
    }
    ???
  }*/

  private def PROTECTED_GRAPH(prog: PProgram, graph_exp: PExp, fields: Seq[String]): PExp = {
    OuroborosHelper.ourFold[PExp](PUnExp("!", PBinExp(PNullLit(), "in", graph_exp.deepCopyAll[PExp])) +:
    collectQPsForRefFields(fields, graph_exp, PBinExp(PIntLit(1), "/", PIntLit(2))),
      PBoolLit(false),
      (exp1, exp2) => PBinExp(exp1, "&&", exp2))
  }

  private def EDGE(prog: PProgram, graph_exp: PExp, lhs_node_exp: PExp, rhs_node_exp: PExp, c: PCall): PExp = PCall(
    PIdnUse(getIdentifier("edge")),
    Seq(
      PCall(PIdnUse(getIdentifier("$$")), Seq(graph_exp)).setPos(c),
      lhs_node_exp.deepCopyAll[PExp],
      rhs_node_exp.deepCopyAll[PExp])).setPos(c)

  private def EDGES(program: PProgram, graph: PExp, c: PCall): PExp = PCall(
    PIdnUse(getIdentifier("$$")),
    Seq(graph)
  ).setPos(c)

  private def EXISTS_PATH(prog: PProgram, graph_exp: PExp, lhs_node_exp: PExp, rhs_node_exp: PExp, c: PCall): PExp = PCall(
    PIdnUse(getIdentifier("exists_path")),
    Seq(
      PCall(PIdnUse(getIdentifier("$$")), Seq(graph_exp.deepCopyAll[PExp])).setPos(c),
      lhs_node_exp.deepCopyAll[PExp],
      rhs_node_exp.deepCopyAll[PExp])).setPos(c)

  private def EXISTS_SPATH(prog: PProgram, graph_exp: PExp, lhs_node_exp: PExp, rhs_node_exp: PExp, c: PCall): PExp = PCall(
    PIdnUse(getIdentifier("exists_spath")),
    Seq(
      PCall(PIdnUse(getIdentifier("$$")), Seq(graph_exp.deepCopyAll[PExp])).setPos(c),
      lhs_node_exp.deepCopyAll[PExp],
      rhs_node_exp.deepCopyAll[PExp])).setPos(c)

  private def IS_GLOBAL_ROOT(prog: PProgram, graph_exp: PExp, root_node: PExp, c: PCall) = PForall(
    Seq(PFormalArgDecl(PIdnDef(n_Identifier), TypeHelper.Ref)),
    Seq( PTrigger(Seq(EXISTS_PATH(prog, graph_exp, root_node.deepCopyAll[PExp], PIdnUse(n_Identifier), c))) ),
    PBinExp(PBinExp(PIdnUse(n_Identifier), "in", graph_exp.deepCopyAll[PExp]), "==>", EXISTS_PATH(prog, graph_exp, root_node.deepCopyAll[PExp], PIdnUse(n_Identifier), c)) //TODO change that "n" is unique
  ).setPos(c)

  private def FUNCTIONAL(prog: PProgram, graph_exp: PExp, c: PCall) = PCall(
    PIdnUse(getIdentifier("func_graph")),
    Seq(PCall(PIdnUse(getIdentifier("$$")), Seq(graph_exp.deepCopyAll[PExp])))).setPos(c)

  private def UNSHARED(prog: PProgram, graph_exp: PExp, c: PCall) = PCall(
    PIdnUse(getIdentifier("unshared_graph")),
    Seq(PCall(PIdnUse(getIdentifier("$$")), Seq(graph_exp.deepCopyAll[PExp])))).setPos(c)

  private def ACYCLIC(prog: PProgram, graph_exp: PExp, c: PCall) = PCall(
    PIdnUse(getIdentifier("acyclic_graph")),
    Seq(PCall(PIdnUse(getIdentifier("$$")), Seq(graph_exp.deepCopyAll[PExp])))).setPos(c)

  private def ACYCLIC_LIST_SEGMENT(prog: PProgram, graph_exp: PExp, c: PCall): PExp = PBinExp(
    ACYCLIC(prog, graph_exp.deepCopyAll[PExp], c), "&&", PBinExp(FUNCTIONAL(prog, graph_exp.deepCopyAll[PExp], c), "&&", UNSHARED(prog, graph_exp.deepCopyAll[PExp], c))).setPos(c)

  private def explicitGraph(program: PProgram, elems: Seq[PExp], call: PCall): PExp = {
    if(elems.nonEmpty) PExplicitSet(elems).setPos(call)
    else PEmptySet(TypeHelper.Ref).setPos(call)
  }

  private def FRAMING(prog: PProgram, g0: PExp, g1: PExp, c: PCall): PCall = {
    PCall(PIdnUse(getIdentifier("apply_TCFraming")), Seq(g0, g1)).setPos(c)
  }

  private def NO_EXIT(prog: PProgram, edgesFrom: PExp, u: PExp, m: PExp, c: PCall): PCall = {
    PCall(PIdnUse(getIdentifier("apply_noExit")), Seq(PCall(PIdnUse(getIdentifier("$$")), Seq(edgesFrom)), u, m)).setPos(c)
  }

  def ref_fields(prog: PProgram): Seq[String] = prog.fields.collect {
    case PField(f, t) if t == TypeHelper.Ref => Seq(f.name)
    case x:PField => x.typ match {
      case d: PDomainType if d.domain.name == "Node" => Seq(x.idndef.name)
      case _ => Seq()
    }
  }.flatten





  def handlePMethod(input: PProgram, m: PMethod): (PNode, Seq[AbstractError]) = {

    var errors: Seq[AbstractError] = Seq()

    def collect_objects(collection: Seq[PFormalArgDecl]): Seq[OurObject] = collection.flatMap {
      x: PFormalArgDecl => x.typ match {
          case d: PDomainType =>
            val getOurObject = OurTypes.getOurGraphObject(d)
            errors ++= getOurObject._2
            getOurObject._1 match {
              case None => Seq()
              case Some(ourType) => Seq(OurObject(x.idndef.name, ourType))
            }
          case _ => Seq()
        } //TODO set of Graphs
    }

    def collect_nodes(decls: Seq[PFormalArgDecl], universe: Set[String]): Seq[OurNode] = decls.flatMap(decl => {
      decl.typ match {
        case d: PDomainType if d.domain.name == "Node" =>
          val getGraphAndErrors = OurTypes.getGraphOfNode(d, universe, true)
          errors ++= getGraphAndErrors._2
          Seq(OurNode(decl.idndef.name, getGraphAndErrors._1))
        case _ => Seq()
      }
    })

    val input_graphs: Seq[OurObject] = collect_objects(m.formalArgs)
    val inputGraphNames: Set[String] = input_graphs.map(ourObject => ourObject.name).toSet
    val input_nodes: Seq[OurNode] = collect_nodes(m.formalArgs, inputGraphNames)
    val output_graphs: Seq[OurObject] = collect_objects(m.formalReturns)
    val inputOutputGraphNames: Set[String] = inputGraphNames ++ output_graphs.map(ourObject => ourObject.name)
    val output_nodes: Seq[OurNode] = collect_nodes(m.formalReturns, inputOutputGraphNames)


    //TODO handle MethodBody in a separate method

    lazy val mBody: Option[PStmt] = m.body match {
      case None => None
      case Some(body) => Some(handlePMethodBody(body))
    }

    def handlePMethodBody(body: PStmt): PStmt = body match {
      case pSeqn: PSeqn => PSeqn(
        (PLocalVarDecl(PIdnDef(getIdentifier("UNIVERSE")), PSetType(TypeHelper.Ref), None) +:
        output_graphs.map(f =>
          PInhale(PCall(PIdnUse(OurTypes.getTypeDeclFunctionName(f.typ)), Seq(PIdnUse(f.name))))
      )) ++ output_nodes.map(ourNode => OurTypes.getNodeDeclFunctionCall(ourNode.name, ourNode.graphs)) ++
          pSeqn.ss.flatMap(s => handlePStmtInBody(s)))
      case _ => body
    }

    def handlePStmtInBody(stmt: PStmt): Seq[PStmt] = stmt match {
      case seqn: PSeqn => Seq(PSeqn(seqn.ss.flatMap(s => handlePStmtInBody(s))).setPos(seqn))
      case pIf: PIf => Seq(PIf(pIf.cond, handlePStmtInBody(pIf.thn).head.asInstanceOf[PSeqn], handlePStmtInBody(pIf.els).head.asInstanceOf[PSeqn]).setPos(pIf))
      case pWhile: PWhile => Seq(PWhile(pWhile.cond, pWhile.invs, handlePStmtInBody(pWhile.body).head.asInstanceOf[PSeqn]).setPos(pWhile))
        //TODO are there more cases?
      case pNewStmt: PRegularNewStmt =>
        val newFieldNames = pNewStmt.fields.map(_.name)
        def getError(message: String, pos: PNode): Seq[AbstractError] = {
          val newMessage = FastMessaging.message(pos, message)
          newMessage.map(m => {
            OuroborosInvalidNewStmtError( m.label,
              m.pos match {
                case fp: FilePosition =>
                  SourcePosition(fp.file, m.pos.line, m.pos.column)
                case _ =>
                  NoPosition
              }
            )
          })
        }
        if(ref_fields(input).exists(field => !newFieldNames.contains(field))) {
          val errMessage = "New Statements need to have access permissions to all reference typed fields."
          errors ++= getError(errMessage, pNewStmt)
        }

        Seq(pNewStmt)
      case l: PLocalVarDecl => l.typ match {
        case d: PDomainType => d.domain.name match {
          case "Node" =>
            //TODO put inhale into method body, such that we can use this information for field updates
            val graphOfNodeErrors = OurTypes.getGraphOfNodePExp(d)
            errors ++= graphOfNodeErrors._2
//            val nodeInGraphExp = PBinExp(PIdnUse(l.idndef.name), "in", graphOfNodeErrors._1).setPos(l)
            val graphNames = graphOfNodeErrors._3
//            val assume = PAssume(nodeInGraphExp).setPos(l)
            val nodeDecl = OurTypes.getNodeDeclFunctionCall(l.idndef.name, graphNames)
            val init = l.init match {
              case None => Seq()
              case Some(x) => Seq(PVarAssign(PIdnUse(l.idndef.name), x).setPos(x))
            }
            val newDecl = PLocalVarDecl(l.idndef, TypeHelper.Ref, None).setPos(l)
            Seq(newDecl, nodeDecl) ++ init
          case _ =>
            val getOurObject = OurTypes.getOurGraphObject(d)
            errors ++= getOurObject._2
            getOurObject._1 match {
              case None => Seq(l)
              case Some(ourType) =>
                val assign: Seq[PStmt] = l.init match {
                  case None => Seq()
                  case Some(init) =>
                    Seq(PVarAssign(PIdnUse(l.idndef.name), init).setPos(l))
                }
                  Seq(
                    PLocalVarDecl(l.idndef, PSetType(TypeHelper.Ref).setPos(l.typ), None).setPos(l),
                    PInhale(
                      PCall(
                        PIdnUse(OurTypes.getTypeDeclFunctionName(ourType)),
                        Seq(PIdnUse(l.idndef.name))
                      ).setPos(l)
                    ).setPos(l)
                  ) ++ assign
            }
        }
        case _ => Seq(l)
      }
      case _ => Seq(stmt)
    }

    // Store the graph specifications for future reference.
    graph_definitions(m.idndef.name) = OurGraphSpec(input_graphs, output_graphs, input_nodes, output_nodes)

    var objects: Seq[OurObject] = Seq()
    val presAndPostsRewriter = StrategyBuilder.Slim[PNode](
      {
        case n: PCall => handlePCall(input, n, Some(objects))
      }
    )

    (
      PMethod(
        m.idndef,
        m.formalArgs.map(x => {
          handlePFormalArgDecl(input, x, false)._1
        }),
        m.formalReturns.map(x => {
          handlePFormalArgDecl(input, x, false)._1
        }),
        m.pres.map(pre => {
          objects = input_graphs
          presAndPostsRewriter.execute[PExp](pre)
        }),
        m.posts.map(post => {
          objects = input_graphs ++ output_graphs
          presAndPostsRewriter.execute[PExp](post)
        }),
        mBody
      ).setPos(m),
      errors
    )
  }

  def handlePField(input: PProgram, m: PField): (PField, Seq[AbstractError])= {
    m.typ match {//TODO If fields of type Graph are used in a method, do we need to put requires Graph and ensures Graph?
      case d: PDomainType =>
        d.domain.name match {
          case "Node" if d.typeArguments.isEmpty => (PField(m.idndef, TypeHelper.Ref), Seq())
          case "Node" => (PField(m.idndef, TypeHelper.Ref), OurTypes.getError("Node field cannot have any type arguments.", d))
          case "Graph" =>
            (PField(m.idndef, PSetType(TypeHelper.Ref)),OurTypes.getError("Cannot use fields of type Graph.", d))
          //case "ZOPG" | "ClosedZOPG" => PField(m.idndef, PSetType(TypeHelper.Ref))
          case _ => (m, Seq())
        }
      case d: PSetType =>
        val res = handlePField(input, PField(m.idndef, d.elementType))
        val handledField = res._1
        (PField(m.idndef, PSetType(handledField.typ)), res._2)
      case _ => (m, Seq())
    }
  }
//
//  def handlePExp(input: PProgram, m: PExp): PExp = {
//    m match {
//      case m: PQuantifier => handlePQuantifier(input, m)
//      case _ => m//TODO
//    }
//  }
//
//  def handlePQuantifier(input: PProgram, m: PQuantifier): PQuantifier = {
//    m match {
//      case m: PForall => PForall(m.vars.map(x => handlePFormalArgDecl(input, x)), m.triggers/*.map(x => PTrigger(x.exp.map(x => handlePExp(input, x))))*/,
//        handlePExp(input, m.body))
//      case m: PExists => PExists(m.vars.map(x => handlePFormalArgDecl(input, x)), m.body)//TODO handle PTrigger, PBody?
//      case m: PForPerm => m
//    }
//  }

  def handlePCall(input: PProgram, m: PCall, objects: Option[Seq[OurObject]]): PNode = {

    m.func.name match {
      case "CLOSED_GRAPH" if m.args.length == 1 => GRAPH(input, m.args.head, ref_fields(input), m, true)
      case "GRAPH" if m.args.length == 1 => GRAPH(input, m.args.head, ref_fields(input), m, false)
      case "PROTECTED_GRAPH" if m.args.length == 3 => m.args(2) match {
        case PIdnUse(f_name) =>
          PROTECTED_GRAPH(input, m.args.head, ref_fields(input), m.args(1), f_name, m)
        case _ => m
      }
      case "PROTECTED_GRAPH" if m.args.length == 1 => PROTECTED_GRAPH(input, m.args.head, ref_fields(input))

      case "EDGE" if m.args.length == 3 => EDGE(input, m.args.head, m.args(1), m.args(2), m)
      case "EDGE" if m.args.length == 2 => EDGE(input, if(objects.isEmpty) universeExp() else getUnion(objects.get), m.args.head, m.args.last, m)
      case "EDGES" if m.args.length == 1 => EDGES(input, m.args.head, m)
      case "EXISTS_PATH" if m.args.length == 3 => EXISTS_PATH(input, m.args.head, m.args(1), m.args(2), m)
      case "EXISTS_PATH" if m.args.length == 2 => EXISTS_PATH(input, if(objects.isEmpty) universeExp() else getUnion(objects.get), m.args.head, m.args.last, m)
      case "EXISTS_SPATH" if m.args.length == 3 => EXISTS_SPATH(input, m.args.head, m.args(1), m.args(2), m)
      case "EXISTS_SPATH" if m.args.length == 2 => EXISTS_SPATH(input, if(objects.isEmpty) universeExp() else getUnion(objects.get), m.args.head, m.args.last, m)
      case "IS_GLOBAL_ROOT" if m.args.length == 2 => IS_GLOBAL_ROOT(input, m.args.head, m.args(1), m)

      case "FUNCTIONAL" if m.args.length == 1 => FUNCTIONAL(input, m.args.head, m)
      case "UNSHARED" if m.args.length == 1 => UNSHARED(input, m.args.head, m)
      case "ACYCLIC" if m.args.length == 1 => ACYCLIC(input, m.args.head, m)
      case "ACYCLIC_LIST_SEGMENT" if m.args.length == 1 => ACYCLIC_LIST_SEGMENT(input, m.args.head, m)
      case "Graph" => explicitGraph(input, m.args, m)
      case "FRAMING" if m.args.length == 2 => FRAMING(input, m.args.head, m.args.last, m)
      case "NO_EXIT" if m.args.length == 3 => NO_EXIT(input, m.args.head, m.args(1), m.args.last, m)
      case _ => m
    }

  }

  def handlePMethodCall(input: PProgram, m: PMethodCall): PNode = {
    m.method.name match {
      case "UPDATE" if m.args.length == 4 => genericUpdate(input, field = m.args.head, graph = m.args(1), lhsNode = m.args(2), rhsNode = m.args.last, m)
      case "UPDATE" if m.args.length == 3 => genericUpdate(input, field = m.args.head, graph = universeExp(), lhsNode = m.args(1), rhsNode = m.args.last, m)

      case "UNLINK" if m.args.length == 3 => genericLinkOrUnlink(input, field = m.args.head, graph = m.args(1), lhsNode = m.args.last, rhsNode = None, m)
      case "UNLINK" if m.args.length == 2 => genericLinkOrUnlink(input, field = m.args.head, graph = universeExp(), lhsNode = m.args.last, rhsNode = None, m)
      case "LINK" if m.args.length == 4 => genericLinkOrUnlink(input, field = m.args.head, graph = m.args(1), lhsNode = m.args(2), rhsNode = Some(m.args.last), m)
      case "LINK" if m.args.length == 3 => genericLinkOrUnlink(input, field = m.args.head, graph = universeExp(), lhsNode = m.args(1), rhsNode = Some(m.args.last), m)

      case "UPDATE_ZOPG" if m.args.length == 4 => zopgUpdate(input, field = m.args.head, graph = m.args(1), lhsNode = m.args(2), rhsNode = m.args.last, m)
      case "UPDATE_ZOPG" if m.args.length == 3 => zopgUpdate(input, field = m.args.head, graph = universeExp(), lhsNode = m.args(1), rhsNode = m.args.last, m)

      case "UNLINK_ZOPG" if m.args.length == 3 => zopgLinkOrUnlink(input, field = m.args.head, graph = m.args(1), lhsNode = m.args.last, rhsNode = None, m)
      case "UNLINK_ZOPG" if m.args.length == 2 => zopgLinkOrUnlink(input, field = m.args.head, graph = universeExp(), lhsNode = m.args.last, rhsNode = None, m)
      case "LINK_ZOPG" if m.args.length == 4 => zopgLinkOrUnlink(input, field = m.args.head, graph = m.args(1), lhsNode = m.args(2), rhsNode = Some(m.args.last), m)
      case "LINK_ZOPG" if m.args.length == 3 => zopgLinkOrUnlink(input, field = m.args.head, graph = universeExp(), lhsNode = m.args(1), rhsNode = Some(m.args.last), m)

      case "UPDATE_DAG" if m.args.length == 4 => dagUpdate(input, field = m.args.head, graph = m.args(1), lhsNode = m.args(2), rhsNode = m.args.last, m)
      case "UPDATE_DAG" if m.args.length == 3 => dagUpdate(input, field = m.args.head, graph = universeExp(), lhsNode = m.args(1), rhsNode = m.args.last, m)

      case "UNLINK_DAG" if m.args.length == 3 => dagLinkOrUnlink(input, field = m.args.head, graph = m.args(1), lhsNode = m.args(2), rhsNode = None, m)
      case "UNLINK_DAG" if m.args.length == 2 => dagLinkOrUnlink(input, field = m.args.head, graph = universeExp(), lhsNode = m.args(1), rhsNode = None, m)
      case "LINK_DAG" if m.args.length == 4 => dagLinkOrUnlink(input, field = m.args.head, graph = m.args(1), lhsNode = m.args(2), rhsNode = Some(m.args.last), m)
      case "LINK_DAG" if m.args.length == 3 => dagLinkOrUnlink(input, field = m.args.head, graph = universeExp(), lhsNode = m.args(1), rhsNode = Some(m.args.last), m)

      case "FRAMING" if m.args.length == 2 => FRAMING(input, m.args.head, m.args.last, m)
      case "NO_EXIT" if m.args.length == 3 => NO_EXIT(input, m.args.head, m.args(1), m.args.last, m)
      case _ => m
    }
  }

  def genericUpdate(input: PProgram, field: PExp, graph: PExp, lhsNode: PExp, rhsNode: PExp, m: PMethodCall): PStmt = field match {
    case field: PIdnUse =>
      val fieldName = field.name
      val updateMethodName = getIdentifier(s"update_$fieldName")
      //val copier = StrategyBuilder.Slim[PNode](PartialFunction.empty).duplicateEverything

      val updateMethodCall = PMethodCall(
        Seq(),
        PIdnUse(updateMethodName).setPos(m.method),
        Seq(graph, lhsNode, rhsNode) //TODO needed?
      ).setPos(m)

      //println(s"$linkMethodName arguments: " + linkMethod.args)

      updateMethodCall
    case _ => m //TODO throw error
  }

  def genericLinkOrUnlink(input: PProgram, field: PExp, graph: PExp, lhsNode: PExp, rhsNode: Option[PExp], m: PMethodCall): PStmt = field match {
    case field: PIdnUse =>
      val fieldName = field.name
      val methodName = rhsNode match {
        case None => getIdentifier(s"unlink_$fieldName")
        case _ =>    getIdentifier(s"link_$fieldName")
      }
      val methodCall = PMethodCall(
        Seq(),
        PIdnUse(methodName).setPos(m.method),
        Seq(graph, lhsNode) ++
          (if(rhsNode.isEmpty) Seq()
          else Seq(rhsNode.get))
      ).setPos(m)

      methodCall
    case _ => m //TODO throw error
  }

  def zopgUpdate(input: PProgram, field: PExp, graph: PExp, lhsNode: PExp, rhsNode: PExp, m: PMethodCall): PStmt = field match {
    case field: PIdnUse =>
      val fieldName = field.name
      val updateMethodName = getIdentifier(s"update_ZOPG_$fieldName")
      //val copier = StrategyBuilder.Slim[PNode](PartialFunction.empty).duplicateEverything
      val updateMethodCall = PMethodCall(
        Seq(),
        PIdnUse(updateMethodName).setPos(m.method),
        Seq(graph, lhsNode, rhsNode) //TODO needed?
      ).setPos(m)

      updateMethodCall
    case _ => m
  }

  def zopgLinkOrUnlink(input: PProgram, field: PExp, graph: PExp, lhsNode: PExp, rhsNode: Option[PExp], m: PMethodCall): PStmt = field match {
    case field: PIdnUse =>
      OuroborosConfig.zopgUsed = true
      val fieldName = field.name
      val methodName = rhsNode match {
        case None => getIdentifier(s"unlink_ZOPG_$fieldName")
        case _ => getIdentifier(s"link_ZOPG_$fieldName")
      }

      val methodCall = PMethodCall(
        Seq(),
        PIdnUse(methodName).setPos(m.method),
        Seq(graph, lhsNode) ++
          (if (rhsNode.isEmpty) Seq()
          else Seq(rhsNode.get))
      ).setPos(m)

      methodCall

    case _ => m
  }

  def dagUpdate(input: PProgram, field: PExp, graph: PExp, lhsNode: PExp, rhsNode: PExp, m:PMethodCall): PStmt = field match {
    case field: PIdnUse =>
      val fieldName = field.name
      val updateMethodName = getIdentifier(s"update_DAG_$fieldName")
      //val copier = StrategyBuilder.Slim[PNode](PartialFunction.empty).duplicateEverything
      val updateMethodCall = PMethodCall(
        Seq(),
        PIdnUse(updateMethodName).setPos(m.method),
        Seq(graph, lhsNode, rhsNode) //TODO needed?
      ).setPos(m)

      updateMethodCall
    case _ => m
  }

  def dagLinkOrUnlink(input: PProgram, field: PExp, graph: PExp, lhsNode: PExp, rhsNode: Option[PExp], m: PMethodCall): PStmt = field match {
    case field: PIdnUse =>
      val fieldName = field.name
      val methodName = rhsNode match {
        case None => getIdentifier(s"unlink_DAG_$fieldName")
        case _ => getIdentifier(s"link_DAG_$fieldName")
      }
      val methodCall = PMethodCall(
        Seq(),
        PIdnUse(methodName).setPos(m.method),
        Seq(graph, lhsNode) ++
          (if (rhsNode.isEmpty) Seq()
          else Seq(rhsNode.get))
      ).setPos(m)

      methodCall

    case _ => m
  }

  private def FRAMING(prog: PProgram, g0: PExp, g1: PExp, mc: PMethodCall): PStmt = {
    PInhale(
      PCall(PIdnUse(getIdentifier("apply_TCFraming")), Seq(g0, g1)).setPos(mc)
    ).setPos(mc)
  }

  private def NO_EXIT(prog: PProgram, edgesFrom: PExp, u: PExp, m: PExp, mc: PMethodCall): PStmt = {
    PInhale(
      PCall(PIdnUse(getIdentifier("apply_noExit")), Seq(PCall(PIdnUse(getIdentifier("$$")), Seq(edgesFrom)), u, m)).setPos(mc)
    ).setPos(mc)
  }

  /*private def getNoExitWisdom(input: Program, g0:Exp, g1:Exp)(pos: Position = NoPosition, info: Info = NoInfo, errT: ErrorTrafo = NoTrafos): Stmt = {
    val $$_func = input.findFunction(getIdentifier("$$"))
    val exists_path_funbc = input.findDomainFunction(getIdentifier("exists_path"))

    def apply_NoExit_framing_forall(G0: Exp, G1: Exp) = {
      require(G0 == g0 && G1 == g1 || G0 == g1 && G1 == g0)
      Forall(
        Seq(
          LocalVarDecl("u", Ref)(pos, info, errT),
          LocalVarDecl("v", Ref)(pos, info, errT)),
        Seq(
          Trigger(Seq(
            DomainFuncApp(
              exists_path_funbc,
              Seq(
                FuncApp(
                  $$_func,
                  Seq(AnySetUnion(g0, g1)(pos, info, errT)))(pos, info, errT),
                LocalVar("u")(Ref, pos, info, errT),
                LocalVar("v")(Ref, pos, info, errT)),
              Map.empty[TypeVar, Type])(pos, info, errT),
            AnySetContains(LocalVar("u")(Ref, pos, info, errT), G0)(pos, info, errT),
            AnySetContains(LocalVar("v")(Ref, pos, info, errT), G0)(pos, info, errT)
          ))(pos, info, errT)
        ),
        Implies(
          And(
            AnySetContains(LocalVar("u")(Ref, pos, info, errT), G0)(pos, info, errT),
            Not( AnySetContains(LocalVar("v")(Ref, pos, info, errT), G0)(pos, info, errT) )(pos, info, errT)
          )(pos, info, errT),
          Not(
            DomainFuncApp(
              exists_path_funbc,
              Seq(
                FuncApp(
                  $$_func,
                  Seq(AnySetUnion(g0, g1)(pos, info, errT)))(pos, info, errT),
                LocalVar("u")(Ref, pos, info, errT),
                LocalVar("v")(Ref, pos, info, errT)),
              Map.empty[TypeVar, Type])(pos, info, errT) )(pos, info, errT)
        )(pos, info, errT))(pos, info, errT)
    }
    Inhale(And(apply_NoExit_framing_forall(g0,g1),apply_NoExit_framing_forall(g1,g0))(pos, info, errT))(pos, info, errT)
  }

  private def getFramingWisdom(input: Program, g0:Exp, g1:Exp)(pos: Position = NoPosition, info: Info = NoInfo, errT: ErrorTrafo = NoTrafos): Stmt = {
    val apply_TCFraming_func = input.findFunction("apply_TCFraming")
    Inhale(FuncApp(apply_TCFraming_func, Seq(g0, g1))(pos, info, errT))(pos, info, errT)
  }

  private def getOperationalWisdoms(input: Program, local_m: Method, ctx: ContextC[Node, String])(pos: Position = NoPosition, info: Info = NoInfo, errT: ErrorTrafo = NoTrafos): Stmt = {

    val graph_defs: OurGraphSpec = graph_definitions(local_m.name)
    val distinct_graphs: Seq[OurObject] = graph_defs.inputGraphs.collect {
      case o => o.typ match {
        case g@ OurGraph => o
        case g@ OurClosedGraph => o //TODO more graphs types
      }
    }
    println(s">>> getOperationalWisdoms(local_m = ${local_m.name})")
    println(s">>>  distinct_graphs = ${distinct_graphs.map(_.name)}")

    val tmp1: Seq[Seqn] = distinct_graphs.collect {
      case g =>
        println(s">>> >>> g = ${g.name}")
        (distinct_graphs diff Seq(g)).toList.combinations(distinct_graphs.size - 1).collect {
          case x :: xs if xs != Nil || g.name < x.name =>
            println(s">>> >>> >>> x :: xs = ${(x :: xs).map(_.name)}")
            val subframe_gs: Seq[LocalVar] = (x :: xs).map { subframe => LocalVar(subframe.name)(SetType(Ref), pos, info, errT) }
            Seqn(
              Seq(
                //  getFramingWisdom(input, LocalVar(g.name)(SetType(Ref), pos, info, errT), seqOfExpToUnionExp(subframe_gs)(pos, info, errT))(pos, info, errT),
                getNoExitWisdom(input, LocalVar(g.name)(SetType(Ref), pos, info, errT), seqOfExpToUnionExp(subframe_gs)(pos, info, errT))(pos, info, errT)),
              Seq())(pos, info, errT)
      }
    } flatten

    Seqn(tmp1, Seq())(pos, info, errT)
  }

  def handleAssignments(input: Program, fa: FieldAssign, ctx: ContextC[Node, String]): Node = {
    val unlinkErrTrafo: ErrTrafo = {//TODO improve Error messages
      ErrTrafo({
        case x: PreconditionInCallFalse =>
          x.reason match {
            case r: InsufficientPermission =>  OuroborosAssignmentError(x.offendingNode,
              InsufficientGraphPermission(x.offendingNode, s"There might be insufficient permissiion to get read access to the ${fa.lhs.field.name} fields of all elements in ${x.offendingNode.args.head} " +
                s"and write access to the ${fa.lhs.field.name} field of ${x.offendingNode.args(1)}. Original message: " + x.reason.readableMessage),
              x.cached)

            case r: AssertionFalse =>  OuroborosAssignmentError(x.offendingNode,
              NotInGraphReason(x.offendingNode, s"${x.offendingNode.args(1)} might not be in ${x.offendingNode.args.head}" +
                s" or null might be in ${x.offendingNode.args.head}. Original message: " + x.reason.readableMessage),
              x.cached)

            case _ =>  OuroborosAssignmentError(x.offendingNode,
              InternalReason(x.offendingNode, "internal error in unlink: " + x.reason.readableMessage),
              x.cached)
          }
        case x => x
      })
    }

    val linkErrTrafo: ErrTrafo = {
      ErrTrafo({
        case x: PreconditionInCallFalse =>
          x.reason match {
            case r: AssertionFalse =>  OuroborosAssignmentError(x.offendingNode,
              NotInGraphReason(x.offendingNode, s"Assignment Error: ${x.offendingNode.args(2)} might not be in ${x.offendingNode.args.head}. " +
                s"Original Message: ${x.reason.readableMessage}"),
              x.cached)

            case xy =>  OuroborosAssignmentError(x.offendingNode,
              InternalReason(x.offendingNode, "internal error in link: " + x.reason.readableMessage),
              x.cached)
          }
        case x => x
      })
    }

    Seqn(input.methods.collect { case m: Method =>
      m.deepCollectInBody({
        case some_fa: FieldAssign if some_fa == fa =>
          val graph_defs = graph_definitions(m.name)
          val local_g =
            if (graph_defs.outputGraphs.nonEmpty)
              LocalVar(graph_defs.outputGraphs.last.name)(SetType(Ref), fa.pos, fa.info, unlinkErrTrafo)//TODO change for multiple graph_definitions
            else
              seqOfExpToUnionExp(graph_defs.inputGraphs.map { in => LocalVar(in.name)(SetType(Ref), fa.pos, fa.info, unlinkErrTrafo) })(fa.pos, fa.info, unlinkErrTrafo) //TODO causes an error, if there is no graph as input

          val unlinkMethodCall = MethodCall(getIdentifier(s"unlink_${fa.lhs.field.name}"), Seq(local_g, fa.lhs.rcv), Seq())(fa.pos, fa.info, unlinkErrTrafo)
          val linkMethodCall = MethodCall(getIdentifier(s"link_${fa.lhs.field.name}"), Seq(local_g, fa.lhs.rcv, fa.rhs), Seq())(fa.pos, fa.info, linkErrTrafo)

//          val unlinkInlined =
////            if (OuroborosNames.macroNames.contains(unlinkMethodCall.methodName))
////              OuroborosMemberInliner.inlineMethod(unlinkMethodCall, input, unlinkMethodCall.pos, unlinkMethodCall.info, unlinkMethodCall.errT)
////            else
//              unlinkMethodCall
//          val linkInlined =
////            if (OuroborosNames.macroNames.contains(linkMethodCall.methodName))
////              OuroborosMemberInliner.inlineMethod(linkMethodCall, input, linkMethodCall.pos, linkMethodCall.info, linkMethodCall.errT)
////            else
//              linkMethodCall

          Seqn(
            Seq(
//              getOperationalWisdoms(input, m, ctx)(fa.pos, fa.info, unlinkErrTrafo),
              unlinkMethodCall,
              linkMethodCall),
            Seq())(fa.pos, fa.info, unlinkErrTrafo)
      })
    } flatten, Seq())(fa.pos, fa.info, unlinkErrTrafo)
  }*/

  def getIdentifier(name : String): String = OuroborosNames.getIdentifier(name)

  def universeExp(): PExp = PIdnUse(getIdentifier("UNIVERSE"))

  def getUnion(objects: Seq[OurObject]): PExp = {
    OuroborosHelper.transformAndFold[OurObject, PExp](
      objects,
      PEmptySet(PSetType(TypeHelper.Ref)),
      (union, graph) => PBinExp(union, "union", graph),
      obj => PIdnUse(obj.name)
    )
  }
}
