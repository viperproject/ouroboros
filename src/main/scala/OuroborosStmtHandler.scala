package viper.silver.plugin

import viper.silver.ast._
import viper.silver.ast.utility.Rewriter.StrategyBuilder

import scala.collection.mutable

class OuroborosStmtHandler {
  val graphHandler = new OuroborosGraphHandler
  val namesHandler = new OuroborosNamesHandler

  def handleMethod(method: Method, spec: Option[OurGraphSpec], input: Program): Method = {
    Method(
      method.name,
      method.formalArgs,
      method.formalReturns,
      method.pres,
      method.posts,
      method.body match {
        case None => None
        case Some(body) =>
          Some(handleBody(body, method, spec, input))
      }
    )(
      //TODO
    )
  }

  def handleBody(seqn: Seqn, method: Method, spec: Option[OurGraphSpec], input: Program): Seqn = {

      val inputGraphs : Map[String, OurType] = spec match {
        case None => Map.empty[String, OurType]
        case Some(graphSpec) => {
          var inputs: mutable.Map[String, OurType]= mutable.Map.empty[String, OurType]
          graphSpec.inputs.map(obj =>
          {
            val objDecls = method.formalArgs.filter(p => p.name == obj.name)
            objDecls.size match {
              case 1 =>
                val objDecl = objDecls.head
                inputs.put(objDecl.name, obj.typ)
              case _ => //Should never happen
            }
            obj
          })
          Map.empty[String, OurType] ++ inputs
        }
      }


      var existingGraphs : mutable.Map[String, OurType] = mutable.Map.empty[String, OurType]
      existingGraphs ++= inputGraphs //TODO if we have fields of graph type, it will be more complex
    val wrapper: OuroborosStmtWrapper = OuroborosStmtWrapper(inputGraphs, existingGraphs, mutable.Set.empty[Declaration])
    handleStmt(seqn, wrapper, input: Program) match {
      case s: Seqn => s
      case s => Seqn(Seq(s), Seq())(s.pos, s.info, s.errT)
    }
  }

  def handleStmt(stmt: Stmt, wrapper: OuroborosStmtWrapper, input: Program): Stmt = { //TODO check if existingGraphs changes
      stmt match {
        case whileStmt: While => handleWhile(whileStmt, wrapper, input) //Add type invariants + handle body
        case methodCall:MethodCall => handleMethodCall(methodCall, wrapper, input) //Type Invariance Checking
        case seqn: Seqn => handleSeqn(seqn, wrapper, input) //visit stmts
        case ifStmt: If => handleIf(ifStmt, wrapper, input) //Handle existing graphs in thn and els
        case inhale:Inhale => handleInhale(inhale, wrapper, input) //If state of some graph is changed, type invariance checking
        case newStmt: NewStmt => handleNewStmt(newStmt, wrapper, input) //Create new graph only consisting of this Node. TCFraming
        case _ => stmt
        case exhale:Exhale => handleExhale(exhale, wrapper) //Fork. TODO Check Type Invariance? For that we need Protected Graphs
        case fieldAssign:FieldAssign => handleFieldAssign(fieldAssign, wrapper) //handleAssignment
        case localVarAssign: LocalVarAssign => handleLocalVarAssign(localVarAssign, wrapper)/*{
          val localGraphMapping = wrapper.existingGraphs
          val existingGraphs = wrapper.existingGraphs
          localGraphMapping.get(lhs.name) match {
            case None => {
              stmt
            }
            case Some(graph) => {
              existingGraphs.get(lhs.name) match {
                case None => {
                  existingGraphs.put(lhs.name, graph)
                  Seqn(
                    Seq(stmt, TYPE(graph)),         //TODO applyTCFraming with every other existing graph
                    Seq()
                  )(stmt.pos, stmt.info, stmt.errT) //TODO errorTransforming
                }
                case Some(existingGraph) => {
                  Seqn(
                    Seq(stmt, TYPE(graph)),
                    Seq()
                  )(stmt.pos, stmt.info, stmt.errT) //TODO errorTransforming
                } //TODO Do we need to do applyTCFraming?
              }
            }
          }
        } //add to existing Graph, if graph is being assigned. TCFraming*/
/*        case Package(wand, proofScript) => stmt //Don't know
        case Goto(target) => stmt //Don't know
        case Assert(exp) => stmt //Don't know
        case Fold(acc) => stmt //Don't know
        case Constraining(vars, body) => stmt //Don't know
        case Fresh(vars) => stmt //Don't know
        case Label(name, invs) => stmt //Don't do anything
        case Unfold(acc) => stmt //Don't know
        case Apply(exp) => stmt //Don't know
        case localDecl:LocalVarDeclStmt => handleLocalVarDeclStmt(localDecl, wrapper)*/

      }
  }

  def handleWhile(stmt: While, wrapper: OuroborosStmtWrapper, input: Program): While = {
    val existingGraphs = wrapper.existingGraphs
    val graphInvs = existingGraphs.map(a => TYPE(a, input, stmt))
    While(stmt.cond, graphInvs.toSeq ++ stmt.invs, handleSeqn(stmt.body, wrapper, input))(stmt.pos, stmt.info, stmt.errT)
  }

  def handleIf(ifStmt: If, wrapper: OuroborosStmtWrapper, input: Program): If = {
    If(ifStmt.cond, handleSeqn(ifStmt.thn, wrapper.copy(), input), handleSeqn(ifStmt.els, wrapper.copy(), input))(ifStmt.pos, ifStmt.info, ifStmt.errT)
  }

  def handleSeqn(seqn: Seqn, wrapper: OuroborosStmtWrapper, input: Program): Seqn = {
    var newScopedDecls: Set[Declaration] = Set()
    val newSS = seqn.ss.map(s => {
      val newStmt = handleStmt(s, wrapper, input)
      newScopedDecls ++= wrapper.newScopedDecls
      wrapper.newScopedDecls.clear()
      newStmt
    })
    Seqn(newSS, seqn.scopedDecls ++ newScopedDecls)(seqn.pos, seqn.info, seqn.errT)
  }

  def handleMethodCall(call: MethodCall, wrapper: OuroborosStmtWrapper, input: Program): Stmt = {
    val updateMethodNames: mutable.Map[String, Field] = mutable.Map.empty
    input.fields.map(field => updateMethodNames.put(OuroborosNames.getIdentifier(s"update_${field.name}"), field))
    call.methodName match {
      case x => updateMethodNames.get(x) match {
        case None => call
        case Some(field) =>
          //TODO need to find out, which update method to use
          val copier = StrategyBuilder.Slim[Node](PartialFunction.empty).duplicateEverything
          val fieldName = field.name
          val unlinkMethodName = OuroborosNames.getIdentifier(s"unlink_$fieldName")
          val linkMethodName = OuroborosNames.getIdentifier(s"link_$fieldName")
          val unlinkMethod = input.findMethod(unlinkMethodName)
          val linkMethod = input.findMethod(linkMethodName)

          val unlinkMethodCall = MethodCall(
            unlinkMethod,
            call.args.collect({
              case arg if call.args.indexOf(arg) + 1 < call.args.size => copier.execute[Exp](arg)
            }),
            Seq()
          )(call.pos, call.info, call.errT) //TODO own errT

          val linkMethodCall = MethodCall(
            linkMethod,
            call.args.map(arg => copier.execute[Exp](arg)),
            Seq()
          )(call.pos, call.info, call.errT)

          Seqn(
            Seq(
              unlinkMethodCall,
              linkMethodCall
            ),
            Seq()
          )(call.pos, call.info, call.errT)
      }
    }
  }

  def handleExhale(exhale: Exhale, wrapper: OuroborosStmtWrapper): Stmt = { //TODO Fork
    exhale
  }

  def handleInhale(inhale: Inhale, wrapper: OuroborosStmtWrapper, input: Program): Stmt = inhale.exp match {//TODO insert framing Axioms
    case func: FuncApp => func.funcname match {
      case x if x == OuroborosNames.getIdentifier("GRAPH_decl") =>
        //println("GRAPH_DECL")
        val thisGraph = func.args.head.asInstanceOf[LocalVar]
        wrapper.existingGraphs.put(thisGraph.name, OurGraph)
        val framingFunctions: mutable.Iterable[Stmt] = wrapper.existingGraphs.collect({
          case tuple if tuple._1 != thisGraph.name =>
            val graphName = tuple._1
            val graph: LocalVar = LocalVar(graphName)(SetType(Ref), thisGraph.pos, thisGraph.info, thisGraph.errT)
            val framingFunction = input.findFunction(OuroborosNames.getIdentifier("apply_TCFraming"))
            Inhale(
              FuncApp(framingFunction, Seq(graph, AnySetMinus(thisGraph, graph)()))(thisGraph.pos, thisGraph.info, thisGraph.errT) //TODO setMinus
            )(thisGraph.pos, thisGraph.info, thisGraph.errT)
        })
        val inhaleGraphFunction = Inhale(graphHandler.GRAPH(thisGraph, input.fields, input, false))(inhale.pos, inhale.info, inhale.errT)
        Seqn(
          inhaleGraphFunction +: framingFunctions.toSeq,
          Seq()
        )(inhale.pos, inhale.info, inhale.errT)
      case x if x == OuroborosNames.getIdentifier("CLOSED_GRAPH_decl") =>
        //println("CLOSED_GRAPH_DECL")
        val thisGraph = func.args.head.asInstanceOf[LocalVar]
        wrapper.existingGraphs.put(thisGraph.name, OurClosedGraph)
        val framingFunctions: mutable.Iterable[Stmt] = wrapper.existingGraphs.map(tuple => {
          val graphName = tuple._1
          val graph: LocalVar = LocalVar(graphName)(SetType(Ref), thisGraph.pos, thisGraph.info, thisGraph.errT)
          val framingFunction = input.findFunction(OuroborosNames.getIdentifier("apply_TCFraming"))
          Inhale(
            FuncApp(framingFunction, Seq(graph, AnySetMinus(thisGraph, graph)()))(thisGraph.pos, thisGraph.info, thisGraph.errT) //TODO setMinus
          )(thisGraph.pos, thisGraph.info, thisGraph.errT)
        })
        val inhaleGraphFunction = Inhale(graphHandler.GRAPH(func.args.head.asInstanceOf[LocalVar], input.fields, input, true))(inhale.pos, inhale.info, inhale.errT)
        Seqn(
          inhaleGraphFunction +: framingFunctions.toSeq,
          Seq()
        )(inhale.pos, inhale.info, inhale.errT)
      case _ => inhale //TODO other cases (Type Invariance)
    }
    case _ => inhale //TODO other cases (Type Invariance)
  }

  def handleFieldAssign(assign: FieldAssign, wrapper: OuroborosStmtWrapper): Stmt = {
    assign
  }

  def handleLocalVarAssign(assign: LocalVarAssign, wrapper: OuroborosStmtWrapper): Stmt = {
    assign
  }

  def handleNewStmt(stmt: NewStmt, wrapper: OuroborosStmtWrapper, input: Program): Stmt = stmt.fields.size match {
    case x if x == input.fields.size =>
      val n_Identifier = OuroborosNames.getIdentifier("n")
      val lhs = stmt.lhs
      val singletonGraphName = namesHandler.getNewName(s"g_consisting_${lhs.name}")
      val singletonGraphDecl: Declaration = LocalVarDecl(singletonGraphName, SetType(Ref))()
      val singletonGraphSpec = Inhale(
        And(
          AnySetContains(
            lhs.duplicate(lhs.getChildren).asInstanceOf[LocalVar],
            LocalVar(singletonGraphName)(SetType(Ref))
          )(),
          Forall(
            Seq(
              LocalVarDecl(
                n_Identifier,
                Ref
              )()
            ),
            Seq(
              //TODO
            ),
            Implies(
              NeCmp(
                LocalVar(n_Identifier)(Ref),
                LocalVar(lhs.name)(Ref)
              )(),
              Not(
                AnySetContains(
                  LocalVar(n_Identifier)(Ref),
                  LocalVar(singletonGraphName)(SetType(Ref))
                )()
              )()
            )()
          )()
        )()
      )()

      wrapper.existingGraphs.put(singletonGraphName, OurGraph)
      wrapper.newScopedDecls.add(singletonGraphDecl)
      Seqn(
        Seq(
          stmt,
          singletonGraphSpec
        ),
        Seq()
      )()
    case _ => stmt
  }

  def TYPE(tuple: (String, OurType), input: Program, pos: Infoed with Positioned with TransformableErrors): Exp = {
    //TODO Type Invariance Checking
    val ourType: OurType = tuple._2
    val name: String = tuple._1
    val fields = input.fields
    ourType match {
      case OurGraph => graphHandler.GRAPH(LocalVar(name)(SetType(Ref), pos.pos, pos.info, pos.errT), fields, input, false)
      case OurClosedGraph => graphHandler.GRAPH(LocalVar(name)(SetType(Ref), pos.pos, pos.info, pos.errT), fields, input, true)
      case _ => BoolLit(true)()
    }
      //LocalVar(tuple._1)(tuple._1.typ, pos.pos, pos.info, pos.errT)
  }

  def nextStmt(stmt: Stmt): Stmt = stmt match { //TODO put into object
    case stmt: Seqn =>
      stmt.ss.size match {
        case 0 => stmt
        case _ => nextStmt(stmt.ss.head)
      }
    case _ => stmt
  }

}

case class OuroborosStmtWrapper(inputGraphs: Map[String, OurType], existingGraphs: mutable.Map[String, (OurType)], newScopedDecls: mutable.Set[Declaration])
{
  def copy(): OuroborosStmtWrapper = {
    val inputCopy: Map[String, OurType] = Map.empty ++ inputGraphs
    val existingCopy: mutable.Map[String, OurType] = mutable.Map.empty ++ existingGraphs
    val newScopedCopy: mutable.Set[Declaration] = mutable.Set.empty[Declaration] ++ newScopedDecls
    OuroborosStmtWrapper(inputCopy, existingCopy, newScopedCopy)
  }
}
