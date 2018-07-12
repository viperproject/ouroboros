package viper.silver.plugin

import viper.silver.ast._
import viper.silver.ast.utility.Rewriter.StrategyBuilder
import viper.silver.plugin.errors.OuroborosAssignmentError
import viper.silver.plugin.reasons.{InsufficientGraphPermission, NotInGraphReason}
import viper.silver.verifier.errors.PreconditionInCallFalse
import viper.silver.verifier.reasons.{AssertionFalse, InsufficientPermission, InternalReason}

import scala.collection.mutable

class OuroborosStmtHandler {
  val graphHandler = new OuroborosGraphHandler

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

      val inputGraphs : Map[String, Topology with Closedness] = spec match {
        case None => Map.empty[String, Topology with Closedness]
        case Some(graphSpec) =>
          val inputs: mutable.Map[String, Topology with Closedness]= mutable.Map.empty[String, Topology with Closedness]
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
          Map.empty[String, Topology with Closedness] ++ inputs
      }


      var existingGraphs : mutable.Map[String, Topology with Closedness] = mutable.Map.empty[String, Topology with Closedness]
      existingGraphs ++= inputGraphs //TODO if we have fields of graph type, it will be more complex
    val wrapper: OuroborosStmtWrapper = OuroborosStmtWrapper(input, inputGraphs, existingGraphs, mutable.Set.empty[String], mutable.Set.empty[Declaration])
    handleStmt(seqn, wrapper) match {
      case s: Seqn => s
      case s => Seqn(Seq(s), Seq())(s.pos, s.info, s.errT)
    }
  }

  def handleStmt(stmt: Stmt, wrapper: OuroborosStmtWrapper): Stmt = { //TODO check if existingGraphs changes
      stmt match {
        case whileStmt: While => handleWhile(whileStmt, wrapper) //Add type invariants + handle body
        case methodCall:MethodCall => handleMethodCall(methodCall, wrapper) //Type Invariance Checking
        case seqn: Seqn => handleSeqn(seqn, wrapper) //visit stmts
        case ifStmt: If => handleIf(ifStmt, wrapper) //Handle existing graphs in thn and els
        case inhale:Inhale => handleInhale(inhale, wrapper) //If state of some graph is changed, type invariance checking
        case newStmt: NewStmt => handleNewStmt(newStmt, wrapper) //Create new graph only consisting of this Node. TCFraming
        case fieldAssign:FieldAssign => handleFieldAssign(fieldAssign, wrapper) //handleAssignment
        case _ => stmt
        case exhale:Exhale => handleExhale(exhale, wrapper) //Fork. TODO Check Type Invariance? For that we need Protected Graphs
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

  def handleWhile(stmt: While, wrapper: OuroborosStmtWrapper): While = {
    val userDefiniedGraphs = wrapper.userDefinedGraphs
    val graphInvs = userDefiniedGraphs.flatMap(a => TYPE(a, wrapper.input, stmt))
    val closed = wrapper.input.findFunction(OuroborosNames.getIdentifier("CLOSED"))
    val allExistingGraphsExp : Exp = OuroborosHelper.transformAndFold[String, Exp](
        wrapper.allExistingGraphs().toSeq,
        EmptySet(Ref)(),(foldedGraphs, graph) => AnySetUnion(foldedGraphs, graph)(),
        graphName => LocalVar(graphName)(SetType(Ref))
    )
    val closednessSpec : Exp = FuncApp(closed, Seq(allExistingGraphsExp))()

    While(stmt.cond, graphInvs.toSeq ++ stmt.invs :+ closednessSpec, handleSeqn(stmt.body, wrapper.copy()))(stmt.pos, stmt.info, stmt.errT)
  }

  def handleIf(ifStmt: If, wrapper: OuroborosStmtWrapper): If = {
    val input = wrapper.input
    If(ifStmt.cond, handleSeqn(ifStmt.thn, wrapper.copy()), handleSeqn(ifStmt.els, wrapper.copy()))(ifStmt.pos, ifStmt.info, ifStmt.errT)
  }

  def handleSeqn(seqn: Seqn, wrapper: OuroborosStmtWrapper): Seqn = {
    var newScopedDecls: mutable.Set[Declaration] = mutable.Set.empty[Declaration]
    val newSS = seqn.ss.map(s => {
      val newStmt = handleStmt(s, wrapper)
      newScopedDecls ++= wrapper.newlyDeclaredVariables
      wrapper.newlyDeclaredVariables.clear()
      newStmt
    })
    val newDeclNames = newScopedDecls.collect({
      case x: LocalVarDecl => x.name
    })

    Seqn(newSS, seqn.scopedDecls ++ newScopedDecls)(seqn.pos, seqn.info, seqn.errT)
  }

  def handleMethodCall(call: MethodCall, wrapper: OuroborosStmtWrapper): Stmt = {
    val input = wrapper.input
    val genericUpdateNames: mutable.Map[String, Field] = mutable.Map.empty
    input.fields.map(field => genericUpdateNames.put(OuroborosNames.getIdentifier(s"update_${field.name}"), field))
    val ZOPGUpdateNames: mutable.Map[String, Field] = mutable.Map.empty[String, Field] ++ input.fields.map(field => /*genericUpdateNames.put*/(OuroborosNames.getIdentifier(s"update_ZOPG_${field.name}"), field))
    call.methodName match {
      case x if x == "new_node" =>
        val universe = OuroborosHelper.transformAndFold[String, Exp](
          wrapper.allExistingGraphs().toSeq,
          EmptySet(Ref)(),
          (exp1, exp2) => AnySetUnion(exp1, exp2)(),
          graphName => LocalVar(graphName)(SetType(Ref))
        )

        val newCall = MethodCall(OuroborosNames.getIdentifier("create_node"), Seq(universe), call.targets)(call.pos, call.info, call.errT)
        if (OuroborosNames.macroNames.contains(newCall.methodName))
          {
            val inlinedCall: Seqn = OuroborosMemberInliner.inlineMethod(newCall, wrapper.input, call.pos, call.info, call.errT).asInstanceOf[Seqn]
            val decls = inlinedCall.scopedDecls
            wrapper.newlyDeclaredVariables ++= decls
            wrapper.singletonGraphs ++= decls.collect({
              case x:LocalVarDecl if x.typ.isInstanceOf[SetType] && x.typ.asInstanceOf[SetType].elementType == Ref => x.name
            })
            Seqn(inlinedCall.ss, Seq())(inlinedCall.pos, SimpleInfo(Seq("",s"inlined: create_node(universe = $universe)\n")), inlinedCall.errT)
          }
        else
          call
      case x => genericUpdateNames.get(x) match {
        case Some(field) =>
          //TODO need to find out, which update method to use
          val copier = StrategyBuilder.Slim[Node](PartialFunction.empty).duplicateEverything
          val fieldName = field.name
          val $$Name = OuroborosNames.getIdentifier("$$")
          val unlinkMethodName = OuroborosNames.getIdentifier(s"unlink_$fieldName")
          val applyNoExitName = OuroborosNames.getIdentifier(s"apply_noExit")
          val linkMethodName = OuroborosNames.getIdentifier(s"link_$fieldName")
          val $$Function = input.findFunction($$Name)
          val unlinkMethod = input.findMethod(unlinkMethodName)
          val applyNoExitFunction = input.findDomainFunction(applyNoExitName)
          val linkMethod = input.findMethod(linkMethodName)
          val universe = OuroborosHelper.transformAndFold[String, Exp](
              wrapper.allExistingGraphs().toSeq,
              EmptySet(Ref)(),
              (foldedGraphs, graph) => AnySetUnion(foldedGraphs, graph)(),
              graphName => LocalVar(graphName)(SetType(Ref))
          )

          val unlinkMethodCall = MethodCall(
            unlinkMethod,
            call.args.collect({
              case arg if call.args.indexOf(arg) + 1 < call.args.size => copier.execute[Exp](arg)
            }),
            Seq()
          )(call.pos, call.info, call.errT) //TODO own errT

          val applyNoExitFuncInhale = Inhale(
            DomainFuncApp(applyNoExitFunction, Seq(
              FuncApp($$Function, Seq(copier.execute[Exp](universe)))(call.pos, call.info, call.errT),
              universe,
              ExplicitSet(Seq(copier.execute[Exp](call.args(1))))()
            ), Map.empty[TypeVar, Type])(call.pos, call.info, call.errT)
          )(call.pos, call.info, call.errT)

          val linkMethodCall = MethodCall(
            linkMethod,
            call.args.map(arg => copier.execute[Exp](arg)),
            Seq()
          )(call.pos, call.info, call.errT)

          Seqn(
            Seq(
              unlinkMethodCall,
              applyNoExitFuncInhale,
              linkMethodCall
            ),
            Seq()
          )(call.pos, call.info, call.errT)
        case None => ZOPGUpdateNames.get(x) match {
          case Some(field) =>
            OuroborosMemberInliner.zopgUsed = true
            val copier = StrategyBuilder.Slim[Node](PartialFunction.empty).duplicateEverything
            val fieldName = field.name
            val $$Name = OuroborosNames.getIdentifier("$$")
            val unlinkMethodName = OuroborosNames.getIdentifier(s"unlink_ZOPG_$fieldName")
            val applyNoExitName = OuroborosNames.getIdentifier(s"apply_noExit")
            val linkMethodName = OuroborosNames.getIdentifier(s"link_ZOPG_$fieldName")
            val $$Function = input.findFunction($$Name)
            val unlinkMethod = input.findMethod(unlinkMethodName)
            val applyNoExitFunction = input.findDomainFunction(applyNoExitName)
            val linkMethod = input.findMethod(linkMethodName)
            val universe = OuroborosHelper.transformAndFold[String, Exp](
                wrapper.allExistingGraphs().toSeq,
                EmptySet(Ref)(),
                (foldedGraphs, graph) => AnySetUnion(foldedGraphs, graph)(),
                graphName => LocalVar(graphName)(SetType(Ref))
              )
            val unlinkMethodCall = MethodCall(
              unlinkMethod,
              call.args.collect({
                case arg if call.args.indexOf(arg) + 1 < call.args.size => copier.execute[Exp](arg)
              }),
              Seq()
            )(call.pos, call.info, call.errT) //TODO own errT

            val applyNoExitFuncInhale = Inhale(
              DomainFuncApp(applyNoExitFunction, Seq(
                FuncApp($$Function, Seq(copier.execute[Exp](universe)))(call.pos, call.info, call.errT),
                universe,
                ExplicitSet(Seq(copier.execute[Exp](call.args(1))))()
              ), Map.empty[TypeVar, Type])(call.pos, call.info, call.errT)
            )(call.pos, call.info, call.errT)

            val linkMethodCall = MethodCall(
              linkMethod,
              call.args.map(arg => copier.execute[Exp](arg)),
              Seq()
            )(call.pos, call.info, call.errT)

            Seqn(
              Seq(
                unlinkMethodCall,
                applyNoExitFuncInhale,
                linkMethodCall
              ),
              Seq()
            )(call.pos, call.info, call.errT)

          case None => call
        }
      }
    }
  }

  def handleExhale(exhale: Exhale, wrapper: OuroborosStmtWrapper): Stmt = { //TODO Fork
    exhale
  }

  def handleInhale(inhale: Inhale, wrapper: OuroborosStmtWrapper): Stmt = {
    def foldFunction(graphName: String, pos: Infoed with Positioned): (Exp, Exp) => Exp = {
      val graphErrTrafo = OuroborosErrorTransformers.graphErrTrafo(graphName)
      (foldedExp, exp) => And(foldedExp, exp)(pos.pos, pos.info, graphErrTrafo)
    }
    val input : Program = wrapper.input

    inhale.exp match {//TODO insert framing Axioms
      case func: FuncApp => func.funcname match {
        case x if x == OuroborosNames.getIdentifier("GRAPH_decl") =>
          //println("GRAPH_DECL")
          val thisGraph = func.args.head.asInstanceOf[LocalVar]
          wrapper.userDefinedGraphs.put(thisGraph.name, OurGraph)
          val framingFunctions: mutable.Set[Stmt] = wrapper.allExistingGraphs().collect({
            case graphName if graphName != thisGraph.name =>
              val graph: LocalVar = LocalVar(graphName)(SetType(Ref), thisGraph.pos, thisGraph.info, thisGraph.errT)
              val framingFunction = input.findFunction(OuroborosNames.getIdentifier("apply_TCFraming"))
              Inhale(
                FuncApp(framingFunction, Seq(graph, AnySetMinus(thisGraph, graph)()))(thisGraph.pos, thisGraph.info, thisGraph.errT) //TODO setMinus
              )(thisGraph.pos, thisGraph.info, thisGraph.errT)
          })

          val inhaleGraphFunction = Inhale(
            graphHandler.fold_GRAPH(
              thisGraph, input.fields, input, false, true, TrueLit()(), foldFunction(thisGraph.name, thisGraph)
            )
          )(inhale.pos, inhale.info, inhale.errT)
          Seqn(
            inhaleGraphFunction +: framingFunctions.toSeq,
            Seq()
          )(inhale.pos, inhale.info, inhale.errT)
        case x if x == OuroborosNames.getIdentifier("CLOSED_GRAPH_decl") =>
          //println("CLOSED_GRAPH_DECL")
          val thisGraph = func.args.head.asInstanceOf[LocalVar]
          wrapper.userDefinedGraphs.put(thisGraph.name, OurClosedGraph)
          val framingFunctions: Set[Stmt] = /*wrapper.userDefinedGraphs.map(tuple => {
            val graphName = tuple._1
            val graph: LocalVar = LocalVar(graphName)(SetType(Ref), thisGraph.pos, thisGraph.info, thisGraph.errT)
            val framingFunction = input.findFunction(OuroborosNames.getIdentifier("apply_TCFraming"))
            Inhale(
              FuncApp(framingFunction, Seq(graph, AnySetMinus(thisGraph, graph)()))(thisGraph.pos, thisGraph.info, thisGraph.errT) //TODO setMinus
            )(thisGraph.pos, thisGraph.info, thisGraph.errT)
          })*/
          Set() ++ wrapper.allExistingGraphs().collect({
            case graphName if graphName != thisGraph.name =>
              val graph: LocalVar = LocalVar(graphName)(SetType(Ref), thisGraph.pos, thisGraph.info, thisGraph.errT)
              val framingFunction = input.findFunction(OuroborosNames.getIdentifier("apply_TCFraming"))
              Inhale(
                FuncApp(framingFunction, Seq(graph, AnySetMinus(thisGraph, graph)()))(thisGraph.pos, thisGraph.info, thisGraph.errT) //TODO setMinus
              )(thisGraph.pos, thisGraph.info, thisGraph.errT)
          })
          val inhaleGraphFunction = Inhale(
            graphHandler.fold_GRAPH(
              thisGraph, input.fields, input, true, true, TrueLit()(), foldFunction(thisGraph.name, thisGraph)
            )
          )(inhale.pos, inhale.info, inhale.errT)
          Seqn(
            inhaleGraphFunction +: framingFunctions.toSeq,
            Seq()
          )(inhale.pos, inhale.info, inhale.errT)
        case _ => inhale //TODO other cases (Type Invariance)
      }
      case _ => inhale //TODO other cases (Type Invariance)
    }
  }

  def handleFieldAssign(fa: FieldAssign, wrapper: OuroborosStmtWrapper): Stmt = {
    val input = wrapper.input
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

    val allExistingGraphsExp : Exp = OuroborosHelper.transformAndFold[String, Exp](
        wrapper.allExistingGraphs().toSeq,
        EmptySet(Ref)(),
        (foldedGraphs, graph) => AnySetUnion(foldedGraphs, graph)(),
        graphName => LocalVar(graphName)(SetType(Ref))
      )

    val unlinkMethodCall = MethodCall(OuroborosNames.getIdentifier(s"unlink_${fa.lhs.field.name}"), Seq(allExistingGraphsExp, fa.lhs.rcv), Seq())(fa.pos, fa.info, unlinkErrTrafo)
    val linkMethodCall = MethodCall(OuroborosNames.getIdentifier(s"link_${fa.lhs.field.name}"), Seq(allExistingGraphsExp, fa.lhs.rcv, fa.rhs), Seq())(fa.pos, fa.info, linkErrTrafo)

//    val unlinkInlined =
////      if (OuroborosNames.macroNames.contains(unlinkMethodCall.methodName))
////        OuroborosMemberInliner.inlineMethod(unlinkMethodCall, input, unlinkMethodCall.pos, unlinkMethodCall.info, unlinkMethodCall.errT)
////      else
//        unlinkMethodCall
//    val linkInlined =
////      if (OuroborosNames.macroNames.contains(linkMethodCall.methodName))
////        OuroborosMemberInliner.inlineMethod(linkMethodCall, input, linkMethodCall.pos, linkMethodCall.info, linkMethodCall.errT)
////      else
//        linkMethodCall

    Seqn(
      Seq(
//              getOperationalWisdoms(input, m, ctx)(fa.pos, fa.info, unlinkErrTrafo),
        unlinkMethodCall,
        linkMethodCall),
      Seq())(fa.pos, fa.info, unlinkErrTrafo)

  }

  def handleLocalVarAssign(assign: LocalVarAssign, wrapper: OuroborosStmtWrapper): Stmt = {
    assign
  }

  def handleNewStmt(stmt: NewStmt, wrapper: OuroborosStmtWrapper): Stmt = stmt.fields.size match {
    case x if x == wrapper.input.fields.size =>
      val call = MethodCall(OuroborosNames.getIdentifier("new_node"), Seq(), Seq(stmt.lhs))(stmt.pos, stmt.info, stmt.errT)
      handleMethodCall(call, wrapper)
    case _ => stmt
  }

  def TYPE(tuple: (String, Topology with Closedness), input: Program, pos: Infoed with Positioned with TransformableErrors): Seq[Exp] = {
    //TODO Type Invariance Checking
    val ourType: Topology with Closedness = tuple._2
    val name: String = tuple._1
    val fields = input.fields
    ourType match {
      case OurGraph => graphHandler.GRAPH(LocalVar(name)(SetType(Ref), pos.pos, pos.info, pos.errT), fields, input, false, true)
      case OurClosedGraph => graphHandler.GRAPH(LocalVar(name)(SetType(Ref), pos.pos, pos.info, pos.errT), fields, input, true, true)
      case _ => Seq(BoolLit(true)())
    }
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

case class OuroborosStmtWrapper(input: Program, inputGraphs: Map[String, Topology with Closedness], userDefinedGraphs: mutable.Map[String, Topology with Closedness], singletonGraphs: mutable.Set[String], newlyDeclaredVariables: mutable.Set[Declaration])
{
  def copy(): OuroborosStmtWrapper = {
    val inputCopy: Map[String, Topology with Closedness] = Map.empty ++ inputGraphs
    val existingCopy: mutable.Map[String, Topology with Closedness] = mutable.Map.empty ++ userDefinedGraphs
    val singletonCopy: mutable.Set[String] = mutable.Set.empty[String] ++ singletonGraphs
    val newlyDeclaredCopy: mutable.Set[Declaration] = mutable.Set.empty[Declaration] ++ newlyDeclaredVariables
    OuroborosStmtWrapper(input, inputCopy, existingCopy, singletonCopy, newlyDeclaredCopy)
  }

  def allExistingGraphs(): mutable.Set[String] =  singletonGraphs ++ userDefinedGraphs.keySet
}
