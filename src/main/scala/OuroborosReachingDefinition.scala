package viper.silver.plugin

import viper.silver.ast
import viper.silver.ast._
import viper.silver.ast.utility.Rewriter.StrategyBuilder
import viper.silver.plugin.GraphState.GraphState
import viper.silver.plugin.errors.{OuroborosNotSupportedError, OuroborosTypeError}
import viper.silver.plugin.reasons.{ExhaleNotSupportedReason, WrongTypeReason}

import scala.collection.mutable

class OuroborosReachingDefinition {

  val graphHandler = new OuroborosGraphHandler()
  val typeChecker = new OuroborosTypeCheck()

  def handleMethod(method: Method, specs: mutable.Map[String, OurGraphSpec], input: Program): (Method, Seq[OuroborosAbstractVerificationError]) = {

    val (newMethod, maybeWrapper) = method.body match {
      case None =>
        (method, None)
      case Some(body) =>
        val result = handleBody(body, method, specs, input)

        (
          Method(
            method.name,
            method.formalArgs,
            method.formalReturns,
            method.pres,
            method.posts,
            Some(result._1)
          )(
            method.pos,
            method.info,
            method.errT
            //TODO
          ),
          Some(result._2)
        )
    }

    maybeWrapper match {
      case None => (newMethod, mutable.Seq.empty[OuroborosAbstractVerificationError])
      case Some(wrapper) =>
        val stateCopies = wrapper.stateCopies
        var copiedStates: Set[Stmt] = Set()
        val newMethodRewriter = StrategyBuilder.Slim[Node]({
          case m: Method =>
            val decls: Iterable[LocalVarDecl] = stateCopies.values.flatMap(stateCopy => stateCopy.newDecls)
            val newBody = m.body match {
              case None => None
              case Some(seqn) =>
                Some(Seqn(seqn.ss, seqn.scopedDecls ++ decls)(seqn. pos, seqn.info, seqn.errT))
            }
            Method(
              m.name,
              m.formalArgs,
              m.formalReturns,
              m.pres,
              m.posts,
              newBody
            )(
              m.pos,
              m.info,
              m.errT
            )
          case stmt: Stmt if !copiedStates.contains(stmt) && stateCopies.contains(stmt) =>
            val stateCopy: StateCopyWrapper = stateCopies(stmt)
            val stmtsToAdd = stateCopy.newStmts

            copiedStates += stmt
            Seqn(stmtsToAdd :+ stmt, Seq())(stmt.pos, NoInfo, stmt.errT)
        })

        val finalMethod = newMethodRewriter.execute[Method](newMethod)
        (finalMethod, wrapper.errors)
    }

  }

  def handleBody(seqn: Seqn, method: Method, specs: mutable.Map[String, OurGraphSpec], input: Program): (Seqn, OuroborosStateWrapper) = {

    val spec = specs.get(method.name)
    val inputGraphs: Map[String, Topology with Closedness] = spec match {
      case None => Map.empty[String, Topology with Closedness]
      case Some(graphSpec) =>
        val inputs: mutable.Map[String, Topology with Closedness] = mutable.Map.empty[String, Topology with Closedness]
        graphSpec.inputGraphs.foreach(obj => {
          val objDecls = method.formalArgs.filter(p => p.name == obj.name)
          objDecls.size match {
            case 1 =>
              val objDecl = objDecls.head
              inputs.put(objDecl.name, obj.typ)
            case _ => //Should never happen
          }
        })
        Map.empty[String, Topology with Closedness] ++ inputs
    }

    val inputNodes: Map[String, Set[String]] = spec match {
      case None => Map.empty[String, Set[String]]
      case Some(graphSpec) =>
        graphSpec.inputNodes.map(ourNode => (ourNode.name, ourNode.graphs)).toMap
    }


    val programSpecs: Map[String, OurGraphSpec] = Map.empty[String, OurGraphSpec] ++ specs
    val existingGraphs: mutable.Map[String, (Topology with Closedness, LocalVarDecl, Integer)] =
      mutable.Map.empty[String, (Topology with Closedness, LocalVarDecl, Integer)]
    val existingNodes: mutable.Map[String, Set[String]] =
      mutable.Map.empty[String, Set[String]]
    val definitions: mutable.Map[String, mutable.Map[Integer, (Stmt, OuroborosStateWrapper)]] = mutable.Map.empty[String, mutable.Map[Integer, (Stmt, OuroborosStateWrapper)]]
    val errors: mutable.Buffer[OuroborosAbstractVerificationError] = mutable.Buffer.empty[OuroborosAbstractVerificationError]
    val stateCopies: mutable.Map[Stmt, StateCopyWrapper] = mutable.Map.empty[Stmt, StateCopyWrapper]
    val wrapper: OuroborosStateWrapper = OuroborosStateWrapper(input, programSpecs, inputGraphs, inputNodes, stateCopies, existingGraphs, existingNodes, definitions, errors, true)
    val newSeqn = handleSeqn(seqn, wrapper, true) match {
      case s: Seqn => Seqn(s.ss, s.scopedDecls)(s.pos, s.info, s.errT)
      case s => Seqn(Seq(s), Seq())(s.pos, s.info, s.errT)
    }

    (newSeqn, wrapper)
  }

  def handleStmt(stmt: Stmt, wrapper: OuroborosStateWrapper): Stmt = { //TODO check if existingGraphs changes
    stmt match {
      case whileStmt: While => handleWhile(whileStmt, wrapper) //Add type invariants + handle body
      case methodCall: MethodCall => handleMethodCall(methodCall, wrapper) //Type Invariance Checking
      case seqn: Seqn => handleSeqn(seqn, wrapper, false) //visit stmts
      case ifStmt: If => handleIf(ifStmt, wrapper) //Handle existing graphs in thn and els
      case inhale: Inhale => handleInhale(inhale, wrapper) //If state of some graph is changed, type invariance checking
//      case newStmt: NewStmt => handleNewStmt(newStmt, wrapper) //Create new graph only consisting of this Node. TCFraming
      case fieldAssign: FieldAssign => handleFieldAssign(fieldAssign, wrapper) //handleAssignment
      case localVarAssign: LocalVarAssign => handleLocalVarAssign(localVarAssign, wrapper)
      case exhale: Exhale => handleExhale(exhale, wrapper) //Fork. TODO Check Type Invariance? For that we need Protected Graphs
      case _ => stmt

    }
  }

  def handleWhile(whileStmt: While, wrapper: OuroborosStateWrapper): Stmt = {
    val body = whileStmt.body
    val firstBodyWrapper = wrapper.copy(checkType = false)
    val secondBodyWrapper = wrapper.copy(checkType = wrapper.typeCheck)

    val newStmt = handleSeqn(body, firstBodyWrapper, isTop = false)

    secondBodyWrapper.joinAfterWhile(firstBodyWrapper)


    val newBody = handleSeqn(newStmt, secondBodyWrapper, isTop = false)

    wrapper.joinAfterWhile(secondBodyWrapper)
    wrapper.getLastDefinitionValues(secondBodyWrapper)

    val whileInvs: Seq[Exp] = if(wrapper.typeCheck) wrapper.localGraphs.collect({
      case (graphName, (_, initVarDecl, _)) =>
        val initVarName = initVarDecl.name
        wrapper.definitions.get(graphName) match {
          case None =>
            assert(false, "Internal Error.")
            return whileStmt
          case Some(defs) =>
            //TODO maybe, we could preserve the definitions, too in the invariants

            val initVals = defs.keys.map(initVal => {
              val initVar = LocalVar(initVarName)(Int)

              EqCmp(initVar, IntLit(initVal.toInt)())()
            }).toSeq

            val initValsExp = OuroborosHelper.ourFold[Exp](initVals, FalseLit()(), (exp1, exp2) => Or(exp1, exp2)())

            initValsExp
        }
    }).toSeq else Seq()


    While(whileStmt.cond, whileInvs ++ whileStmt.invs, newBody)(whileStmt.pos, whileStmt.info, whileStmt.errT)
  }

  def handleMethodCall(call: MethodCall, wrapper: OuroborosStateWrapper): Stmt = {
    val input = wrapper.input
    val genericLinkNames: mutable.Map[String, Field] = mutable.Map.empty[String, Field] ++ input.fields.map(field => (OuroborosNames.getIdentifier(s"link_${field.name}"), field))
    val ZOPGLinkNames: mutable.Map[String, Field] = mutable.Map.empty[String, Field] ++ input.fields.map(field => (OuroborosNames.getIdentifier(s"link_ZOPG_${field.name}"), field))
    val DAGLinkNames: mutable.Map[String, Field] = mutable.Map.empty[String, Field] ++ input.fields.map(field => (OuroborosNames.getIdentifier(s"link_DAG_${field.name}"), field))

    val genericUnlinkNames: mutable.Map[String, Field] = mutable.Map.empty[String, Field] ++ input.fields.map(field => (OuroborosNames.getIdentifier(s"unlink_${field.name}"), field))
    val ZOPGUnlinkNames: mutable.Map[String, Field] = mutable.Map.empty[String, Field] ++ input.fields.map(field => (OuroborosNames.getIdentifier(s"unlink_ZOPG_${field.name}"), field))
    val DAGUnlinkNames: mutable.Map[String, Field] = mutable.Map.empty[String, Field] ++ input.fields.map(field => (OuroborosNames.getIdentifier(s"unlink_DAG_${field.name}"), field))

    (genericLinkNames ++ ZOPGLinkNames ++ DAGLinkNames).get(call.methodName) match {
      case Some(field) if wrapper.typeCheck =>
        val typ: Topology with Closedness = if(genericLinkNames.contains(call.methodName))
          OurGraph
         else if (DAGLinkNames.contains(call.methodName))
          OurDAG
         else
          OurZOPG

        return handleLinkMethod(call, typ, field, wrapper)
      case _ =>
    }

    (genericUnlinkNames ++ ZOPGUnlinkNames ++ DAGUnlinkNames).get(call.methodName) match {
      case Some(field) if wrapper.typeCheck =>
        val typ: Topology with Closedness = if(genericUnlinkNames.contains(call.methodName))
          OurGraph
        else if (DAGUnlinkNames.contains(call.methodName))
          OurDAG
        else
          OurZOPG

        return handleUnlinkMethod(call, typ, field, wrapper)
      case _ =>
    }

    //We collect all the checked vars, such that we don't check them twice.
    var alreadyCheckedVars: Set[String] = Set()



    //first check types of the targets and assignments to unique values
    val targetChecksAfterCall: Seq[Stmt] = call.targets.collect({
      //If !wrapper.typeCheck, we still need to add the definition to the wrapper.
      case localVar if wrapper.localGraphs.contains(localVar.name) =>
        val assignUniqueValue = addDefinition(call, localVar.name, wrapper)
        val localVarSpecs: (Topology with Closedness, LocalVarDecl, Integer) = wrapper.localGraphs(localVar.name)
        val localVarType = localVarSpecs._1

        if(wrapper.typeCheck) {
          val maybeCheckExp = typeChecker.checkDefinition(localVarType, call, localVar.name, stateCopyNeeded = false, wrapper, Set(), call)

          alreadyCheckedVars += localVar.name

          val asserts = maybeCheckExp match {
            case None =>
              //the type of the method call does not return the wanted Type
              wrapper.errors += OuroborosTypeError(call, WrongTypeReason(call, s"Variable $localVar might not be of wished type after the method call $call."))
              Seq()
            case Some(checkExps) =>
              if (checkExps.isEmpty) {
                //We don't need to add any assertions
                Seq()
              } else {
                //We need to assert the checkExps
                val checkExp = OuroborosHelper.ourFold[Exp](
                  checkExps,
                  TrueLit()(),
                  (exp1, exp2) => And(exp1, exp2)()
                )

                val assertCheck = Assert(checkExp
                )(call.pos,
                  SimpleInfo(Seq("", s"Added assertion to type check MethodCall.", "")),
                  OuroborosErrorTransformers.wrongTypeErrTrafo(call, localVarType)
                )
                Seq(assertCheck)
              }
          }

          assignUniqueValue +: asserts
        } else Seq()
    }).flatten


    val (argChecksBeforeCall, argChecksAfterCall, graphArgs): (Seq[Stmt], Seq[Stmt], Seq[Exp]) = if(wrapper.typeCheck) {
      val method = wrapper.input.findMethod(call.methodName)
      val methodSpec = wrapper.specs(call.methodName)
      val formalArgNames = method.formalArgs.map(_.name)
      val graphArgIndices: Seq[Int] = methodSpec.inputGraphs.collect({
        case ourObject => formalArgNames.indexOf(ourObject.name)
      })

      var resultBeforeCall: Seq[Stmt] = Seq()
      var resultAfterCall: Seq[Stmt] = Seq()
      var resultGraphArgs: Seq[Exp] = Seq()

      for(i <- graphArgIndices) {
        val arg = call.args(i)
        val ourObject = methodSpec.inputGraphs(i)
        val formalType = ourObject.typ
        val setExp = SetExp.getSetExp(arg, wrapper)

        resultGraphArgs :+= setExp.getDuplicateExp(arg.pos, arg.info, arg.errT)

        val checkTypeOfArgBeforeCall = typeChecker.checkTypeOfExp(formalType, arg, wrapper, call)

        val checkTypeOfArgAfterCall = setExp match {
          case setVar: SetVar =>
            //check Type of formalArg is subType of varType after Call
            val varType = setVar.ourType
            val isSubTopology = OurTypes.isSubTopology(formalType, varType)
            val isSubClosedness = OurTypes.isSubClosedness(formalType, varType)

            val checks: Seq[Stmt] = varType match {
              case _ if isSubTopology && isSubClosedness =>
                Seq()
              case _: ZOPG if !formalType.isInstanceOf[ZOPG] =>
                val newBoolName = OuroborosNames.getNewName(s"${setVar.varName}_ZOPG_check")
                val newBoolDecl = LocalVarDecl(newBoolName, Bool)()
                val boolVar = LocalVar(newBoolName)(Bool)
                val assertBool = Assert(boolVar)(call.pos,
                  SimpleInfo(Seq("", s"Checking that ${setVar.varName} is of Type $varType after the method call is not possible.", "")),
                  OuroborosErrorTransformers.ZOPGCheckErrTrafo(arg)
                )

                val assertSeqn = Seqn(Seq(assertBool), Seq(newBoolDecl))()

                Seq(assertSeqn)
              case _ =>
                val dag = varType.isInstanceOf[DAG] && !formalType.isInstanceOf[DAG]
                val closed = varType.isInstanceOf[Closed] && !formalType.isInstanceOf[Closed]
                val zopg = varType.isInstanceOf[ZOPG] && !formalType.isInstanceOf[ZOPG]
                val qpsNeeded = false
                val nonNullNeeded = false
                val newArgExp = setExp.getDuplicateExp(arg.pos, arg.info, arg.errT)
                val checkExp = graphHandler.fold_GRAPH(newArgExp, graphHandler.ref_fields(wrapper.input.fields), wrapper.input, closed, qpsNeeded, nonNullNeeded, dag, zopg, TrueLit()(), (exp1, exp2) => And(exp1, exp2)())
                val assertCheck = Assert(checkExp)(call.pos,
                  SimpleInfo(Seq("", s"Checking that $arg is of type $varType after the method call.", "")),
                  OuroborosErrorTransformers.wrongTypeAfterCallErrTrafo(arg, varType)
                )

                Seq(assertCheck)
            }

            alreadyCheckedVars += setVar.varName
            checks
          case _ =>
            Seq()
        }

        resultBeforeCall ++= checkTypeOfArgBeforeCall
        resultAfterCall ++= checkTypeOfArgAfterCall
      }

      (resultBeforeCall, resultAfterCall, resultGraphArgs)
    } else {
      (Seq(), Seq(), Seq())
    }

    val unionOfGraphArgs: Option[Exp] =
      if(graphArgs.isEmpty)
        None
      else
        Some(OuroborosHelper.ourFold[Exp](graphArgs, ast.EmptySet(Ref)(), (exp1, exp2) => AnySetUnion(exp1, exp2)()))

    val remainingChecksAfterCall: Seq[Stmt] = if(unionOfGraphArgs.isEmpty || !wrapper.typeCheck) {
      //No graph is used in a method call. Hence, we don't need to check the type of any graph.
      Seq()
    }
      else {
      //We need to check the type of all graphs, that intersect with the unionOfGraphArgs
      val union = unionOfGraphArgs.get
      val remainingGraphs = wrapper.localGraphs.collect({
        case (graphName, (graphType, _, _)) if !alreadyCheckedVars.contains(graphName) => (graphName, graphType)
      }) ++ wrapper.inputGraphs.filter(tuple => !alreadyCheckedVars.contains(tuple._1))

      val remainingGraphsChecks: Seq[Stmt] = remainingGraphs.collect( {
        case (graphName, graphType) =>
          val graph = LocalVar(graphName)(SetType(Ref))
          val interSectionNonEmpty = NeCmp(AnySetIntersection(graph, union)(), EmptySet(Ref)())()
          val ifCondition: Exp = wrapper.localGraphs.get(graphName) match {
            case None => interSectionNonEmpty
            case Some((_, initDecl, _)) =>
              val graphDefs = wrapper.definitions(graphName)
              if (graphDefs.contains(0)) {
                //It could be that this graph is not initialized yet.
                // If it is not initialized, we don't need to check its type.
                val initVar = LocalVar(initDecl.name)(Int)
                val isInit = NeCmp(initVar, IntLit(0)())()

                And(isInit, interSectionNonEmpty)()
              } else {
                interSectionNonEmpty
              }
          }

          val maybeAssert: Option[Stmt] = graphType match {
            case _: ZOPG =>
              val newBoolName = OuroborosNames.getNewName(s"${graphName}_ZOPG_check")
              val newBoolDecl = LocalVarDecl(newBoolName, Bool)()
              val boolVar = LocalVar(newBoolName)(Bool)
              val assertBool = Assert(boolVar)(call.pos,
                SimpleInfo(Seq("", s"Checking that $graphName remains of Type $graphType after the method call is not possible.", "")),
                OuroborosErrorTransformers.ZOPGCheckErrTrafo(graph)
              )

              val assertSeqn = Seqn(Seq(assertBool), Seq(newBoolDecl))()
              Some(assertSeqn)
            case _ =>
              val dag = graphType.isInstanceOf[DAG]
              val zopg = graphType.isInstanceOf[ZOPG]
              val closed = graphType.isInstanceOf[Closed]
              val qpsNeeded = false //TODO do we need to check qps?
              val nonNullNeeded = false

              val checks: Seq[Exp] = if(!dag && !closed && !qpsNeeded)
                Seq()
              else
                graphHandler.GRAPH(graph, graphHandler.ref_fields(wrapper.input.fields), wrapper.input, closed, qpsNeeded, nonNullNeeded, dag, zopg)

              if(checks.isEmpty)
                None
              else {
                val checkExp = OuroborosHelper.ourFold[Exp](checks, TrueLit()(), (exp1, exp2) => And(exp1, exp2)())
                val assertCheck = Assert(checkExp)(call.pos,
                  SimpleInfo(Seq("", s"Checking that $graphName is of type $graphType after the method call.", "")),
                  OuroborosErrorTransformers.wrongTypeAfterCallErrTrafo(graph, graphType)
                )

                Some(assertCheck)
              }
          }

          val assertIfNonEmpty = maybeAssert match {
            case None => Seq()
            case Some(assert) =>
              Seq(If(ifCondition, Seqn(Seq(assert), Seq())(), Seqn(Seq(), Seq())())(call.pos, call.info, call.errT))
          }
          assertIfNonEmpty
      }).flatten.toSeq

      remainingGraphsChecks
    }

    if((targetChecksAfterCall ++ remainingChecksAfterCall ++ argChecksAfterCall ++ argChecksBeforeCall).isEmpty || !wrapper.typeCheck) {
      call
    } else {
      val seqStmt = (argChecksBeforeCall :+ call) ++ argChecksAfterCall ++ remainingChecksAfterCall ++ targetChecksAfterCall
      Seqn(seqStmt, Seq())(call.pos, NoInfo, call.errT)
    }
  }

  def replaceGraphUpdateCall(newCall: MethodCall, graph: Exp, from: Exp, to: Option[Exp], wrapper: OuroborosStateWrapper): MethodCall = graph match {
    case LocalVar(graphName) if graphName == OuroborosNames.getIdentifier("UNIVERSE") => from match {
      case LocalVar(fromName) if to.isEmpty || to.get.isInstanceOf[LocalVar] =>
        val toName = if(to.isEmpty) None else Some(to.get.asInstanceOf[LocalVar].name)
        val allNodes = wrapper.inputNodes ++ wrapper.localNodes
        allNodes.get(fromName) match {
          case Some(graphNames) if toName.isEmpty || allNodes.get(toName.get ).contains(graphNames) =>
            //We only replace the graph, if it is an unlink, or if the specified graphs of allNodes are equivalent.
            val localGraphsMapping = wrapper.localGraphs.map({
              case (gName, triple) =>
                val reachingDefs: mutable.Map[Integer, (Stmt, OuroborosStateWrapper)] = wrapper.definitions(gName)
                val graphState: GraphState = if(!reachingDefs.contains(0))
                  GraphState.ALWAYS_INITIALIZED
                else if(reachingDefs.contains(0) && reachingDefs.size == 1)
                  GraphState.NEVER_INITIALIZED
                else
                  GraphState.UNKNOWN

                (gName, (triple._2, graphState))
            })

            val newGraph = OurNode.getGraphExp(graphNames, localGraphsMapping, optimize = true).duplicateMeta((graph.pos, graph.info, graph.errT)).asInstanceOf[Exp]
            val replaceGraphStrategy = StrategyBuilder.Slim[Node]({
              case x: Exp if x == graph => newGraph
            })

            replaceGraphStrategy.execute[MethodCall](newCall)
          case _ =>
            newCall
        }
      case _ =>
        newCall
    }
    case _ =>
      newCall
  }

  def replaceTopologyUpdateCall(
                          call: MethodCall, checkStmtBeforeCall: Seq[Stmt],
                          typ: Topology with Closedness,
                          field: Field,
                          DAGMethod: Method,
                          ZOPGMethod: Method,
                          wrapper: OuroborosStateWrapper) = {
    val graph = call.args.head
    var newCall = call
    var newType = typ
    var newCheckStmtBeforeCall = checkStmtBeforeCall
    if(!typ.isInstanceOf[DAG] && !typ.isInstanceOf[ZOPG]) {
      var newErrorWrapper = wrapper.copyError()
      val checkStmtForDAGBeforeCall = typeChecker.checkTypeOfExp(OurDAG, graph, newErrorWrapper, call)
      if(checkStmtForDAGBeforeCall.isEmpty && newErrorWrapper.errors.size == wrapper.errors.size) {
        newCall = MethodCall(DAGMethod, call.args, Seq())(call.pos, SimpleInfo(Seq("", "Changed from generic update to DAG Update.", "")), call.errT)
        newCheckStmtBeforeCall = checkStmtForDAGBeforeCall //is empty
        newType = OurDAG
      } else {
        newErrorWrapper = wrapper.copyError()
        val checkStmtForZOPGBeforeCall = typeChecker.checkTypeOfExp(OurZOPG, graph, newErrorWrapper, call)
        if(checkStmtForZOPGBeforeCall.isEmpty && newErrorWrapper.errors.size == wrapper.errors.size) {
          OuroborosConfig.zopgUsed = true
          newCall = MethodCall(ZOPGMethod, call.args, Seq())(call.pos, SimpleInfo(Seq("", "Changed from generic update to ZOPG Update.", "")), call.errT)
          newCheckStmtBeforeCall = checkStmtForZOPGBeforeCall //is empty
          newType = OurZOPG
        }
      }
    }

    (newCall, newType, newCheckStmtBeforeCall)
  }

  def handleLinkMethod(call: MethodCall, typ: Topology with Closedness, field: Field, wrapper: OuroborosStateWrapper): Stmt = {
    val updateZOPGInvariantName = OuroborosNames.getIdentifier("update_ZOPG_invariant")
    val updateDAGInvariantName = OuroborosNames.getIdentifier("update_DAG_invariant")
    val input = wrapper.input
    val ZOPGInvFunction = input.findFunction(updateZOPGInvariantName)
    val DAGInvFunction = input.findFunction(updateDAGInvariantName)

    var newCall: MethodCall = call
    var newType: Topology with Closedness = typ

    def callArgsCopy: Seq[Exp] = newCall.args.map(exp => exp.duplicateMeta((exp.pos, exp.info, exp.errT)).asInstanceOf[Exp])
    def ZOPGInvCall(args: Seq[Exp]) = FuncApp(ZOPGInvFunction, args)(call.pos, call.info, call.errT)
    def DAGInvCall(args: Seq[Exp]) = FuncApp(DAGInvFunction, args)(call.pos, call.info, call.errT)
    def graph = newCall.args.head

    val from = newCall.args(1)
    val to = newCall.args.last
    def setGraph = SetExp.getSetExp(graph, wrapper)
    var checkStmtBeforeCall: Seq[Stmt] = typeChecker.checkTypeOfExp(typ, graph, wrapper, call)

    newCall = replaceGraphUpdateCall(newCall, graph, from, Some(to), wrapper)

    val DAGLinkName = OuroborosNames.getIdentifier(s"link_DAG_${field.name}")
    val DAGLinkMethod = wrapper.input.findMethod(DAGLinkName)
    val ZOPGLinkName = OuroborosNames.getIdentifier(s"link_ZOPG_${field.name}")
    val ZOPGLinkMethod = wrapper.input.findMethod(ZOPGLinkName)

    val res = replaceTopologyUpdateCall(newCall, checkStmtBeforeCall, newType, field, DAGLinkMethod, ZOPGLinkMethod, wrapper)
    newCall = res._1
    newType = res._2
    checkStmtBeforeCall = res._3


    var DAGChecked = false
    var ZOPGChecked = false

    var alreadyCheckedGraph: Option[String] = None

    val graphDependentInvs: Seq[Exp] = setGraph match {
      case setVar: SetVar =>
        val closed = setVar.ourType.isInstanceOf[Closed]
        val toInGraph: Seq[Exp] = if(closed) {
          Seq(Implies(NeCmp(to, NullLit()())(), AnySetContains(to, graph)())())
        }
        else Seq()
        alreadyCheckedGraph = Some(setVar.varName)
        val invStmts: Seq[FuncApp] = setVar.ourType match {
          case _ if !OuroborosConfig.update_invariants => Seq()
          case _: Forest =>
            DAGChecked = true
            ZOPGChecked = true
            Seq(ZOPGInvCall(callArgsCopy), DAGInvCall(callArgsCopy))
          case _: DAG =>
            DAGChecked = true
            Seq(DAGInvCall(callArgsCopy))
          case _: ZOPG =>
            ZOPGChecked = true
            Seq(ZOPGInvCall(callArgsCopy))
          case _ => Seq()
        }

        toInGraph ++ invStmts
      case _ =>
        Seq()
    }

    val callDependentInvs: Seq[Exp] = typ match { //Here, we only want to check the update invariant, if the user has told us to
      case _ if !OuroborosConfig.update_invariants => Seq()
      case _: DAG if !DAGChecked=>
        Seq(DAGInvCall(callArgsCopy))
      case _: ZOPG if !ZOPGChecked =>
        Seq(ZOPGInvCall(callArgsCopy))
      case _ =>
        Seq()
    }

    val allGraphs: Map[String, Topology with Closedness] = wrapper.inputGraphs ++ wrapper.localGraphs.map(set => (set._1, set._2._1))

    val remainingChecks: Seq[Stmt] = allGraphs.collect({
      case (graphName, graphType) if alreadyCheckedGraph.isEmpty || alreadyCheckedGraph.get != graphName =>
        def localGraph = LocalVar(graphName)(SetType(Ref))

        val graphContainsFrom = AnySetContains(from, localGraph)()

        def localCallArgs =  localGraph +: callArgsCopy.tail

        val isInit: Seq[Exp] = wrapper.localGraphs.get(graphName) match {
          case None => Seq()
          case Some((_, initDecl, _)) =>
            if(wrapper.definitions(graphName).contains(0)) {
              val initVar = LocalVar(initDecl.name)(Int)
              Seq(NeCmp(initVar, IntLit(0)())())
            } else {
              Seq()
            }
        }
        val cond = OuroborosHelper.ourFold[Exp](graphContainsFrom +: isInit, TrueLit()(), (exp1, exp2) => And(exp1, exp2)())

        val closedCheck: Seq[Exp] = if(graphType.isInstanceOf[Closed]) {
          Seq(Implies(NeCmp(to, NullLit()())(), AnySetContains(to, localGraph)())())
        } else Seq()

        val topoChecks: Seq[Exp] = graphType match {
          case _ if !OuroborosConfig.update_invariants => Seq()
          case _: Forest =>
            Seq(DAGInvCall(localCallArgs), ZOPGInvCall(localCallArgs))
          case _: DAG =>
            Seq(DAGInvCall(localCallArgs))
          case _: ZOPG =>
            Seq(ZOPGInvCall(localCallArgs))
          case _ => Seq()
        }

        val checkExps = closedCheck ++ topoChecks

        val checks = checkExps.map(exp => {
          Assert(exp)(call.pos, exp.info, exp.errT)
        })

        val checkStmt: Seq[Stmt] = if(checks.isEmpty)
          Seq()
        else
          Seq(
            If(cond, Seqn(checks, Seq())(), Seqn(Seq(), Seq())())(call.pos, NoInfo, NoTrafos)
          )

        checkStmt
    }).flatten.toSeq

    val allChecks = checkStmtBeforeCall ++ (graphDependentInvs ++ callDependentInvs).map(exp => Assert(exp)(call.pos, NoInfo, call.errT)) ++ remainingChecks


    Seqn(allChecks :+ newCall, Seq())(call.pos, NoInfo, call.errT)

  }

  def handleUnlinkMethod(call: MethodCall, typ: Topology with Closedness, field: Field, wrapper: OuroborosStateWrapper): Stmt = {
    val input = wrapper.input

    val graph = call.args.head
    val from = call.args.last
    var checkStmtBeforeCall: Seq[Stmt] = typeChecker.checkTypeOfExp(typ, graph, wrapper, call)
    var newCall: MethodCall = call

    newCall = replaceGraphUpdateCall(newCall, graph, from, None, wrapper)

    val DAGUnlinkName = OuroborosNames.getIdentifier(s"unlink_DAG_${field.name}")
    val DAGUnlinkMethod = wrapper.input.findMethod(DAGUnlinkName)
    val ZOPGUnlinkName = OuroborosNames.getIdentifier(s"unlink_ZOPG_${field.name}")
    val ZOPGUnlinkMethod = wrapper.input.findMethod(ZOPGUnlinkName)

    val res = replaceTopologyUpdateCall(newCall, checkStmtBeforeCall, typ, field, DAGUnlinkMethod, ZOPGUnlinkMethod, wrapper)
    newCall = res._1
    checkStmtBeforeCall = res._3
    Seqn(checkStmtBeforeCall :+ newCall, Seq())()
  }

  def handleSeqn(seqn: Seqn, wrapper: OuroborosStateWrapper, isTop: Boolean): Seqn = {
    Seqn(seqn.ss.map(stmt => handleStmt(stmt, wrapper)), seqn.scopedDecls)(seqn.pos, seqn.info, seqn.errT)
  }

  def handleIf(ifStmt: If, wrapper: OuroborosStateWrapper): Stmt = {
    val thnWrapper = wrapper.copy(wrapper.typeCheck)

    val thn = handleSeqn(ifStmt.thn, thnWrapper, false)

    wrapper.getLastDefinitionValues(thnWrapper)
    val elsWrapper = wrapper.copy(wrapper.typeCheck)

    val els = handleSeqn(ifStmt.els, elsWrapper, false)

    wrapper.joinAfterIf(thnWrapper, elsWrapper)

    If(ifStmt.cond, thn, els)(ifStmt.pos, ifStmt.info, ifStmt.errT)
  }


  def handleInhale(inhale: Inhale, wrapper: OuroborosStateWrapper): Stmt = {
    def foldFunction(graphName: String, pos: Infoed with Positioned): (Exp, Exp) => Exp = {
      val graphErrTrafo = OuroborosErrorTransformers.graphErrTrafo(graphName)
      (foldedExp, exp) => And(foldedExp, exp)(pos.pos, pos.info, graphErrTrafo)
    }

    inhale.exp match {
      //TODO insert framing Axioms
      case func: FuncApp =>
        OurTypes.getOurTypeFromFunction(func.funcname) match {
          case Some(ourType) =>
            val thisGraph = func.args.head.asInstanceOf[LocalVar]
            val initVar = func.args.last.asInstanceOf[LocalVar]
            val integerMapping: mutable.Map[Integer, (Stmt, OuroborosStateWrapper)] = mutable.Map.empty[Integer, (Stmt, OuroborosStateWrapper)]
            val fakeDef = LocalVarAssign(LocalVar(thisGraph.name)(SetType(Ref)), LocalVar(thisGraph.name)(SetType(Ref)))()

            integerMapping.put(0, (fakeDef, wrapper.copy()))
            wrapper.localGraphs.put(thisGraph.name, (ourType, LocalVarDecl(initVar.name, Int)(), 0))
            wrapper.definitions.put(thisGraph.name, integerMapping)

            if(wrapper.typeCheck)
              Seqn(Seq(), Seq())(inhale.pos, inhale.info, inhale.errT)
            else
              inhale

          case None =>
            OurTypes.getNodeAndGraphsFromFunctionCall(func) match {
              case None =>
                inhale
              case Some((node, graphs)) =>
                wrapper.localNodes.put(node.name, graphs)
                if(wrapper.typeCheck)
                  Seqn(Seq(), Seq())(inhale.pos, inhale.info, inhale.errT)
                else
                  inhale
            }
        }
      case _ => inhale //TODO other cases (Type checking)
    }
  }

  def handleFieldAssign(assign: FieldAssign, wrapper: OuroborosStateWrapper): Stmt = {
    //We shouldn not have a edge update here, because they are already translated to a method call in the previous step.
    assign
  }

  def handleLocalVarAssign(assign: LocalVarAssign, wrapper: OuroborosStateWrapper): Stmt = {
    val lhs = assign.lhs
    wrapper.localGraphs.get(lhs.name) match {
      case None => assign
      case Some((ourType, initDecl, lastDefVal)) =>


        var allStmts: Seq[Stmt] = Seq()

        if(wrapper.typeCheck) {
          val typeCheckResult = typeChecker.checkTypeOfExp(ourType, assign.rhs, wrapper, assign)
          val assignUniqueValue = addDefinition(assign, lhs.name, wrapper)
          // typeCheckResult is None, if no checks have to be added.
          allStmts =  Seq(assignUniqueValue, assign) ++ typeCheckResult
        }

        val integerMapping: mutable.Map[Integer, (Stmt, OuroborosStateWrapper)] = mutable.Map.empty[Integer, (Stmt, OuroborosStateWrapper)]
        integerMapping.put(lastDefVal + 1, (assign, wrapper.copy()))
        wrapper.definitions.put(lhs.name, integerMapping)
        wrapper.localGraphs.put(lhs.name, (ourType, initDecl, lastDefVal + 1))

        if(wrapper.typeCheck)
          Seqn(allStmts, Seq())(assign.pos, NoInfo, assign.errT)
        else
          assign
    }
  }

  def handleExhale(exhale: Exhale, wrapper: OuroborosStateWrapper): Stmt = {
    val notSupportedError = OuroborosNotSupportedError(exhale,
      ExhaleNotSupportedReason(exhale, "Exhale is not yet supported in the frontend."),
      false
    )

    wrapper.errors += notSupportedError

    exhale
  }

  //puts definition as only definition for definedVarName
  //increments last defined init value in userDefinedGraphs
  //returns assignment statement for setting unique value
  def addDefinition(definition: Stmt, definedVarName: String, wrapper: OuroborosStateWrapper): Stmt = {
    wrapper.localGraphs.get(definedVarName) match {
      case None =>
        assert(false, s"internal Error")
        Seqn(Seq(), Seq())()
      case Some((ourType, initDecl, lastDefVal)) =>
        val assignUniqueValue = LocalVarAssign(LocalVar(initDecl.name)(Int), IntLit(lastDefVal + 1)())(definition.pos, SimpleInfo(Seq("", s"assign unique value ${lastDefVal + 1} to the assignment of $definedVarName.", "")), definition.errT)

        val integerMapping: mutable.Map[Integer, (Stmt, OuroborosStateWrapper)] = mutable.Map.empty[Integer, (Stmt, OuroborosStateWrapper)]
        integerMapping.put(lastDefVal + 1, (definition, wrapper.copy()))
        wrapper.definitions.put(definedVarName, integerMapping)

        wrapper.localGraphs.put(definedVarName, (ourType, initDecl, lastDefVal + 1))

        assignUniqueValue

    }
  }
}
