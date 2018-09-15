package viper.silver.plugin

import viper.silver.ast._
import viper.silver.ast.utility.Rewriter.StrategyBuilder
import viper.silver.plugin.GraphState.GraphState

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

    val universeName = OuroborosNames.getIdentifier("UNIVERSE")
    val unionInputGraphs = OuroborosHelper.transformAndFold[String, Exp](
      inputGraphs.keySet.toSeq,
      EmptySet(Ref)(),
      (union, graph) => AnySetUnion(union, graph)(),
      graphName => LocalVar(graphName)(SetType(Ref))
    )
    val inputGraphsUniverse = LocalVarAssign(LocalVar(universeName)(SetType(Ref)), unionInputGraphs)()


    val localGraphs: mutable.Map[String, GraphIsInit] =
      mutable.Map.empty[String, GraphIsInit]

    val localNodes: mutable.Map[String, Set[String]] = mutable.Map.empty[String, Set[String]]
    //TODO if we have fields of graph type, it will be more complex
    val wrapper: OuroborosStmtWrapper = OuroborosStmtWrapper(input, inputGraphs, localNodes, localGraphs, None, mutable.Map.empty, mutable.Buffer.empty, mutable.Set.empty)
    handleSeqn(seqn, wrapper, true) match {
      case s: Seqn => Seqn(inputGraphsUniverse +: s.ss, (s.scopedDecls) /*++ outputGraphs.values.map(x => x._2)*/)(s.pos, s.info, s.errT)
      case s => Seqn(Seq(inputGraphsUniverse, s), Seq() /*++ outputGraphs.values.map(x => x._2)*/)(s.pos, s.info, s.errT)
    }
  }

  def handleStmt(stmt: Stmt, wrapper: OuroborosStmtWrapper): Stmt = { //TODO check if existingGraphs changes
    val handledStmt = stmt match {
      case whileStmt: While => handleWhile(whileStmt, wrapper) //Add type invariants + handle body
      case methodCall: MethodCall => handleMethodCall(methodCall, wrapper) //Type Invariance Checking
      case seqn: Seqn => handleSeqn(seqn, wrapper, false) //visit stmts
      case ifStmt: If => handleIf(ifStmt, wrapper) //Handle existing graphs in thn and els
      case inhale: Inhale => handleInhale(inhale, wrapper) //If state of some graph is changed, type invariance checking
      case newStmt: NewStmt => handleNewStmt(newStmt, wrapper) //Create new graph only consisting of this Node. TCFraming
      case fieldAssign: FieldAssign => handleFieldAssign(fieldAssign, wrapper) //handleAssignment
      case localVarAssign: LocalVarAssign => handleLocalVarAssign(localVarAssign, wrapper)
      case _ => stmt
      case exhale: Exhale => handleExhale(exhale, wrapper) //Fork. TODO Check Type Invariance? For that we need Protected Graphs
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

    val isInitRewriter = StrategyBuilder.Slim[Node]({
      case funcApp: FuncApp if
        funcApp.funcname == OuroborosNames.getIdentifier("IS_INITIALIZED") &&
          funcApp.args.head.isInstanceOf[LocalVar] =>
        val graph = funcApp.args.head.asInstanceOf[LocalVar]
        wrapper.localGraphs.get(graph.name) match {
          case None if wrapper.inputGraphs.contains(graph.name) =>
            TrueLit()(funcApp.pos, NoInfo, funcApp.errT)
          case None =>
            funcApp
          case Some(GraphIsInit(_, isInitDecl, _)) => isInitDecl.typ match {
            case Int => NeCmp(LocalVar(isInitDecl.name)(Int), IntLit(0)())(funcApp.pos, NoInfo, funcApp.errT)
            case Bool => LocalVar(isInitDecl.name)(Bool, funcApp.pos, NoInfo, funcApp.errT)
          }
        }
    })

    val rewrittenStmt = isInitRewriter.execute[Stmt](handledStmt)

    rewrittenStmt
  }

  def isInit(initDecl: LocalVarDecl): Exp = initDecl.typ match {
    case Bool => LocalVar(initDecl.name)(Bool)
    case Int => NeCmp(LocalVar(initDecl.name)(Int), IntLit(0)())()
  }

  def handleWhile(stmt: While, wrapper: OuroborosStmtWrapper): Stmt = {
    val localGraphs = wrapper.localGraphs



    //Access invariants for fresh nodes
/*    val conditionedgraphInvs: mutable.Iterable[Exp] = wrapper.newlyDeclaredVariables.map(f => {
      val maybeScope = f._1
      val newDecls = f._2
      maybeScope match {
        case None => newDecls.flatMap(a => getGraphPropertiesExceptAccess((a.name, OurGraph), false, false, wrapper.input, stmt, false))
        case Some(scope) => newDecls.flatMap(a => {
          getGraphPropertiesExceptAccess((a.name, OurGraph), false, false, wrapper.input, stmt, false).map(exp =>
            Implies(LocalVar(scope.name)(Bool), exp)(exp.pos, exp.info, exp.errT))
        })
      }
    }).flatten*/

    val graphInvs: mutable.Iterable[Exp] = //conditionedgraphInvs ++
    //Graph Invariants for local Nodes
    localGraphs.flatMap(p => {
      val graphIsInit = p._2
      val initDecl = graphIsInit.isInitDecl
      val graphName = p._1
      val isInitializedExp = isInit(initDecl)
      val isInitialized = graphIsInit.graphState == GraphState.ALWAYS_INITIALIZED
      val graphPropertiesIfInitialized = getGraphPropertiesExceptAccess((graphName, graphIsInit.typ), false, false, wrapper.input, stmt, true)
      if(isInitialized) {
        //We don't need to check, if the graph is Initialized
        graphPropertiesIfInitialized
      } else {
        //We need to check
        graphPropertiesIfInitialized.map(exp =>
          Implies(isInitializedExp, exp)(exp.pos, exp.info, exp.errT))
      }
    }) ++ wrapper.inputGraphs.flatMap(a => {
      getGraphPropertiesExceptAccess(a, false, false, wrapper.input, stmt, true)
    })

    val nodeInvs: Iterable[Exp] = wrapper.localNodes.map({
      case (node, graphs) =>
        val localGraphsMapping = getLocalGraphMapping(wrapper)
        val graphsExp = OurNode.getGraphExp(graphs, localGraphsMapping)
        def nodeVar = LocalVar(node)(Ref)
        val nodeInGraphs = AnySetContains(nodeVar, graphsExp)(stmt.pos, NoInfo, OuroborosErrorTransformers.nodeNotInGraphErrTrafo(
          nodeVar,
          graphsExp
        ))
        val ifNonNull = Implies(NeCmp(nodeVar, NullLit()())(), nodeInGraphs)(stmt.pos, NoInfo, OuroborosErrorTransformers.nodeNotInGraphErrTrafo(
          nodeVar,
          graphsExp
        ))
        ifNonNull
    })

    val universeAccess = graphHandler.GRAPH(universe(stmt.pos), graphHandler.ref_fields(wrapper.input.fields), wrapper.input, false, true, true, false, false)

    val bodyScopeName = OuroborosNames.getNewName("bodyScope")
    val bodyScope = Some(LocalVarDecl(bodyScopeName, Bool)(stmt.pos, stmt.info, stmt.errT))
    val bodyScopeTrue = LocalVarAssign(LocalVar(bodyScopeName)(Bool), TrueLit()())()
    val bodyScopeFalse = LocalVarAssign(LocalVar(bodyScopeName)(Bool), FalseLit()())()
    val bodyWrapper = wrapper.setScopeAndCopyLocalVars(bodyScope)
    val handledBody = handleSeqn(stmt.body, bodyWrapper, false)
    val bodyScopeUsed = wrapper.newlyDeclaredVariables.contains(bodyScope)

    bodyWrapper.localGraphs.collect({
      case (graphName, graphIsInit) if wrapper.localGraphs.contains(graphName) =>
        if(wrapper.localGraphs(graphName) != graphIsInit)
          wrapper.localGraphs.put(graphName, GraphIsInit(graphIsInit.typ, graphIsInit.isInitDecl, GraphState.UNKNOWN))
    })
//    val initBodyScopeWithFalse = if(bodyScopeUsed) Seq(bodyScopeFalse) else Seq()


    val graphsSubsetOfUniverse: Set[Exp with Serializable] = wrapper.localGraphs.map(triple => {
      val graphName = triple._1
      val graphIsInit = triple._2
      val initDecl = graphIsInit.isInitDecl
      val isInitialized = graphIsInit.graphState == GraphState.ALWAYS_INITIALIZED
      val graph = LocalVar(graphName)(SetType(Ref))

      val isInitializedExp = isInit(initDecl)

      val condGraph = if(isInitialized)
        graph
       else
        CondExp(isInitializedExp, graph, EmptySet(Ref)())()

      AnySetSubset(
        condGraph,
        universe(stmt.pos))(stmt.pos,SimpleInfo(Seq(s"Preserve that the universe contains $graphName.", ""))) //TODO ErrorTrafo


    }).toSet ++ wrapper.newlyDeclaredVariables.flatMap(tuple => {
      val scope = tuple._1
      val decls = tuple._2
      decls.map(decl => {
        scope match {
          case None => AnySetContains(
            LocalVar(decl.name)(Ref),
            universe(stmt.pos))(stmt.pos,SimpleInfo(Seq(s"Preserve that the universe contains ${decl.name}.", "")))
          case Some(s) => CondExp(
            LocalVar(s.name)(Bool),
            AnySetContains(
              LocalVar(decl.name)(Ref),
              universe(stmt.pos))(stmt.pos,SimpleInfo(Seq(s"Preserve that the universe contains ${decl.name}.", ""))) ,
            TrueLit()())()

        }
      })
    }) ++ wrapper.inputGraphs.map(tuple => {
      val graphName = tuple._1
      AnySetSubset(
        LocalVar(graphName)(SetType(Ref)),
        universe()
      )()
    })

    val newBody = if(bodyScopeUsed) {
      Seqn(Seq(bodyScopeTrue, handledBody),
        Seq())(handledBody.pos, handledBody.info, handledBody.errT)
    } else {
      handledBody
    }

    val newWhile = While(stmt.cond,
      graphsSubsetOfUniverse.toSeq ++ universeAccess ++
        graphInvs ++ nodeInvs ++ stmt.invs /*++ newConditionedClosedness*/,
      newBody
    )(stmt.pos, stmt.info, stmt.errT)

    val toReturn: Stmt = if(bodyScopeUsed) {
      Seqn(Seq(bodyScopeFalse, newWhile), Seq())()
    } else {
      newWhile
    }

    toReturn
/*    While(stmt.cond,
      graphsSubsetOfUniverse.toSeq ++ universeAccess ++
      graphInvs ++ nodeInvs ++ stmt.invs /*++ newConditionedClosedness*/,
      if (wrapper.newlyDeclaredVariables.get(bodyScope).isDefined) Seqn(Seq(bodyScopeTrue, handledBody),
        Seq())(handledBody.pos, handledBody.info, handledBody.errT) else handledBody
    )(stmt.pos, stmt.info, stmt.errT)*/
  }

  def handleIf(ifStmt: If, wrapper: OuroborosStmtWrapper): Stmt = {
    val thnScopeName = OuroborosNames.getNewName("thnScope")
    val elsScopeName = OuroborosNames.getNewName("elsScope")
    val thnScope = Some(LocalVarDecl(thnScopeName, Bool)(ifStmt.pos, ifStmt.info, ifStmt.errT))
    val elsScope = Some(LocalVarDecl(elsScopeName, Bool)(ifStmt.pos, ifStmt.info, ifStmt.errT))
    val thnScopeTrue = LocalVarAssign(
      LocalVar(thnScopeName)(Bool), TrueLit()()
    )()
    val thnScopeFalse = LocalVarAssign(
      LocalVar(thnScopeName)(Bool), FalseLit()()
    )()
    val elsScopeTrue = LocalVarAssign(
      LocalVar(elsScopeName)(Bool), TrueLit()()
    )()
    val elsScopeFalse = LocalVarAssign(
      LocalVar(elsScopeName)(Bool), FalseLit()()
    )()

    val thnWrapper = wrapper.setScopeAndCopyLocalVars(thnScope)
    val handledThnBlock = handleSeqn(ifStmt.thn, thnWrapper, false)

    wrapper.dontConsiderScopes.add(thnScope)
    val elsWrapper = wrapper.setScopeAndCopyLocalVars(elsScope)
    val handledElsBlock = handleSeqn(ifStmt.els, elsWrapper, false)
    wrapper.dontConsiderScopes.remove(thnScope)

    //If a variable is initialized in thn and in els, we can be sure that it is always initialized after the if block
    thnWrapper.localGraphs.collect({
      case (graphName, graphIsInit) if wrapper.localGraphs.contains(graphName) =>
        val thnState = thnWrapper.localGraphs(graphName).graphState
        val elsState = elsWrapper.localGraphs(graphName).graphState
        if(elsState != thnState) {
          wrapper.localGraphs.put(graphName, GraphIsInit(graphIsInit.typ, graphIsInit.isInitDecl,GraphState.UNKNOWN))
        } else {
          wrapper.localGraphs.put(graphName, graphIsInit)
        }
    })
    val setScopesToFalse = (if(wrapper.newlyDeclaredVariables.contains(thnScope)) Seq(thnScopeFalse) else Seq()) ++
      (if(wrapper.newlyDeclaredVariables.contains(elsScope)) Seq(elsScopeFalse) else Seq())

    if(setScopesToFalse.isEmpty) {
      If(ifStmt.cond,
          handledThnBlock,
          handledElsBlock)(ifStmt.pos, ifStmt.info, ifStmt.errT)
    } else {
      val newIf = If(ifStmt.cond,
        if (wrapper.newlyDeclaredVariables.contains(thnScope))
          Seqn(Seq(thnScopeTrue, handledThnBlock), Seq())()
        else
          handledThnBlock,
        if (wrapper.newlyDeclaredVariables.contains(elsScope))
          Seqn(Seq(elsScopeTrue, handledElsBlock), Seq())()
        else
          handledElsBlock)(ifStmt.pos, ifStmt.info, ifStmt.errT)

      val toReturn = Seqn(setScopesToFalse :+ newIf, Seq())()

      toReturn
    }
  }

  def handleSeqn(seqn: Seqn, wrapper: OuroborosStmtWrapper, isTop: Boolean): Seqn = {
    //var newScopedDecls: mutable.Map[Option[LocalVarDecl],Set[LocalVarDecl]] = mutable.Map.empty[Option[LocalVarDecl],Set[LocalVarDecl]]
    val newSS = seqn.ss.map(s => {
      val newStmt = handleStmt(s, wrapper)
      newStmt
    })
    lazy val newScopedDecls = wrapper.newlyDeclaredVariables.values.flatten ++ wrapper.newlyDeclaredVariables.keySet.collect({
      case Some(x) => x
    })

    lazy val newInitDecls = wrapper.newlyDeclaredInitVariables

    lazy val initFalseStmts = newInitDecls.map(decl => {
      val typ = decl.typ
      val initVal = typ match {
        case Bool => FalseLit()()
        case Int => IntLit(0)()
      }
      LocalVarAssign(LocalVar(decl.name)(typ, decl.pos, decl.info, decl.errT), initVal)(decl.pos, decl.info, decl.errT)
    })
    lazy val scopesFalseStmts: scala.collection.Set[Stmt] = wrapper.newlyDeclaredVariables.keySet.collect({
      case Some(decl) => LocalVarAssign(LocalVar(decl.name)(Bool, decl.pos, decl.info, decl.errT), FalseLit()())(decl.pos, decl.info, decl.errT)
    })
    /*    val newDeclNames = newScopedDecls.values.collect({
      case x: LocalVarDecl => x.name
    })*/

    Seqn(Seq() ++ (if (isTop) scopesFalseStmts ++ initFalseStmts else Seq()) ++ newSS, seqn.scopedDecls ++ (if (isTop) newScopedDecls ++ newInitDecls else Seq()) /*TODO change*/)(seqn.pos, seqn.info, seqn.errT)
  }

  def handleMethodCall(call: MethodCall, wrapper: OuroborosStmtWrapper): Stmt = {
    val input = wrapper.input
    val genericUpdateNames: Map[String, Field] = input.fields.map(field => (OuroborosNames.getIdentifier(s"update_${field.name}"), field)).toMap
    val ZOPGUpdateNames: Map[String, Field] = input.fields.map(field => (OuroborosNames.getIdentifier(s"update_ZOPG_${field.name}"), field)).toMap
    val DAGUpdateNames: Map[String, Field] = input.fields.map(field => (OuroborosNames.getIdentifier(s"update_DAG_${field.name}"), field)).toMap
    call.methodName match {
      case x if x == OuroborosNames.getIdentifier("NEW") =>
        val universe = LocalVar(OuroborosNames.getIdentifier("UNIVERSE"))(SetType(Ref))
        assert(call.targets.size == 1) //TODO throw correct error
        val node = call.targets.head
        val fresh_x = OuroborosNames.getNewName(s"fresh_$node")
        val fresh_xDecl = LocalVarDecl(fresh_x, Ref)()
        val createCall = MethodCall(OuroborosNames.getIdentifier("create_node"), Seq(universe), Seq(LocalVar(fresh_x)(Ref)))(call.pos, call.info, call.errT)
        val nodeAssign = LocalVarAssign(node, LocalVar(fresh_x)(Ref))(call.pos, call.info, call.errT)

        val framingAxioms = getFramingAxioms(ExplicitSet(Seq(node.duplicateMeta((node.pos, node.info, node.errT)).asInstanceOf[Exp]))(), input, wrapper)

        wrapper.newlyDeclaredVariables.get(wrapper.scope) match {
          case None => wrapper.newlyDeclaredVariables.put(wrapper.scope, Set(fresh_xDecl))
          case Some(decls) => wrapper.newlyDeclaredVariables.put(wrapper.scope, decls + fresh_xDecl)
        }

        val newUniverse = AnySetUnion(universe.duplicateMeta((NoPosition, NoInfo, NoTrafos)).asInstanceOf[Exp], ExplicitSet(Seq(node.duplicateMeta((node.pos, node.info, node.errT)).asInstanceOf[Exp]))() )()
        val newUniverseAssign = LocalVarAssign(universe.duplicateMeta((NoPosition, NoInfo, NoTrafos)).asInstanceOf[LocalVar], newUniverse)()

        val nodeCheck = wrapper.localNodes.get(node.name) match {
          case None => Seq()
          case Some(graphs) =>
            val nodeCopy = node.duplicateMeta((node.pos, node.info, node.errT)).asInstanceOf[LocalVar]
            val localGraphsMapping: mutable.Map[String, (LocalVarDecl, GraphState)] = getLocalGraphMapping(wrapper)
            val graphsExp = OurNode.getGraphExp(graphs, localGraphsMapping)
            val nodeInGraphs = AnySetContains(nodeCopy, graphsExp)()
            val assertContains = Assert(nodeInGraphs)(call.pos,
              SimpleInfo(Seq("", s"Assert that $node stays in the graph $graphsExp.", "")),
              OuroborosErrorTransformers.nodeNotInGraphErrTrafo(node, graphsExp))
            Seq(assertContains)
        }

        Seqn(
          Seq(createCall, nodeAssign, framingAxioms, newUniverseAssign) ++ nodeCheck,
          Seq()
        )(call.pos, SimpleInfo(Seq("", s"$node := NEW()", "")), call.errT)

      case methodName => (genericUpdateNames ++ ZOPGUpdateNames ++ DAGUpdateNames).get(methodName) match {
        case Some(field) =>
          if (ZOPGUpdateNames.contains(methodName)) OuroborosConfig.zopgUsed = true
          val copier = StrategyBuilder.Slim[Node](PartialFunction.empty).duplicateEverything
          val fieldName = field.name
          val methodNames = if (genericUpdateNames.contains(methodName))
            (OuroborosNames.getIdentifier(s"unlink_$fieldName"),
              OuroborosNames.getIdentifier(s"link_$fieldName"))
          else if (ZOPGUpdateNames.contains(methodName))
            (OuroborosNames.getIdentifier(s"unlink_ZOPG_$fieldName"),  OuroborosNames.getIdentifier(s"link_ZOPG_$fieldName"))
          else
            (OuroborosNames.getIdentifier(s"unlink_DAG_$fieldName"),  OuroborosNames.getIdentifier(s"link_DAG_$fieldName"))

          val invariantFunctionName = if(OuroborosConfig.update_invariants)
            if (ZOPGUpdateNames.contains(methodName))
              Some(OuroborosNames.getIdentifier("update_ZOPG_invariant"))
            else if (DAGUpdateNames.contains(methodName))
              Some(OuroborosNames.getIdentifier("update_DAG_invariant"))
            else
              None
          else
            None


          val unlinkMethod = input.findMethod(methodNames._1)
          val linkMethod = input.findMethod(methodNames._2)
          val invariantFunction = if(invariantFunctionName.isDefined)
            Some(input.findFunction(invariantFunctionName.get))
          else
            None

          val unlinkMethodCall = MethodCall(
            unlinkMethod,
            call.args.init.map(arg => copier.execute[Exp](arg)),
            Seq()
          )(call.pos, call.info, call.errT) //TODO own errT

          val noExitInhale = getNoExitAxioms(ExplicitSet(Seq(copier.execute[Exp](call.args(1))))(), input, wrapper)


          val unlinkIfFieldIsNonNull = If(
            NeCmp(
              FieldAccess(unlinkMethodCall.args.last, field)(call.pos, call.info, call.errT),
              NullLit()(call.pos, call.info, call.errT)
            )(call.pos, call.info, call.errT),
            Seqn(Seq(unlinkMethodCall/*, noExitInhale*/), Seq())(call.pos, call.info, call.errT),
            Seqn(Seq(), Seq())(call.pos, call.info, call.errT))(call.pos, call.info, call.errT) //TODO own errT
          //val framingAxioms = getFramingAxioms(call.args.head, input, wrapper)

          val invariantFuncAppAssertion = if(invariantFunction.isDefined) Some(Assert(
            FuncApp(
              invariantFunction.get,
              call.args.map(arg => copier.execute[Exp](arg))
            )()
          )(call.pos, SimpleInfo(Seq("", s"Inserted invariant that is needed to preserve graph property after update.", "")), call.errT)) //TODO errT
          else None

          val linkMethodCall = MethodCall(
            linkMethod,
            call.args.map(arg => copier.execute[Exp](arg)),
            Seq()
          )(call.pos, call.info, call.errT)

          val linkIfRhsIsNonNull = If(
            NeCmp(
              copier.execute[Exp](linkMethodCall.args.last),
              NullLit()(call.pos, call.info, call.errT)
            )(call.pos, call.info, call.errT),
            Seqn(Seq(linkMethodCall), Seq())(call.pos, call.info, call.errT),
            Seqn(Seq(), Seq())(call.pos, call.info, call.errT)
          )(call.pos, call.info, call.errT) //TODO errTrafo

          val seqOfStmts = if(invariantFuncAppAssertion.isDefined)
            Seq(unlinkMethodCall/*, noExitInhale*/, invariantFuncAppAssertion.get, linkMethodCall)
          else
            Seq(unlinkMethodCall/*, noExitInhale*/, linkMethodCall)

          Seqn(
            seqOfStmts,
            Seq()
          )(call.pos, call.info, call.errT)
        case None =>
          val localGraphs = wrapper.localGraphs

          val graphTargets: Seq[(LocalVar, GraphIsInit)] = call.targets.collect({
            case target if localGraphs.contains(target.name) =>
              (target, wrapper.localGraphs(target.name))
          })

          val updateUniverseAndInit = graphTargets.flatMap(tuple => {
            val graphIsInit = tuple._2
            val initDecl = graphIsInit.isInitDecl
            val typ = graphIsInit.typ
            val graph = tuple._1
            wrapper.localGraphs.put(graph.name, GraphIsInit(typ, initDecl, GraphState.ALWAYS_INITIALIZED))
            val initTrue = initDecl.typ match {
              case Bool => Seq(LocalVarAssign(LocalVar(initDecl.name)(Bool), TrueLit()())())
              case Int => Seq()
            }
            //Seq(LocalVarAssign(LocalVar(initDecl.name)(Bool), TrueLit()())(),
            initTrue :+ LocalVarAssign(universe(), AnySetUnion(universe(), LocalVar(graph.name)(SetType(Ref)))())()
            //)
          })

          val targetNames = call.targets.map(v => v.name)
          val nodeChecksNeeded: mutable.Iterable[Stmt] = wrapper.localNodes.flatMap({
            case (node, graphs) =>

              def targetNamesContainsGraphs(graphNames: Set[String]): Boolean =
                graphNames.exists(graphName => targetNames.contains(graphName))

              if(targetNames.contains(node) || targetNamesContainsGraphs(graphs)) {
                val localGraphsMapping: mutable.Map[String, (LocalVarDecl, GraphState)] = getLocalGraphMapping(wrapper)
                val graphsExp = OurNode.getGraphExp(graphs, localGraphsMapping)
                def nodeExp = LocalVar(node)(Ref)
                val nodeInGraphs = AnySetContains(nodeExp, graphsExp)()
                val ifNonNull = Implies(NeCmp(nodeExp, NullLit()())(), nodeInGraphs)()
                val assert = Assert(ifNonNull)(
                  call.pos,
                  SimpleInfo(Seq("", s"Checking that $node still remains in $graphsExp.", "")),
                  OuroborosErrorTransformers.nodeNotInGraphErrTrafo(nodeExp, graphsExp))

                Seq(assert)
              } else {
                Seq()
              }
          })


          if(updateUniverseAndInit.isEmpty)
            call
          else
            Seqn(
              (call +: updateUniverseAndInit) ++ nodeChecksNeeded,
              Seq()
            )(call.pos, SimpleInfo(Seq("", s"enlarge Universe by $graphTargets", "")))
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

    val input: Program = wrapper.input

    inhale.exp match {
      //TODO insert framing Axioms
      case func: FuncApp =>
        OurTypes.getOurTypeFromFunction(func.funcname) match {
          case Some(ourType) =>
            val thisGraph = func.args.head.asInstanceOf[LocalVar]
            val initVarName = OuroborosNames.getNewName(s"${thisGraph}_init")
            val typ = if (OuroborosConfig.type_check) Int else Bool
            val initVarDecl = LocalVarDecl(initVarName, typ)()
            val initToZero = LocalVarAssign(LocalVar(initVarName)(typ),
              if(OuroborosConfig.type_check) IntLit(0)() else FalseLit()()
            )(inhale.pos, SimpleInfo(Seq("", s"Initialize the unique variable of ${thisGraph.name}.", "")), inhale.errT)
            val isInit: GraphState = GraphState.NEVER_INITIALIZED
            val graphIsInit = GraphIsInit(ourType, initVarDecl, isInit)

            lazy val newTypeDeclFuncApp = FuncApp(func.funcname, func.args ++ Seq(LocalVar(initVarName)(Int)))(NoPosition, NoInfo, Bool, Seq(), NoTrafos) //TODO check if this causes error
            lazy val newInhale = Inhale(newTypeDeclFuncApp)()

            //val framingFunctions = getFramingAxioms(thisGraph, input, wrapper)
            wrapper.localGraphs.put(thisGraph.name, graphIsInit)
            wrapper.newlyDeclaredInitVariables += initVarDecl

            if(OuroborosConfig.type_check)
              Seqn(Seq(newInhale, initToZero), Seq())(inhale.pos, inhale.info, inhale.errT)
            else
             Seqn(Seq(initToZero),Seq())(inhale.pos, inhale.info, inhale.errT)
          case None =>
            OurTypes.getNodeAndGraphsFromFunctionCall(func) match {
              case None =>
                inhale
              case Some((node, graphs)) =>
                wrapper.localNodes.put(node.name, graphs)
                val localGraphsMapping: mutable.Map[String, (LocalVarDecl, GraphState)] = getLocalGraphMapping(wrapper)
                val graphExp = OurNode.getGraphExp(graphs, localGraphsMapping)
                val nodeInGraph = AnySetContains(node, graphExp)(func.pos, NoInfo, func.errT)
                val ifNonNull = Implies(NeCmp(node, NullLit()())(), nodeInGraph)(func.pos, NoInfo, func.errT)
                val assumeNodeInGraphs = Inhale(ifNonNull)(inhale.pos, SimpleInfo(Seq("", s"Assuming that $node is in $graphExp.", "")), inhale.errT)
                if(OuroborosConfig.type_check)
                  Seqn(Seq(inhale, assumeNodeInGraphs), Seq())(inhale.pos, inhale.info, inhale.errT)
                else
                  assumeNodeInGraphs
            }
        }
      case _ => inhale //TODO other cases (Type Invariance)
    }
  }

  def handleFieldAssign(fa: FieldAssign, wrapper: OuroborosStmtWrapper): Stmt = {
    val input = wrapper.input

    fa.lhs.field.typ match {
      case Ref =>
        val field = fa.lhs.field
        val updateName = OuroborosNames.getIdentifier(s"update_${field.name}")
        val updateMethod = input.findMethod(updateName)
        val updateMethodCall: MethodCall = MethodCall(updateMethod, Seq(universe(), fa.lhs.rcv, fa.rhs), Seq())(
          fa.pos, SimpleInfo(Seq("", "Changed from field Assign to Method Call.", "")), fa.errT)

          handleMethodCall(updateMethodCall, wrapper)
      case _ => fa
    }

  }

  def handleLocalVarAssign(assign: LocalVarAssign, wrapper: OuroborosStmtWrapper): Stmt = {

    val lhs = assign.lhs
    wrapper.localGraphs.get(lhs.name) match {
      case Some(graphIsInit) =>
        val initDecl = graphIsInit.isInitDecl
        wrapper.localGraphs.put(lhs.name, GraphIsInit(graphIsInit.typ, initDecl, GraphState.ALWAYS_INITIALIZED))
        val framingAxioms = getFramingAxioms(LocalVar(lhs.name)(SetType(Ref)), wrapper.input, wrapper)
        val nodeChecks: Iterable[Stmt] = wrapper.localNodes.collect({
          case (nodeName, graphs) if graphs.contains(lhs.name) =>
            val localGraphsMapping: mutable.Map[String, (LocalVarDecl, GraphState)] = getLocalGraphMapping(wrapper)
            val graphsExp = OurNode.getGraphExp(graphs, localGraphsMapping)
            val nodeExp = LocalVar(nodeName)(Ref)
            val nodeInGraph = AnySetContains(nodeExp, graphsExp)()
            val ifNonNull = Implies(NeCmp(nodeExp, NullLit()())(), nodeInGraph)()

            Assert(ifNonNull)(
              assign.pos, SimpleInfo(Seq("", s"Check that $lhs is still in $graphs", "")),
              OuroborosErrorTransformers.nodeNotInGraphErrTrafo(nodeExp, graphsExp)
            )
        })

        val initTrue = initDecl.typ match {
          case Bool => Seq(LocalVarAssign(LocalVar(initDecl.name)(Bool),TrueLit()())(
            assign.pos, SimpleInfo(Seq("",s"update Universe and set ${initDecl.name} to true", "")), assign.errT))
          case Int => Seq()
        }
        val newUniverse = LocalVarAssign(universe(), AnySetUnion(universe(), lhs.duplicateMeta((lhs.pos,lhs.info,lhs.errT)).asInstanceOf[LocalVar])())()
        Seqn(
          ((assign +: initTrue) :+ newUniverse) ++ nodeChecks ++ framingAxioms.ss, Seq()
        )(assign.pos, framingAxioms.info, assign.errT)

      case None => wrapper.localNodes.get(lhs.name) match {
        case None =>
          assign
        case Some(graph) =>
          val localGraphsMapping: mutable.Map[String, (LocalVarDecl, GraphState)] = getLocalGraphMapping(wrapper)
          val graphs = OurNode.getGraphExp(graph, localGraphsMapping)
          val lhsInGraph = AnySetContains(LocalVar(lhs.name)(Ref),
            graphs.duplicateMeta((assign.pos, assign.info, assign.errT)).asInstanceOf[Exp])(assign.pos, NoInfo, assign.errT)
          val ifNonNull = Implies(NeCmp(LocalVar(lhs.name)(Ref), NullLit()())(), lhsInGraph)(assign.pos, NoInfo, assign.errT)
          val assert = Assert(ifNonNull)(assign.pos, SimpleInfo(Seq("", s"Check that $lhs is still in $graphs", "")), OuroborosErrorTransformers.nodeNotInGraphErrTrafo(lhs, graphs))
          Seqn(Seq(assign, assert), Seq())(assign.pos, NoInfo, assign.errT)
      }
}
  }

  def handleNewStmt(stmt: NewStmt, wrapper: OuroborosStmtWrapper): Stmt = {
    val ref_fields = graphHandler.ref_fields(wrapper.input.fields)
    def rcvr: LocalVar = stmt.lhs.duplicateMeta((stmt.lhs.pos, stmt.lhs.info, stmt.lhs.errT)).asInstanceOf[LocalVar]
    stmt.fields match {
      case x if ref_fields.forall(x.contains(_)) =>
        val call = MethodCall(OuroborosNames.getIdentifier("NEW"), Seq(), Seq(stmt.lhs))(stmt.pos, stmt.info, stmt.errT) //TODO get field access to other fields
        val newNodeRefFields = handleMethodCall(call, wrapper)
        val accessToNotRefFields = x.collect({
          case field if !ref_fields.contains(field) =>
            FieldAccessPredicate(FieldAccess(rcvr, field)(), FullPerm()())()
        })

        if(accessToNotRefFields.isEmpty) {
          newNodeRefFields
        } else {
          val accessExp = OuroborosHelper.ourFold[Exp](
            accessToNotRefFields,
            TrueLit()(),
            (exp1, exp2) => And(exp1, exp2)()
          )
          val inhaleExp = Inhale(accessExp)(stmt.pos, SimpleInfo(Seq("","Inhaling access permissions for all non Node Fields.", "")),stmt.errT)
          Seqn(Seq(newNodeRefFields, inhaleExp), Seq())()
        }
      case _ =>
        val assertFalse = Assert(FalseLit()())(stmt.pos,
          SimpleInfo(Seq("", "new statements need at least access to all reference typed fields.", "")), OuroborosErrorTransformers.newStmtNotHandledErrTrafo())
        Seqn(Seq(assertFalse, stmt), Seq())()
    }
  }

  def getGraphPropertiesExceptAccess(tuple: (String, Topology with Closedness), qpsNeeded: Boolean, noNullNeeded: Boolean, input: Program, pos: Infoed with Positioned with TransformableErrors, isSetType: Boolean): Seq[Exp] = {
    val ourType: Topology with Closedness = tuple._2
    val name: String = tuple._1
    def graph = if(isSetType)
      LocalVar(name)(SetType(Ref), pos.pos, pos.info, pos.errT)

    else
      ExplicitSet(Seq(LocalVar(name)(Ref)))(pos.pos, pos.info, pos.errT)
      graphHandler.GRAPH(graph, graphHandler.ref_fields(input.fields), input, ourType.isInstanceOf[Closed], qpsNeeded, noNullNeeded, ourType.isInstanceOf[DAG], false)//ourType.isInstanceOf[ZOPG]) We do not want to check isZOPG, as this will probably fail
  }

  def getNoExitAxioms(thisGraph: Exp, input: Program, wrapper: OuroborosStmtWrapper): Seqn = {
    val noExitFunction = input.findDomainFunction(OuroborosNames.getIdentifier("apply_noExit"))
    val $$Function = input.findFunction(OuroborosNames.getIdentifier("$$"))
    val allGraphsMapping = wrapper.allGraphsMapping()
    val noneGraphs: Seq[Exp] = allGraphsMapping.get(None) match {
      case None => Seq()
      case Some(graphs) => graphs.toSeq
    }
    val newAllScopes = (allGraphsMapping.keySet &~ wrapper.dontConsiderScopes) - None
    val noneAxioms = {
      val allGraphCombinations = (1 to noneGraphs.size).flatMap(no => noneGraphs.combinations(no))
      allGraphCombinations.map(graphNames => {
        val graphUnion = OuroborosHelper.ourFold[Exp](
          graphNames,
          EmptySet(Ref)(),
          (union, graph) => AnySetUnion(union, graph)()
        )
        Inhale(
          DomainFuncApp(
            noExitFunction,
            Seq(
              FuncApp($$Function,Seq(graphUnion))(),
              universe(),
              thisGraph
            ),
            Map.empty[TypeVar, Type])()
        )()
      })
    }

    val condAxioms = {
      val newAllScopeSubsets = (1 to newAllScopes.size).flatMap(no => newAllScopes.toSeq.combinations(no))
      val toReturn: Seq[Stmt] = newAllScopeSubsets.map(trues => {

        val graphsByScope = trues.map(scope => allGraphsMapping(scope))
        val newTrueGraphs: Set[Exp] = graphsByScope.flatten.toSet ++ noneGraphs
        val newTrueGraphsSubsets = newTrueGraphs.subsets().collect({
          case subset if
          graphsByScope.forall(scopeGraphs => scopeGraphs.intersect(subset).nonEmpty) =>
            val unionOfSubset = OuroborosHelper.ourFold[Exp](
              subset.toSeq,
              EmptySet(Ref)(),
              (union, graph) => AnySetUnion(union, graph)()
            )
            DomainFuncApp(noExitFunction, Seq(FuncApp($$Function, Seq(unionOfSubset))(), universe(), thisGraph), Map.empty[TypeVar, Type])()

        })

        val andExp = OuroborosHelper.ourFold[Exp](newTrueGraphsSubsets.toSeq, FalseLit()(), (and, funcApp) => And(and, funcApp)())
        getExpOfTruesAndFalses(trues, Seq()) match {
          case None => Inhale(andExp)()
          case Some(exp) => Inhale(Implies(exp, andExp)())()
        }
      })
      toReturn
    }

    Seqn(
      noneAxioms ++ condAxioms
      /*conditionedAxioms.toSeq*/,
      Seq()
    )(info = SimpleInfo(Seq("", "insert NoExit Axioms for combinations of sets", "")))
  }

  def getFramingAxioms(thisGraph: Exp, input: Program, wrapper: OuroborosStmtWrapper) = {
    val framingFunction = input.findFunction(OuroborosNames.getIdentifier("apply_TCFraming"))
    val inputGraphsFramingFunctions = wrapper.inputGraphs.map(tuple => {
      val graphName = tuple._1
      val graph: LocalVar = LocalVar(graphName)(SetType(Ref), thisGraph.pos, thisGraph.info, thisGraph.errT)
      Inhale(
        FuncApp(framingFunction, Seq(graph, thisGraph))(thisGraph.pos, thisGraph.info, thisGraph.errT)
      )(thisGraph.pos, SimpleInfo(Seq("", s"Apply TC Framing for $graph and $thisGraph", "")), thisGraph.errT)
    })


    val userDefinedFramingFunctions: Iterable[If] = wrapper.localGraphs.map(
      graphSpec => {
        val graphName = graphSpec._1
        val graphIsInit = graphSpec._2
        val graphInit = graphIsInit.isInitDecl
        val typ = graphInit.typ
        val graphInitVar = LocalVar(graphInit.name)(typ)
        val isInit = typ match {
          case Bool => graphInitVar
          case Int => NeCmp(graphInitVar, IntLit(0)())()
        }

        val graph: LocalVar = LocalVar(graphName)(SetType(Ref), thisGraph.pos, thisGraph.info, thisGraph.errT)
        If(
          isInit,
          Seqn(
            Seq(Inhale(
              FuncApp(framingFunction, Seq(graph, thisGraph))(thisGraph.pos, thisGraph.info, thisGraph.errT)
            )(thisGraph.pos, SimpleInfo(Seq("", s"Apply TC Framing for $graph and $thisGraph setminus $graph", "")), thisGraph.errT)),
            Seq())(),
          Seqn(Seq(),Seq())()
        )()
      }
    )

    val newlyDeclaredFramingFunctions: mutable.Iterable[Stmt] = wrapper.newlyDeclaredVariables.collect({
      case tuple if tuple._1.isEmpty => //if scope is None
        val graphs = tuple._2
        graphs.map(graphDecl => {
          val graphName = graphDecl.name
          val node: LocalVar = LocalVar(graphName)(Ref, thisGraph.pos, thisGraph.info, thisGraph.errT)
          val graph: ExplicitSet = ExplicitSet(Seq(node))(thisGraph.pos, thisGraph.info, thisGraph.errT)
          Inhale(
            FuncApp(framingFunction, Seq(graph, thisGraph))(thisGraph.pos, thisGraph.info, thisGraph.errT)
          )(thisGraph.pos, SimpleInfo(Seq("", s"Apply TC Framing for Set($node) and $thisGraph", "")), thisGraph.errT)
        })

      case tuple =>
        val scopeDecl = tuple._1.get
        val graphs = tuple._2
        val framingAxioms: Set[Stmt] = graphs.map(graphDecl => {
          val graphName = graphDecl.name
          val node: LocalVar = LocalVar(graphName)(Ref, thisGraph.pos, thisGraph.info, thisGraph.errT)
          val graph: ExplicitSet = ExplicitSet(Seq(node))(thisGraph.pos, thisGraph.info, thisGraph.errT)
          Inhale(
            FuncApp(framingFunction, Seq(graph, thisGraph))(
              thisGraph.pos, thisGraph.info, thisGraph.errT))(
            thisGraph.pos, SimpleInfo(Seq("", s"Apply TC Framing for Set($node) and $thisGraph", "")), thisGraph.errT)
        })
        Set(If(
          LocalVar(scopeDecl.name)(Bool),
          Seqn(
            framingAxioms.toSeq,
            Seq()
          )(thisGraph.pos, NoInfo, thisGraph.errT),
          Seqn(Seq(), Seq())()
        )(thisGraph.pos, SimpleInfo(Seq("", s"Apply TC Framing for graphs in the scope of ${scopeDecl.name}", "")), thisGraph.errT))
    }).flatten

    val allFramingFunctions = inputGraphsFramingFunctions ++ userDefinedFramingFunctions ++ newlyDeclaredFramingFunctions

    Seqn(allFramingFunctions.toSeq, Seq())(info = SimpleInfo(Seq("", s"Apply TC Framing for $thisGraph with all possible Graphs.", "")))
  }


  def getExpOfTruesAndFalses(trues: Seq[Option[LocalVarDecl]], falses: Seq[Option[LocalVarDecl]]) = {
      lazy val truesExp = OuroborosHelper.transformAndFold[Option[LocalVarDecl], Exp](
        trues,
        TrueLit()(),
        (foldedExp, exp) => And(foldedExp, exp)(),
        {
          case Some(decl) if decl.typ == Bool => LocalVar(decl.name)(Bool)
          case Some(decl) if decl.typ == Int => NeCmp(LocalVar(decl.name)(Int), IntLit(0)())()
        }
      )

      lazy val falsesExp = OuroborosHelper.transformAndFold[Option[LocalVarDecl], Exp](
        falses,
        TrueLit()(),
        (foldedExp, exp) => And(foldedExp, exp)(),
        {
          case Some(decl) if decl.typ == Bool => Not(LocalVar(decl.name)(Bool))()
          case Some(decl) if decl.typ == Int => NeCmp(LocalVar(decl.name)(Int), IntLit(0)())()
        }
      )
      if(falses.isEmpty && trues.isEmpty)
        None
      else if(falses.isEmpty)
        Some(truesExp)
      else if(trues.isEmpty)
        Some(falsesExp)
      else
        Some(
          And(truesExp,
            falsesExp
          )()
        )
  }

  def universe(pos: Position = NoPosition, info: Info = NoInfo, errT: ErrorTrafo = NoTrafos): LocalVar = {
    LocalVar(OuroborosNames.getIdentifier("UNIVERSE"))(SetType(Ref), pos, info, errT)
  }

  def getLocalGraphMapping(wrapper: OuroborosStmtWrapper): mutable.Map[String, (LocalVarDecl, GraphState.GraphState)] = {
    wrapper.localGraphs.map({
      case (gName, GraphIsInit(_, isInitDecl, graphState)) => (gName, (isInitDecl, graphState))
    })
  }
}
