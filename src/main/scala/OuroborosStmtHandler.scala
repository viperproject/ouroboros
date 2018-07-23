package viper.silver.plugin

import viper.silver.ast._
import viper.silver.ast.utility.Rewriter.StrategyBuilder

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
        graphSpec.inputs.foreach(obj => {
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
    val universeGraphDecl = LocalVarDecl(universeName, SetType(Ref))()
    val unionInputGraphs = OuroborosHelper.transformAndFold[String, Exp](
      inputGraphs.keySet.toSeq,
      EmptySet(Ref)(),
      (union, graph) => AnySetUnion(union, graph)(),
      graphName => LocalVar(graphName)(SetType(Ref))
    )
    val inputGraphsUniverse = LocalVarAssign(LocalVar(universeName)(SetType(Ref)), unionInputGraphs)()


    val existingGraphs: mutable.Map[Option[LocalVarDecl], mutable.Map[String, (Topology with Closedness, LocalVarDecl)]] =
      mutable.Map.empty[Option[LocalVarDecl], mutable.Map[String, (Topology with Closedness, LocalVarDecl)]]
    //val initialMap: mutable.Map[String, (Topology with Closedness, LocalVarDecl)] = mutable.Map.empty// ++ inputGraphs
    existingGraphs.put(None, mutable.Map.empty /*++ outputGraphs*/) //TODO if we have fields of graph type, it will be more complex
    val wrapper: OuroborosStmtWrapper = OuroborosStmtWrapper(input, inputGraphs, existingGraphs, mutable.Buffer(None), mutable.Map.empty, mutable.Buffer.empty, mutable.Set.empty)
    handleSeqn(seqn, wrapper, true) match {
      case s: Seqn => Seqn(inputGraphsUniverse +: s.ss, (s.scopedDecls :+ universeGraphDecl) /*++ outputGraphs.values.map(x => x._2)*/)(s.pos, s.info, s.errT)
      case s => Seqn(Seq(inputGraphsUniverse, s), Seq(universeGraphDecl) /*++ outputGraphs.values.map(x => x._2)*/)(s.pos, s.info, s.errT)
    }
  }

  def handleStmt(stmt: Stmt, wrapper: OuroborosStmtWrapper): Stmt = { //TODO check if existingGraphs changes
    stmt match {
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
  }

  def handleWhile(stmt: While, wrapper: OuroborosStmtWrapper): While = {
    val userDefinedGraphs = wrapper.userDefinedGraphs.values.flatten
    val conditionedgraphInvs: mutable.Iterable[Exp] = wrapper.newlyDeclaredVariables.map(f => {
      f._1 match {
        case None => f._2.flatMap(a => getGraphPropertiesExceptAccess((a.name, OurGraph), wrapper.input, stmt))
        case Some(scope) => f._2.flatMap(a => {
          getGraphPropertiesExceptAccess((a.name, OurGraph), wrapper.input, stmt).map(exp => Implies(LocalVar(scope.name)(Bool), exp)(exp.pos, exp.info, exp.errT))
        })
      }
    }).flatten

    val graphInvs: mutable.Iterable[Exp] = conditionedgraphInvs ++ userDefinedGraphs.flatMap(p => {
      val initDecl = p._2._2
      val graphName = p._1
      getGraphPropertiesExceptAccess((graphName, p._2._1), wrapper.input, stmt).map(exp => Implies(LocalVar(initDecl.name)(Bool), exp)(exp.pos, exp.info, exp.errT))
    }) ++ wrapper.inputGraphs.flatMap(a => {
      getGraphPropertiesExceptAccess(a, wrapper.input, stmt)
    })

    val closed = wrapper.input.findFunction(OuroborosNames.getIdentifier("CLOSED"))
    val allScopes = (wrapper.newlyDeclaredVariables.keySet - None) &~ wrapper.dontConsiderScopes
    val allScopeSubsets = allScopes.subsets()

    val graphsSubsetOfUniverse: Set[AnySetSubset] = wrapper.userDefinedGraphs.values.flatMap(tuple => {
      tuple.map(triple => {
        val graphName = triple._1
        val initDecl = triple._2._2
        val graph = LocalVar(graphName)(SetType(Ref))

        AnySetSubset(
          CondExp(LocalVar(initDecl.name)(Bool), graph, EmptySet(Ref)())(),
          universe(stmt.pos))(stmt.pos,SimpleInfo(Seq(s"Preserve that the universe contains $graphName \n"))) //TODO ErrorTrafo

      })
    }).toSet ++ wrapper.newlyDeclaredVariables.flatMap(tuple => {
      val scope = tuple._1
      val decls = tuple._2
      decls.map(decl => {
        scope match {
          case None => AnySetSubset(
            LocalVar(decl.name)(SetType(Ref)),
            universe(stmt.pos))(stmt.pos,SimpleInfo(Seq(s"Preserve that the universe contains ${decl.name} \n")))
          case Some(s) => AnySetSubset(
            CondExp(LocalVar(s.name)(Bool), LocalVar(decl.name)(SetType(Ref)), EmptySet(Ref)())(),
            universe(stmt.pos))(stmt.pos,SimpleInfo(Seq(s"Preserve that the universe contains ${decl.name} \n")))
        }
      })
    }) ++ wrapper.inputGraphs.map(tuple => {
      val graphName = tuple._1
      AnySetSubset(
        LocalVar(graphName)(SetType(Ref)),
        universe()
      )()
    })

    val universeAccess = graphHandler.GRAPH(universe(stmt.pos), graphHandler.ref_fields(wrapper.input.fields), wrapper.input, true, true)

    val bodyScopeName = OuroborosNames.getNewName("bodyScope")
    val bodyScope = Some(LocalVarDecl(bodyScopeName, Bool)(stmt.pos, stmt.info, stmt.errT))
    val bodyScopeTrue = LocalVarAssign(LocalVar(bodyScopeName)(Bool), TrueLit()())()
    val handledBody = handleSeqn(stmt.body, wrapper.setScope(bodyScope), false)

    val inBodyDefinedGraphsSpecs: Set[Exp] = (wrapper.newlyDeclaredVariables.get(bodyScope) match {
      case None => Set()
      case Some(decls) =>
        decls.map(decl => AnySetSubset(CondExp(
          LocalVar(bodyScopeName)(Bool),
          LocalVar(decl.name)(SetType(Ref)),
          EmptySet(Ref)()
        )(), universe())())
    }) ++ (wrapper.userDefinedGraphs.get(bodyScope) match {
      case None => Set()
      case Some(graphMap) =>
        graphMap.flatMap(tuple => {
          val initDecl = tuple._2._2
          val initVar = LocalVar(initDecl.name)(Bool)
          getGraphPropertiesExceptAccess((tuple._1, tuple._2._1), wrapper.input, stmt) :+
            AnySetSubset(CondExp(
              initVar,
              LocalVar(tuple._1)(SetType(Ref)),
              EmptySet(Ref)()
            )(), universe())()
        }
        )
    })

    While(stmt.cond,
      graphsSubsetOfUniverse.toSeq ++ universeAccess ++
      graphInvs.toSeq ++ inBodyDefinedGraphsSpecs ++ stmt.invs /*++ newConditionedClosedness*/,
      if (wrapper.newlyDeclaredVariables.get(bodyScope).isDefined) Seqn(Seq(bodyScopeTrue, handledBody),
        Seq())(handledBody.pos, handledBody.info, handledBody.errT) else handledBody
    )(stmt.pos, stmt.info, stmt.errT)
  }

  def handleIf(ifStmt: If, wrapper: OuroborosStmtWrapper): If = {
    val thnScopeName = OuroborosNames.getNewName("thnScope")
    val elsScopeName = OuroborosNames.getNewName("elsScope")
    val thnScope = Some(LocalVarDecl(thnScopeName, Bool)(ifStmt.pos, ifStmt.info, ifStmt.errT))
    val elsScope = Some(LocalVarDecl(elsScopeName, Bool)(ifStmt.pos, ifStmt.info, ifStmt.errT))
    val thnScopeTrue = LocalVarAssign(
      LocalVar(thnScopeName)(Bool), TrueLit()()
    )()
    val elsScopeTrue = LocalVarAssign(
      LocalVar(elsScopeName)(Bool), TrueLit()()
    )()
    val handledThnBlock = handleSeqn(ifStmt.thn, wrapper.setScope(thnScope), false)

    wrapper.dontConsiderScopes.add(thnScope)
    val handledElsBlock = handleSeqn(ifStmt.els, wrapper.setScope(elsScope), false)
    wrapper.dontConsiderScopes.remove(thnScope)

    If(ifStmt.cond,
      if (wrapper.newlyDeclaredVariables.contains(thnScope))
        Seqn(Seq(thnScopeTrue, handledThnBlock), Seq())()
      else
        handledThnBlock,
      if (wrapper.newlyDeclaredVariables.contains(elsScope))
        Seqn(Seq(elsScopeTrue, handledElsBlock), Seq())()
      else
        handledElsBlock)(ifStmt.pos, ifStmt.info, ifStmt.errT)
  }

  def handleSeqn(seqn: Seqn, wrapper: OuroborosStmtWrapper, isTop: Boolean): Seqn = {
    //var newScopedDecls: mutable.Map[Option[LocalVarDecl],Set[LocalVarDecl]] = mutable.Map.empty[Option[LocalVarDecl],Set[LocalVarDecl]]
    val newSS = seqn.ss.map(s => {
      val newStmt = handleStmt(s, wrapper)
      newStmt
    })
    val newScopedDecls = wrapper.newlyDeclaredVariables.values.flatten ++ wrapper.newlyDeclaredVariables.keySet.collect({
      case Some(x) => x
    })

    val newInitDecls = wrapper.newlyDeclaredInitVariables

    val initFalseStmts = newInitDecls.map(decl => {
      LocalVarAssign(LocalVar(decl.name)(Bool, decl.pos, decl.info, decl.errT), FalseLit()())(decl.pos, decl.info, decl.errT)
    })
    val scopesFalseStmts: scala.collection.Set[Stmt] = wrapper.newlyDeclaredVariables.keySet.collect({
      case Some(decl) => LocalVarAssign(LocalVar(decl.name)(Bool, decl.pos, decl.info, decl.errT), FalseLit()())(decl.pos, decl.info, decl.errT)
    })
    /*    val newDeclNames = newScopedDecls.values.collect({
      case x: LocalVarDecl => x.name
    })*/

    Seqn(Seq() ++ (if (isTop) scopesFalseStmts ++ initFalseStmts else Seq()) ++ newSS, seqn.scopedDecls ++ (if (isTop) newScopedDecls ++ newInitDecls else Seq()) /*TODO change*/)(seqn.pos, seqn.info, seqn.errT)
  }

  def handleMethodCall(call: MethodCall, wrapper: OuroborosStmtWrapper): Stmt = {
    val input = wrapper.input
    val genericUpdateNames: mutable.Map[String, Field] = mutable.Map.empty
    input.fields.map(field => genericUpdateNames.put(OuroborosNames.getIdentifier(s"update_${field.name}"), field))
    val ZOPGUpdateNames: mutable.Map[String, Field] = mutable.Map.empty[String, Field] ++ input.fields.map(field => (OuroborosNames.getIdentifier(s"update_ZOPG_${field.name}"), field))
    val DAGUpdateNames: mutable.Map[String, Field] = mutable.Map.empty[String, Field] ++ input.fields.map(field => (OuroborosNames.getIdentifier(s"update_DAG_${field.name}"), field))
    call.methodName match {
      case x if x == "new_node" =>
        val universe = LocalVar(OuroborosNames.getIdentifier("UNIVERSE"))(SetType(Ref))/*OuroborosHelper.transformAndFold[String, Exp](
          wrapper.allGraphs().toSeq,
          EmptySet(Ref)(),
          (exp1, exp2) => AnySetUnion(exp1, exp2)(),
          graphName => LocalVar(graphName)(SetType(Ref))
        )*/

        val newCall = MethodCall(OuroborosNames.getIdentifier("create_node"), Seq(universe), call.targets)(call.pos, call.info, call.errT)
        if (OuroborosNames.macroNames.contains(newCall.methodName)) {
          val inlinedCall: Seqn = OuroborosMemberInliner.inlineMethodCall(newCall, wrapper.input, call.pos, call.info, call.errT).asInstanceOf[Seqn]
          val decls: mutable.Map[Option[LocalVarDecl], Set[LocalVarDecl]] = mutable.Map.empty

          val singletonGraph = inlinedCall.scopedDecls.filter(p => p.isInstanceOf[LocalVarDecl] && p.asInstanceOf[LocalVarDecl].typ == SetType(Ref)).head
          val newUniverse = AnySetUnion(universe.duplicateMeta((NoPosition, NoInfo, NoTrafos)).asInstanceOf[Exp], LocalVar(singletonGraph.name)(SetType(Ref)) )()
          val newUniverseAssign = LocalVarAssign(universe.duplicateMeta((NoPosition, NoInfo, NoTrafos)).asInstanceOf[LocalVar], newUniverse)()
          val framingAxioms = getFramingAxioms(LocalVar(singletonGraph.name)(SetType(Ref), inlinedCall.pos, NoInfo, inlinedCall.errT), input, wrapper)

          inlinedCall.scopedDecls.collect({
            case x: LocalVarDecl if x.typ == SetType(Ref) =>
              wrapper.newlyDeclaredVariables.get(wrapper.scope.last) match {
                case None => wrapper.newlyDeclaredVariables.put(wrapper.scope.last, Set(x))
                case Some(localVarDecls) => wrapper.newlyDeclaredVariables.put(wrapper.scope.last, localVarDecls + x)
              }
          })

          Seqn((inlinedCall.ss :+ framingAxioms) :+ newUniverseAssign, inlinedCall.scopedDecls.filter(x => x.isInstanceOf[LocalVarDecl] && x.asInstanceOf[LocalVarDecl].typ != SetType(Ref)))(inlinedCall.pos, SimpleInfo(Seq("", s"inlined: create_node(universe = $universe)\n")), inlinedCall.errT)
        }
        else
          call
      case x => (genericUpdateNames ++ ZOPGUpdateNames ++ DAGUpdateNames).get(x) match {
        case Some(field) =>
          //TODO need to find out, which update method to use
          if (ZOPGUpdateNames.contains(x)) OuroborosMemberInliner.zopgUsed = true
          val copier = StrategyBuilder.Slim[Node](PartialFunction.empty).duplicateEverything
          val fieldName = field.name
          val $$Name = OuroborosNames.getIdentifier("$$")
          val methodNames = if (genericUpdateNames.contains(x))
            (OuroborosNames.getIdentifier(s"unlink_$fieldName"), OuroborosNames.getIdentifier(s"link_$fieldName"))
          else if (ZOPGUpdateNames.contains(x))
            (OuroborosNames.getIdentifier(s"unlink_ZOPG_$fieldName"),  OuroborosNames.getIdentifier(s"link_ZOPG_$fieldName"))
          else
            (OuroborosNames.getIdentifier(s"unlink_DAG_$fieldName"),  OuroborosNames.getIdentifier(s"link_DAG_$fieldName"))


          val unlinkMethod = input.findMethod(methodNames._1)
          val linkMethod = input.findMethod(methodNames._2)

          val unlinkMethodCall = MethodCall(
            unlinkMethod,
            call.args.init.map(arg => copier.execute[Exp](arg)), /*
            call.args.collect({
              case arg if call.args.indexOf(arg) + 1 < call.args.size => copier.execute[Exp](arg)
            }),*/
            Seq()
          )(call.pos, call.info, call.errT) //TODO own errT

          val noExitInhale = getNoExitAxioms(ExplicitSet(Seq(copier.execute[Exp](call.args(1))))(), input, wrapper)

          //val framingAxioms = getFramingAxioms(call.args.head, input, wrapper)

          val linkMethodCall = MethodCall(
            linkMethod,
            call.args.map(arg => copier.execute[Exp](arg)),
            Seq()
          )(call.pos, call.info, call.errT)

          Seqn(
            Seq(unlinkMethodCall,
              (noExitInhale /*:+
                framingAxioms */),
              linkMethodCall),
            Seq()
          )(call.pos, call.info, call.errT)
        case None =>
          val userDefinedGraphs = wrapper.allUserDefinedGraphsOfScope(wrapper.scope)
          val graphTargets = call.targets.collect({
            case target if userDefinedGraphs.contains(target.name) =>
              (target, wrapper.getUserDefinedGraphInitDecl(target.name, wrapper.scope).get)
          })
          val updateUniverseAndInit = graphTargets.flatMap(tuple => {
            val initDecl = tuple._2
            val graph = tuple._1
            Seq(LocalVarAssign(LocalVar(initDecl.name)(Bool), TrueLit()())(),
              LocalVarAssign(universe(), AnySetUnion(universe(), LocalVar(graph.name)(SetType(Ref)))())()
            )
          })

          if(updateUniverseAndInit.isEmpty)
            call
          else
            Seqn(
              call +: updateUniverseAndInit,
              Seq()
            )(call.pos, SimpleInfo(Seq("", s"set graphInits to true and enlarge Universe by $graphTargets\n")))
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
            val initVarDecl = LocalVarDecl(initVarName, Bool)()

            val framingFunctions = getFramingAxioms(thisGraph, input, wrapper)
            wrapper.userDefinedGraphs.get(wrapper.scope.last) match {
              case None =>
                val map = mutable.Map.empty[String, (Topology with Closedness, LocalVarDecl)]
                map.put(thisGraph.name, (ourType, initVarDecl))
                wrapper.userDefinedGraphs.put(wrapper.scope.last, map)
              case Some(map) =>
                map.put(thisGraph.name, (ourType, initVarDecl))
            }
            wrapper.newlyDeclaredInitVariables += initVarDecl
            Seqn(Seq(),Seq())(inhale.pos, inhale.info, inhale.errT)
          case None => inhale
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
        val scopes = (wrapper.newlyDeclaredVariables.keySet &~ wrapper.dontConsiderScopes) - None
        val scopeSubsets = scopes.subsets()

          handleMethodCall(MethodCall(updateMethod, Seq(universe(), fa.lhs.rcv, fa.rhs), Seq())(), wrapper)
      case _ => fa
    }

  }

  def handleLocalVarAssign(assign: LocalVarAssign, wrapper: OuroborosStmtWrapper): Stmt = { //TODO Type Invariance


    assign.lhs match{
      case lhs:LocalVar =>
        wrapper.getUserDefinedGraphInitDecl(lhs.name, wrapper.scope) match {
          case None => assign
          case Some(initDecl) =>
            val initTrue = LocalVarAssign(LocalVar(initDecl.name)(Bool), TrueLit()())()
            val newUniverse = LocalVarAssign(universe(), AnySetUnion(universe(), lhs.duplicateMeta((lhs.pos,lhs.info,lhs.errT)).asInstanceOf[LocalVar])())()
            Seqn(
              Seq(assign, initTrue, newUniverse), Seq()
            )(assign.pos, SimpleInfo(Seq("",s"update Universe and set $initDecl to true\n")), assign.errT)
        }
      case _ => assign
    }
  }

  def handleNewStmt(stmt: NewStmt, wrapper: OuroborosStmtWrapper): Stmt = stmt.fields.size match {
    case x if x == wrapper.input.fields.size =>
      val call = MethodCall(OuroborosNames.getIdentifier("new_node"), Seq(), Seq(stmt.lhs))(stmt.pos, stmt.info, stmt.errT)
      handleMethodCall(call, wrapper)
    case _ => stmt
  }

  def getGraphPropertiesExceptAccess(tuple: (String, Topology with Closedness), input: Program, pos: Infoed with Positioned with TransformableErrors): Seq[Exp] = {
    //TODO Type Invariance Checking
    val ourType: Topology with Closedness = tuple._2
    val name: String = tuple._1
    val fields = input.fields
    val acyclicGraphName = OuroborosNames.getIdentifier("acyclic_graph")
    val $$FunctionName = OuroborosNames.getIdentifier("$$")
    val acyclicGraphFunction = input.findDomainFunction(acyclicGraphName)
    val $$Function = input.findFunction($$FunctionName)
    def graph = LocalVar(name)(SetType(Ref), pos.pos, pos.info, pos.errT)
    val closednessProp = ourType match {
      case _: Closed =>
        //graphHandler.GRAPH(LocalVar(name)(SetType(Ref), pos.pos, pos.info, pos.errT), fields, input, true, false)
        Seq(graphHandler.CLOSED(graph, input))
      case _ =>
        //graphHandler.GRAPH(LocalVar(name)(SetType(Ref), pos.pos, pos.info, pos.errT), fields, input, false, false)
        Seq()
    }

    val topologyProp = ourType match {
      case _: DAG =>
        Seq(DomainFuncApp(acyclicGraphFunction, Seq(FuncApp($$Function, Seq(graph))()), Map.empty[TypeVar,Type])(pos.pos, NoInfo, OuroborosErrorTransformers.acyclicGraphErrTrafo(graph))) //TODO ErrorTrafo
      case _ => Seq()
    }
    closednessProp ++ topologyProp
  }

  def getNoExitAxioms(thisGraph: Exp, input: Program, wrapper: OuroborosStmtWrapper): Seqn = {
    val noExitFunction = input.findDomainFunction(OuroborosNames.getIdentifier("apply_noExit"))
    val $$Function = input.findFunction(OuroborosNames.getIdentifier("$$"))
    val allScopes = (wrapper.newlyDeclaredVariables.keySet &~ wrapper.dontConsiderScopes) - None
    val allScopeSubsets = allScopes.subsets()
    val allGraphsMapping = wrapper.allGraphsMapping()
    val newAllScopes = (allGraphsMapping.keySet &~ wrapper.dontConsiderScopes) - None
    val noneAxioms = {
      val noneGraphs: Seq[String] = allGraphsMapping.get(None) match {
        case None => Seq()
        case Some(graphs) => graphs.toSeq
      }
      val allGraphCombinations = (1 to noneGraphs.size).flatMap(no => noneGraphs.combinations(no))
      allGraphCombinations.map(graphNames => {
        val graphUnion = OuroborosHelper.transformAndFold[String, Exp](
          graphNames,
          EmptySet(Ref)(),
          (union, graph) => AnySetUnion(union, graph)(),
          graphName => LocalVar(graphName)(SetType(Ref))
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
        val noneGraphs: Set[String] = allGraphsMapping.get(None) match {
          case None => Set()
          case Some(graphs) => graphs
        }

        val graphsByScope = trues.map(scope => allGraphsMapping(scope))
        val newTrueGraphs: Set[String] = graphsByScope.flatten.toSet ++ noneGraphs
        val newTrueGraphsSubsets = newTrueGraphs.subsets().collect({
          case subset if
          graphsByScope.forall(scopeGraphs => scopeGraphs.intersect(subset).nonEmpty) =>
            val unionOfSubset = OuroborosHelper.transformAndFold[String, Exp](
              subset.toSeq,
              EmptySet(Ref)(),
              (union, graph) => AnySetUnion(union, graph)(),
              graphName => LocalVar(graphName)(SetType(Ref))
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
    )(info = SimpleInfo(Seq("", "insert NoExit Axioms for combinations of sets\n")))
  }

  def getFramingAxioms(thisGraph: Exp, input: Program, wrapper: OuroborosStmtWrapper) = {
    val framingFunction = input.findFunction(OuroborosNames.getIdentifier("apply_TCFraming"))
    val inputGraphsFramingFunctions = wrapper.inputGraphs.map(tuple => {
      val graphName = tuple._1
      val graph: LocalVar = LocalVar(graphName)(SetType(Ref), thisGraph.pos, thisGraph.info, thisGraph.errT)
      Inhale(
        FuncApp(framingFunction, Seq(graph, AnySetMinus(thisGraph, graph)()))(thisGraph.pos, thisGraph.info, thisGraph.errT)
      )(thisGraph.pos, SimpleInfo(Seq("", s"Apply TC Framing for $graph and $thisGraph setminus $graph\n")), thisGraph.errT)
    })


    val userDefinedFramingFunctions = wrapper.userDefinedGraphs.values.flatMap(tuple => {
      tuple.map(graphSpec => {
        val graphName = graphSpec._1
        val graphInit = graphSpec._2._2
        val graphInitVar = LocalVar(graphInit.name)(Bool)
        val graph: LocalVar = LocalVar(graphName)(SetType(Ref), thisGraph.pos, thisGraph.info, thisGraph.errT)
        If(
          graphInitVar,
          Seqn(
            Seq(Inhale(
              FuncApp(framingFunction, Seq(graph, AnySetMinus(thisGraph, graph)()))(thisGraph.pos, thisGraph.info, thisGraph.errT)
            )(thisGraph.pos, SimpleInfo(Seq("", s"Apply TC Framing for $graph and $thisGraph setminus $graph\n")), thisGraph.errT)),
            Seq())(),
          Seqn(Seq(),Seq())()
        )()
      })
    })

    val newlyDeclaredFramingFunctions: mutable.Iterable[Stmt] = wrapper.newlyDeclaredVariables.collect({
      case tuple if tuple._1.isEmpty => //if scope is None
        val graphs = tuple._2
        graphs.map(graphDecl => {
          val graphName = graphDecl.name
          val graph: LocalVar = LocalVar(graphName)(SetType(Ref), thisGraph.pos, thisGraph.info, thisGraph.errT)
          Inhale(
            FuncApp(framingFunction, Seq(graph, AnySetMinus(thisGraph, graph)()))(thisGraph.pos, thisGraph.info, thisGraph.errT)
          )(thisGraph.pos, SimpleInfo(Seq("", s"Apply TC Framing for $graph and $thisGraph setminus $graph\n")), thisGraph.errT)
        })

      case tuple =>
        val scopeDecl = tuple._1.get
        val graphs = tuple._2
        val framingAxioms: Set[Stmt] = graphs.map(graphDecl => {
          val graphName = graphDecl.name
          val graph: LocalVar = LocalVar(graphName)(SetType(Ref), thisGraph.pos, thisGraph.info, thisGraph.errT)
          Inhale(
            FuncApp(framingFunction, Seq(graph, AnySetMinus(thisGraph, graph)()))(
              thisGraph.pos, thisGraph.info, thisGraph.errT))(
            thisGraph.pos, SimpleInfo(Seq("", s"Apply TC Framing for $graph and $thisGraph setminus $graph\n")), thisGraph.errT)
        })
        Set(If(
          LocalVar(scopeDecl.name)(Bool),
          Seqn(
            framingAxioms.toSeq,
            Seq()
          )(thisGraph.pos, NoInfo, thisGraph.errT),
          Seqn(Seq(), Seq())()
        )(thisGraph.pos, SimpleInfo(Seq("", s"Apply TC Framing for graphs in the scope of ${scopeDecl.name}\n")), thisGraph.errT))
    }).flatten

    val allFramingFunctions = inputGraphsFramingFunctions ++ userDefinedFramingFunctions ++ newlyDeclaredFramingFunctions

    Seqn(allFramingFunctions.toSeq, Seq())(info = SimpleInfo(Seq("", s"Apply TC Framing for $thisGraph with all possible Graphs")))
  }

  def getExpOfTruesAndFalses(trues: Seq[Option[LocalVarDecl]], falses: Seq[Option[LocalVarDecl]]) = {
      val truesExp = OuroborosHelper.transformAndFold[Option[LocalVarDecl], Exp](
        trues,
        TrueLit()(),
        (foldedExp, exp) => And(foldedExp, exp)(),
        decl => LocalVar(decl.get.name)(Ref)
      )

      val falsesExp = OuroborosHelper.transformAndFold[Option[LocalVarDecl], Exp](
        falses,
        TrueLit()(),
        (foldedExp, exp) => And(foldedExp, exp)(),
        decl => Not(LocalVar(decl.get.name)(Ref))()
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
}


case class OuroborosStmtWrapper(
                                 input: Program,
                                 inputGraphs: Map[String, Topology with Closedness],
                                 userDefinedGraphs: mutable.Map[Option[LocalVarDecl], mutable.Map[String, (Topology with Closedness, LocalVarDecl)]],
                                 scope: mutable.Buffer[Option[LocalVarDecl]],
                                 newlyDeclaredVariables: mutable.Map[Option[LocalVarDecl], Set[LocalVarDecl]],
                                 newlyDeclaredInitVariables: mutable.Buffer[LocalVarDecl],
                                 dontConsiderScopes: mutable.Set[Option[LocalVarDecl]]
                               )
{

  def setScope(newScope: Option[LocalVarDecl]): OuroborosStmtWrapper = {
    val existingCopy: mutable.Map[Option[LocalVarDecl], mutable.Map[String, (Topology with Closedness, LocalVarDecl)]] = mutable.Map.empty ++ userDefinedGraphs
    OuroborosStmtWrapper(input,inputGraphs, existingCopy, scope :+ newScope, newlyDeclaredVariables, newlyDeclaredInitVariables, dontConsiderScopes)
  }

  def allGraphsMapping(): mutable.Map[Option[LocalVarDecl], Set[String]] = {
    val toReturn: mutable.Map[Option[LocalVarDecl], Set[String]] = newlyDeclaredVariables.map(tuple => (tuple._1, tuple._2.map(decl => decl.name)))
    userDefinedGraphs foreach(tuple =>{
      val scope = tuple._1
      val names = Set() ++ tuple._2.keySet
      toReturn.get(scope) match {
        case None => toReturn.put(scope, names)
        case Some(oldNames) => toReturn.put(scope, oldNames ++ names)
      }
    })

    toReturn.get(None) match {
      case None => toReturn.put(None, inputGraphs.keySet)
      case Some(decls) => toReturn.put(None, decls ++ inputGraphs.keySet)
    }

    toReturn
  }

  def allUserDefinedGraphsOfScope(scopes: mutable.Buffer[Option[LocalVarDecl]]): Set[String] = {
    userDefinedGraphs.collect({
      case tuple if scopes.contains(tuple._1) => tuple._2.keySet
    }).flatten.toSet
  }

  def getUserDefinedGraphInitDecl(graphName: String, scopes: mutable.Buffer[Option[LocalVarDecl]]): Option[LocalVarDecl] = {
    var graphInitDecl: Option[LocalVarDecl] = None
    scopes.reverse.takeWhile(scope => {
      userDefinedGraphs.get(scope) match {
        case None =>
        case Some(declMapping) => declMapping.get(graphName) match {
          case None =>
          case Some(decl) => graphInitDecl = Some(decl._2)
        }
      }

      graphInitDecl.isEmpty
    })

    graphInitDecl
  }
}
