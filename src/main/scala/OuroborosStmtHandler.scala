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

    val inputGraphs: Map[String, Topology with Closedness] = spec match {
      case None => Map.empty[String, Topology with Closedness]
      case Some(graphSpec) =>
        val inputs: mutable.Map[String, Topology with Closedness] = mutable.Map.empty[String, Topology with Closedness]
        graphSpec.inputs.map(obj => {
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


    var existingGraphs: mutable.Map[String, Topology with Closedness] = mutable.Map.empty[String, Topology with Closedness]
    existingGraphs ++= inputGraphs //TODO if we have fields of graph type, it will be more complex
    val wrapper: OuroborosStmtWrapper = OuroborosStmtWrapper(input, inputGraphs, existingGraphs, None, mutable.Map.empty, mutable.Set.empty)
    handleSeqn(seqn, wrapper, true) match {
      case s: Seqn => s
      case s => Seqn(Seq(s), Seq())(s.pos, s.info, s.errT)
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
      case _ => stmt
      case exhale: Exhale => handleExhale(exhale, wrapper) //Fork. TODO Check Type Invariance? For that we need Protected Graphs
      case localVarAssign: LocalVarAssign => handleLocalVarAssign(localVarAssign, wrapper) /*{
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
    val userDefinedGraphs = wrapper.userDefinedGraphs
    val conditionedgraphInvs: mutable.Iterable[Exp] = wrapper.newlyDeclaredVariables.map(f => {
      f._1 match {
        case None => f._2.flatMap(a => TYPE((a.name, OurGraph), wrapper.input, stmt))
        case Some(scope) => f._2.flatMap(a => {
          TYPE((a.name, OurGraph), wrapper.input, stmt).map(exp => Implies(LocalVar(scope.name)(Bool), exp)(exp.pos, exp.info, exp.errT))
        })
      }
    }).flatten
    val graphInvs: mutable.Iterable[Exp] = conditionedgraphInvs ++ userDefinedGraphs.flatMap(a => TYPE(a, wrapper.input, stmt))

    val closed = wrapper.input.findFunction(OuroborosNames.getIdentifier("CLOSED"))
    val allScopes = (wrapper.newlyDeclaredVariables.keySet - None) &~ wrapper.dontConsiderScopes
    val allScopeSubsets = allScopes.subsets()

    val bodyScopeName = OuroborosNames.getNewName("bodyScope")
    val bodyScope = Some(LocalVarDecl(bodyScopeName, Bool)(stmt.pos, stmt.info, stmt.errT))
    val bodyScopeTrue = LocalVarAssign(LocalVar(bodyScopeName)(Bool), TrueLit()())()
    val handledBody = handleSeqn(stmt.body, wrapper.setScopeAndCopyUserDefinedGraphs(bodyScope), false)

    val newlyDefinedGraphSpecs = wrapper.newlyDeclaredVariables.get(bodyScope) match {
      case None => Seq()
      case Some(decls) =>
        decls.map(decl => Implies(
          LocalVar(bodyScopeName)(Bool),
          graphHandler.fold_GRAPH(LocalVar(decl.name)(SetType(Ref)), wrapper.input.fields, wrapper.input, false, true, TrueLit()(), (exp1, exp2) => And(exp1, exp2)(exp1.pos, exp1.info, exp1.errT))
        )())
    }

    val newConditionedClosedness = allScopeSubsets.flatMap(trues => {
      val falses = allScopes &~ trues
      val lhs = getExpOfTruesAndFalses(trues.toSeq, falses.toSeq)

      val unionGraphsWithoutBodyScope = OuroborosHelper.transformAndFold[String, Exp](
        wrapper.userDefinedGraphs.keySet.toSeq ++ {
          wrapper.newlyDeclaredVariables.get(None) match {
            case None => Seq()
            case Some(decls) => decls.map(decl => decl.name)
          }
        } ++
          trues.flatMap(t => wrapper.newlyDeclaredVariables(t).map(va => va.name)),
        EmptySet(Ref)(),
        (foldedGraphs, graph) => AnySetUnion(foldedGraphs, graph)(),
        graphName => LocalVar(graphName)(SetType(Ref))
      )

      val closedWithoutBody = FuncApp(closed, Seq(unionGraphsWithoutBodyScope))()

      wrapper.newlyDeclaredVariables.get(bodyScope) match {
        case None =>
          lhs match {
            case None => Seq(closedWithoutBody)
            case Some(exp) => Seq(Implies(exp, closedWithoutBody)())
          }
        case Some(vars) =>
          val unionGraphsOfBodyScope = OuroborosHelper.transformAndFold[String, Exp](
            wrapper.userDefinedGraphs.keySet.toSeq ++ {
              wrapper.newlyDeclaredVariables.get(None) match {
                case None => Seq()
                case Some(decls) => decls.map(decl => decl.name)
              }
            } ++
              trues.flatMap(t => wrapper.newlyDeclaredVariables(t).map(va => va.name)) ++ vars.map(decl => decl.name),
            EmptySet(Ref)(),
            (foldedGraphs, graph) => AnySetUnion(foldedGraphs, graph)(),
            graphName => LocalVar(graphName)(SetType(Ref))
          )
          val unionGraphsWithBodyScope = unionGraphsOfBodyScope//AnySetUnion(unionGraphsWithoutBodyScope, unionGraphsOfBodyScope)()

          val closedWithBody = FuncApp(closed, Seq(unionGraphsWithBodyScope))()
          lhs match {
            case None => Seq(
              Implies(Not(LocalVar(bodyScopeName)(Bool))(), closedWithoutBody)(),
              Implies(LocalVar(bodyScopeName)(Bool), closedWithBody)()
            )

            case Some(exp) => Seq(
              Implies(And(Not(LocalVar(bodyScopeName)(Bool))(), exp)(), closedWithoutBody)(),
              Implies(And(LocalVar(bodyScopeName)(Bool), exp)(), closedWithBody)()
            )
          }
      }
    })

    While(stmt.cond,
      graphInvs.toSeq ++ newlyDefinedGraphSpecs ++ stmt.invs ++ newConditionedClosedness,
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
    val handledThnBlock = handleSeqn(ifStmt.thn, wrapper.setScopeAndCopyUserDefinedGraphs(thnScope), false)

    wrapper.dontConsiderScopes.add(thnScope)
    val handledElsBlock = handleSeqn(ifStmt.els, wrapper.setScopeAndCopyUserDefinedGraphs(elsScope), false)
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
    val scopesFalseStmts: scala.collection.Set[Stmt] = wrapper.newlyDeclaredVariables.keySet.collect({
      case Some(decl) => LocalVarAssign(LocalVar(decl.name)(Bool, decl.pos, decl.info, decl.errT), FalseLit()())(decl.pos, decl.info, decl.errT)
    })
    /*    val newDeclNames = newScopedDecls.values.collect({
      case x: LocalVarDecl => x.name
    })*/

    Seqn(Seq() ++ (if (isTop) scopesFalseStmts else Seq()) ++ newSS, seqn.scopedDecls ++ (if (isTop) newScopedDecls else Seq()) /*TODO change*/)(seqn.pos, seqn.info, seqn.errT)
  }

  def handleMethodCall(call: MethodCall, wrapper: OuroborosStmtWrapper): Stmt = {
    val input = wrapper.input
    val genericUpdateNames: mutable.Map[String, Field] = mutable.Map.empty
    input.fields.map(field => genericUpdateNames.put(OuroborosNames.getIdentifier(s"update_${field.name}"), field))
    val ZOPGUpdateNames: mutable.Map[String, Field] = mutable.Map.empty[String, Field] ++ input.fields.map(field => /*genericUpdateNames.put*/ (OuroborosNames.getIdentifier(s"update_ZOPG_${field.name}"), field))
    call.methodName match {
      case x if x == "new_node" =>
        val universe = OuroborosHelper.transformAndFold[String, Exp](
          wrapper.allGraphs().toSeq,
          EmptySet(Ref)(),
          (exp1, exp2) => AnySetUnion(exp1, exp2)(),
          graphName => LocalVar(graphName)(SetType(Ref))
        )

        val newCall = MethodCall(OuroborosNames.getIdentifier("create_node"), Seq(universe), call.targets)(call.pos, call.info, call.errT)
        if (OuroborosNames.macroNames.contains(newCall.methodName)) {
          val inlinedCall: Seqn = OuroborosMemberInliner.inlineMethod(newCall, wrapper.input, call.pos, call.info, call.errT).asInstanceOf[Seqn]
          val decls: mutable.Map[Option[LocalVarDecl], Set[LocalVarDecl]] = mutable.Map.empty

          val singletonGraph = inlinedCall.scopedDecls.filter(p => p.isInstanceOf[LocalVarDecl] && p.asInstanceOf[LocalVarDecl].typ == SetType(Ref)).head
          val framingAxioms = getFramingAxioms(LocalVar(singletonGraph.name)(SetType(Ref), inlinedCall.pos, NoInfo, inlinedCall.errT), input, wrapper)

          inlinedCall.scopedDecls.collect({
            case x: LocalVarDecl if x.typ == SetType(Ref) =>
              wrapper.newlyDeclaredVariables.get(wrapper.scope) match {
                case None => wrapper.newlyDeclaredVariables.put(wrapper.scope, Set(x))
                case Some(localVarDecls) => wrapper.newlyDeclaredVariables.put(wrapper.scope, localVarDecls + x)
              }
          })

          Seqn(inlinedCall.ss :+ framingAxioms, inlinedCall.scopedDecls.filter(x => x.isInstanceOf[LocalVarDecl] && x.asInstanceOf[LocalVarDecl].typ != SetType(Ref)))(inlinedCall.pos, SimpleInfo(Seq("", s"inlined: create_node(universe = $universe)\n")), inlinedCall.errT)
        }
        else
          call
      case x => (genericUpdateNames ++ ZOPGUpdateNames).get(x) match {
        case Some(field) =>
          //TODO need to find out, which update method to use
          if (ZOPGUpdateNames.contains(x)) OuroborosMemberInliner.zopgUsed = true
          val copier = StrategyBuilder.Slim[Node](PartialFunction.empty).duplicateEverything
          val fieldName = field.name
          val $$Name = OuroborosNames.getIdentifier("$$")
          val unlinkMethodName = if (genericUpdateNames.contains(x))
            OuroborosNames.getIdentifier(s"unlink_$fieldName")
          else
            OuroborosNames.getIdentifier(s"unlink_ZOPG_$fieldName")
          val linkMethodName = if (genericUpdateNames.contains(x))
            OuroborosNames.getIdentifier(s"link_$fieldName")
          else
            OuroborosNames.getIdentifier(s"link_ZOPG_$fieldName")
          val unlinkMethod = input.findMethod(unlinkMethodName)
          val linkMethod = input.findMethod(linkMethodName)

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
        case None => call
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

            val framingFunctions = getFramingAxioms(thisGraph, input, wrapper)
            wrapper.userDefinedGraphs.put(thisGraph.name, ourType)
            val inhaleGraphFunction = Inhale(
              graphHandler.fold_GRAPH(
                thisGraph, input.fields, input, if (ourType.isInstanceOf[Closed]) true else false, true, TrueLit()(), foldFunction(thisGraph.name, thisGraph)
              )
            )(inhale.pos, SimpleInfo(Seq("", s"Register that $thisGraph is of type $ourType, inhale GRAPH($thisGraph) ${if (ourType.isInstanceOf[Closed]) "\n" else s"and CLOSED($thisGraph)\n"}")), inhale.errT)
            Seqn(
              Seq(inhaleGraphFunction, framingFunctions), // +: newFramingFunctions.toSeq,
              Seq()
            )(inhale.pos, inhale.info, inhale.errT)
          case None => inhale
        }
      case _ => inhale //TODO other cases (Type Invariance)
    }
  }

  def handleFieldAssign(fa: FieldAssign, wrapper: OuroborosStmtWrapper): Stmt = {
    val input = wrapper.input
    val unlinkErrTrafo: ErrTrafo = {
      //TODO improve Error messages
      ErrTrafo({
        case x: PreconditionInCallFalse =>
          x.reason match {
            case r: InsufficientPermission => OuroborosAssignmentError(x.offendingNode,
              InsufficientGraphPermission(x.offendingNode, s"There might be insufficient permissiion to get read access to the ${fa.lhs.field.name} fields of all elements in ${x.offendingNode.args.head} " +
                s"and write access to the ${fa.lhs.field.name} field of ${x.offendingNode.args(1)}. Original message: " + x.reason.readableMessage),
              x.cached)

            case r: AssertionFalse => OuroborosAssignmentError(x.offendingNode,
              NotInGraphReason(x.offendingNode, s"${x.offendingNode.args(1)} might not be in ${x.offendingNode.args.head}" +
                s" or null might be in ${x.offendingNode.args.head}. Original message: " + x.reason.readableMessage),
              x.cached)

            case _ => OuroborosAssignmentError(x.offendingNode,
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
            case r: AssertionFalse => OuroborosAssignmentError(x.offendingNode,
              NotInGraphReason(x.offendingNode, s"Assignment Error: ${x.offendingNode.args(2)} might not be in ${x.offendingNode.args.head}. " +
                s"Original Message: ${x.reason.readableMessage}"),
              x.cached)

            case xy => OuroborosAssignmentError(x.offendingNode,
              InternalReason(x.offendingNode, "internal error in link: " + x.reason.readableMessage),
              x.cached)
          }
        case x => x
      })
    }

    fa.lhs.field.typ match {
      case Ref =>
        val field = fa.lhs.field
        val updateName = OuroborosNames.getIdentifier(s"update_${field.name}")
        val updateMethod = input.findMethod(updateName)
        val scopes = (wrapper.newlyDeclaredVariables.keySet &~ wrapper.dontConsiderScopes) - None
        val scopeSubsets = scopes.subsets()
        if (wrapper.newlyDeclaredVariables.keySet.isEmpty || (wrapper.newlyDeclaredVariables.keySet.size == 1 && wrapper.newlyDeclaredVariables.keySet.contains(None))) {
          val universeNames: scala.collection.Set[String] = wrapper.userDefinedGraphs.keySet ++ (wrapper.newlyDeclaredVariables.get(None) match {
            case None => Seq()
            case Some(decls) => decls.map(decl => decl.name)
          })

          val universeExp = OuroborosHelper.transformAndFold[String, Exp](
            universeNames.toSeq,
            EmptySet(Ref)(),
            (graphs, graph) => AnySetUnion(graphs, graph)(),
            graphName => LocalVar(graphName)(SetType(Ref))
          )
          handleMethodCall(MethodCall(updateMethod, Seq(universeExp, fa.lhs.rcv, fa.rhs), Seq())(), wrapper)
        } else {
          val conditionedUpdate = OuroborosHelper.transformAndFold[scala.collection.Set[Option[LocalVarDecl]], If](
            scopeSubsets.toSeq,
            If(TrueLit()(), Seqn(Seq(), Seq())(), Seqn(Seq(), Seq())())(),
            (ifStmt1, ifStmt2) => If(ifStmt2.cond, ifStmt2.thn, Seqn(Seq(ifStmt1), Seq())())(),
            trues => {
              val falses = scopes &~ trues
              val scopesExp = getExpOfTruesAndFalses(trues.toSeq, falses.toSeq).get//if (trues.isEmpty) falsesExp else if (falses.isEmpty) truesExp else And(truesExp, falsesExp)()

              val universeNames: scala.collection.Set[String] = wrapper.userDefinedGraphs.keySet ++ (wrapper.newlyDeclaredVariables.get(None) match {
                case None => Seq()
                case Some(decls) => decls.map(decl => decl.name)
              }) ++ trues.flatMap(t => wrapper.newlyDeclaredVariables(t).map(decl => decl.name))

              val universe = OuroborosHelper.transformAndFold[String, Exp](
                universeNames.toSeq,
                EmptySet(Ref)(),
                (union, graph) => AnySetUnion(union, graph)(),
                graphName => LocalVar(graphName)(SetType(Ref))
              )

              val thnStmt = MethodCall(
                updateMethod,
                Seq(universe, fa.lhs.rcv, fa.rhs),
                Seq()
              )()

              If(scopesExp, Seqn(Seq(thnStmt), Seq())(), Seqn(Seq(), Seq())())()
            }
          )
          handleIf(conditionedUpdate, wrapper)
        }
      case _ => fa
    }

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
      case _: Closed => graphHandler.GRAPH(LocalVar(name)(SetType(Ref), pos.pos, pos.info, pos.errT), fields, input, true, true)
      case _: Closedness => graphHandler.GRAPH(LocalVar(name)(SetType(Ref), pos.pos, pos.info, pos.errT), fields, input, false, true)
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

  def getNoExitAxioms(thisGraph: Exp, input: Program, wrapper: OuroborosStmtWrapper): Seqn = {
    val noExitFunction = input.findDomainFunction(OuroborosNames.getIdentifier("apply_noExit"))
    val $$Function = input.findFunction(OuroborosNames.getIdentifier("$$"))
    val allScopes = (wrapper.newlyDeclaredVariables.keySet &~ wrapper.dontConsiderScopes) - None
    val allScopeSubsets = allScopes.subsets()
    val conditionedAxioms = allScopeSubsets.map(trues => {
      val falses = allScopes &~ trues
      val maybeExp = getExpOfTruesAndFalses(trues.toSeq, falses.toSeq)
      val existingGraphNames = wrapper.userDefinedGraphs.keySet ++
        (wrapper.newlyDeclaredVariables.get(None) match {
          case None => Seq()
          case Some(decls) => decls.map(decl => decl.name)
        }) ++ trues.flatMap(t => wrapper.newlyDeclaredVariables(t).map(decl => decl.name))
      val existingGraphsUnion: Exp = OuroborosHelper.transformAndFold[String, Exp](
        existingGraphNames.toSeq,
        EmptySet(Ref)(),
        (folded, graph) => AnySetUnion(folded, graph)(),
        graphName => LocalVar(graphName)(SetType(Ref))
      )
      val existingGraphNamesSubsets = existingGraphNames.subsets().filter(p => p.nonEmpty)
      val graphSubsetsUnion = existingGraphNamesSubsets.map(theseGraphs => OuroborosHelper.transformAndFold[String, Exp](
        theseGraphs.toSeq,
        EmptySet(Ref)(),
        (folded, graph) => AnySetUnion(folded, graph)(),
        graphName => LocalVar(graphName)(SetType(Ref))
      ))
      val noExitAxioms = OuroborosHelper.transformAndFold[Exp,Exp](
        graphSubsetsUnion.toSeq,
        TrueLit()(),
        (wisdoms, wisdom) => And(
          wisdoms,
          wisdom
        )(),
        graphUnion => DomainFuncApp(noExitFunction, Seq(FuncApp($$Function, Seq(graphUnion))(), existingGraphsUnion, thisGraph), Map.empty[TypeVar, Type])()
      )

      if(maybeExp.isEmpty)
        Inhale(noExitAxioms)()
      else
        Inhale(Implies(maybeExp.get, noExitAxioms)())()
    })
    Seqn(
      conditionedAxioms.toSeq,
      Seq()
    )(info = SimpleInfo(Seq("", "insert NoExit Axioms for combinations of sets\n")))
  }

  def getFramingAxioms(thisGraph: Exp, input: Program, wrapper: OuroborosStmtWrapper) = {
    val framingFunction = input.findFunction(OuroborosNames.getIdentifier("apply_TCFraming"))
    val userDefinedFramingFunctions = wrapper.userDefinedGraphs.keySet.map(graphName => {
      val graph: LocalVar = LocalVar(graphName)(SetType(Ref), thisGraph.pos, thisGraph.info, thisGraph.errT)
      Inhale(
        FuncApp(framingFunction, Seq(graph, AnySetMinus(thisGraph, graph)()))(thisGraph.pos, thisGraph.info, thisGraph.errT)
      )(thisGraph.pos, SimpleInfo(Seq("", s"Apply TC Framing for $graph and $thisGraph setminus $graph\n")), thisGraph.errT)
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

    val allFramingFunctions = userDefinedFramingFunctions ++ newlyDeclaredFramingFunctions

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
}

case class OuroborosStmtWrapper(
                                 input: Program,
                                 inputGraphs: Map[String, Topology with Closedness],
                                 userDefinedGraphs: mutable.Map[String, Topology with Closedness],
                                 scope: Option[LocalVarDecl],
                                 newlyDeclaredVariables: mutable.Map[Option[LocalVarDecl], Set[LocalVarDecl]],
                                 dontConsiderScopes: mutable.Set[Option[LocalVarDecl]]
                               )
{
  def copy(): OuroborosStmtWrapper = {
    val inputCopy: Map[String, Topology with Closedness] = Map.empty ++ inputGraphs
    val existingCopy: mutable.Map[String, Topology with Closedness] = mutable.Map.empty ++ userDefinedGraphs
    //val singletonCopy: mutable.Set[String] = mutable.Set.empty[String] ++ singletonGraphs
    val scopeCopy = scope.map(f => LocalVarDecl(f.name, f.typ)(f.pos, f.info, f.errT))
    val newlyDeclaredCopy: mutable.Map[Option[LocalVarDecl], Set[LocalVarDecl]] = mutable.Map.empty[Option[LocalVarDecl], Set[LocalVarDecl]] ++ newlyDeclaredVariables
    val dontConsiderCopy = mutable.Set.empty[Option[LocalVarDecl]] ++ dontConsiderScopes
    val wrapperCopy = OuroborosStmtWrapper(input, inputCopy, existingCopy, scopeCopy, newlyDeclaredCopy, dontConsiderCopy)
    wrapperCopy
  }

  def setScopeAndCopyUserDefinedGraphs(newScope: Option[LocalVarDecl]): OuroborosStmtWrapper = {
    val existingCopy: mutable.Map[String, Topology with Closedness] = mutable.Map.empty ++ userDefinedGraphs
    OuroborosStmtWrapper(input,inputGraphs,existingCopy, newScope, newlyDeclaredVariables, dontConsiderScopes)
  }

  //def allExistingGraphs(): mutable.Set[String] =  /*singletonGraphs ++ */mutable.Set.empty ++ newlyDeclaredVariables.values.flatten.map(x => x.name) ++ userDefinedGraphs.keySet
  def allExistingGraphs(scopes: Set[LocalVarDecl]): scala.collection.Set[String] = {
    val scopeNamesUnFlattened =     scopes.map(scope => {
      newlyDeclaredVariables.get(Some(scope)) match {
        case None => Set()
        case Some(decls) => decls.map(decl => decl.name)
      }
    })
    val scopeNames: Set[String] = scopeNamesUnFlattened.flatten
    userDefinedGraphs.keySet ++ (newlyDeclaredVariables.get(None) match {
      case None => mutable.Set()
      case Some(decls) => decls.map(decl => decl.name)
    }) ++ scopeNames
  }

  def allGraphs(): Set[String] = {
    Set() ++ userDefinedGraphs.keySet ++ newlyDeclaredVariables.values.flatten.map(f => f.name)
  }
}
