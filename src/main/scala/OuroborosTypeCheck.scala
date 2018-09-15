package viper.silver.plugin

import viper.silver.ast.{And, Assert, EqCmp, Exp, FalseLit, FuncApp, Implies, Int, IntLit, LocalVar, LocalVarAssign, LocalVarDecl, MethodCall, NeCmp, NoInfo, Node, Not, Or, Positioned, Ref, SetType, SimpleInfo, Stmt, TransformableErrors, TrueLit}
import viper.silver.ast.utility.Rewriter.Rewritable
import viper.silver.plugin.errors.OuroborosTypeError
import viper.silver.plugin.reasons.WrongTypeReason

import scala.collection.mutable

class OuroborosTypeCheck {
  val graphHandler = new OuroborosGraphHandler()

  /**Returns an empty Seq, if no new statements have to be added to get the wantedType**/
  def checkTypeOfExp(wantedType: Topology with Closedness, exp: Exp, wrapper: OuroborosStateWrapper, errorNode: Node with Positioned with TransformableErrors with Rewritable, addErrors: Boolean = true): Seq[Stmt] = {
    val setExp = SetExp.getSetExp(exp, wrapper)
    val checkResult = checkTypeOfSetExp(wantedType, setExp, wrapper, Set(), None, errorNode)

    checkResult match {
      case None =>
        //We can't verify, that exp is of type wantedType
        if(addErrors) {
          val error = OuroborosTypeError(exp, WrongTypeReason(exp, s"the expression $exp might not be of type $wantedType."), false)
          wrapper.errors += error
        }
        Seq()

      case Some(checkExps) =>
        //If checkExps hold, then we know that exp is of wantedType.
        //If checkExps.isEmpty, exp is always of wantedType
        if(checkExps.isEmpty) {
          Seq()
        } else {
          val pureCheckExps = checkExps.filter(_.isPure)
          val nonPureCheckExps = checkExps.filter(exp => !exp.isPure)
          val checkExp = OuroborosHelper.ourFold[Exp](pureCheckExps, TrueLit()(), (exp1, exp2) => And(exp1, exp2)())
          val assertCheck = Assert(checkExp)(
            exp.pos,
            SimpleInfo(Seq("", s"added assertion for typechecking.", "")),
            OuroborosErrorTransformers.wrongTypeErrTrafo(exp, wantedType)
          )

          val nonPureAssertCheck = nonPureCheckExps.map(nonPureExp => Assert(nonPureExp)(
            exp.pos,
            SimpleInfo(Seq("", s"added assertion for typechecking.", "")),
            OuroborosErrorTransformers.wrongTypeErrTrafo(exp, wantedType)
          ))

          if(pureCheckExps.isEmpty)
            nonPureAssertCheck
          else if(nonPureCheckExps.isEmpty)
            Seq(assertCheck)
          else
            nonPureAssertCheck :+ assertCheck
        }

    }
  }

  //If we are checking the type of a reaching definition, we want to use the state of the definition. Hence, we can define a stateCopy.
  //Returns None, if the exp cannot be verified to be of type wantedType.
  //Returns Some(exps), if the exp is of type wantedType, under the condition, that exps hold
  // if exps.isEmpty, the wantedType is fulfilled without any additional conditions
  def checkTypeOfSetExp(wantedType: Topology with Closedness, setExp: SetExp, wrapper: OuroborosStateWrapper, takeSuperTypes: Set[String], maybeStateCopy: Option[StateCopyWrapper], position: Node with Positioned with TransformableErrors with Rewritable): Option[Seq[Exp]] = {
    setExp match {
      case setVar:SetVar =>
        checkTypeOfSetVarExp(wantedType, setVar, wrapper, takeSuperTypes, maybeStateCopy, position)
      case setBinExp: SetBinExp =>
        checkTypeOfSetBinExp(wantedType, setBinExp, wrapper, takeSuperTypes, maybeStateCopy, position)
      case explicitSetExp: ExplicitSetExp =>
        checkTypeOfExplicitSetExp(wantedType, explicitSetExp, wrapper, takeSuperTypes, maybeStateCopy, position)
      case condSetExp: CondSetExp =>
        checkTypeOfCondSetExp(wantedType, condSetExp, wrapper, takeSuperTypes, maybeStateCopy, position)
      case _: EmptySetExp => //We don't need to check anything, as an empty set is always closed, and fulfills all topologies
        Some(Seq())
    }
  }

  def checkTypeOfSetVarExp(wantedType: Topology with Closedness, setVar: SetVar, wrapper: OuroborosStateWrapper, takeSuperTypes: Set[String], maybeStateCopy: Option[StateCopyWrapper], position: Node with Positioned with TransformableErrors with Rewritable): Option[Seq[Exp]] = {
    val varType = setVar.ourType
    val stateCopyNeeded: Boolean = true

    val isSubClosedness = OurTypes.isSubClosedness(varType, wantedType)
    val isSubTopology = OurTypes.isSubTopology(varType, wantedType)
    val isStaticSubType = isSubClosedness && isSubTopology


    if(isStaticSubType) {
      //As the static type is a sub type of the wanted type, we know that the dynamic type is also a sub type
      wrapper.definitions.get(setVar.varName) match {
        case Some(defs) if defs.contains(0) =>
          val varExp = setVar.getDuplicateExp()
          val res = wrapper.localGraphs(setVar.varName)
          val initVarName = res._2.name
          val initVar = LocalVar(initVarName)(Int)
          val ref_fields = graphHandler.ref_fields(wrapper.input.fields)
          val checkExps = NeCmp(initVar, IntLit(0)())()//graphHandler.fold_GRAPH(varExp, ref_fields, wrapper.input, false, true, true, false, TrueLit()(), (exp1, exp2) => And(exp1, exp2)())
          return Some(Seq(checkExps))
        case _ =>
          return Some(Seq())
      }
      return Some(Seq())//(true, Seq())
    }

    val (setVarExp, maybeInitVarName): (Exp, Option[String]) = maybeStateCopy match {
      case _ if setVar.initVarName.isEmpty =>
        //setVar is an input Graph
        (setVar.getDuplicateExp(position.pos, NoInfo, position.errT), setVar.initVarName)

      case None =>
        (setVar.getDuplicateExp(position.pos, NoInfo, position.errT), setVar.initVarName)

      case Some(stateCopy) =>
        //setVar is a local Graph, and we need to use the variables defined in stateCopy
        val (copyVarName, copyInitName): (String, String) = stateCopy.localVarNamesMapping.get(setVar.varName) match {
          case None =>
            assert(false, "Internal error") //TODO test that this does not happen
            return None
          case Some(newName) => (newName.newLocalVarName, newName.newInitVarName)
        }
        val copyVar = LocalVar(copyVarName)(SetType(Ref), position.pos, NoInfo, position.errT)
        (copyVar, Some(copyInitName))
    }


    if(takeSuperTypes.contains(setVar.varName) || setVar.varName == OuroborosNames.getIdentifier("UNIVERSE")) {
      //We should not check the definitions of setVar, and setVar is not of type wantedType

      val allChecksExp: Exp = wantedType match {
        case _ =>
          //We know that either the topology or closedness of the setVar is not of wantedType
          val zopg = wantedType.isInstanceOf[ZOPG] && !setVar.ourType.isInstanceOf[ZOPG]
          val dag = wantedType.isInstanceOf[DAG] && !setVar.ourType.isInstanceOf[DAG]
          val closed = wantedType.isInstanceOf[Closed] && !setVar.ourType.isInstanceOf[Closed]
          val ref_fields = graphHandler.ref_fields(wrapper.input.fields)

          graphHandler.fold_GRAPH(setVarExp, ref_fields, wrapper.input, closed, qpsNeeded = false, noNullNeeded = false, dag, zopg, TrueLit()(), (exp1, exp2) => And(exp1, exp2)())
      }

      return Some(Seq(allChecksExp))
    }

    if(isSubTopology && !isSubClosedness) {
      //we only need to check closedness of the variable
      //If all definitions of the variable are closed, we don't check anything. Otherwise, we check CLOSED(setVar)
      val newWantedType = OurClosedGraph
      wrapper.definitions.get(setVar.varName) match {
        case None =>
          //setVar is an input graph
          val input = wrapper.input
          val closedFunc = graphHandler.CLOSED(setVarExp, input)
          return Some(Seq(closedFunc))
        case Some(defs) =>
          var defsAreSubClosedness = true
          defs.collect({
            case (_, (definition, stateWrapper)) if defsAreSubClosedness =>
              val maybeCheckExp = checkDefinition(newWantedType, definition, setVar.varName, stateCopyNeeded, stateWrapper, takeSuperTypes, position)
              maybeCheckExp match {
                case Some(exps) if exps.isEmpty =>
                case _ =>
                  defsAreSubClosedness = false
              }
          })

          if(defsAreSubClosedness) {
            return Some(Seq())
          } else {
            val input = wrapper.input
            val closedFunc = if(defs.contains(0)){
              val res = wrapper.localGraphs(setVar.varName)
              val initVarName = res._2.name
              val initVar = LocalVar(initVarName)(Int)
              val closed = graphHandler.CLOSED(setVarExp, input)
              val notZero = NeCmp(initVar, IntLit(0)())()
              And(notZero, closed)()
              //graphHandler.fold_GRAPH(setVarExp, graphHandler.ref_fields(wrapper.input.fields), wrapper.input, true, true, true, false, TrueLit()(), (exp1, exp2) => And(exp1, exp2)())
            }
            else
              graphHandler.CLOSED(setVarExp, input)
            return Some(Seq(closedFunc))
          }
      }
    }

    // !isSubTopology holds

    if(setVar.initVarName.isEmpty) {
      //setVar is an inputGraph
      //An inputGraph cannot be redefined, hence we only have the static type.
      //We can only show closedness and acyclicity
      val closedFunc =
        if(!isSubClosedness)
          Seq(graphHandler.CLOSED(setVarExp, wrapper.input))
        else
          Seq()

      val topoFunc: Seq[Exp] = wantedType match {
        case _ =>
          val dag = wantedType.isInstanceOf[DAG] && !varType.isInstanceOf[DAG]
          val zopg = wantedType.isInstanceOf[ZOPG] && !varType.isInstanceOf[ZOPG]

          val zopgFunc = if(zopg) Seq(graphHandler.ZOPG(setVarExp, wrapper.input)) else Seq()
          val dagFunc = if(dag) Seq(graphHandler.DAG(setVarExp, wrapper.input)) else Seq()

          zopgFunc ++ dagFunc

        //As we know that !isSubTopology, we know that wantedType is either of type Forest, ZOPG or DAG. We don't need more cases.
      }

      val neededFuncs = closedFunc ++ topoFunc
      val assertFunc = OuroborosHelper.ourFold[Exp](neededFuncs, TrueLit()(), (exp1, exp2) => And(exp1, exp2)())

      return Some(Seq(assertFunc))
    }

    //We know that setVar is not an input Graph

    val initVarName = maybeInitVarName.get

    var checkType = wantedType
    if(!isSubTopology && isSubClosedness) {
      //we only need to check the topology type
      if(wantedType.isInstanceOf[Closed]) {
        checkType = OurTypes.getNonClosedType(wantedType.asInstanceOf[Topology with Closed])
      }
    }

    wrapper.definitions.get(setVar.varName) match {
      case None =>
        //We should not end here, as there is a fake definition for each user defined variable
        assert(false, s"Fake definition for variable ${setVar.varName} is not inserted.")

        None
      case Some(defs) =>
        var isInit: Option[Exp] = None //Only needed, if fake definition reaches

        val maybeCheckExps: Seq[Option[Seq[Exp]]] = defs.collect({
          case map if map._1 == 0 =>
            //We need to assert that the graph is already defined
            val initVar = LocalVar(initVarName)(Int)
            isInit = Some(NeCmp(initVar, IntLit(0)())())

            None
          case map =>
            val initValue = map._1.toInt
            val definition = map._2._1
            val definitionState = map._2._2
            val initVar = LocalVar(initVarName)(Int)
            val defReachesExp = EqCmp(initVar, IntLit(initValue)())()
            val defCheckExp = checkDefinition(checkType, definition, setVar.varName, stateCopyNeeded, definitionState, takeSuperTypes, position, maybeStateCopy)

            defCheckExp match {
              case None => None
              case Some(toCheckExps) =>
                val pureToCheckExps = toCheckExps.filter(_.isPure)
                val nonPureToCheckExps = toCheckExps.filter(exp => !exp.isPure)
                val pureCheck = OuroborosHelper.ourFold[Exp](defReachesExp +: pureToCheckExps, TrueLit()(), (exp1, exp2) => And(exp1, exp2)())
                val nonPureCheck =
                  nonPureToCheckExps.map(nonPureExp => Implies(defReachesExp, nonPureExp)())
                  OuroborosHelper.ourFold[Exp](defReachesExp +: nonPureToCheckExps, TrueLit()(), (exp1, exp2) => And(exp1, exp2)())
                val reachesAndCheck = if(pureToCheckExps.isEmpty)
                  Some(nonPureCheck)
                else if(nonPureToCheckExps.isEmpty)
                  Some(Seq(pureCheck))
                else
                  Some(nonPureCheck :+ pureCheck)

                reachesAndCheck
            }

        }).toSeq

        val checkExps = maybeCheckExps.collect {
          case Some(checkExp) =>
            checkExp
        }.flatten

        if(checkExps.isEmpty) {
          Some(Seq())
        } else {
          val pureExps = checkExps.filter(_.isPure)
          val nonPureExps = checkExps.filter(exp => !exp.isPure)
          val pureCheck = OuroborosHelper.ourFold[Exp](pureExps, FalseLit()(), (exp1, exp2) => Or(exp1, exp2)())
          val check = if(pureExps.isEmpty)
            nonPureExps
          else if(nonPureExps.isEmpty)
            Seq(pureCheck)
          else
            nonPureExps :+ pureCheck

          isInit match {
            case None =>
              Some(check)
            case Some(checkIsInit) =>
              val checkWithIsInit = check.map(exp => And(checkIsInit, exp)())
              Some(checkWithIsInit)
          }
        }

    }


  }

  def checkDefinition(wantedType: Topology with Closedness,
                      definition: Stmt, definedVarName: String,
                      stateCopyNeeded: Boolean,
                      wrapper: OuroborosStateWrapper,
                      takeSuperTypes: Set[String],
                      position: Node with Positioned with TransformableErrors with Rewritable,
                     //take State Copy is used for the case that we need to check the left hand side of a method call.
                      takeStateCopy: Option[StateCopyWrapper] = None): Option[Seq[Exp]] = definition match {
    case assign: LocalVarAssign =>
      assert(definedVarName == assign.lhs.name)
      val rhs = assign.rhs
      val rhsSetExp = SetExp.getSetExp(rhs, wrapper)
      val stateCopy = if(stateCopyNeeded) wrapper.stateCopies.get(definition) match {
      case None =>
        val stateCopy = StateCopyWrapper.createStateCopy(rhsSetExp)
        if(!stateCopy.isEmpty) {
          wrapper.stateCopies.put(definition, stateCopy)
        }
        Some(stateCopy)
      case copy =>
          copy
      } else None

      checkTypeOfSetExp(wantedType, rhsSetExp, wrapper, takeSuperTypes + definedVarName, stateCopy, position)
    case call: MethodCall =>
      val copiedVarName = if(takeStateCopy.isDefined) takeStateCopy.get.localVarNamesMapping.get(definedVarName) match {
        case None => definedVarName
        case Some(newNameWrapper) =>
          newNameWrapper.newLocalVarName
      } else definedVarName
      val specs = wrapper.specs
      val methodName = call.methodName
      val method = wrapper.input.findMethod(methodName)
      var index = -1
      call.targets.collect {
        case localVar: LocalVar if localVar.name == definedVarName =>
          index = call.targets.indexOf(localVar)
      }

      assert(index >= 0)

      val returnDecl: LocalVarDecl = method.formalReturns(index)
      val returnName = returnDecl.name
      var maybeReturnType: Option[Topology with Closedness] = None
      specs.get(methodName) match {
        case None => //TODO should not happen?
        case Some(graphSpec) =>
          graphSpec.outputGraphs.collect( {
            case obj: OurObject if obj.name == returnName =>
              maybeReturnType = Some(obj.typ)
          })
      }

      assert(maybeReturnType.nonEmpty)

      val returnType = maybeReturnType.get

      val isSubTopology = OurTypes.isSubTopology(returnType, wantedType)
      val isSubClosedness = OurTypes.isSubClosedness(returnType, wantedType)

      if(isSubTopology && isSubClosedness) {
        return Some(Seq())
      } else if (isSubTopology && !isSubClosedness) {
        val closedExp = graphHandler.CLOSED(LocalVar(copiedVarName)(SetType(Ref)), wrapper.input)
        return Some(Seq(closedExp))
      } else { //!isSubTopology
          val qpsNeeded = false
          val nonNullNeeded = false
          val isDag = wantedType.isInstanceOf[DAG]
          val isZopg = wantedType.isInstanceOf[ZOPG]
          val ref_fields = graphHandler.ref_fields(wrapper.input.fields)
          val checkExp = graphHandler.fold_GRAPH(LocalVar(copiedVarName)(SetType(Ref)), ref_fields, wrapper.input, !isSubClosedness, qpsNeeded, nonNullNeeded, isDag, isZopg, TrueLit()(), (exp1, exp2) => And(exp1, exp2)())
          return Some(Seq(checkExp))
      }
    //case _ => TODO are there other definition statements?
  }

  def checkTypeOfSetBinExp(wantedType: Topology with Closedness, setBinExp: SetBinExp, wrapper: OuroborosStateWrapper, takeSuperTypes: Set[String], maybeStateCopy: Option[StateCopyWrapper], position: Node with Positioned with TransformableErrors with Rewritable): Option[Seq[Exp]] = {
    val binExp = setBinExp.getDuplicateExp(position.pos, NoInfo, position.errT)
    val lhs = setBinExp.lhs
    val rhs = setBinExp.rhs
//    val relevantGraphs = SetExp.getSuperSetOfGraphs(setBinExp, true) //Idea: if we get a superset of the setBinaryExp, which is a union of inputgraphs, then we know that the binary exp is disjoint
//    val onlyInputGraphs = relevantGraphs.forall(graphName => wrapper.inputGraphs.contains(graphName))
//    val isDisjointSetminus: Boolean = onlyInputGraphs && setBinExp.isInstanceOf[SetMinus]

    val maybeDisjointCheck: Seq[Exp] = setBinExp match {
      case setMinus: SetMinus =>
        //if the left hand side does not need any additional checks to be of wanted type, then
        // we know that disjointness is sufficient for having the wished type.
        val checkLhs = checkTypeOfSetExp(wantedType, lhs, wrapper, takeSuperTypes, maybeStateCopy, position)
        if(checkLhs.isDefined && checkLhs.get.isEmpty) {
          val disjointName = OuroborosNames.getIdentifier("DISJOINT")
          val disjointFunction = wrapper.input.findFunction(disjointName)
          val disjointFuncApp = FuncApp(disjointFunction, Seq(lhs.getDuplicateExp(), rhs.getDuplicateExp()))(position.pos, NoInfo, position.errT)
          Seq(disjointFuncApp)
        } else {
          Seq()
        }
      case setIntersection: SetIntersection =>
        //If the both graphs are disjoint, we get an empty closed forest. Hence,
        //checking disjointness of graphs is always sufficient to obtain a specific type
        val disjointName = OuroborosNames.getIdentifier("DISJOINT")
        val disjointFunction = wrapper.input.findFunction(disjointName)
        val disjointFuncApp = FuncApp(disjointFunction, Seq(lhs.getDuplicateExp(), rhs.getDuplicateExp()))(position.pos, NoInfo, position.errT)
        Seq(disjointFuncApp)
      case _ =>
        Seq()
    }

/*      if(setBinExp.isInstanceOf[SetMinus]) {
      //We only need to check that the left hand side is of type wantedType
      return checkTypeOfSetExp(wantedType, lhs, wrapper, takeSuperTypes, maybeStateCopy, position)
    }*/

    val mapping = setBinExp match {
      case _: SetUnion =>/* if(onlyInputGraphs) OurTypes.disjointUnionMapping else*/ OurTypes.unionMapping
      case _: SetMinus => OurTypes.setminusMapping
      case _: SetIntersection => OurTypes.intersectionMapping
    }

    val possibilities = getPossibilites(wantedType, setBinExp, isDisjoint = false)// onlyInputGraphs)

    if(possibilities.isEmpty) {
      //We don't know, how to get the wished type with a binary expression
      val qpsNeeded: Boolean = true //TODO should we check the permissions?
      val nonNullNeeded: Boolean = true

      val dag: Boolean = wantedType.isInstanceOf[DAG]
      val zopg: Boolean = wantedType.isInstanceOf[ZOPG]

      val closed: Boolean = wantedType match {
        case _: Closed => true
        case _ => false
      }

      val ref_fields = graphHandler.ref_fields(wrapper.input.fields)
      val graphExps = graphHandler.GRAPH(binExp, ref_fields, wrapper.input, closed, qpsNeeded, nonNullNeeded, dag, zopg)

      return Some(graphExps)
    }

    //val allOptions: Set[BinaryTypesWrapper] = possibilities.values.flatten.toSet
    var satisfyingTupleFound: Boolean = false

    var allChecks: Seq[Exp] = maybeDisjointCheck

    possibilities.collect({
      case tuple if !satisfyingTupleFound =>
        val closedAcyclicWrapper = tuple._1
        val checkClosed = closedAcyclicWrapper.checkClosedness
        val checkAcyclic = closedAcyclicWrapper.checkAcyclicity
        val options = tuple._2
        options.collect({
          case option if !satisfyingTupleFound =>
            val possibleLHSType = option.lhs
            val possibleRHSType = option.rhs
            val maybeCheckLHS = checkTypeOfSetExp(possibleLHSType, lhs, wrapper, takeSuperTypes, maybeStateCopy, position)
            maybeCheckLHS match {
              case None =>
              //We cannot show that the lhs is of the wished type
              case Some(checkLHS) =>
                val maybeCheckRHS = checkTypeOfSetExp(possibleRHSType, rhs, wrapper, takeSuperTypes, maybeStateCopy, position)
                maybeCheckRHS match {
                  case None =>
                  //We cannot show that the rhs is of the wished type
                  case Some(checkRHS) =>
                    if(checkLHS.isEmpty && checkRHS.isEmpty && !checkClosed && !checkAcyclic) {
                      //We have found a type for the lhs and the rhs, which always holds,
                      // and hence we know that the binary expression has the wished type
                      satisfyingTupleFound = true
                    } else {
                      val closedCheck = if(checkClosed) Seq(graphHandler.CLOSED(binExp, wrapper.input)) else Seq()
                      val dagCheck = if(checkAcyclic) Seq(graphHandler.DAG(binExp, wrapper.input)) else Seq()
                      val pureLHSRHS = (checkLHS ++ checkRHS).filter(_.isPure)
                      val nonPureLHSRHS = (checkLHS ++ checkRHS).filter(exp => !exp.isPure)

                      val pureOptionChecks = pureLHSRHS ++ closedCheck ++ dagCheck
                      val pureOptionChecksExp = OuroborosHelper.ourFold[Exp](
                        pureOptionChecks,
                        TrueLit()(),
                        (exp1, exp2) => And(exp1, exp2)(position.pos, NoInfo, position.errT)
                      )

                      allChecks ++= (if(pureLHSRHS.isEmpty) nonPureLHSRHS
                      else if(nonPureLHSRHS.isEmpty)
                        Seq(pureOptionChecksExp)
                      else
                        nonPureLHSRHS :+ pureOptionChecksExp)
                    }
                }
            }

        })
    })

    if(satisfyingTupleFound) {
      //This means that we don't need to use allChecks, as we know that at least one of the options always holds
      Some(Seq())
    } else {
      val pureChecks = allChecks.filter(_.isPure)
      val nonPureChecks = allChecks.filter(exp => !exp.isPure)
      val check = OuroborosHelper.ourFold[Exp](
        pureChecks,
        TrueLit()(),
        (exp1, exp2) => Or(exp1, exp2)(position.pos, NoInfo, position.errT)
      )

      if(pureChecks.isEmpty)
        Some(nonPureChecks)
      else if(nonPureChecks.isEmpty)
        Some(Seq(check))
      else
        Some(nonPureChecks :+ check)
    }
  }

  def checkTypeOfExplicitSetExp(wantedType: Topology with Closedness, explicitSetExp: ExplicitSetExp, wrapper: OuroborosStateWrapper, takeSuperTypes: Set[String], maybeStateCopy: Option[StateCopyWrapper], position: Node with Positioned with TransformableErrors with Rewritable): Option[Seq[Exp]] = {
    val astExp: Exp = maybeStateCopy match {
      case None =>
        explicitSetExp.getDuplicateExp(position.pos, NoInfo, position.errT)
      case Some(stateCopy) =>
        stateCopy.explicitSetsMapping.get(explicitSetExp) match {
          case None =>
            assert(false, "internal error") //TODO test, that we never end here
            return None
          case Some(varName) =>
            LocalVar(varName)(SetType(Ref), position.pos, NoInfo, position.errT)
        }
    }

    val isForest: Boolean = explicitSetExp.elems.size <= 1 //If at most one element is in the explicit Set, the set is automatically a forest
    wantedType match {
      case _ if isForest =>
        val checkQPs = graphHandler.fold_GRAPH(astExp, graphHandler.ref_fields(wrapper.input.fields), wrapper.input, closed = wantedType.isInstanceOf[Closed], true, true, dag = false, zopg = false, TrueLit()(), (exp1, exp2) => And(exp1, exp2)())
        Some(Seq(checkQPs))
      case _ =>
        val checkQPs = graphHandler.fold_GRAPH(astExp, graphHandler.ref_fields(wrapper.input.fields), wrapper.input, closed = wantedType.isInstanceOf[Closed], true, true, dag = wantedType.isInstanceOf[DAG], zopg = wantedType.isInstanceOf[ZOPG], TrueLit()(), (exp1, exp2) => And(exp1, exp2)())
        Some(Seq(checkQPs))
    }
  }

  def checkTypeOfCondSetExp(wantedType: Topology with Closedness, condSetExp: CondSetExp, wrapper: OuroborosStateWrapper, takeSuperTypes: Set[String], maybeStateCopy: Option[StateCopyWrapper], position: Node with Positioned with TransformableErrors with Rewritable): Option[Seq[Exp]] = {
    def transformToImplies(exps: Seq[Exp], lhsOfImplies: Exp) = {
      def lhsCopy = lhsOfImplies.duplicateMeta(position.pos, NoInfo, position.errT).asInstanceOf[Exp]

      exps.map(exp => Implies(lhsCopy, exp)(position.pos, NoInfo, position.errT))
    }

    val checkTypeForThn: Seq[Exp] = checkTypeOfSetExp(wantedType, condSetExp.thn, wrapper, takeSuperTypes, maybeStateCopy, position) match {
      case None => return None
      case Some(exps) => exps
    }
    val thnTransformed = transformToImplies(checkTypeForThn, condSetExp.cond)

    val checkTypeForEls: Seq[Exp] = checkTypeOfSetExp(wantedType, condSetExp.els, wrapper, takeSuperTypes, maybeStateCopy, position) match {
      case None => return None
      case Some(exps) => exps
    }
    val elsTransformed = transformToImplies(checkTypeForEls, Not(condSetExp.cond)(position.pos, NoInfo, position.errT))


    Some(thnTransformed ++ elsTransformed)
  }
  //returns set of pairs of type and boolean
  //type: boolean says, if Closed needs to be checked for this subtype
  //the type is a subtype of ourType, if the boolean is false. Otherwise, its Closed Type is a subtype of ourType
  def getAllSubTypes(ourType: Topology with Closedness): Set[TypeClosedAcyclicWrapper] = {
    val ourTypeIsClosed: Boolean = ourType match {
      case _: Closed => true
      case _ => false
    }

    val checkClosedAndAcyclic = ClosedAcyclicWrapper(true, true)
    val checkClosed = ClosedAcyclicWrapper(true, false)
    val checkAcyclic = ClosedAcyclicWrapper(false, true)
    val checkNothing = ClosedAcyclicWrapper(false, false)

    var result: Set[TypeClosedAcyclicWrapper] = if (ourTypeIsClosed) {
      Set(TypeClosedAcyclicWrapper(ourType, checkNothing),
        TypeClosedAcyclicWrapper(OurTypes.getNonClosedType(ourType.asInstanceOf[Topology with Closed]), checkClosed))
    } else {
      Set(TypeClosedAcyclicWrapper(ourType, checkNothing), TypeClosedAcyclicWrapper(OurTypes.getClosedType(ourType), checkNothing))
    }


    ourType match {
      case _: Forest if ourTypeIsClosed=>
        //We can add ZOPGs, if they are closed, with acyclicity check
        result ++= Set(TypeClosedAcyclicWrapper(OurClosedZOPG, checkAcyclic), TypeClosedAcyclicWrapper(OurZOPG, checkClosedAndAcyclic))
      case _: Forest if !ourTypeIsClosed =>
        //We can add all ZOPGS with acyclicity check
        result ++= Set(TypeClosedAcyclicWrapper(OurClosedZOPG, checkAcyclic), TypeClosedAcyclicWrapper(OurZOPG, checkAcyclic))
      case _: ZOPG if ourTypeIsClosed =>
        //We can add the forest type, as it is a subtype of the ZOPG type, under the condition, that the forest is closed
        result ++= Set(TypeClosedAcyclicWrapper(OurClosedForest, checkNothing), TypeClosedAcyclicWrapper(OurForest, checkClosed))
      case _: ZOPG if !ourTypeIsClosed =>
        //We can add the forest types, as they are a subtype of the ZOPG type
        result ++= Set(TypeClosedAcyclicWrapper(OurClosedForest, checkNothing), TypeClosedAcyclicWrapper(OurForest, checkNothing))
      case _: DAG if ourTypeIsClosed =>
        //We can add the forest type, as it is a subtype of the ZOPG type, under the condition, that the forest is closed
        //Additionally, we can add the ZOPG and general Graph types, if they are closed and acyclic
        result ++= Set(TypeClosedAcyclicWrapper(OurClosedForest, checkNothing), TypeClosedAcyclicWrapper(OurForest, checkClosed))
        result ++= Set(TypeClosedAcyclicWrapper(OurClosedZOPG, checkAcyclic), TypeClosedAcyclicWrapper(OurZOPG, checkClosedAndAcyclic))
        result ++= Set(TypeClosedAcyclicWrapper(OurClosedGraph, checkAcyclic), TypeClosedAcyclicWrapper(OurGraph, checkClosedAndAcyclic))
      case _: DAG if !ourTypeIsClosed =>
        //We can add the forest types, as they are a subtype of the DAG type
        result ++= Set(TypeClosedAcyclicWrapper(OurClosedForest, checkNothing), TypeClosedAcyclicWrapper(OurForest, checkNothing))
        result ++= Set(TypeClosedAcyclicWrapper(OurClosedZOPG, checkAcyclic), TypeClosedAcyclicWrapper(OurZOPG, checkAcyclic))
        result ++= Set(TypeClosedAcyclicWrapper(OurClosedGraph, checkAcyclic), TypeClosedAcyclicWrapper(OurGraph, checkAcyclic))
      case _ =>
        //We can add all types, but we may have to check closedness
        val checkClosedOrNot = if(ourTypeIsClosed) checkClosed else checkNothing
        result ++= Set(
          TypeClosedAcyclicWrapper(OurClosedForest, checkNothing),
          TypeClosedAcyclicWrapper(OurClosedZOPG, checkNothing),
          TypeClosedAcyclicWrapper(OurClosedDAG, checkNothing),
          TypeClosedAcyclicWrapper(OurClosedGraph, checkNothing),
          TypeClosedAcyclicWrapper(OurForest, checkClosedOrNot),
          TypeClosedAcyclicWrapper(OurZOPG, checkClosedOrNot),
          TypeClosedAcyclicWrapper(OurDAG, checkClosedOrNot),
          TypeClosedAcyclicWrapper(OurGraph, checkClosedOrNot)
        )
    }

    result
  }

  //returns a mapping from a boolean value to a set of pairs of types
  //Each pair of tuple is unique (it only appears either in True or False, or not at all). This follows from the structure of the csv table
  //The Boolean says, if we need to check closedness
  def getPossibilites(ourType: Topology with Closedness, setBinaryExp: SetBinExp, isDisjoint: Boolean): Map[ClosedAcyclicWrapper, Set[BinaryTypesWrapper]] = {
    val subTypes = getAllSubTypes(ourType)
    val mapping = setBinaryExp match {
      case _: SetUnion => if(isDisjoint) OurTypes.disjointUnionMapping else OurTypes.unionMapping
      case _: SetMinus => if(isDisjoint) OurTypes.disjointSetminusMapping else OurTypes.setminusMapping
      case _: SetIntersection => if(isDisjoint) OurTypes.disjointIntersectionMapping else OurTypes.intersectionMapping
    }
    var allPossibilities: mutable.Map[ClosedAcyclicWrapper, Set[BinaryTypesWrapper]] = mutable.Map.empty[ClosedAcyclicWrapper, Set[BinaryTypesWrapper]]

    subTypes.foreach( wrapper => {
      val typ = wrapper.ourType
      val checkClosed = wrapper.closedAcyclicWrapper.checkClosedness
      val checkAcyclicity = wrapper.closedAcyclicWrapper.checkAcyclicity
      mapping.get(typ) match {
        case None =>
        case Some(possibilities) =>
          val possibilitiesWrapper = possibilities.map(poss => BinaryTypesWrapper(poss._1, poss._2))
          val closedAcyclicWrapper = ClosedAcyclicWrapper(checkClosed, checkAcyclicity)
          allPossibilities.get(closedAcyclicWrapper) match {
            case None =>
              allPossibilities.put(closedAcyclicWrapper, possibilitiesWrapper)
            case Some(wrappers) =>
              allPossibilities.put(closedAcyclicWrapper, possibilitiesWrapper ++ wrappers)
          }
      }
    })

    Map.empty[ClosedAcyclicWrapper, Set[BinaryTypesWrapper]] ++ allPossibilities
  }


}
