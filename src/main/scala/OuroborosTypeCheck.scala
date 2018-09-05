package viper.silver.plugin

import viper.silver.ast.{And, Assert, EqCmp, Exp, FalseLit, Int, IntLit, LocalVar, LocalVarAssign, LocalVarDecl, MethodCall, NeCmp, NoInfo, Node, Or, Positioned, Ref, SetType, SimpleInfo, Stmt, TransformableErrors, TrueLit}
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
          val checkExp = OuroborosHelper.ourFold[Exp](checkExps, TrueLit()(), (exp1, exp2) => And(exp1, exp2)())
          val assertCheck = Assert(checkExp)(
            exp.pos,
            SimpleInfo(Seq("", s"added assertion for typechecking.\n")),
            OuroborosErrorTransformers.wrongTypeErrTrafo(exp, wantedType)
          )

          Seq(assertCheck)
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
        case _: ZOPG if !setVar.ourType.isInstanceOf[ZOPG] =>
          return None
        case _ =>
          //We know that either the topology or closedness of the setVar is not of wantedType
          val dag = wantedType.isInstanceOf[DAG] && !setVar.ourType.isInstanceOf[DAG]
          val closed = wantedType.isInstanceOf[Closed] && !setVar.ourType.isInstanceOf[Closed]
          val ref_fields = graphHandler.ref_fields(wrapper.input.fields)
          graphHandler.fold_GRAPH(setVarExp, ref_fields, wrapper.input, closed, qpsNeeded = false, nonNullNeeded = false, dag, TrueLit()(), (exp1, exp2) => And(exp1, exp2)())
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
            val closedFunc = graphHandler.CLOSED(setVarExp, input)
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

      val acyclicFunc: Seq[Exp] = wantedType match {
        case _: ZOPG if !varType.isInstanceOf[ZOPG] =>
          //wantedType is either ZOPG or Forest, but varType is not ZOPG or Forest
          return None
        case _: DAG =>
          Seq(graphHandler.DAG(setVarExp, wrapper.input))

        //As we know that !isSubTopology, we know that wantedType is either of type Forest, ZOPG or DAG. We don't need more cases.
      }

      val neededFuncs = closedFunc ++ acyclicFunc
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

        val maybeCheckExps: Seq[Option[Exp]] = defs.collect({
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
            val defCheckExp = checkDefinition(checkType, definition, setVar.varName, stateCopyNeeded, definitionState, takeSuperTypes, position)

            defCheckExp match {
              case None => None
              case Some(toCheckExps) =>
                val reachesAndCheck =
                  Some(OuroborosHelper.ourFold[Exp](defReachesExp +: toCheckExps, TrueLit()(), (exp1, exp2) => And(exp1, exp2)()))

                reachesAndCheck
            }

        }).toSeq

        val checkExps = maybeCheckExps.collect {
          case Some(checkExp) =>
            checkExp
        }

        if(checkExps.isEmpty) {
          Some(Seq())
        } else {
          val check = OuroborosHelper.ourFold[Exp](checkExps, FalseLit()(), (exp1, exp2) => Or(exp1, exp2)())
          isInit match {
            case None =>
              Some(Seq(check))
            case Some(checkIsInit) =>
              Some(Seq(And(checkIsInit, check)()))
          }
        }

    }


  }

  def checkDefinition(wantedType: Topology with Closedness, definition: Stmt, definedVarName: String, stateCopyNeeded: Boolean, wrapper: OuroborosStateWrapper, takeSuperTypes: Set[String], position: Node with Positioned with TransformableErrors with Rewritable): Option[Seq[Exp]] = definition match {
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
          graphSpec.outputs.collect( {
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
        val closedExp = graphHandler.CLOSED(LocalVar(definedVarName)(SetType(Ref)), wrapper.input)
        return Some(Seq(closedExp))
      } else { //!isSubTopology
        wantedType match {
          case _: Forest if !returnType.isInstanceOf[ZOPG] =>
            //We cannot check ZOPG
            return None
          case _: DAG =>
            val qpsNeeded = false
            val nonNullNeeded = false
            val ref_fields = graphHandler.ref_fields(wrapper.input.fields)
            val checkExp = graphHandler.fold_GRAPH(LocalVar(definedVarName)(SetType(Ref)), ref_fields, wrapper.input, !isSubClosedness, qpsNeeded, nonNullNeeded, true, TrueLit()(), (exp1, exp2) => And(exp1, exp2)())
            return Some(Seq(checkExp))
          case _ => return None
        }
      }
    //case _ => TODO are there other definition statements?
  }

  def checkTypeOfSetBinExp(wantedType: Topology with Closedness, setBinExp: SetBinExp, wrapper: OuroborosStateWrapper, takeSuperTypes: Set[String], maybeStateCopy: Option[StateCopyWrapper], position: Node with Positioned with TransformableErrors with Rewritable): Option[Seq[Exp]] = {
    val binExp = setBinExp.getDuplicateExp(position.pos, NoInfo, position.errT)
    val lhs = setBinExp.lhs
    val rhs = setBinExp.rhs
    val relevantGraphs = SetExp.getSuperSetOfGraphs(setBinExp, true) //Idea: if we get a superset of the setBinaryExp, which is a union of inputgraphs, then we know that the binary exp is disjoint
    val onlyInputGraphs = relevantGraphs.forall(graphName => wrapper.inputGraphs.contains(graphName))
    val isDisjointSetminus: Boolean = onlyInputGraphs && setBinExp.isInstanceOf[SetMinus]

    if(isDisjointSetminus) {
      //We only need to check that the left hand side is of type wantedType
      return checkTypeOfSetExp(wantedType, lhs, wrapper, takeSuperTypes, maybeStateCopy, position)
    }

    val mapping = setBinExp match {
      case _: SetUnion => if(onlyInputGraphs) OurTypes.disjointUnionMapping else OurTypes.unionMapping
      case _: SetMinus => OurTypes.setminusMapping
    }

    val possibilities = getPossibilites(wantedType, setBinExp, onlyInputGraphs)

    if(possibilities.isEmpty) {
      //We don't know, how to get the wished type with a binary expression
      val qpsNeeded: Boolean = true //TODO should we check the permissions?
      val nonNullNeeded: Boolean = true

      var dag: Boolean = false
      wantedType match {
        case _: ZOPG => //Forests are also instances of ZOPG
          //We don't know how to specify the ZOPG property
          return None
        case _: DAG =>
          dag = true
        case _ =>
      }

      val closed: Boolean = wantedType match {
        case _: Closed => true
        case _ => false
      }

      val ref_fields = graphHandler.ref_fields(wrapper.input.fields)
      val graphExps = graphHandler.GRAPH(binExp, ref_fields, wrapper.input, closed, qpsNeeded, nonNullNeeded, dag)

      return Some(graphExps)
    }

    //val allOptions: Set[BinaryTypesWrapper] = possibilities.values.flatten.toSet
    var satisfyingTupleFound: Boolean = false

    var allChecks: Seq[Exp] = Seq()

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
                      val optionChecks = checkLHS ++ checkRHS ++ closedCheck ++ dagCheck
                      val optionChecksExp = OuroborosHelper.ourFold[Exp](
                        optionChecks,
                        TrueLit()(),
                        (exp1, exp2) => And(exp1, exp2)(position.pos, NoInfo, position.errT)
                      )

                      allChecks :+= optionChecksExp
                    }
                }
            }

        })
    })

    if(satisfyingTupleFound) {
      //This means that we don't need to use allChecks, as we know that at least one of the options always holds
      Some(Seq())
    } else {
      val check = OuroborosHelper.ourFold[Exp](
        allChecks,
        TrueLit()(),
        (exp1, exp2) => Or(exp1, exp2)(position.pos, NoInfo, position.errT)
      )

      Some(Seq(check))
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
    wantedType match {
      case _: ZOPG =>
        None
      case _ =>
        val checkQPs = graphHandler.fold_GRAPH(astExp, graphHandler.ref_fields(wrapper.input.fields), wrapper.input, closed = wantedType.isInstanceOf[Closed], true, true, dag = wantedType.isInstanceOf[DAG], TrueLit()(), (exp1, exp2) => And(exp1, exp2)())
        Some(Seq(checkQPs))
    }
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