package viper.silver.plugin

import viper.silver.ast._

import scala.collection.mutable

case class OuroborosStmtWrapper(
                                 input: Program,
                                 inputGraphs: Map[String, Topology with Closedness],
                                 userDefinedGraphs: mutable.Map[String, (Topology with Closedness, LocalVarDecl)],
                                 scope: Option[LocalVarDecl],
                                 newlyDeclaredVariables: mutable.Map[Option[LocalVarDecl], Set[LocalVarDecl]],
                                 newlyDeclaredInitVariables: mutable.Buffer[LocalVarDecl],
                                 dontConsiderScopes: mutable.Set[Option[LocalVarDecl]]
                               )
{

  def setScope(newScope: Option[LocalVarDecl]): OuroborosStmtWrapper = {
    val existingCopy: mutable.Map[String, (Topology with Closedness, LocalVarDecl)]
    = mutable.Map.empty ++ userDefinedGraphs
    OuroborosStmtWrapper(input,inputGraphs, existingCopy, newScope, newlyDeclaredVariables, newlyDeclaredInitVariables, dontConsiderScopes)
  }

  def allGraphsMapping(/*scopes: mutable.Buffer[Option[LocalVarDecl]]*/): mutable.Map[Option[LocalVarDecl], Set[Exp]] = {
    val toReturn: mutable.Map[Option[LocalVarDecl], Set[Exp]] = newlyDeclaredVariables.map(tuple => (tuple._1, tuple._2.map(decl =>
      ExplicitSet(Seq(LocalVar(decl.name)(Ref)))().asInstanceOf[Exp]))) //TODO why do we need to cast?
    userDefinedGraphs foreach(tuple =>{
      val graphName = tuple._1
      val initDecl = tuple._2._2
      toReturn.put(Some(initDecl), Set(LocalVar(graphName)(SetType(Ref))))
      /*      toReturn.get(scope) match {
              case None => toReturn.put(scope, names)
              case Some(oldNames) => toReturn.put(scope, oldNames ++ names)
            }*/
    })


    toReturn.get(None) match {
      case None => toReturn.put(None, inputGraphs.keySet.map(graphName => LocalVar(graphName)(SetType(Ref))))
      case Some(decls) => toReturn.put(None, decls ++ inputGraphs.keySet.map(graphName => LocalVar(graphName)(SetType(Ref))))
    }

    toReturn
  }

  def allUserDefinedGraphs(/*scopes: mutable.Buffer[Option[LocalVarDecl]]*/): Set[String] = {
    userDefinedGraphs.collect({
      case tuple /*if scopes.contains(tuple._1)*/ => tuple._1
    })/*.flatten*/.toSet
  }

  def getUserDefinedGraphInitDecl(graphName: String/*, scopes: mutable.Buffer[Option[LocalVarDecl]]*/): Option[LocalVarDecl] = {
    val graphInitDecl: Option[LocalVarDecl] = userDefinedGraphs.get(graphName) match {
      case None => None
      case Some(tuple) => Some(tuple._2)
    }

    graphInitDecl
  }
}


case class OuroborosStateWrapper(
                                  input: Program,
                                  specs: Map[String, OurGraphSpec],
                                  inputGraphs: Map[String, Topology with Closedness],
                                  stateCopies: mutable.Map[Stmt, StateCopyWrapper],
                                  userDefinedGraphs: mutable.Map[String, (Topology with Closedness, LocalVarDecl, Integer)],
                                  definitions: mutable.Map[String, mutable.Map[Integer, (Stmt, OuroborosStateWrapper)]],
                                  errors: mutable.Buffer[OuroborosAbstractVerificationError],
                                  typeCheck: Boolean
                                ) {

  def copy(checkType: Boolean): OuroborosStateWrapper = {
    val newInputGraphs = Map.empty[String, Topology with Closedness] ++ inputGraphs //TODO needed?
    val newUserDefinedGraphs = mutable.Map.empty[String, (Topology with Closedness, LocalVarDecl, Integer)] ++ userDefinedGraphs
    val newDefs = mutable.Map.empty[String, mutable.Map[Integer, (Stmt, OuroborosStateWrapper)]] ++ definitions
    OuroborosStateWrapper(input, specs, newInputGraphs, stateCopies, newUserDefinedGraphs, newDefs, errors, checkType)

  }

  def copy(): OuroborosStateWrapper = {
    copy(typeCheck)
  }

  def copyError(): OuroborosStateWrapper = {
    val newErrors = mutable.Buffer.empty[OuroborosAbstractVerificationError] ++ errors
    OuroborosStateWrapper(input, specs, inputGraphs, stateCopies, userDefinedGraphs, definitions, newErrors, typeCheck)
  }


  //This Function is used, if the next line executed with this Wrapper and otherWrapper are the same
  def joinAfterWhile(otherWrapper: OuroborosStateWrapper): Unit = {
    //TODO inputGraphs: get new lastDefValues (use method getLastDefValues)
    //input, specs, inputGraphs, userDefinedGraphs and typeChecks stay
    //definitions: All definitions, that have not been locally declared, are added
    otherWrapper.definitions.collect({
      case tuple if definitions.contains(tuple._1) =>
        val graphName = tuple._1
        val graphDefinitions = tuple._2
        definitions(tuple._1) ++= graphDefinitions
    })

    //getLastDefinitionValues(otherWrapper)


  }

  def joinAfterIf(succ1: OuroborosStateWrapper, succ2: OuroborosStateWrapper): Unit = {
    //TODO join two states with this
    //input, specs, inputGraphs and typeChecks stay
    //userDefinedGraphs get new last definition values
    //
    //getLastDefinitionValues(succ1) //Already done in handleIf
    getLastDefinitionValues(succ2)

    succ1.definitions.collect( {
      case (s, succ1Map) if definitions.contains(s) =>
        val succ2Map = succ2.definitions(s)
        val resultMap: mutable.Map[Integer, (Stmt, OuroborosStateWrapper)] = succ1Map ++ succ2Map
        definitions.put(s, resultMap)
    })
  }


  def getType(graphName: String): Topology with Closedness = {
    if(graphName == OuroborosNames.getIdentifier("UNIVERSE")) {
      return OurGraph
    }
    inputGraphs.get(graphName) match {
      case None =>
        userDefinedGraphs.get(graphName) match {
          //case None => //TODO should not happen
          case Some(tuple) =>
            tuple._1
        }
      case Some(ourType) =>
        ourType
    }
  }

  def getLastDefinitionValues(otherWrapper: OuroborosStateWrapper): Unit = {
    otherWrapper.userDefinedGraphs.foreach(tuple => {
      val graphName = tuple._1
      if(userDefinedGraphs.contains(graphName)) {
        val thisSpecs = userDefinedGraphs(graphName)
        val thisLastDefValue = thisSpecs._3
        val otherLastDefValue = tuple._2._3
        if(thisLastDefValue < otherLastDefValue) {
          val ourType = thisSpecs._1
          val initDecl = thisSpecs._2
          userDefinedGraphs.put(graphName, (ourType, initDecl, otherLastDefValue))
        }
      }
    })
  }

}

case class TypeClosedAcyclicWrapper(ourType: Topology with Closedness, closedAcyclicWrapper: ClosedAcyclicWrapper)
case class ClosedAcyclicWrapper(checkClosedness: Boolean, checkAcyclicity: Boolean)
case class BinaryTypesWrapper(lhs: Topology with Closedness, rhs: Topology with Closedness)

case class StateCopyWrapper(
                                      localVarNamesMapping: Map[String, NewNameWrapper],
                                      explicitSetsMapping: Map[ExplicitSetExp, String],
                                      newStmts: Seq[Stmt],
                                      newDecls: Seq[LocalVarDecl]
                                    )
{

  def isEmpty: Boolean = localVarNamesMapping.isEmpty && explicitSetsMapping.isEmpty && newStmts.isEmpty && newDecls.isEmpty

}

object StateCopyWrapper {
  def createStateCopy(
                       setExp: SetExp,
                       existingStateCopy: StateCopyWrapper = StateCopyWrapper(Map.empty[String, NewNameWrapper], Map.empty[ExplicitSetExp, String], Seq(), Seq())
                     ):
  StateCopyWrapper = setExp match {
    case setVar: SetVar => existingStateCopy.localVarNamesMapping.get(setVar.varName) match {
      case None =>

        setVar.initVarName match {
          case None =>
            //this localVar has no init Variable. This means that it must be an input Graph, which cannot be reassigned.
            //Hence, we don't need to do anything.
            existingStateCopy
          case Some(oldInitVarName) =>
            //We need to copy this variable, and its init Variable.
            val oldLocalVar: LocalVar = setVar.getDuplicateExp().asInstanceOf[LocalVar]
            val newVarName = OuroborosNames.getNewName(s"${oldLocalVar}_copy")
            val varDecl = LocalVarDecl(newVarName, SetType(Ref))()
            val newLocalVar = LocalVar(newVarName)(SetType(Ref))
            val varAssign: LocalVarAssign = LocalVarAssign(newLocalVar, oldLocalVar)()
            val newInitName = OuroborosNames.getNewName(s"${oldLocalVar}_init_copy")
            val oldInitVar = LocalVar(oldInitVarName)(Int)
            val newInitVar = LocalVar(newInitName)(Int)
            val newInitVarDecl = LocalVarDecl(newInitName, Int)()
            val initAssign: LocalVarAssign = LocalVarAssign(newInitVar, oldInitVar)()
            val newNameWrapper = NewNameWrapper(newVarName, newInitName)

            val localVarMapping: Map[String, NewNameWrapper] = existingStateCopy.localVarNamesMapping + ((setVar.varName, newNameWrapper))
            val decls: Seq[LocalVarDecl] = existingStateCopy.newDecls ++ Seq(varDecl, newInitVarDecl)
            val stmts: Seq[Stmt] =  Seq(varAssign, initAssign) ++ existingStateCopy.newStmts

            StateCopyWrapper(localVarMapping, existingStateCopy.explicitSetsMapping, stmts, decls)
        }


      case _ =>
        //this variable has already been copied.
        existingStateCopy
    }

    case setBinExp: SetBinExp =>
      val stateCopyLeft: StateCopyWrapper = createStateCopy(setBinExp.lhs, existingStateCopy)
      val stateCopyRight: StateCopyWrapper = createStateCopy(setBinExp.rhs, stateCopyLeft)

      stateCopyRight
    case explicitSetExp: ExplicitSetExp => existingStateCopy.explicitSetsMapping.get(explicitSetExp) match {
      case None =>
        //We need to copy this explicit Set
        val explicitSet: Exp = explicitSetExp.getDuplicateExp()
        val varName = OuroborosNames.getNewName("explicitSetCopy")
        val varDecl = LocalVarDecl(varName, SetType(Ref))()
        val localVar = LocalVar(varName)(SetType(Ref))
        val varAssign: LocalVarAssign = LocalVarAssign(localVar, explicitSet)()

        val allStmts = varAssign +: existingStateCopy.newStmts
        val allDecls = varDecl +: existingStateCopy.newDecls
        val explSetMapping: Map[ExplicitSetExp, String] = existingStateCopy.explicitSetsMapping + ((explicitSetExp, varName))
        StateCopyWrapper(existingStateCopy.localVarNamesMapping, explSetMapping, allStmts, allDecls)
      case Some(_) =>
        //There is already a copy of an explicit Set, consisting of the same elements.
        existingStateCopy
    }
  }
}

case class NewNameWrapper(
                           newLocalVarName: String,
                           newInitVarName: String
                         )