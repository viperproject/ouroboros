package viper.silver.plugin

import viper.silver.ast._
import viper.silver.ast.utility.Rewriter.Rewritable
import viper.silver.plugin
import viper.silver.plugin._
import viper.silver.plugin.errors.OuroborosTypeError
import viper.silver.plugin.reasons.WrongTypeReason

import scala.collection.mutable

//TODO need to add unique IDs for each assignment

trait SetExp {
  def getDuplicateExp(pos: Position = NoPosition, info: Info = NoInfo, errT: ErrorTrafo = NoTrafos): Exp

}

object SetExp {
  def getSetExp(setExp: Exp, wrapper: OuroborosStateWrapper): SetExp = setExp match {
    case union: AnySetUnion =>
      SetUnion(getSetExp(union.left, wrapper), getSetExp(union.right, wrapper))
    case setminus: AnySetMinus =>
      SetMinus(getSetExp(setminus.left, wrapper), getSetExp(setminus.right, wrapper))
    case localVar: LocalVar =>
      SetVar(localVar.name, wrapper.getType(localVar.name))
    case explicitSet: ExplicitSet =>
      ExplicitSetExp(Seq() ++ explicitSet.elems)
    //case _ => //TODO throw error
  }
}

abstract class SetBinExp extends SetExp {
  val lhs: SetExp
  val rhs: SetExp
  def operator(): String

}
case class SetUnion(lhsUnion:SetExp, rhsUnion:SetExp) extends SetBinExp {
  override val lhs: SetExp = lhsUnion
  override val rhs: SetExp = rhsUnion
  override def operator(): String = "set union"

  override def getDuplicateExp(pos: Position, info: Info, errT: ErrorTrafo): Exp = {
    val lhsExp = lhsUnion.getDuplicateExp(pos, info, errT)
    val rhsExp = rhsUnion.getDuplicateExp(pos, info, errT)
    AnySetUnion(lhsExp, rhsExp)(pos, info, errT)
  }
}
//case class SetIntersect
case class SetMinus(lhsSetMinus:SetExp, rhsSetMinus:SetExp) extends SetBinExp {
  override val lhs: SetExp = lhsSetMinus
  override val rhs: SetExp = rhsSetMinus
  override def operator(): String = "set minus"

  override def getDuplicateExp(pos: Position, info: Info, errT: ErrorTrafo): Exp = {
    val lhsExp = lhsSetMinus.getDuplicateExp(pos, info, errT)
    val rhsExp = lhsSetMinus.getDuplicateExp(pos, info, errT)
    AnySetMinus(lhsExp, rhsExp)(pos, info, errT)
  }
}
case class SetVar(varName: String, ourType: Topology with Closedness) extends SetExp {
  override def getDuplicateExp(pos: Position, info: Info, errT: ErrorTrafo): Exp = {
    LocalVar(varName)(SetType(Ref), pos, info, errT)
  }
}
case class ExplicitSetExp(elems: Seq[Exp]) extends SetExp {
  override def getDuplicateExp(pos: Position, info: Info, errT: ErrorTrafo): Exp = {
    ExplicitSet(elems.map(exp => exp.duplicateMeta(pos, info, errT).asInstanceOf[Exp]))(pos, info, errT)
  }
}

class OuroborosReachingDefinition {

  val graphHandler = new OuroborosGraphHandler()
  val typeChecker = new OuroborosTypeCheck()

  def handleMethod(method: Method, specs: mutable.Map[String, OurGraphSpec], input: Program): (Method, Seq[OuroborosAbstractVerificationError]) = method.body match {
      case None =>
        (method, mutable.Seq.empty[OuroborosAbstractVerificationError])
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
          result._2
        )
   }

  def handleBody(seqn: Seqn, method: Method, specs: mutable.Map[String, OurGraphSpec], input: Program): (Seqn, mutable.Seq[OuroborosAbstractVerificationError]) = {

    val spec = specs.get(method.name)
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


    val programSpecs: Map[String, OurGraphSpec] = Map.empty[String, OurGraphSpec] ++ specs
    val existingGraphs: mutable.Map[String, (Topology with Closedness, LocalVarDecl, Integer)] =
      mutable.Map.empty[String, (Topology with Closedness, LocalVarDecl, Integer)]
    val definitions: mutable.Map[String, mutable.Map[Integer, (Stmt, OuroborosStateWrapper)]] = mutable.Map.empty[String, mutable.Map[Integer, (Stmt, OuroborosStateWrapper)]]
    val errors: mutable.Buffer[OuroborosAbstractVerificationError] = mutable.Buffer.empty[OuroborosAbstractVerificationError]
    val wrapper: OuroborosStateWrapper = OuroborosStateWrapper(input, programSpecs, inputGraphs, existingGraphs, definitions, errors, true)
    val newSeqn = handleSeqn(seqn, wrapper, true) match {
      case s: Seqn => Seqn(s.ss, s.scopedDecls)(s.pos, s.info, s.errT)
      case s => Seqn(Seq(s), Seq())(s.pos, s.info, s.errT)
    }

    (newSeqn, wrapper.errors)
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
      case _ => stmt
//      case exhale: Exhale => handleExhale(exhale, wrapper) //Fork. TODO Check Type Invariance? For that we need Protected Graphs

    }
  }

  def handleWhile(whileStmt: While, wrapper: OuroborosStateWrapper): Stmt = {
    val body = whileStmt.body
    val bodyWrapper = wrapper.copy(checkType = false)

    val newStmt = handleSeqn(body, bodyWrapper, isTop = false)

    wrapper.join(bodyWrapper)


    val newBody = handleSeqn(newStmt, wrapper, isTop = false)
    While(whileStmt.cond, whileStmt.invs, newBody)(whileStmt.pos, whileStmt.info, whileStmt.errT)
  }

  def handleMethodCall(call: MethodCall, wrapper: OuroborosStateWrapper): Stmt = {
    //TODO translate update methods correctly
    //TODO delete all definitions! (or add new fake definitions?)
    //TODO or add methodcall as definiton to all userDefinedGraphs => change type check
    val asserts: Seq[Stmt] = if(wrapper.typeCheck) {
      call.targets.collect({
        case localVar if wrapper.userDefinedGraphs.contains(localVar.name) =>
          val assignUniqueValue = addDefinition(call, localVar.name, wrapper)
          val localVarSpecs: (Topology with Closedness, LocalVarDecl, Integer) = wrapper.userDefinedGraphs(localVar.name)
          val localVarType = localVarSpecs._1
          val maybeCheckExp = typeChecker.checkDefinition(localVarType, call, localVar.name, wrapper, call)
          maybeCheckExp match {
            case None =>
              //the type of the method call does not return the wanted Type
              wrapper.errors += OuroborosTypeError(call, WrongTypeReason(call, s"Variable $localVar might not be of wished type after the method call $call."))
              Seq()
            case Some(checkExps) =>
              if(checkExps.isEmpty) {
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
                  SimpleInfo(Seq("", s"Added assertion to type check MethodCall.\n")),
                  OuroborosErrorTransformers.wrongTypeErrTrafo(call, localVarType)
                )

                Seq(assignUniqueValue, assertCheck)
              }
          }
      }).flatten
    } else Seq()

    if(asserts.isEmpty) {
      call
    } else {
      Seqn(call +: asserts, Seq())(call.pos, NoInfo, call.errT)
    }
  }

  def handleSeqn(seqn: Seqn, wrapper: OuroborosStateWrapper, isTop: Boolean): Seqn = {
    Seqn(seqn.ss.map(stmt => handleStmt(stmt, wrapper)), seqn.scopedDecls)(seqn.pos, seqn.info, seqn.errT)
  }

  def handleIf(ifStmt: If, wrapper: OuroborosStateWrapper): Stmt = {
    //TODO take separate wrappers for if or else blocks.
    //TODO after iterating over both blocks, take union of them and set as new wrapper state.
    val thnWrapper = wrapper.copy(wrapper.typeCheck)

    val thn = handleSeqn(ifStmt.thn, thnWrapper, false)

    wrapper.getLastDefinitionValues(thnWrapper)
    val elsWrapper = wrapper.copy(wrapper.typeCheck)

    val els = handleSeqn(ifStmt.els, elsWrapper, false)

    wrapper.join(thnWrapper, elsWrapper)

    If(ifStmt.cond, thn, els)(ifStmt.pos, ifStmt.info, ifStmt.errT)
  }


  def handleInhale(inhale: Inhale, wrapper: OuroborosStateWrapper): Stmt = {
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
            val initVar = func.args.last.asInstanceOf[LocalVar]
            val integerMapping: mutable.Map[Integer, (Stmt, OuroborosStateWrapper)] = mutable.Map.empty[Integer, (Stmt, OuroborosStateWrapper)]
            val fakeDef = LocalVarAssign(LocalVar(thisGraph.name)(SetType(Ref)), LocalVar(thisGraph.name)(SetType(Ref)))()

            integerMapping.put(0, (fakeDef, wrapper.copy()))
            wrapper.userDefinedGraphs.put(thisGraph.name, (ourType, LocalVarDecl(initVar.name, Int)(), 0))
            wrapper.definitions.put(thisGraph.name, integerMapping)
            Seqn(Seq(),Seq())(inhale.pos, inhale.info, inhale.errT)
          case None => inhale
        }
      case _ => inhale //TODO other cases (Type checking)
    }
  }

  def handleFieldAssign(assign: FieldAssign, wrapper: OuroborosStateWrapper): Stmt = {
    val inputGraphs = wrapper.inputGraphs
    val userDefinedGraphs = wrapper.userDefinedGraphs
    assign
  }

  def handleLocalVarAssign(assign: LocalVarAssign, wrapper: OuroborosStateWrapper): Stmt = {
    val lhs = assign.lhs
    wrapper.userDefinedGraphs.get(lhs.name) match {
      case None => assign
      case Some(tuple) =>
        val ourType = tuple._1
        val initDecl = tuple._2
        val lastDefVal = tuple._3

        val assignUniqueValue = LocalVarAssign(LocalVar(initDecl.name)(Int), IntLit(lastDefVal + 1)())(assign.pos, SimpleInfo(Seq("", s"assign unique value ${lastDefVal + 1} to the assignment of $lhs\n")), assign.errT)

        var allStmts: Seq[Stmt] = Seq(assignUniqueValue, assign)

        if(wrapper.typeCheck) {
          val typeCheckResult = typeChecker.checkTypeOfExp(ourType, assign.rhs, wrapper, assign)
          // typeCheckResult is None, if no checks have to be added.
          if (typeCheckResult.isDefined)
            allStmts =  Seq(assignUniqueValue, assign, typeCheckResult.get)
        }

        val integerMapping: mutable.Map[Integer, (Stmt, OuroborosStateWrapper)] = mutable.Map.empty[Integer, (Stmt, OuroborosStateWrapper)]
        integerMapping.put(lastDefVal + 1, (assign, wrapper.copy()))
        wrapper.definitions.put(lhs.name, integerMapping)
        wrapper.userDefinedGraphs.put(lhs.name, (ourType, initDecl, lastDefVal + 1))

        Seqn(allStmts, Seq())(assign.pos, NoInfo, assign.errT)
    }
  }

  def addDefinition(definition: Stmt, definedVarName: String, wrapper: OuroborosStateWrapper): Stmt = {
    wrapper.userDefinedGraphs.get(definedVarName) match {
      case None =>
        assert(false, s"internal Error")
        Seqn(Seq(), Seq())()
      case Some(triple) =>
        val ourType = triple._1
        val initDecl = triple._2
        val lastDefVal = triple._3
        val assignUniqueValue = LocalVarAssign(LocalVar(initDecl.name)(Int), IntLit(lastDefVal + 1)())(definition.pos, SimpleInfo(Seq("", s"assign unique value ${lastDefVal + 1} to the assignment of $definedVarName \n")), definition.errT)

        val integerMapping: mutable.Map[Integer, (Stmt, OuroborosStateWrapper)] = mutable.Map.empty[Integer, (Stmt, OuroborosStateWrapper)]
        integerMapping.put(lastDefVal + 1, (definition, wrapper.copy()))
        wrapper.definitions.put(definedVarName, integerMapping)
        wrapper.userDefinedGraphs.put(definedVarName, (ourType, initDecl, lastDefVal + 1))

        assignUniqueValue

    }
  }
}

case class OuroborosStateWrapper(
                                  input: Program,
                                  specs: Map[String, OurGraphSpec],
                                  inputGraphs: Map[String, Topology with Closedness],
                                  userDefinedGraphs: mutable.Map[String, (Topology with Closedness, LocalVarDecl, Integer)],
                                  definitions: mutable.Map[String, mutable.Map[Integer, (Stmt, OuroborosStateWrapper)]],
                                  errors: mutable.Buffer[OuroborosAbstractVerificationError],
                                  typeCheck: Boolean
                           ) {

  def copy(checkType: Boolean): OuroborosStateWrapper = {
    val newInputGraphs = Map.empty[String, Topology with Closedness] ++ inputGraphs
    val newUserDefinedGraphs = mutable.Map.empty[String, (Topology with Closedness, LocalVarDecl, Integer)] ++ userDefinedGraphs
    val newDefs = mutable.Map.empty[String, mutable.Map[Integer, (Stmt, OuroborosStateWrapper)]] ++ definitions
    OuroborosStateWrapper(input, specs, newInputGraphs, newUserDefinedGraphs, newDefs, errors, checkType)

  }

  def copy(): OuroborosStateWrapper = {
    copy(typeCheck)
  }

  def join(otherWrapper: OuroborosStateWrapper): Unit = {
    //TODO inputGraphs: get new lastDefValues (use method getLastDefValues)
    //input, specs, inputGraphs, userDefinedGraphs and typeChecks stay
    //definitions: All definitions, that have not been locally declared, are added
    otherWrapper.definitions.collect({
      case tuple if definitions.contains(tuple._1) =>
        val graphName = tuple._1
        val graphDefinitions = tuple._2
        definitions(tuple._1) ++= graphDefinitions
    })

    getLastDefinitionValues(otherWrapper)


  }

  def join(succ1: OuroborosStateWrapper, succ2: OuroborosStateWrapper): Unit = {
    //TODO join two states
    //input, specs, inputGraphs
    //getLastDefinitionValues(succ1)
    getLastDefinitionValues(succ2)
    succ1.join(succ2)
    join(succ1)

  }

  def checkType(wantedType: Topology with Closedness, setExp: Exp): Boolean = {

    false
  }

  def getType(graphName: String): Topology with Closedness = {
    if(graphName == "UNIVERSE") {
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


