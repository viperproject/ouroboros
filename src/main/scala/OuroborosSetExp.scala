package viper.silver.plugin

import viper.silver.ast._
import viper.silver.plugin.{Closedness, OuroborosStateWrapper, Topology}

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
      val mayBeInitName = wrapper.userDefinedGraphs.get(localVar.name) match {
        case None =>
          //must be an inputGraph, cannot be reassigned
          None
        case Some((_, initVarDecl, _)) =>
          //is a local variable
          Some(initVarDecl.name)
      }
      SetVar(localVar.name, mayBeInitName, wrapper.getType(localVar.name))
    case explicitSet: ExplicitSet =>
      ExplicitSetExp(Seq() ++ explicitSet.elems)
    //case _ => //TODO throw error
  }

  def getSuperSetOfGraphs(setExp: SetExp, isTop: Boolean): Seq[String] = setExp match {
    case setBinExp: SetBinExp if isTop =>
      val lhsGraphs = getSuperSetOfGraphs(setBinExp.lhs, false)
      val rhsGraphs = getSuperSetOfGraphs(setBinExp.rhs, false)
      lhsGraphs ++ rhsGraphs
    case setBinExp: SetBinExp if !isTop =>
      val lhsGraphs = getSuperSetOfGraphs(setBinExp.lhs, false)
      val rhsGraphs = setBinExp match {
        case _: SetMinus => Seq()
        case _: SetUnion => getSuperSetOfGraphs(setBinExp.rhs, false)
      }
      lhsGraphs ++ rhsGraphs
    case setVar: SetVar =>
      Seq(setVar.varName)
    case setExp: ExplicitSetExp =>
      Seq(OuroborosNames.getIdentifier("UNIVERSE")) //TODO do it nicer
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
case class SetVar(varName: String, initVarName: Option[String], ourType: Topology with Closedness) extends SetExp {
  override def getDuplicateExp(pos: Position, info: Info, errT: ErrorTrafo): Exp = {
    LocalVar(varName)(SetType(Ref), pos, info, errT)
  }
}
case class ExplicitSetExp(elems: Seq[Exp]) extends SetExp {
  override def getDuplicateExp(pos: Position, info: Info, errT: ErrorTrafo): Exp = {
    ExplicitSet(elems.map(exp => exp.duplicateMeta(pos, info, errT).asInstanceOf[Exp]))(pos, info, errT)
  }
}