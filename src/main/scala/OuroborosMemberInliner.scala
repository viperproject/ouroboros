package viper.silver.plugin

import viper.silver.ast._
import viper.silver.ast.utility.Rewriter.{ContextC, StrategyBuilder}

import scala.collection.mutable

object OuroborosMemberInliner {
  var zopgUsed: Boolean = false
  def inlineFunction(fc: FuncApp, input: Program, pos: Position, info: Info, errT: ErrorTrafo): Exp = {
    val func = input.findFunction(fc.funcname)
    func.body match {
      case Some(macro_def) =>
        val funcArgs = func.formalArgs.map(arg => arg.name)
        val callArgs = fc.getArgs
        StrategyBuilder.Slim[Node](
          {
            case x: LocalVar if funcArgs.contains(x.name) =>
              callArgs(funcArgs.indexOf(x.name)).duplicateMeta((pos, info, errT))
            case n => n.duplicateMeta((pos, info, errT))
          }
        ).duplicateEverything.execute[Exp](macro_def) //TODO CLOSED: "graph might not be closed" and not wellformed => insufficient permission

      case None => fc
    }
  }

  def inlineMethod(mc: MethodCall, input: Program, pos: Position, info: Info, errT: ErrorTrafo): Stmt = {
    val calledMethod = input.findMethod(mc.methodName)
    val methodArgs = calledMethod.formalArgs.map(arg => arg.name)
    val callArgs = mc.args
    val label = Label(
      OuroborosNames.getNewName(s"inlinedMethodCall_${mc.methodName}"), Seq())()
    assert(methodArgs.size == callArgs.size)
    val contractsRewriter = StrategyBuilder.Slim[Node](
      {
        case x: LocalVar if methodArgs.contains(x.name) =>
          callArgs(methodArgs.indexOf(x.name)).duplicateMeta((pos, info, errT))
        case o: Old => LabelledOld(o.exp, label.name)(pos, info, errT)
        case n => n.duplicateMeta((pos, info, errT))
      }
    ).duplicateEverything

    calledMethod.body match {
      case None =>
        var contractsInlined : Seq[Stmt] = Seq()
        contractsInlined ++= calledMethod.pres.map(exp => Exhale(contractsRewriter.execute[Exp](exp))(pos, info, errT))
        contractsInlined ++= calledMethod.posts.map(exp => Inhale(contractsRewriter.execute[Exp](exp))(pos, info, errT))
        Seqn(label +: contractsInlined, Seq())(pos, SimpleInfo(Seq("", s"inlined $mc \n")), errT)

      case Some(body) =>
        assert(calledMethod.pres.isEmpty && calledMethod.posts.isEmpty)
        assert(calledMethod.name == OuroborosNames.getIdentifier("create_node"))
        assert(mc.targets.size == 1)
        assert(callArgs.size == 1)
        val formalArg = methodArgs.head
        val universe = mc.args.head
        val target = mc.targets.head
        val oldLhsNode = body.scopedDecls.find({
          case x:LocalVarDecl => x.name.startsWith("lhs_node")
          case _ => false
        }).get.name
        val lhs_node = target.name
        val oldFreshX = body.scopedDecls.find({
          case x:LocalVarDecl => x.name.startsWith("fresh_x")
          case _ => false
        }).get.asInstanceOf[LocalVarDecl].name
        val newFreshTarget = OuroborosNames.getNewName(s"fresh_${target.name}")
        val oldSingletonGraph = body.scopedDecls.find({
          case x:LocalVarDecl => x.name.startsWith("singleton_graph")
          case _ => false
        }).get.asInstanceOf[LocalVarDecl].name
        val newSingletonGraph = OuroborosNames.getNewName(s"singleton_graph_${target.name}")
        val bodySynthesizer = StrategyBuilder.Slim[Node]({
          case x: LocalVar if x.name == oldLhsNode => LocalVar(lhs_node)(Ref)
          case x: LocalVar if x.name == oldFreshX => LocalVar(newFreshTarget)(Ref)
          case x: LocalVar if x.name == oldSingletonGraph => LocalVar(newSingletonGraph)(SetType(Ref))
          case x: LocalVar if x.name == formalArg => universe.duplicateMeta((x.pos, x.info, x.errT))
        })
        val fresh_xDecl = LocalVarDecl(newFreshTarget, Ref)()
        val singleton_graphDecl = LocalVarDecl(newSingletonGraph, SetType(Ref))()
        val decls = Seq(fresh_xDecl, singleton_graphDecl)
        Seqn(bodySynthesizer.execute[Seqn](body).ss,decls)(body.pos, SimpleInfo(Seq("", s"create_node(universe = $universe)\n")), body.errT)

    }
  }

  def inlineInhaleFunction(inhale: Inhale, fc: FuncApp,  input: Program, pos: Position, info: Info, errT: ErrorTrafo): Stmt = {
    val func = input.findFunction(fc.funcname)
    val funcArgs = func.formalArgs.map(arg => arg.name)
    val callArgs = fc.getArgs
    func.body match {
      case Some(_) => inhale //TODO

      case None => {
        var contractsInlined : Seq[Stmt] = Seq()

        val contractsRewriter = StrategyBuilder.Slim[Node](
          {
            case x: LocalVar if funcArgs.contains(x.name) =>
              callArgs(funcArgs.indexOf(x.name)).duplicateMeta((pos, info, errT))
            case n => n.duplicateMeta((pos, info, errT))
          }
        ).duplicateEverything

        //var impureExps : Seq[Stmt] = Seq()
        contractsInlined ++= func.pres.collect({
          case exp: Exp if exp.isPure => {
            //if (!exp.isPure) impureExps :+= Inhale(contractsRewriter.execute[Exp](exp))(pos, info, errT)
            Exhale(contractsRewriter.execute[Exp](exp))(pos, info, errT)
          }
        }
        )
       // contractsInlined ++= impureExps
        contractsInlined ++= func.posts.map(exp => Inhale(contractsRewriter.execute[Exp](exp))(pos, info, errT))
        Seqn(contractsInlined, Seq())(pos, info, errT)
      }
    }
  }
}
