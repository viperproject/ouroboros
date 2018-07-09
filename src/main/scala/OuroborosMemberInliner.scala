package viper.silver.plugin

import viper.silver.ast._
import viper.silver.ast.utility.Rewriter.StrategyBuilder

object OuroborosMemberInliner {

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
    val namesHandler = new OuroborosNamesHandler
      val method = input.findMethod(mc.methodName)
      val methodArgs = method.formalArgs.map(arg => arg.name)
      val callArgs = mc.args
      val label = Label(
        namesHandler.getNewName(s"inlinedMethodCall_${mc.methodName}"), Seq())()
      if(methodArgs.size != callArgs.size) { //only consider methods that don't return anything
        return mc
      }
      val contractsRewriter = StrategyBuilder.Slim[Node](
        {
          case x: LocalVar if methodArgs.contains(x.name) =>
            callArgs(methodArgs.indexOf(x.name)).duplicateMeta((pos, info, errT))
          case o: Old => LabelledOld(o.exp, label.name)(pos, info, errT)
          case n => n.duplicateMeta((pos, info, errT))
        }
      ).duplicateEverything

      var contractsInlined : Seq[Stmt] = Seq()

      contractsInlined ++= method.pres.map(exp => Exhale(contractsRewriter.execute[Exp](exp))(pos, info, errT))
      contractsInlined ++= method.posts.map(exp => Inhale(contractsRewriter.execute[Exp](exp))(pos, info, errT))
      Seqn(label +: contractsInlined, Seq())(pos, info, errT)
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
