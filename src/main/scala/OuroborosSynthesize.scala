package viper.silver.plugin

import viper.silver.ast.Inhale
import viper.silver.ast.utility.Rewriter.StrategyBuilder
import viper.silver.parser._

import scala.collection.mutable

object OuroborosSynthesize {

  def synthesize(program: PProgram, fields: Seq[String]) = {
    PProgram(
      program.imports,
      Seq(),//program.macros,
      program.domains,
      program.fields,
      program.functions.map(f => synthesizeFunction(f, fields)),
      program.predicates,
      program.methods.flatMap(m => synthesizeMethod(m, fields)),
      program.errors
    )
  }

/*
  def synthesizeMacro(define: PDefine, fields: Seq[String]) = {
    define.idndef.name match {
      case "CLOSED" => synthesizeClosed(define, fields)
      case _ => define
    }
  }
*/

  def synthesizeFunction(function: PFunction, fields: Seq[String]) = {

    function.idndef.name match {
      case "apply_TCFraming" => {
        function.deepCopy(pres =
          collectQPsForRefFields(fields, PIdnUse("g0"), this.read) ++
            collectQPsForRefFields(fields, PIdnUse("g1"), this.read) ++
            function.pres)
      }

      case "$$" => synthesize$$(function, fields)

      case "CLOSED" => synthesizeClosed(function, fields)

      case _ => function
      }
  }

  def synthesize$$(proto_f: PFunction,fields:Seq[String])= {
      proto_f.deepCopy(pres =
        collectQPsForRefFields(fields, PIdnUse("nodes"), this.read) ++
          proto_f.pres,
        posts =  Seq(PForall(
          Seq(
            PFormalArgDecl(PIdnDef("p"), TypeHelper.Ref),
            PFormalArgDecl(PIdnDef("s"), TypeHelper.Ref)),
          Seq(
            PTrigger(Seq(
              PCall(PIdnUse("create_edge"),Seq(PIdnUse("p"),PIdnUse("s")))))),
          PBinExp(
            PBinExp(
              PBinExp(
                PBinExp(
                  PBinExp(PIdnUse("p"), "in", PIdnUse("nodes")),
                  "&&",
                  PBinExp(PIdnUse("s"), "in", PIdnUse("nodes"))),
                "&&",
                OuroborosHelper.transformAndFold[String, PExp](fields, PBoolLit(false), (expr1, expr2) => PBinExp(expr1, "||", expr2), f => PBinExp(
                  PFieldAccess(PIdnUse("p"),PIdnUse(f) ), "==", PIdnUse("s")))),
              "&&",
              PBinExp(PIdnUse("p"), "!=", PIdnUse("s"))),
            "<==>",
            PBinExp(
              PCall(PIdnUse("create_edge"),Seq(PIdnUse("p"),PIdnUse("s"))),
              "in",
              PResultLit()
            )
          )
        )) ++ proto_f.posts
      )
  }

  def synthesizeClosed(function: PFunction, fields: Seq[String]): PFunction = {
    function.body match {
      case None => function
      case Some(body) =>
        var fieldName = "$field$"
        val bodySynthesizer = StrategyBuilder.Slim[PNode](
          {
            case i: PIdnUse if i.name == "$field$" => PIdnUse(fieldName)
          }
        ).duplicateEverything

        function.deepCopy(
          pres = function.pres.map(p =>
            OuroborosHelper.transformAndFold[String, PExp](fields, PBoolLit(true), (exp1, exp2) => PBinExp(exp1, "&&", exp2), f => {
              fieldName = f
              bodySynthesizer.execute[PExp](p)
            })),
          body = Some(
            OuroborosHelper.transformAndFold[String, PExp](fields, PBoolLit(true), (exp1, exp2) => PBinExp(exp1, "&&", exp2), f => {
              fieldName = f
              bodySynthesizer.execute[PExp](body)
            }))
        )
    }

  }

  private def read = PBinExp(PIntLit(1), "/", PIntLit(2)).deepCopyAll[PExp]

  private def collectQPsForRefFields(fields: Seq[String], graph_exp: PExp, perm_exp: PExp = PFullPerm()): Seq[PExp] =
    fields.map(f => getQPForGraphNodes(graph_exp, f, perm_exp))

  private def getQPForGraphNodes(graph_exp: PExp, field: String, perm_exp: PExp = PFullPerm()): PExp = PForall(
    Seq(PFormalArgDecl(PIdnDef("n"), TypeHelper.Ref)),
    Seq(PTrigger( Seq( PFieldAccess(PIdnUse("n"),PIdnUse(field))))),
    PBinExp( PBinExp(PIdnUse("n"), "in", graph_exp.deepCopyAll[PExp]), "==>", PAccPred(PFieldAccess(PIdnUse("n"), PIdnUse(field)), perm_exp.deepCopyAll[PExp])))

  def synthesizeMethod(method: PMethod, fields: Seq[String]) = {
    method match {
      case m: PMethod if m.idndef.name == "link_$field$" =>
        fields.map(
          { f =>
            val new_m = m.deepCopyWithNameSubstitution(
              idndef = PIdnDef(s"link_${f}"))(
              "$field$", f)
            new_m
          }
        )


      case m: PMethod if m.idndef.name == "unlink_$field$" =>
        fields.map(
          { f =>
            val new_m = m.deepCopyWithNameSubstitution(
              idndef = PIdnDef(s"unlink_$f"))(
              "$field$", f)
            new_m
          }
        )
      case m: PMethod if m.idndef.name == "update_$field$" =>
        //println("UPDATE")
        fields.map(
          f =>
            m.deepCopyWithNameSubstitution(
              idndef = PIdnDef(s"update_$f"))(
              "$field$", f)
        )
      case m: PMethod if m.idndef.name == "link_ZOPG_$field$" =>
        fields.map(
          f =>
            m.deepCopyWithNameSubstitution(
              idndef = PIdnDef(s"link_ZOPG_$f"))(
              "$field$", f)
        )
      case m: PMethod if m.idndef.name == "unlink_ZOPG_$field$" =>
        fields.map(
          f =>
            m.deepCopyWithNameSubstitution(
              idndef = PIdnDef(s"unlink_ZOPG_$f"))(
              "$field$", f)
        )
      case m: PMethod if m.idndef.name == "update_ZOPG_$field$" =>
        fields.map(
          f =>
            m.deepCopyWithNameSubstitution(
              idndef = PIdnDef(s"update_ZOPG_$f"))(
              "$field$", f)
        )
      case m: PMethod if m.idndef.name == "link_DAG_$field$" =>
        fields.map(
          f =>
            m.deepCopyWithNameSubstitution(
              idndef = PIdnDef(s"link_DAG_$f"))(
              "$field$", f)
        )
      case m: PMethod if m.idndef.name == "unlink_DAG_$field$" =>
        fields.map(
          f =>
            m.deepCopyWithNameSubstitution(
              idndef = PIdnDef(s"unlink_DAG_$f"))(
              "$field$", f)
        )
      case m: PMethod if m.idndef.name == "update_DAG_$field$" =>
        fields.map(
          f =>
            m.deepCopyWithNameSubstitution(
              idndef = PIdnDef(s"update_DAG_$f"))(
              "$field$", f)
        )
      case m: PMethod if m.idndef.name == "create_node" =>
        var fieldName = "$field$"
        val postSynthesizer = StrategyBuilder.Slim[PNode](
          {
            case i: PIdnUse if i.name == "$field$" => PIdnUse(fieldName)
          }
        ).duplicateEverything
        var containsDollarFieldDollar = false
        val containsDollarFieldDollarStrategy = StrategyBuilder.Slim[PNode](
          {
            case i: PIdnUse if i.name == "$field$" => containsDollarFieldDollar = true; i
          }
        )
        val newMethod = PMethod(
          m.idndef,
          m.formalArgs,
          m.formalReturns,
          m.pres,
          m.posts.map(post => {
            containsDollarFieldDollar = false
            containsDollarFieldDollarStrategy.execute[PExp](post)
            if(containsDollarFieldDollar)
              OuroborosHelper.transformAndFold[String, PExp](
                fields, PBoolLit(true), (exp1, exp2) => PBinExp(exp1, "&&", exp2), f => {
                  fieldName = f
                  postSynthesizer.execute[PExp](post)
                }
              )
            else
              post
          }),
          m.body
        ).setPos(m)

        Seq(newMethod)
      case m: PMethod => Seq(m)
    }
  }
}
