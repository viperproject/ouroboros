package viper.silver.plugin

import viper.silver.ast.utility.Rewriter.StrategyBuilder
import viper.silver.parser._

import scala.collection.mutable

object OuroborosSynthesize {

  var method_keywords : Set[String] = Set()

  def synthesize(program: PProgram, fields: Seq[String]) = {
    method_keywords = Set()
    (PProgram(
      program.imports,
      program.macros,
      program.domains,
      program.fields,
      program.functions.map(f => synthesizeFunction(f, fields)),
      program.predicates,
      program.methods.flatMap(m => synthesizeMethod(m, fields)),
      program.errors
    ),
      method_keywords)
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

    fields.foldRight[PExp](PBoolLit(true))( (f, expr) => PBinExp(PBinExp(
      PFieldAccess(PIdnUse("p"),PIdnUse(f) ), "==", PIdnUse("s")), "||", expr))//TODO for what is that?
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
                fields.foldRight[PExp](PBoolLit(true))( (f, expr) => PBinExp(PBinExp(
                  PFieldAccess(PIdnUse("p"),PIdnUse(f) ), "==", PIdnUse("s")), "||", expr))),
              "&&",
              PBinExp(PIdnUse("p"), "!=", PIdnUse("s"))),
            "<==>",
            PBinExp(
              PCall(PIdnUse("create_edge"),Seq(PIdnUse("p"),PIdnUse("s"))),
              "in",
              PResultLit()))))++ proto_f.posts
      )
  }

  def synthesizeClosed(function: PFunction, fields: Seq[String]): PFunction = {
    function.body match {
      case None => function
      case Some(body) => {
        var fieldName = "$field$"
        val bodySynthesizer = StrategyBuilder.Slim[PNode](
          {
            case i: PIdnUse if i.name == "$field$" => PIdnUse(fieldName)
          }
        ).duplicateEverything

        function.deepCopy(
          pres = function.pres.map(p => fields.foldRight[PExp](PBoolLit(true))((field, exp) => {
            fieldName = field
            val expToAdd = bodySynthesizer.execute[PExp](p)
            PBinExp(exp, "&&", expToAdd)
          })),
          body = Some(fields.foldRight[PExp](PBoolLit(true))((field, exp) => {
            fieldName = field
            val expToAdd = bodySynthesizer.execute[PExp](body)
            PBinExp(exp, "&&", expToAdd)
          }))
        )
      }
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
            method_keywords += s"link_${f}"
            new_m
          }
        )


      case m: PMethod if m.idndef.name == "unlink_$field$" =>
        fields.map(
          { f =>
            val new_m = m.deepCopyWithNameSubstitution(
              idndef = PIdnDef(s"unlink_${f}"))(
              "$field$", f)
            method_keywords += s"unlink_${f}"
            new_m
          }
        )

      case m: PMethod => Seq(m)
    }
  }

  def synthesizeMethods(methods: Seq[PMethod], fields: Seq[String]) = {
    var methodsMapping : mutable.Map[String, Seq[PMethod]] = new mutable.HashMap[String, Seq[PMethod]]()
    methods.map {
      case m: PMethod if m.idndef.name == "link_$field$" =>
        fields map { f =>
          val new_m = m.deepCopyWithNameSubstitution(
            idndef = PIdnDef(s"link_${f}"))(
            "$field$", f)
          method_keywords += s"link_${f}"
          methodsMapping.put(f, Seq(new_m))
          new_m
        }


      case m: PMethod if m.idndef.name == "unlink_$field$" =>
        fields.map(
          { f =>
            val new_m = m.deepCopyWithNameSubstitution(
              idndef = PIdnDef(s"unlink_${f}"))(
              "$field$", f)
            method_keywords += s"unlink_${f}"
            methodsMapping.get(f) match {
              case None => methodsMapping.put(f, Seq(new_m))
              case Some(new_ms) => methodsMapping.put(f, new_ms :+ new_m)
            }
            new_m
          }
        )

      case m: PMethod => Seq(m)
    }
  }
}
