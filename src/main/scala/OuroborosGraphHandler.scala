package viper.silver.plugin

import viper.silver.ast._
import viper.silver.ast.utility.Rewriter.ContextC
import viper.silver.parser._

class OuroborosGraphHandler {

  def handleMethod(input: Program, m: Method, s: Option[OurGraphSpec], ctx: ContextC[Node, String]): Method = s match {
    case None => m
    case Some(ss) => {
     /* println("handle Method: " + m.name + ",  with GraphSpec: " + s)
      println("PRES: " + m.pres)*/
      val inputGraphs = m.formalArgs.filter(x => ss.inputs.map(y => y.name).contains(x.name))
      val outputGraphs = m.formalReturns.filter(x => ss.outputs.map(y => y.name).contains(x.name))
      Method(
        m.name,
        m.formalArgs,
        m.formalReturns,
        GRAPH(inputGraphs, input.fields) ++ disjointGraphs(inputGraphs) ++ m.pres,
        GRAPH(outputGraphs, input.fields) ++ m.posts,
        handleMethodBody(input, m.body, inputGraphs, outputGraphs) /* ++ TCFraming*/
      ) (m.pos, m.info, m.errT)
    }
  }

def GRAPH(decls: Seq[LocalVarDecl], fields: Seq[Field]): Seq[Exp] = {
  var toReturn : Seq[Exp] = Seq()
  var a = 0
  //print("Decls: " + decls + " ")
  for(a <- decls.indices){
   // print("a: " + a + " ")
    val decl = decls(a)
    val unExp : UnExp = Not(AnySetContains(NullLit()(decl.pos, decl.info, decl.errT), LocalVar(decl.name)(decl.typ, decl.pos, decl.info, decl.errT))(decl.pos, decl.info, decl.errT))(decl.pos, decl.info, decl.errT)
    val QPForRefFields : Seq[Exp] = collectQPsForRefFields(fields, decl, FullPerm()(decl.pos, decl.info, decl.errT))
    val InGraphForallsForRefFields : Seq[Exp] = collectInGraphForallsForRefFields(fields, decl)
    toReturn = toReturn :+ ((unExp +: QPForRefFields) ++ InGraphForallsForRefFields)
      .foldRight[Exp](TrueLit()(decl.pos, decl.info, decl.errT))(
        (x, y) => And(x, y)(decl.pos, decl.info, decl.errT))
  }
  toReturn
}

  private def collectQPsForRefFields(fields : Seq[Field], graph : LocalVarDecl, perm_exp: Exp = FullPerm()(NoPosition, NoInfo, NoTrafos)): Seq[Exp] =
    fields.map(f => getQPForGraphNodes(graph, f, perm_exp))

  private def getQPForGraphNodes(decl: LocalVarDecl, field: Field, exp: Exp): Exp = {
    Forall(
      Seq(LocalVarDecl("n", Ref)(decl.pos, decl.info, decl.errT)),
      Seq(Trigger(Seq(FieldAccess(LocalVar("n")(Ref, decl.pos, decl.info, decl.errT), field)(decl.pos, decl.info, decl.errT)))(decl.pos, decl.info, decl.errT)),
      Implies(AnySetContains(LocalVar("n")(Ref, decl.pos, decl.info, decl.errT), LocalVar(decl.name)(decl.typ, decl.pos, decl.info, decl.errT))(decl.pos, decl.info, decl.errT), FieldAccessPredicate(FieldAccess(LocalVar("n")(Ref, decl.pos, decl.info, decl.errT), field)(decl.pos, decl.info, decl.errT), exp)(decl.pos, decl.info, decl.errT))(decl.pos, decl.info, decl.errT)
    )(decl.pos, decl.info, decl.errT)
  }

  private def collectInGraphForallsForRefFields(fields: Seq[Field], decl: LocalVarDecl): Seq[Exp] =
    fields.map(f => getInGraphForallForField(decl, f))

  private def getInGraphForallForField(decl: LocalVarDecl, field: Field): Exp = {
    Forall(
      Seq(LocalVarDecl("n", Ref)(decl.pos, decl.info, decl.errT)),
      Seq(
        Trigger(Seq(AnySetContains(FieldAccess(LocalVar("n")(Ref, decl.pos, decl.info, decl.errT), field)(decl.pos, decl.info, decl.errT),
          LocalVar(decl.name)(decl.typ, decl.pos, decl.info, decl.errT))(decl.pos, decl.info, decl.errT))
        )(decl.pos, decl.info, decl.errT),
        Trigger(Seq(AnySetContains(LocalVar("n")(Ref, decl.pos, decl.info, decl.errT), LocalVar(decl.name)(decl.typ, decl.pos, decl.info, decl.errT))(decl.pos, decl.info, decl.errT),
          FieldAccess(LocalVar("n")(Ref, decl.pos, decl.info, decl.errT), field)(decl.pos, decl.info, decl.errT)))(decl.pos, decl.info, decl.errT)
      ),
      Implies(
        And(
          AnySetContains(
            LocalVar("n")(Ref, decl.pos, decl.info, decl.errT),
            LocalVar(decl.name)(decl.typ, decl.pos, decl.info, decl.errT)
          )(decl.pos, decl.info, decl.errT),
          NeCmp(
            FieldAccess(LocalVar("n")(Ref, decl.pos, decl.info, decl.errT), field)(decl.pos, decl.info, decl.errT),
            NullLit()(decl.pos, decl.info, decl.errT)
          )(decl.pos, decl.info, decl.errT)
        )(decl.pos, decl.info, decl.errT),
        AnySetContains(
          FieldAccess(LocalVar("n")(Ref, decl.pos, decl.info, decl.errT), field)(decl.pos, decl.info, decl.errT),
          LocalVar(decl.name)(decl.typ, decl.pos, decl.info, decl.errT)
        )(decl.pos, decl.info, decl.errT)
      )(decl.pos, decl.info, decl.errT)
    )(decl.pos, decl.info, decl.errT) //TODO error transform to OuroborosGraphSpecificationError?
  }

  private def disjointGraphs(decls: Seq[LocalVarDecl]): Seq[Exp] = {
    decls.flatMap(x => DISJOINT(x, decls.filter(y => decls.indexOf(y) > decls.indexOf(x))))
  }

  private def DISJOINT(decl : LocalVarDecl, decls: Seq[LocalVarDecl]): Seq[Exp] = {
    decls.map(x => DISJOINT(decl, x))
  }

  private def DISJOINT(g0: LocalVarDecl, g1: LocalVarDecl): Exp = {
    And(
      Forall(
        Seq(LocalVarDecl("n", Ref)(g0.pos, g0.info, g0.errT)),
        Seq(Trigger(Seq(
          AnySetContains(LocalVar("n")(Ref, g0.pos, g0.info, g0.errT), LocalVar(g0.name)(g0.typ, g0.pos, g0.info, g0.errT))(g0.pos, g0.info, g0.errT),
          AnySetContains(LocalVar("n")(Ref, g1.pos, g1.info, g1.errT), LocalVar(g1.name)(g1.typ, g1.pos, g1.info, g1.errT))(g1.pos, g1.info, g1.errT)
        ))(g0.pos, g0.info, g0.errT)),
        Implies(
          AnySetContains(LocalVar("n")(Ref, g0.pos, g0.info, g0.errT), LocalVar(g0.name)(g0.typ, g0.pos, g0.info, g0.errT))(g0.pos, g0.info, g0.errT),
          Not(
            AnySetContains(LocalVar("n")(Ref, g1.pos, g1.info, g1.errT), LocalVar(g1.name)(g1.typ, g1.pos, g1.info, g1.errT))(g1.pos, g1.info, g1.errT)
          )(g1.pos, g1.info, g1.errT)
        )(g0.pos, g0.info, g0.errT)
      )(g0.pos, g0.info, g0.errT)
      ,
      Forall(
        Seq(LocalVarDecl("n", Ref)(g0.pos, g0.info, g0.errT)),
        Seq(Trigger(Seq(
          AnySetContains(LocalVar("n")(Ref, g0.pos, g0.info, g0.errT), LocalVar(g0.name)(g0.typ, g0.pos, g0.info, g0.errT))(g0.pos, g0.info, g0.errT),
          AnySetContains(LocalVar("n")(Ref, g1.pos, g1.info, g1.errT), LocalVar(g1.name)(g1.typ, g1.pos, g1.info, g1.errT))(g1.pos, g1.info, g1.errT)
        ))(g0.pos, g0.info, g0.errT)),
        Implies(
          AnySetContains(LocalVar("n")(Ref, g1.pos, g1.info, g1.errT), LocalVar(g1.name)(g1.typ, g1.pos, g1.info, g1.errT))(g1.pos, g1.info, g1.errT),
          Not(
            AnySetContains(LocalVar("n")(Ref, g0.pos, g0.info, g0.errT), LocalVar(g0.name)(g0.typ, g0.pos, g0.info, g0.errT))(g0.pos, g0.info, g0.errT)
          )(g1.pos, g1.info, g1.errT)
        )(g0.pos, g0.info, g0.errT)
      )(g0.pos, g0.info, g0.errT)
    )(g0.pos, g0.info, g0.errT) //TODO error transforming to OuroborosDisjointError?

  }

  private def handleMethodBody(input: Program, maybeSeqn: Option[Seqn], inputGraphs: Seq[LocalVarDecl], outputGraphs: Seq[LocalVarDecl]): Option[Seqn] = maybeSeqn match{
    case None => maybeSeqn
    case Some(body) => {
      inputGraphs.size match {
        case a if a > 1 => Some(Seqn(getFramingAxioms(input, inputGraphs) ++ body.ss, body.scopedDecls)(
          body.pos, body.info, body.errT
        ))
        case _ => Some(body)
      }
    }
  }

  private def getFramingAxioms(input: Program, inputGraphs: Seq[LocalVarDecl]): Seq[Stmt] = {
    inputGraphs.size match {
      case a if a <= 1 => Seq()
      case _ => inputGraphs.flatMap(a =>
        inputGraphs.filter(b => inputGraphs.indexOf(b) > inputGraphs.indexOf(a)).map(b => assumeApplyTCFraming(input, a,b)))
    }
  }

  private def assumeApplyTCFraming(input: Program, decl: LocalVarDecl, decl1: LocalVarDecl): Stmt = {
    val TCFraming = input.findFunction("apply_TCFraming")
    Inhale(
      FuncApp(
        "apply_TCFraming",
        Seq(
          LocalVar(decl.name)(decl.typ, decl.pos, decl.info, decl.errT),
          LocalVar(decl1.name)(decl1.typ, decl1.pos, decl1.info, decl1.errT)
        )
      )(decl.pos, decl.info, TCFraming.typ, TCFraming.formalArgs, decl.errT) //TODO error transfroming to OuroborosFramingError?
    )(decl.pos, decl.info, decl.errT)
  }

}
