package viper.silver.plugin

import viper.silver.ast._
import viper.silver.ast.utility.Rewriter.ContextC
import viper.silver.plugin.errors.{OuroborosGraphSpecificactionError, OuroborosInternalEncodingError}
import viper.silver.plugin.reasons.{InsufficientGraphPermission, NullInGraphReason, OpenGraphReason}
import viper.silver.verifier.AbstractVerificationError
import viper.silver.verifier.reasons.InternalReason

import scala.collection.mutable

class OuroborosGraphHandler {

  var graph_keywords: mutable.Map[String, String] = mutable.Map.empty[String, String]

  def handleMethod(input: Program, m: Method, s: Option[OurGraphSpec], ctx: ContextC[Node, String]): Method = s match {
    case None => m
    case Some(ss) => {
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

  val qpsForRefFieldErrTrafo : ErrTrafo = ErrTrafo({
    case x => OuroborosGraphSpecificactionError(
      x.offendingNode,
      InsufficientGraphPermission(
        x.offendingNode,
        s"might have insufficient permissions in the graph"
      ),
      x.cached
    )
  })

  val closedGraphErrTrafo : ErrTrafo = ErrTrafo({
    case x => OuroborosGraphSpecificactionError(
      x.offendingNode,
      OpenGraphReason(
        x.offendingNode,
        s"Graph might not be closed"
      ),
      x.cached
    )
  })

def GRAPH(graphs: Seq[LocalVarDecl], fields: Seq[Field] /*, errT : ErrorTrafo*/): Seq[Exp] = {
  val notNullInGraphErrTrafo : ErrTrafo = ErrTrafo({
    case x => OuroborosGraphSpecificactionError(
      x.offendingNode,
      NullInGraphReason(
        x.offendingNode,
        s"Null might be in graph $x"
      ),
      x.cached
    )
  })

  var toReturn : Seq[Exp] = Seq()
  var a = 0
  //print("Decls: " + decls + " ")
  for(a <- graphs.indices){
   // print("a: " + a + " ")
    val decl = graphs(a)
    val unExp : UnExp = Not(AnySetContains(NullLit()(decl.pos, decl.info, notNullInGraphErrTrafo), LocalVar(decl.name)(decl.typ, decl.pos, decl.info, notNullInGraphErrTrafo))(decl.pos, decl.info, notNullInGraphErrTrafo))(decl.pos, decl.info, notNullInGraphErrTrafo)
    val QPForRefFields : Seq[Exp] = collectQPsForRefFields(fields, decl, FullPerm()(decl.pos, decl.info, qpsForRefFieldErrTrafo))
    val InGraphForallsForRefFields : Seq[Exp] = collectInGraphForallsForRefFields(fields, decl)
    toReturn = toReturn :+ ((unExp +: QPForRefFields) ++ InGraphForallsForRefFields)
      .foldRight[Exp](TrueLit()(decl.pos, decl.info, decl.errT))(
        (x, y) => And(x, y)(decl.pos, decl.info, decl.errT)) //TODO If there is an error, then there is an error in the encoding => OuroborosInternalEncodingError
  }
  toReturn
}

  private def collectQPsForRefFields(fields : Seq[Field], graph : LocalVarDecl, perm_exp: Exp = FullPerm()(NoPosition, NoInfo, qpsForRefFieldErrTrafo)): Seq[Exp] =
    fields.map(f => getQPForGraphNodes(graph, f, perm_exp))

  private def getQPForGraphNodes(graph: LocalVarDecl, field: Field, perm: Exp): Exp = {
    Forall(
      Seq(LocalVarDecl("n", Ref)(graph.pos, graph.info, qpsForRefFieldErrTrafo)),
      Seq(Trigger(Seq(FieldAccess(LocalVar("n")(Ref, graph.pos, graph.info, qpsForRefFieldErrTrafo), field)(graph.pos, graph.info, qpsForRefFieldErrTrafo)))(graph.pos, graph.info, qpsForRefFieldErrTrafo)),
      Implies(AnySetContains(LocalVar("n")(Ref, graph.pos, graph.info, qpsForRefFieldErrTrafo), LocalVar(graph.name)(graph.typ, graph.pos, graph.info, qpsForRefFieldErrTrafo))(graph.pos, graph.info, qpsForRefFieldErrTrafo), FieldAccessPredicate(FieldAccess(LocalVar("n")(Ref, graph.pos, graph.info, qpsForRefFieldErrTrafo), field)(graph.pos, graph.info, qpsForRefFieldErrTrafo), perm)(graph.pos, graph.info, qpsForRefFieldErrTrafo))(graph.pos, graph.info, qpsForRefFieldErrTrafo)
    )(graph.pos, graph.info, qpsForRefFieldErrTrafo)
  }

  private def collectInGraphForallsForRefFields(fields: Seq[Field], decl: LocalVarDecl): Seq[Exp] =
    fields.map(f => getInGraphForallForField(decl, f))

  private def getInGraphForallForField(graph: LocalVarDecl, field: Field): Exp = {
    Forall(
      Seq(LocalVarDecl("n", Ref)(graph.pos, graph.info, closedGraphErrTrafo)),
      Seq(
        Trigger(Seq(AnySetContains(FieldAccess(LocalVar("n")(Ref, graph.pos, graph.info, closedGraphErrTrafo), field)(graph.pos, graph.info, closedGraphErrTrafo),
          LocalVar(graph.name)(graph.typ, graph.pos, graph.info, closedGraphErrTrafo))(graph.pos, graph.info, closedGraphErrTrafo))
        )(graph.pos, graph.info, closedGraphErrTrafo),
        Trigger(Seq(AnySetContains(LocalVar("n")(Ref, graph.pos, graph.info, closedGraphErrTrafo), LocalVar(graph.name)(graph.typ, graph.pos, graph.info, closedGraphErrTrafo))(graph.pos, graph.info, closedGraphErrTrafo),
          FieldAccess(LocalVar("n")(Ref, graph.pos, graph.info, closedGraphErrTrafo), field)(graph.pos, graph.info, closedGraphErrTrafo)))(graph.pos, graph.info, closedGraphErrTrafo)
      ),
      Implies(
        And(
          AnySetContains(
            LocalVar("n")(Ref, graph.pos, graph.info, closedGraphErrTrafo),
            LocalVar(graph.name)(graph.typ, graph.pos, graph.info, closedGraphErrTrafo)
          )(graph.pos, graph.info, closedGraphErrTrafo),
          NeCmp(
            FieldAccess(LocalVar("n")(Ref, graph.pos, graph.info, closedGraphErrTrafo), field)(graph.pos, graph.info, closedGraphErrTrafo),
            NullLit()(graph.pos, graph.info, closedGraphErrTrafo)
          )(graph.pos, graph.info, closedGraphErrTrafo)
        )(graph.pos, graph.info, closedGraphErrTrafo),
        AnySetContains(
          FieldAccess(LocalVar("n")(Ref, graph.pos, graph.info, closedGraphErrTrafo), field)(graph.pos, graph.info, closedGraphErrTrafo),
          LocalVar(graph.name)(graph.typ, graph.pos, graph.info, closedGraphErrTrafo)
        )(graph.pos, graph.info, closedGraphErrTrafo)
      )(graph.pos, graph.info, closedGraphErrTrafo)
    )(graph.pos, graph.info, closedGraphErrTrafo) //TODO If there is an error, then there is an error in the encoding => OuroborosInternalEncodingError
  }

  private def disjointGraphs(graphs: Seq[LocalVarDecl]): Seq[Exp] = {
    graphs.flatMap(x => DISJOINT(x, graphs.filter(y => graphs.indexOf(y) > graphs.indexOf(x))))
  }

  private def DISJOINT(g0 : LocalVarDecl, g1: Seq[LocalVarDecl]): Seq[Exp] = {
    g1.map(x => DISJOINT(g0, x))
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
    )(g0.pos, g0.info, g0.errT) //TODO If there is an error, then there is an error in the encoding => OuroborosInternalEncodingError

  }

  private def handleMethodBody(input: Program, maybeBody: Option[Seqn], inputGraphs: Seq[LocalVarDecl], outputGraphs: Seq[LocalVarDecl]): Option[Seqn] = maybeBody match{
    case None => maybeBody
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

  private def assumeApplyTCFraming(input: Program, graph1: LocalVarDecl, graph2: LocalVarDecl): Stmt = {
    val errTrafo: ErrTrafo = {
      ErrTrafo({
        case x => OuroborosInternalEncodingError(x.offendingNode,
          InternalReason(x.offendingNode, "internal framing error: " + x.reason.readableMessage),
          x.cached)
      })
    }
    val apply_TCFraming = getIdentifier("apply_TCFraming")
    val TCFraming = input.findFunction(apply_TCFraming)
    Inhale(
      FuncApp(
        apply_TCFraming,
        Seq(
          LocalVar(graph1.name)(graph1.typ, graph1.pos, graph1.info, errTrafo),
          LocalVar(graph2.name)(graph2.typ, graph2.pos, graph2.info, errTrafo)
        )
      )(graph1.pos, graph1.info, TCFraming.typ, TCFraming.formalArgs, errTrafo)
    )(graph1.pos, graph1.info, errTrafo)
  }

  def getIdentifier(name : String): String = graph_keywords.get(name) match{
    case None => name //TODO maybe throw error
    case Some(newName) => newName
  }
}
