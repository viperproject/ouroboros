package viper.silver.plugin

import viper.silver.ast._
import viper.silver.ast.utility.Rewriter.ContextC
import viper.silver.plugin.errors.OuroborosInternalEncodingError
import viper.silver.verifier.reasons.InternalReason

class OuroborosGraphHandler {

  //var graph_keywords: mutable.Map[String, String] = mutable.Map.empty[String, String]
  def ref_fields(fields: Seq[Field]): Seq[Field] = {
    fields.filter(f => OuroborosNames.ref_fields.contains(f.name))
  }

  def handleMethod(input: Program, m: Method, s: Option[OurGraphSpec], ctx: ContextC[Node, String]): Method = s match {
    case None => m
    case Some(ss) =>
      val refFields = ref_fields(input.fields)
      val inputObjects: Seq[(OurObject, LocalVarDecl)] = ss.inputGraphs.map(obj => (obj,m.formalArgs.filter(arg => arg.name == obj.name).head))
      val inputNodesAndDecls: Seq[(OurNode, LocalVarDecl)] = ss.inputNodes.map(node => (node,m.formalArgs.filter(arg => arg.name == node.name).head))
      val outputObjects: Seq[(OurObject, LocalVarDecl)] = ss.outputGraphs.map(obj => (obj,m.formalReturns.filter(arg => arg.name == obj.name).head))
      val outputNodesAndDecls: Seq[(OurNode, LocalVarDecl)] = ss.outputNodes.map(node => (node,m.formalReturns.filter(arg => arg.name == node.name).head))
      val inputGraphs = {
        val ssInputNames = ss.inputGraphs.map(y => y.name)
        m.formalArgs.filter(x => ssInputNames.contains(x.name))
      }


      val inpNodes = nodesInGraphs(inputNodesAndDecls)

      val outputGraphs = m.formalReturns.filter(x => ss.outputGraphs.map(y => y.name).contains(x.name))
      val outNodes = nodesInGraphs(outputNodesAndDecls)
      Method(
        m.name,
        m.formalArgs,
        m.formalReturns,
        /*disjointGraphs(inputGraphs, input) ++*/ inputTypesAndClosed(inputObjects, refFields, input, m) ++ inpNodes ++ m.pres,
        outputTypes(outputObjects ++ inputObjects, refFields, input, m) ++ outNodes ++ m.posts,
        handleMethodBody(input, m.body, inputGraphs, outputGraphs, inputObjects) /* ++ TCFraming*/
      ) (m.pos, m.info, m.errT)
  }

/*  def handleFuncApp(input: Program, fc: FuncApp, args: Seq[String], ctx: ContextC[Node, String]): Exp = {
    val calledFunction = input.findFunction(fc.funcname)
    val funcArgs = calledFunction.formalArgs.map(arg => arg.name)
    val callArgs = fc.getArgs

    if(callArgs.size != funcArgs.size) return fc

    //fc.getArgs.

    val partialFunction : PartialFunction[String, Exp] = {
      case s if funcArgs.contains(s) => {
        callArgs(funcArgs.indexOf(s))
      }

      case s => LocalVar(s)(Ref)
    }

    calledFunction.body match {
      case None => fc
      case Some(body) => body.deepCopyWithLocalVarSubstitution(partialFunction, fc.pos, fc.info, fc.errT)
    }
  }*/


  def inputTypesAndClosed(objects: Seq[(OurObject, LocalVarDecl)], fields: Seq[Field], input: Program, method: Method): Seq[Exp] = {
    def foldFunction(graphName: String, pos: Infoed with Positioned): (Exp, Exp) => Exp = {
      val graphErrTrafo = OuroborosErrorTransformers.graphErrTrafo(graphName)
      (foldedExp, exp) => And(foldedExp, exp)(pos.pos, pos.info, graphErrTrafo)
    }

    var allGraphs : Option[Exp] = None
    val toReturn : Seq[Exp] = objects.flatMap(
      mapping => {
        val obj = mapping._1
        val decl = mapping._2
        val graphErrTrafo = OuroborosErrorTransformers.graphErrTrafo(decl.name)
        val typ = obj.typ
        val isDag = typ.isInstanceOf[DAG]
        val isZopg = typ.isInstanceOf[ZOPG]
        val isClosed = typ.isInstanceOf[Closed]
        allGraphs match {
          case None => allGraphs = Some(
            LocalVar(
              decl.name
            )(decl.typ, decl.pos, decl.info, graphErrTrafo)
          )
          case Some(prev) => allGraphs = Some(
            AnySetUnion(
              prev,
              LocalVar(
                decl.name
              )(decl.typ, decl.pos, decl.info, graphErrTrafo)
            )(decl.pos, decl.info, graphErrTrafo)
          )
        }

        val localVar = LocalVar(decl.name)(decl.typ, decl.pos, decl.info, decl.errT)
        Seq(fold_GRAPH(localVar, fields, input, isClosed, false, true, isDag, isZopg, TrueLit()(), foldFunction(decl.name, localVar)))
      }
    )

    allGraphs match {
      case None => toReturn
      case Some(graphs) =>
        val qps: Seq[Exp] = collectQPsForRefFields(fields, graphs, FullPerm()())
        val qp: Exp = OuroborosHelper.ourFold[Exp](qps, TrueLit()(), (foldedExps, exp) => And(foldedExps, exp)(exp.pos, exp.info, OuroborosErrorTransformers.qpsForRefFieldErrTrafo(exp.toString())))
        qp +: toReturn// :+ closedGraphParameters(graphs, input, method, true)
    }
  }

  def outputTypes(objects: Seq[(OurObject, LocalVarDecl)], fields: Seq[Field], input: Program, method: Method): Seq[Exp] =
    {
      var additionalPostConditions : Seq[Exp] = Seq()
      var allGraphs : Option[Exp] = None
      objects.map(
        mapping => {
          val obj = mapping._1
          val decl = mapping._2
          val graphErrTrafo = OuroborosErrorTransformers.graphErrTrafo(decl.name)
          val typ = obj.typ
          val isDag = typ.isInstanceOf[DAG]
          val isClosed = typ.isInstanceOf[Closed]
          val isZopg = false //typ.isInstanceOf[ZOPG] We don't want to check "is zopg", in the post condition, as it is probably not provable
          allGraphs match {
            case None => allGraphs = Some(
              LocalVar(
                decl.name
              )(decl.typ, decl.pos, decl.info, graphErrTrafo)
            )
            case Some(prev) => allGraphs = Some(
              AnySetUnion(
                prev,
                LocalVar(
                  decl.name
                )(decl.typ, decl.pos, decl.info, graphErrTrafo)
              )(decl.pos, decl.info, graphErrTrafo) //TODO other position?
            )
          }
          val postConditions : Seq[Exp] =
            /*Seq(
              NO_NULL(LocalVar(decl.name)(decl.typ, decl.pos, decl.info, decl.errT), input),
              CLOSED(LocalVar(decl.name)(decl.typ, decl.pos, decl.info, decl.errT), input))*/
          GRAPH(LocalVar(decl.name)(decl.typ, decl.pos, decl.info, decl.errT), fields, input, isClosed, false, true, isDag, isZopg)

          additionalPostConditions = additionalPostConditions ++ postConditions//:+
           // OuroborosHelper.ourFold[Exp](postConditions, TrueLit()(), (foldedExp, exp) => And(foldedExp, exp)(exp.pos, exp.info, graphErrTrafo))

          mapping
        }
      )
      allGraphs match {
        case Some(graphs) =>
          val qps: Seq[Exp] = collectQPsForRefFields(fields, graphs, FullPerm()())
          val qp: Exp = OuroborosHelper.ourFold[Exp](qps, TrueLit()(), (foldedExps, exp) => And(foldedExps, exp)(exp.pos, exp.info, OuroborosErrorTransformers.qpsForRefFieldErrTrafo(graphs.toString())))
          qp +: additionalPostConditions // :+ closedGraphParameters(graphs, input, method, false)
        case None => Seq()
      }
    }

  def nodesInGraphs(nodes: Seq[(OurNode, LocalVarDecl)]): Seq[Exp] =  nodes.map ({
    case (ourNode, decl) =>
      val nodeName = ourNode.name
      val graphNames = ourNode.graphs
      val graphUnion = OuroborosHelper.transformAndFold[String, Exp](
        graphNames.toSeq,
        EmptySet(SetType(Ref))(),
        (exp1, exp2) => AnySetUnion(exp1, exp2)(),
        graphName => LocalVar(graphName)(SetType(Ref), decl.pos, decl.info, decl.errT)
      )
      def node = LocalVar(nodeName)(Ref, decl.pos, decl.info, decl.errT)

      val nodeInGraphs = AnySetContains(node, graphUnion)(decl.pos, decl.info, decl.errT)
      val ifNonNull = Implies(NeCmp(node, NullLit()())(), nodeInGraphs)(decl.pos, decl.info, OuroborosErrorTransformers.nodeNotInGraphErrTrafo(node, graphUnion))

      ifNonNull
  })
def NO_NULL(decl: Exp, input: Program)= {
  val noNullInGraph = input.findFunction("NoNullInGraph")
  val noNullErrTrafo = OuroborosErrorTransformers.NullInGraphErrTrafo(Seq(decl))
  val noNullCall = FuncApp(noNullInGraph, Seq(decl))(decl.pos, decl.info, noNullErrTrafo)
//  if (OuroborosNames.macroNames.contains(noNullCall.funcname))
//    OuroborosMemberInliner.inlineFunction(noNullCall, input, noNullCall.pos, noNullCall.info, noNullCall.errT)
//  else
    noNullCall
}

def foldAndTransformGRAPH[B](graph: Exp, ref_fields: Seq[Field], input: Program, closed: Boolean, qpsNeeded: Boolean, noNullNeeded: Boolean, dag: Boolean, zopg: Boolean, initialValue: B, transformFunction: (Exp => B), foldFunction: ((B, B) => B)): B = {
  OuroborosHelper.transformAndFold[Exp, B](GRAPH(graph, ref_fields, input, closed, qpsNeeded, noNullNeeded, dag, zopg), initialValue, foldFunction, transformFunction)
}

def fold_GRAPH(graph: Exp, ref_fields: Seq[Field], input: Program, closed: Boolean, qpsNeeded: Boolean, noNullNeeded: Boolean, dag: Boolean, zopg: Boolean, initialValue: Exp, foldFunction: ((Exp, Exp) => Exp)): Exp = {
  OuroborosHelper.ourFold[Exp](GRAPH(graph, ref_fields, input, closed, qpsNeeded, noNullNeeded, dag, zopg), initialValue, foldFunction)
}

def GRAPH(graph: Exp, ref_fields: Seq[Field], input: Program, closed: Boolean, qpsNeeded: Boolean, noNullNeeded: Boolean, dag: Boolean, zopg: Boolean): Seq[Exp] = {
  val qpsForRefFieldErrTrafo = OuroborosErrorTransformers.qpsForRefFieldErrTrafo(graph.toString())
  val noNullProperty : Seq[Exp]= if(noNullNeeded)
    Seq(NO_NULL(graph, input))
  else Seq()
  val QPForRefFields : Seq[Exp] = if(qpsNeeded)
    collectQPsForRefFields(ref_fields, graph.duplicateMeta(graph.pos, graph.info, qpsForRefFieldErrTrafo).asInstanceOf[Exp], FullPerm()(graph.pos, graph.info, qpsForRefFieldErrTrafo))
  else Seq()
  val closedProperty = if(closed)
    Seq(
      CLOSED(graph, input)
    )
  else Seq()

  val dagProperty = if(dag)
    Seq(DAG(graph, input))
  else
    Seq()

  val zopgProperty = if(zopg)
    Seq(ZOPG(graph, input))
  else
    Seq()


  (noNullProperty ++ QPForRefFields) ++ closedProperty ++ dagProperty ++ zopgProperty
}

  def DAG(graph: Exp, input: Program): Exp = {
    val acyclicFunctionName = OuroborosNames.getIdentifier("acyclic_graph")
    val acyclicFunction = input.findDomainFunction(acyclicFunctionName)
    val $$FunctionName = OuroborosNames.getIdentifier("$$")
    val $$Function = input.findFunction($$FunctionName)
    DomainFuncApp(acyclicFunction, Seq(FuncApp($$Function, Seq(graph))(graph.pos, graph.info, graph.errT)), Map.empty[TypeVar, Type])(graph.pos, graph.info, graph.errT)
  }

  def ZOPG(graph: Exp, input: Program): Exp = {
    val zopgFunctionName = OuroborosNames.getIdentifier("IS_ZOPG")
    val zopgFunction = input.findFunction(zopgFunctionName)
    FuncApp(zopgFunction, Seq(graph))(graph.pos, graph.info, graph.errT)
  }
/*def GRAPH[B](graph: Exp, fields: Seq[Field], input: Program, closed: Boolean, initialValue: B, foldFunction: ((B, Exp) => B)): B = {
  val graphErrTrafo = OuroborosErrorTransformers.graphErrTrafo(graph.toString())
  val qpsForRefFieldErrTrafo = OuroborosErrorTransformers.qpsForRefFieldErrTrafo(graph.toString())
  val unExp : Exp = NO_NULL(graph, input)
  val QPForRefFields : Seq[Exp] = collectQPsForRefFields(fields, graph.duplicateMeta(graph.pos, graph.info, qpsForRefFieldErrTrafo).asInstanceOf[Exp], FullPerm()(graph.pos, graph.info, qpsForRefFieldErrTrafo))
  val InGraphForallsForRefFields = if(closed)
    Seq(
      CLOSED(graph, input)
    )//TODO (graph.pos, graph.info, OuroborosErrorTransformers.graphErrTrafo)
  else Seq()
  ((unExp +: QPForRefFields) ++ InGraphForallsForRefFields)
    .foldLeft[B](initialValue)(
      (x, y) => foldFunction(x, y)/*(graph.pos, graph.info, graphErrTrafo)*/) //TODO If there is an error, then there is an error in the encoding => OuroborosInternalEncodingError
}*/



  private def collectQPsForRefFields(fields : Seq[Field], graph : Exp, perm_exp: Exp = FullPerm()(NoPosition, NoInfo, NoTrafos)): Seq[Exp] =
    fields.map(f => getQPForGraphNodes(graph, f, perm_exp))

  private def getQPForGraphNodes(graph: Exp, field: Field, perm: Exp): Exp = {
    val qpsForRefFieldErrTrafo = OuroborosErrorTransformers.qpsForRefFieldErrTrafo(graph.toString())
    Forall(
      Seq(LocalVarDecl(OuroborosNames.getIdentifier("n"), Ref)(graph.pos, graph.info, qpsForRefFieldErrTrafo)),
      Seq(Trigger(Seq(FieldAccess(LocalVar(OuroborosNames.getIdentifier("n"))(Ref, graph.pos, graph.info, qpsForRefFieldErrTrafo), field)(graph.pos, graph.info, qpsForRefFieldErrTrafo)))(graph.pos, graph.info, qpsForRefFieldErrTrafo)),
      Implies(AnySetContains(LocalVar(OuroborosNames.getIdentifier("n"))(Ref, graph.pos, graph.info, qpsForRefFieldErrTrafo), graph)(graph.pos, graph.info, qpsForRefFieldErrTrafo),
        FieldAccessPredicate(FieldAccess(LocalVar(OuroborosNames.getIdentifier("n"))(Ref, graph.pos, graph.info, qpsForRefFieldErrTrafo), field)(graph.pos, graph.info, qpsForRefFieldErrTrafo), perm)(graph.pos, graph.info, qpsForRefFieldErrTrafo))(graph.pos, graph.info, qpsForRefFieldErrTrafo)
    )(graph.pos, graph.info, qpsForRefFieldErrTrafo)
  }

  private def closedGraphParameters(decl: Exp, input: Program, method: Method, pre:Boolean): Exp = {
    CLOSED(decl, input).duplicateMeta(
      (method.pos, method.info, OuroborosErrorTransformers.closedGraphParametersErrTrafo(method.name, decl, pre))
    ).asInstanceOf[Exp]
  }

  def CLOSED( decl: Exp, input: Program): Exp ={
    val closed = input.findFunction(OuroborosNames.getIdentifier("CLOSED"))
    val closedCallErrTrafo = OuroborosErrorTransformers.closedGraphErrTrafo(Seq(decl))
    val closedCall = FuncApp(closed, Seq(decl))(decl.pos, decl.info, closedCallErrTrafo)
//    if (OuroborosNames.macroNames.contains(closedCall.funcname))
//      OuroborosMemberInliner.inlineFunction(closedCall, input, closedCall.pos, closedCall.info, closedCallErrTrafo)
//    else
      closedCall

  }

  private def disjointGraphs(graphs: Seq[LocalVarDecl], input: Program): Seq[Exp] = {
    graphs.flatMap(x => DISJOINT(x, graphs.filter(y => graphs.indexOf(y) > graphs.indexOf(x)), input))
  }

  private def DISJOINT(g0 : LocalVarDecl, g1: Seq[LocalVarDecl], input: Program): Seq[Exp] = {
    g1.map(x => {
      val disjoint = input.findFunction(OuroborosNames.getIdentifier("DISJOINT"))
      val disjointErrTrafo = OuroborosErrorTransformers.disjointGraphsErrTrafo(Seq(g0, x))
      val disjointCall = FuncApp(disjoint, Seq(
        LocalVar(g0.name)(g0.typ, g0.pos, g0.info, g0.errT),
        LocalVar(x.name)(x.typ, x.pos, x.info, x.errT)
      ))(g0.pos, g0.info, disjointErrTrafo)
//      if (OuroborosNames.macroNames.contains(disjointCall.funcname)) OuroborosMemberInliner.inlineFunction(disjointCall, input, g0.pos, g0.info, disjointErrTrafo) else
      disjointCall
    })
  }

  private def handleMethodBody(input: Program, maybeBody: Option[Seqn], inputGraphs: Seq[LocalVarDecl], outputGraphs: Seq[LocalVarDecl], inputObjects:Seq[(OurObject, LocalVarDecl)] ): Option[Seqn] = maybeBody match{
    case None => maybeBody
    case Some(body) =>
      inputGraphs.size match {
        case a if a > 1 => Some(Seqn(getFramingAxioms(input, inputGraphs) ++ getNoExitAxioms(input, inputObjects, inputGraphs) ++ body.ss, body.scopedDecls)(
          body.pos, body.info, body.errT
        ))
        case _ => Some(body)
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
    val errTrafo: ErrTrafo = { //This error is only for the case that the program inserts apply TCFraming automatically
      ErrTrafo({
        case x => OuroborosInternalEncodingError(x.offendingNode,
          InternalReason(x.offendingNode, "internal framing error: " + x.reason.readableMessage),
          x.cached)
      })
    }
    val apply_TCFraming = OuroborosNames.getIdentifier("apply_TCFraming")
    val TCFraming = input.findFunction(apply_TCFraming)
    val apply_TCFramingCall = FuncApp(
      apply_TCFraming,
      Seq(
        LocalVar(graph1.name)(graph1.typ, graph1.pos, graph1.info, errTrafo),
        LocalVar(graph2.name)(graph2.typ, graph2.pos, graph2.info, errTrafo)
      )
    )(graph1.pos, graph1.info, TCFraming.typ, TCFraming.formalArgs, errTrafo)
    val inhaleCall = Inhale(
      apply_TCFramingCall
    )(graph1.pos, SimpleInfo(Seq("", s"Apply TC Framing for input graphs ${graph1.name} and ${graph2.name} ", "")), errTrafo)

//    if(OuroborosNames.macroNames.contains(apply_TCFramingCall.funcname))
//      OuroborosMemberInliner.inlineInhaleFunction(inhaleCall, apply_TCFramingCall, input, inhaleCall.pos, inhaleCall.info, inhaleCall.errT)
//    else
      inhaleCall
  }

  private def getNoExitAxioms(input: Program, inputObjects: Seq[(OurObject, LocalVarDecl)], inputGraphs: Seq[LocalVarDecl]): Seq[Stmt] = {
    val closedGraphs = inputObjects.collect({
      case x if x._1.typ.isInstanceOf[Closed] => x._2
    })

    closedGraphs.flatMap(closedGraph => inputObjects.collect({
      case p if !(p._2 == closedGraph) =>
        assumeNoExitClosed(input, closedGraph, p._2, inputGraphs)
    })
    )
  }

  private def assumeNoExitClosed(input: Program, closedGraph: LocalVarDecl, graph2: LocalVarDecl, inputGraphs: Seq[LocalVarDecl]): Stmt = {
    val NoExitClosed = input.findFunction(OuroborosNames.getIdentifier("apply_no_exit_closed"))
    val purificationFunction = input.findFunction(OuroborosNames.getIdentifier("$$"))
    val unionGraphs = OuroborosHelper.transformAndFold[LocalVarDecl, Exp](inputGraphs, EmptySet(Ref)(), (foldedGraphs, graph) => AnySetUnion(foldedGraphs, graph)(), graphDecl => LocalVar(graphDecl.name)(SetType(Ref)))
    val universeEdges = FuncApp(purificationFunction, Seq(unionGraphs))()
    Inhale(
      FuncApp(NoExitClosed, Seq(
        universeEdges,
        LocalVar(closedGraph.name)(SetType(Ref)),
        LocalVar(graph2.name)(SetType(Ref))
      ))()
    )(closedGraph.pos, SimpleInfo(Seq("", s"Assume there are no paths from closed Graph ${closedGraph.name} to disjoint Graph ${graph2.name}", "")))
  }
}
