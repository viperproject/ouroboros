/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.plugin

import scala.collection.{immutable, mutable}
import viper.silver.{ast, parser}
import viper.silver.ast.utility.Rewriter.{ContextC, Rewritable}
import viper.silver.ast._
import viper.silver.parser.{PFormalArgDecl, _}


trait OurType
case object OurNode extends OurType
case object OurGraph extends OurType
case object OurList extends OurType

case class OurObject(name: String, typ: OurType)

trait OurOperation
//case class OurLink(name: String) extends OurOperation
//case class OurUnlink(name: String) extends OurOperation
case class OurOperPair(name: String) extends OurOperation
case class OurGraphSpec(inputs: Seq[OurObject], outputs: Seq[OurObject])

class OuroborosGraphDefinition(plugin: OuroborosPlugin) {

/*  case class OurGraphSpec(inputs: Seq[OurObject], outputs: Seq[OurObject])*/
  val graph_definitions: mutable.Map[String, OurGraphSpec] = mutable.Map.empty[String, OurGraphSpec]

  def handlePFormalArgDecl(input: PProgram, decl: PFormalArgDecl): PFormalArgDecl = decl.typ match {
    case d: PDomainType =>
      d.domain.name match {
        case "Node" => PFormalArgDecl(decl.idndef, TypeHelper.Ref)
        case "Graph" => PFormalArgDecl(decl.idndef, PSetType(TypeHelper.Ref))
        case "List" => PFormalArgDecl(decl.idndef, PSetType(TypeHelper.Ref))
        case _ => decl
      }
    case d: PSetType =>
      PFormalArgDecl(decl.idndef, PSetType(handlePFormalArgDecl(input, PFormalArgDecl(decl.idndef, d.elementType)).typ))
    case _ => decl
  }

  private def seqOfPExpToPExp(exp_seq: Seq[PExp], binary_oper: String, neutral_element: PExp): PExp = exp_seq.toList match {
    case e :: Nil => e
    case e :: tail => PBinExp(e, binary_oper, seqOfPExpToPExp(tail, binary_oper, neutral_element))
    case Nil =>
      neutral_element
  }

  private def seqOfExpToUnionExp(exp_seq: Seq[Exp])(pos: Position = NoPosition, info: Info = NoInfo, errT: ErrorTrafo = NoTrafos): Exp = exp_seq.toList match {
    case e :: Nil => e
    case e :: tail => AnySetUnion(e, seqOfExpToUnionExp(tail)(pos, info, errT))(pos, info, errT)
    case Nil => EmptySet(Ref)(pos, info, errT)//TrueLit()(pos, info, errT)
  }

  // forall n:Ref :: {n.field_i} n in nodes ==> acc(n.field_i,perm_exp)
  private def getQPForGraphNodes(graph_exp: PExp, field: String, perm_exp: PExp = PFullPerm()): PExp = PForall(
    Seq(PFormalArgDecl(PIdnDef("n"), TypeHelper.Ref)),
    Seq(PTrigger( Seq( PFieldAccess(PIdnUse("n"),PIdnUse(field))))),
    PBinExp( PBinExp(PIdnUse("n"), "in", graph_exp.deepCopyAll[PExp]), "==>", PAccPred(PFieldAccess(PIdnUse("n"), PIdnUse(field)), perm_exp.deepCopyAll[PExp])))

  // ( forall n:Ref :: {n.field_i} n in nodes && n != mutable_node ==> acc(n.field_i,1/2) )
  private def getQPForGraphNodesExcept(graph_exp: PExp, field: String, perm_exp: PExp = PFullPerm(), except_node: PExp): PExp = PForall(
    Seq(PFormalArgDecl(PIdnDef("n"), TypeHelper.Ref)),
    Seq(PTrigger( Seq( PFieldAccess(PIdnUse("n"),PIdnUse(field))))),
    PBinExp( PBinExp( PBinExp(PIdnUse("n"), "in", graph_exp.deepCopyAll[PExp]), "&&", PBinExp(PIdnUse("n"), "!=", except_node.deepCopyAll[PExp])), "==>", PAccPred(PFieldAccess(PIdnUse("n"), PIdnUse(field)), perm_exp.deepCopyAll[PExp])))

  // forall n:Ref ::{n.field_i in nodes}{n in nodes, n.field_i} n in nodes && n.field_i != null ==> n.field_i in nodes
  private def getInGraphForallForField(graph_exp: PExp, field: String): PExp = PForall(
    Seq(PFormalArgDecl(PIdnDef("n"), TypeHelper.Ref)),
    Seq(
      PTrigger( Seq(PBinExp(PFieldAccess(PIdnUse("n"), PIdnUse(field)), "in", graph_exp.deepCopyAll[PExp])) ),
      PTrigger( Seq(PBinExp(PIdnUse("n"), "in", graph_exp.deepCopyAll[PExp]), PFieldAccess(PIdnUse("n"), PIdnUse(field))))),
    PBinExp( PBinExp(PBinExp(PIdnUse("n"), "in", graph_exp.deepCopyAll[PExp]), "&&", PBinExp(PFieldAccess(PIdnUse("n"), PIdnUse(field)), "!=", PNullLit())), "==>", PBinExp(PFieldAccess(PIdnUse("n"), PIdnUse(field)), "in", graph_exp.deepCopyAll[PExp])))


  private def collectQPsForRefFields(fields: Seq[String], graph_exp: PExp, perm_exp: PExp = PFullPerm()): Seq[PExp] =
    fields.map(f => getQPForGraphNodes(graph_exp, f, perm_exp))

  private def collectQPsForRefFieldsProtected(fields: Seq[String], mutable_node_exp: PExp, graph_exp: PExp): Seq[PExp] =
    fields.map(f => getQPForGraphNodesExcept(graph_exp, f, PBinExp(PIntLit(1), "/", PIntLit(2)), mutable_node_exp))

  private def collectInGraphForallsForRefFields(fields: Seq[String], graph_exp: PExp): Seq[PExp] =
    fields.map(f => getInGraphForallForField(graph_exp, f))


  /*
  private def GRAPH(prog: PProgram, graph_exp: PExp) = PBinExp(
    // !(null in nodes)
    PUnExp("!", PBinExp(PNullLit(), "in", graph_exp.deepCopyAll[PExp])),
    "&&", PBinExp(
      seqOfPExpToPExp(getQPsForRefFields(prog.fields, graph_exp.deepCopyAll[PExp]), "&&"), "&&",
      concatInGraphForallsForRefFields(prog.fields, graph_exp.deepCopyAll[PExp])))
  */

  private def GRAPH(prog: PProgram, graph_exp: PExp, fields: Seq[String]) = seqOfPExpToPExp(
    (PUnExp("!", PBinExp(PNullLit(), "in", graph_exp.deepCopyAll[PExp])) +:
    collectQPsForRefFields(fields, graph_exp, PFullPerm())) ++
    collectInGraphForallsForRefFields(fields, graph_exp), "&&", PBoolLit(true))

  private def PROTECTED_GRAPH(prog: PProgram, graph_exp: PExp, fields: Seq[String], mutable_node_exp: PExp, mutable_field: String) = seqOfPExpToPExp(Seq(
    PUnExp("!", PBinExp(PNullLit(), "in", graph_exp.deepCopyAll[PExp])),
    PBinExp(mutable_node_exp.deepCopyAll[PExp], "in", graph_exp.deepCopyAll[PExp])
  ) ++ fields.map(f =>
      if (f == mutable_field)
        PAccPred(PFieldAccess(mutable_node_exp.deepCopyAll[PExp], PIdnUse(f)), PFullPerm())
      else
        PAccPred(PFieldAccess(mutable_node_exp.deepCopyAll[PExp], PIdnUse(f)), PBinExp(PIntLit(1), "/", PIntLit(2)))) ++
    collectQPsForRefFieldsProtected(fields, mutable_node_exp, graph_exp) ++
    collectInGraphForallsForRefFields(fields, graph_exp), "&&", PBoolLit(true))


   /*
    PBinExp(
    PUnExp("!", PBinExp(PNullLit(), "in", graph_exp.deepCopyAll[PExp])),
    "&&", PBinExp( PBinExp(mutable_node_exp.deepCopyAll[PExp], "in", graph_exp.deepCopyAll[PExp]),
      "&&", PBinExp(


            PAccPred(PFieldAccess(mutable_node_exp.deepCopyAll[PExp], PIdnUse(f_name)), PFullPerm()),
            PAccPred(PFieldAccess(mutable_node_exp.deepCopyAll[PExp], PIdnUse(f_name)), PBinExp(PIntLit(1), "/", PIntLit(2)))

        "&&", PBinExp(
          seqOfPExpToPExp(getQPsForRefFieldsProtected(prog.fields, mutable_node_exp, graph_exp.deepCopyAll[PExp]), "&&"), "&&",
          concatInGraphForallsForRefFields(prog.fields, graph_exp.deepCopyAll[PExp])))))
  */

  /* FIXME decided to use old(EXISTS_PATH(...)) for now.
  private def evalEdgeRelationInCorrectState(prog: PProgram, graph_exp: PExp): PExp = {
    prog.methods.collect { case m: PMethod =>
      m.deepCollect({
        case some_exp: PExp if some_exp == graph_exp =>
          val graph_defs: OurGraphSpec = graph_definitions(m.idndef.name)
          graph_defs.inputs
      })
    }
    graph_exp match {
      case PIdnUse(graph_name) if graph_definitions.find(_._1 == graph_name)
    }
    ???
  }*/

  private def EDGE(prog: PProgram, graph_exp: PExp, lhs_node_exp: PExp, rhs_node_exp: PExp): PExp = PCall(
    PIdnUse("edge"),
    Seq(
      PCall(PIdnUse("$$"), Seq(graph_exp)),
      lhs_node_exp.deepCopyAll[PExp],
      rhs_node_exp.deepCopyAll[PExp]))

  private def EXISTS_PATH(prog: PProgram, graph_exp: PExp, lhs_node_exp: PExp, rhs_node_exp: PExp): PExp = PCall(
    PIdnUse("exists_path"),
    Seq(
      PCall(PIdnUse("$$"), Seq(graph_exp.deepCopyAll[PExp])),
      lhs_node_exp.deepCopyAll[PExp],
      rhs_node_exp.deepCopyAll[PExp]))

  private def IS_GLOBAL_ROOT(prog: PProgram, graph_exp: PExp, root_node: PExp) = PForall(
    Seq(PFormalArgDecl(PIdnDef("n"), TypeHelper.Ref)),
    Seq( PTrigger(Seq(EXISTS_PATH(prog, graph_exp, root_node.deepCopyAll[PExp], PIdnUse("n")))) ),
    PBinExp(PBinExp(PIdnUse("n"), "in", graph_exp.deepCopyAll[PExp]), "==>", EXISTS_PATH(prog, graph_exp, root_node.deepCopyAll[PExp], PIdnUse("n")))
  )

  private def FUNCTIONAL(prog: PProgram, graph_exp: PExp) = PCall(
    PIdnUse("func_graph"),
    Seq(PCall(PIdnUse("$$"), Seq(graph_exp.deepCopyAll[PExp]))))

  private def UNSHARED(prog: PProgram, graph_exp: PExp) = PCall(
    PIdnUse("unshared_graph"),
    Seq(PCall(PIdnUse("$$"), Seq(graph_exp.deepCopyAll[PExp]))))

  private def ACYCLIC(prog: PProgram, graph_exp: PExp) = PCall(
    PIdnUse("acyclic_graph"),
    Seq(PCall(PIdnUse("$$"), Seq(graph_exp.deepCopyAll[PExp]))))

  private def ACYCLIC_LIST_SEGMENT(prog: PProgram, graph_exp: PExp): PExp = PBinExp(
    ACYCLIC(prog, graph_exp.deepCopyAll[PExp]), "&&", PBinExp(FUNCTIONAL(prog, graph_exp.deepCopyAll[PExp]), "&&", UNSHARED(prog, graph_exp.deepCopyAll[PExp])))

  private def DISJOINT(g0: PExp, g1: PExp): PExp = PBinExp(
    PForall(
      Seq(PFormalArgDecl(PIdnDef("n"), TypeHelper.Ref)),
      Seq( PTrigger(Seq(
        PBinExp(PIdnUse("n"), "in", g0),
        PBinExp(PIdnUse("n"), "in", g1)
      )) ),
      PBinExp(
        PBinExp(PIdnUse("n"), "in", g0),
        "==>",
        PUnExp("!",
          PBinExp(PIdnUse("n"), "in", g1)))),
    "&&",
    PForall(
      Seq(PFormalArgDecl(PIdnDef("n"), TypeHelper.Ref)),
      Seq( PTrigger(Seq(
        PBinExp(PIdnUse("n"), "in", g0),
        PBinExp(PIdnUse("n"), "in", g1)
      )) ),
      PBinExp(
        PBinExp(PIdnUse("n"), "in", g1),
        "==>",
        PUnExp("!",
          PBinExp(PIdnUse("n"), "in", g0)))))

  def ref_fields(prog: PProgram): Seq[String] = prog.fields.collect {
    case PField(f, t) if t == TypeHelper.Ref => f.name
    case x:PField => x.typ match {
      case d: PDomainType if d.domain.name == "Node" => x.idndef.name
    }
  }

  def handlePMethod(input: PProgram, m: PMethod): PNode = {

    def collect_objects(collection: Seq[PFormalArgDecl], typename: String): Seq[OurObject] = collection.collect {
      case x:PFormalArgDecl if (x.typ match {
        case d: PDomainType if d.domain.name == typename => true
        case _ => false//TODO set of Graphs
      }) => OurObject(x.idndef.name, OurGraph)
    }

    val input_graphs: Seq[OurObject] = collect_objects(m.formalArgs, "Graph")
    val output_graphs: Seq[OurObject] = collect_objects(m.formalReturns, "Graph")

    // Store the graph specifications for future reference.
    graph_definitions(m.idndef.name) = OurGraphSpec(input_graphs, output_graphs)

    def map_graphs_to_contracts(objects: Seq[OurObject]): Seq[PExp] = objects.collect {
      case o => { o.typ match {
        case n@ OurGraph => GRAPH(input, PIdnUse(o.name), ref_fields(input))
      }}
    }

    def disjoint_graph_specs(objects: Seq[OurObject]): Seq[PExp] = {
      val distinct_graphs: Iterator[List[OurObject]] = (objects.collect {
        case o => o.typ match {
          case g@ OurGraph => o
        }
      } toList).combinations(2)
      distinct_graphs.map((g_pair: List[OurObject]) => {
        DISJOINT(
          PIdnUse(g_pair(0).name),
          PIdnUse(g_pair(1).name))
      }) toList
    }

    def union_graph_specs(objects: Seq[OurObject], union_graphs: Seq[OurObject]): Seq[PExp] = union_graphs.toList match {
      case x :: xs if xs != Nil =>
        sys.error(s"In method ${m.idndef.name} we found the following output graphs: ${union_graphs.map(_.name)}, but no more than one output graph is allowed.")
        Seq()
      case x :: Nil => Seq(PBinExp(
        seqOfPExpToPExp(
          objects.map{ case o => PIdnUse(o.name) },
          "union", PEmptySet(TypeHelper.Ref)),
        "==",
        PIdnUse(union_graphs.last.name)))
      case Nil => Seq()
    }

    val output_graphs_footprint: Seq[PExp] =
      if (output_graphs.nonEmpty)
        map_graphs_to_contracts(output_graphs)
      else if (input_graphs.nonEmpty)
        Seq(GRAPH(input, seqOfPExpToPExp(input_graphs.collect {
          case o => { o.typ match { case g@ OurGraph => PIdnUse(o.name) } }
        }, "union", PEmptySet(TypeHelper.Ref)), ref_fields(input)))
      else
        Seq()

    PMethod(
      m.idndef,
      m.formalArgs.map(x => {
        handlePFormalArgDecl(input, x)
      }),
      m.formalReturns.map(x => {
        handlePFormalArgDecl(input, x)
      }),
      /*map_graphs_to_contracts(input_graphs) ++ disjoint_graph_specs(input_graphs) ++*/ m.pres/*.map(x => {
        handlePExp(input, x)
      })*/,
      /*output_graphs_footprint ++*/ union_graph_specs(input_graphs, output_graphs) ++ m.posts/*.map(x => { TODO remove union_graph_specs
        handlePExp(input, x)
      })*/,
      handlePMethodBody(m.body,  input_graphs, output_graphs))
  }

  //add Framing Axioms and later Coloring Axioms
  def handlePMethodBody(body: Option[PStmt], input_graphs: Seq[OurObject], output_graphs: Seq[OurObject]): Option[PStmt] =
    input_graphs.size match {
      case a if a > 1 && output_graphs.size == 1 => Some(PSeqn((Seq(assignUnionGraphWithFraming(input_graphs, output_graphs)) /: body.map(handlePStmt(_, input_graphs)))(_ :+ _)))
      case _ => body.map(handlePStmt(_, input_graphs))
  }

  def assignUnionGraphWithFraming(input_graphs: Seq[OurObject], output_graph: Seq[OurObject]): PStmt = {
    PSeqn(Seq(getFramingAxioms(input_graphs.map(a => PIdnUse(a.name))) /*++ output_graph.map(a => PIdnUse(a.name))*/,//TODO we don't have access to the output graph yet, if we don't know what the output graph is
      PVarAssign(
        PIdnUse(
          output_graph.last.name
        ),
        seqOfPExpToPExp(
          input_graphs.map{ case o => PIdnUse(o.name) },
          "union", PEmptySet(TypeHelper.Ref))
      )
    ))

  }

  def handlePStmt(stmt: PStmt, graphs: Seq[OurObject]): PStmt = {//TODO insert the coloring axioms
    stmt
    /*stmt match {
      case PSeqn(_)  => PSeqn(stmt.childStmts.map(handlePStmt(_, graphs))) //TODO probably need also to visit the conditions
      case PIf(a, b, c)  => PIf(a, PSeqn(b.childStmts.map(handlePStmt(_, graphs))), PSeqn(c.childStmts.map(handlePStmt(_, graphs))))
      case PWhile(a, b, c)  => PWhile(a, b, PSeqn(c.childStmts.map(handlePStmt(_, graphs))))
      case _ => stmt
    }*/
  }

  def handlePField(input: PProgram, m: PField): PField = {
    m.typ match {//TODO If fields of type Graph are used in a method, do we need to put requires Graph and ensures Graph?
      case d: PDomainType =>
        d.domain.name match {
          case "Node" => PField(m.idndef, TypeHelper.Ref)
          case "Graph" => PField(m.idndef, PSetType(TypeHelper.Ref))
          case "List" => PField(m.idndef, PSetType(TypeHelper.Ref))
          case _ => m
        }
      case d: PSetType =>
        PField(m.idndef, PSetType(handlePField(input, PField(m.idndef, d.elementType)).typ))
      case _ => m
    }
  }

  def handlePExp(input: PProgram, m: PExp): PExp = {
    m match {
      case m: PQuantifier => handlePQuantifier(input, m)
      case _ => m//TODO
    }
  }

  def handlePQuantifier(input: PProgram, m: PQuantifier): PQuantifier = {
    m match{
      case m: PForall => PForall(m.vars.map(x => handlePFormalArgDecl(input, x)), m.triggers/*.map(x => PTrigger(x.exp.map(x => handlePExp(input, x))))*/,
        handlePExp(input, m.body))
      case m: PExists => PExists(m.vars.map(x => handlePFormalArgDecl(input, x)), m.body)//TODO handle PTrigger, PBody?
    }
  }

  def getFramingAxioms(graphNames : Seq[PIdnUse]): PStmt = {
    graphNames.size match {
      case a: Int if a <= 1 => PSkip()
      case _ => PSeqn(graphNames.flatMap(a =>
        graphNames.filter(b => !b.name.equals(a.name) && graphNames.indexOf(b) > graphNames.indexOf(a))
          .map(b => assumeApplyTCFraming(a, b))))
    }

  }

  def assumeApplyTCFraming(exp: PExp, exp1: PExp): PStmt = {
    PAssume(PCall(PIdnUse("apply_TCFraming"), Seq(exp, exp1)))
  }


  def handlePCall(input: PProgram, m: PCall): PNode = {

    m.func.name match {
      case "GRAPH" if m.args.length == 1 => GRAPH(input, m.args(0), ref_fields(input))
      case "PROTECTED_GRAPH" if m.args.length == 3 => m.args(2) match {
        case PIdnUse(f_name) =>
          PROTECTED_GRAPH(input, m.args(0), ref_fields(input), m.args(1), f_name)
        case _ => m
      }

      case "EDGE" if m.args.length == 3 => EDGE(input, m.args(0), m.args(1), m.args(2))
      case "EXISTS_PATH" if m.args.length == 3 => EXISTS_PATH(input, m.args(0), m.args(1), m.args(2))
      case "IS_GLOBAL_ROOT" if m.args.length == 2 => IS_GLOBAL_ROOT(input, m.args(0), m.args(1))

      case "FUNCTIONAL" if m.args.length == 1 => FUNCTIONAL(input, m.args(0))
      case "UNSHARED" if m.args.length == 1 => UNSHARED(input, m.args(0))
      case "ACYCLIC" if m.args.length == 1 => ACYCLIC(input, m.args(0))
      case "ACYCLIC_LIST_SEGMENT" if m.args.length == 1 => ACYCLIC_LIST_SEGMENT(input, m.args(0))
      case _ => m
    }

  }

  private def synthesizeFieldParametricMethods(input: PProgram): Seq[PMethod] = input.methods.collect {
    case m: PMethod if m.idndef.name == "link_$field$" =>
      input.fields.collect { // FIXME Ref type?
        case f: PField =>
          val new_m = m.deepCopyWithNameSubstitution(
            idndef = PIdnDef(s"link_${f.idndef.name}"))(
            "$field$", f.idndef.name)
          new_m
      }
    case m: PMethod if m.idndef.name == "unlink_$field$" =>
      input.fields.collect {
        case f: PField =>
          val new_m = m.deepCopyWithNameSubstitution(
            idndef = PIdnDef(s"unlink_${f.idndef.name}"))(
            "$field$", f.idndef.name)
          new_m
      }
    case m: PMethod => Seq(m)

  } flatten

  private def read = PBinExp(PIntLit(1), "/", PIntLit(2)).deepCopyAll[PExp]

  private def synthesizeApplyTCFramingHDF(input: PProgram): Seq[PFunction] = input.functions.collect {
    case proto_f: PFunction if proto_f.idndef.name == "apply_TCFraming" =>
      proto_f.deepCopy(pres =
        collectQPsForRefFields(ref_fields(input), PIdnUse("g0"), this.read) ++
          collectQPsForRefFields(ref_fields(input), PIdnUse("g1"), this.read) ++
          proto_f.pres)
    case f: PFunction => f
  }

  private def $$(input: PProgram) = PFunction(
    PIdnDef("$$"),
    Seq(
      PFormalArgDecl(
        PIdnDef("nodes"),
        PSetType(TypeHelper.Ref)) ),
    PSetType(PDomainType(PIdnUse("Edge"), Seq())),
    collectQPsForRefFields(ref_fields(input), PIdnUse("nodes"), this.read),
    Seq(
      PForall(
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
              seqOfPExpToPExp(input.fields.map( f => PBinExp(
                PFieldAccess(PIdnUse("p"),PIdnUse(f.idndef.name) ), "==", PIdnUse("s"))), "||", PBoolLit(false))),
            "&&",
            PBinExp(PIdnUse("p"), "!=", PIdnUse("s"))),
          "<==>",
          PBinExp(
            PCall(PIdnUse("create_edge"),Seq(PIdnUse("p"),PIdnUse("s"))),
            "in",
            PResultLit()))),
      PForall(
        Seq(
          PFormalArgDecl(PIdnDef("p"), TypeHelper.Ref),
          PFormalArgDecl(PIdnDef("s"), TypeHelper.Ref)),
        Seq(
          PTrigger( Seq(
            PBinExp(PIdnUse("p"), "in", PIdnUse("nodes")),
            PBinExp(PIdnUse("s"), "in", PIdnUse("nodes")),
            PCall(PIdnUse("exists_path"), Seq( PResultLit(), PIdnUse("p"), PIdnUse("s") ))))),
        PBinExp(
          PBinExp(
            PBinExp(PIdnUse("p"), "in", PIdnUse("nodes")),
            "&&",
            PCall(PIdnUse("exists_path"), Seq( PResultLit(), PIdnUse("p"), PIdnUse("s") ))),
          "==>",
          PBinExp(PIdnUse("s"), "in", PIdnUse("nodes")))),
      PForall(
        Seq(
          PFormalArgDecl(PIdnDef("p"), TypeHelper.Ref),
          PFormalArgDecl(PIdnDef("s"), TypeHelper.Ref)),
        Seq(
          PTrigger( Seq(
            PBinExp(PIdnUse("p"), "in", PIdnUse("nodes")),
            PBinExp(PIdnUse("s"), "in", PIdnUse("nodes")),
            PCall(PIdnUse("exists_path"), Seq( PResultLit(), PIdnUse("p"), PIdnUse("s") ))))),
        PBinExp(
          PBinExp(
            PBinExp(PIdnUse("s"), "in", PIdnUse("nodes")),
            "&&",
            PCall(PIdnUse("exists_path"), Seq( PResultLit(), PIdnUse("p"), PIdnUse("s") ))),
          "==>",
          PBinExp(PIdnUse("p"), "in", PIdnUse("nodes"))))),
    None, None)

  def synthesizeParametricEntities(input: PProgram) = PProgram(
    input.imports,
    input.macros,
    input.domains,
    input.fields,
    synthesizeApplyTCFramingHDF(input) :+ $$(input), //functions
    input.predicates,
    synthesizeFieldParametricMethods(input), //methods
    input.errors)

  private def getNoExitWisdom(input: Program, g0:Exp, g1:Exp)(pos: Position = NoPosition, info: Info = NoInfo, errT: ErrorTrafo = NoTrafos): Stmt = {
    val $$_func = input.findFunction("$$")
    val exists_path_funbc = input.findDomainFunction("exists_path")

    def apply_NoExit_framing_forall(G0: Exp, G1: Exp) = {
      require(G0 == g0 && G1 == g1 || G0 == g1 && G1 == g0)
      Forall(
        Seq(
          LocalVarDecl("u", Ref)(pos, info, errT),
          LocalVarDecl("v", Ref)(pos, info, errT)),
        Seq(
          Trigger(Seq(
            DomainFuncApp(
              exists_path_funbc,
              Seq(
                FuncApp(
                  $$_func,
                  Seq(AnySetUnion(g0, g1)(pos, info, errT)))(pos, info, errT),
                LocalVar("u")(Ref, pos, info, errT),
                LocalVar("v")(Ref, pos, info, errT)),
              Map.empty[TypeVar, Type])(pos, info, errT),
            AnySetContains(LocalVar("u")(Ref, pos, info, errT), G0)(pos, info, errT),
            AnySetContains(LocalVar("v")(Ref, pos, info, errT), G0)(pos, info, errT)
          ))(pos, info, errT)
        ),
        Implies(
          And(
            AnySetContains(LocalVar("u")(Ref, pos, info, errT), G0)(pos, info, errT),
            Not( AnySetContains(LocalVar("v")(Ref, pos, info, errT), G0)(pos, info, errT) )(pos, info, errT)
          )(pos, info, errT),
          Not(
            DomainFuncApp(
              exists_path_funbc,
              Seq(
                FuncApp(
                  $$_func,
                  Seq(AnySetUnion(g0, g1)(pos, info, errT)))(pos, info, errT),
                LocalVar("u")(Ref, pos, info, errT),
                LocalVar("v")(Ref, pos, info, errT)),
              Map.empty[TypeVar, Type])(pos, info, errT) )(pos, info, errT)
        )(pos, info, errT))(pos, info, errT)
    }
    Inhale(And(apply_NoExit_framing_forall(g0,g1),apply_NoExit_framing_forall(g1,g0))(pos, info, errT))(pos, info, errT)
  }

  private def getFramingWisdom(input: Program, g0:Exp, g1:Exp)(pos: Position = NoPosition, info: Info = NoInfo, errT: ErrorTrafo = NoTrafos): Stmt = {
    val apply_TCFraming_func = input.findFunction("apply_TCFraming")
    Inhale(FuncApp(apply_TCFraming_func, Seq(g0, g1))(pos, info, errT))(pos, info, errT)
  }

  private def getOperationalWisdoms(input: Program, local_m: Method, ctx: ContextC[Node, String])(pos: Position = NoPosition, info: Info = NoInfo, errT: ErrorTrafo = NoTrafos): Stmt = {

    val graph_defs: OurGraphSpec = graph_definitions(local_m.name)
    val distinct_graphs: Seq[OurObject] = graph_defs.inputs.collect { case o => o.typ match { case g@ OurGraph => o } }

    def all_wisdoms_for_this_frame(g: OurObject, subframe_gs: Seq[LocalVar]) = Seqn(
      Seq(
        getFramingWisdom(input, LocalVar(g.name)(SetType(Ref), pos, info, errT), seqOfExpToUnionExp(subframe_gs)(pos, info, errT))(pos, info, errT),
        getNoExitWisdom(input, LocalVar(g.name)(SetType(Ref), pos, info, errT), seqOfExpToUnionExp(subframe_gs)(pos, info, errT))(pos, info, errT)),
      Seq())(pos, info, errT)

    println(s">>> getOperationalWisdoms(local_m = ${local_m.name})")
    println(s">>>  distinct_graphs = ${distinct_graphs.map(_.name)}")

    val tmp1: Seq[Seqn] = distinct_graphs.collect {
      case g =>
        println(s">>> >>> g = ${g.name}")
        (distinct_graphs diff Seq(g)).toList.combinations(distinct_graphs.size - 1).collect {
          case x :: xs if xs != Nil || g.name < x.name =>
            println(s">>> >>> >>> x :: xs = ${(x :: xs).map(_.name)}")
            val subframe_gs: Seq[LocalVar] = (x :: xs).map { subframe => LocalVar(subframe.name)(SetType(Ref), pos, info, errT) }
            Seqn(
              Seq(
                getFramingWisdom(input, LocalVar(g.name)(SetType(Ref), pos, info, errT), seqOfExpToUnionExp(subframe_gs)(pos, info, errT))(pos, info, errT),
                getNoExitWisdom(input, LocalVar(g.name)(SetType(Ref), pos, info, errT), seqOfExpToUnionExp(subframe_gs)(pos, info, errT))(pos, info, errT)),
              Seq())(pos, info, errT)
      }
    } flatten

    Seqn(tmp1, Seq())(pos, info, errT)
  }

  def handleAssignments(input: Program, fa: FieldAssign, ctx: ContextC[Node, String]): Node = {

    Seqn(input.methods.collect { case m: Method =>
      m.deepCollectInBody({
        case some_fa: FieldAssign if some_fa == fa =>
          val graph_defs = graph_definitions(m.name)
          val local_g =
            if (graph_defs.outputs.nonEmpty)
              LocalVar(graph_defs.outputs.last.name)(SetType(Ref), fa.pos, fa.info, fa.errT)
            else
              seqOfExpToUnionExp(graph_defs.inputs.map { in => LocalVar(in.name)(SetType(Ref), fa.pos, fa.info, fa.errT) })(fa.pos, fa.info, fa.errT) //TODO causes an error, if there is no graph as input

          Seqn(
            Seq(
              getOperationalWisdoms(input, m, ctx)(fa.pos, fa.info, fa.errT),
              MethodCall(s"unlink_${fa.lhs.field.name}", Seq(local_g, fa.lhs.rcv), Seq())(fa.pos, fa.info, fa.errT),
              MethodCall(s"link_${fa.lhs.field.name}", Seq(local_g, fa.lhs.rcv, fa.rhs), Seq())(fa.pos, fa.info, fa.errT)),
            Seq())(fa.pos, fa.info, fa.errT)
      })
    } flatten, Seq())(fa.pos, fa.info, fa.errT)
  }

  def handleMethods(input: Program, m: Method, ctx: ContextC[Node, String]): Node = m
}
