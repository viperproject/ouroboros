package viper.silver.plugin

import viper.silver.ast.{ErrTrafo, Exp, FieldAssign, Node}
import viper.silver.plugin.errors._
import viper.silver.plugin.reasons._
import viper.silver.verifier.AbstractVerificationError
import viper.silver.verifier.errors._
import viper.silver.verifier.reasons.{AssertionFalse, InsufficientPermission, InternalReason}

object OuroborosErrorTransformers {

  def NullInGraphErrTrafo(names:Seq[Node]): ErrTrafo = ErrTrafo(
    {
      case err => OuroborosGraphSpecificactionError(
        names.head.toString(),
        err.offendingNode,
        NullInGraphReason(
          err.offendingNode,
          s"Null might be in Graph ${names.head}"
        )
      )
    }
  )
  def graphErrTrafo(g: String): ErrTrafo = {
    def reasonTransformer(err: AbstractVerificationError): AbstractVerificationError = {
      err.reason match {
        case r : InsufficientPermission => //TODO maybe find out, for which field, we don't have enough permissions
          OuroborosGraphSpecificactionError(
            g,
            err.offendingNode,
            InsufficientGraphPermission(
              err.offendingNode,
              s"There might be insufficient permission to access all fields of nodes inside the graph $g."
            ),
            err.cached
          )
        case r : AssertionFalse if r.readableMessage.contains(s"${OuroborosNames.getIdentifier("CLOSED")}(")=>
          OuroborosGraphSpecificactionError(
            g,
            err.offendingNode,
            OpenGraphReason(
              err.offendingNode,
              s"The graph $g might not be closed."
            ),
            err.cached
          )

        case r : AssertionFalse if r.readableMessage.contains(s"${OuroborosNames.getIdentifier("NoNullInGraph")}(") =>
          OuroborosGraphSpecificactionError(
            g,
            err.offendingNode,
            NullInGraphReason(
              err.offendingNode,
               s"Null might be in the graph $g."
            ),
            err.cached
          )

        case _ => err
      }
    }
    ErrTrafo(
      {
        case err: PostconditionViolated => reasonTransformer(err)
        case err: LoopInvariantNotEstablished => reasonTransformer(err) //TODO different error messages for loop invariant
        case err: LoopInvariantNotPreserved => reasonTransformer(err)
        case err => err
      }
    )
  }

  def closedGraphErrTrafo(names: Seq[Node]) : ErrTrafo = ErrTrafo({
    case x: ContractNotWellformed if x.reason.isInstanceOf[AssertionFalse] => errors.OuroborosTypeError(
      x.offendingNode,
      OpenGraphReason(
        x.offendingNode,
        s"There might not be enough permissions to check closedness of ${names.head}."
      ),
      x.cached
    )

    case x if x.reason.isInstanceOf[AssertionFalse] => errors.OuroborosTypeError(
      x.offendingNode,
      OpenGraphReason(
        x.offendingNode,
        s"Graph ${names.head} might not be closed."
      ),
      x.cached
    )
  })

  def DAGErrTrafo(name: Node) : ErrTrafo = ErrTrafo({
    case x: ContractNotWellformed if x.reason.isInstanceOf[AssertionFalse] => errors.OuroborosTypeError(
      x.offendingNode,
      OpenGraphReason(
        x.offendingNode,
        s"There might not be enough permissions to check acyclicity of $name."
      ),
      x.cached
    )

    case x if x.reason.isInstanceOf[AssertionFalse] => errors.OuroborosTypeError(
      x.offendingNode,
      CyclicGraphReason(
        x.offendingNode,
        s"Graph $name might not be acyclic."
      ),
      x.cached
    )
  })

  def qpsForRefFieldErrTrafo(g: String) : ErrTrafo = ErrTrafo({
    case x => OuroborosGraphSpecificactionError(
      g,
      x.offendingNode,
      InsufficientGraphPermission(
        x.offendingNode,
        s"There might be insufficient permissions for fields in the graph"
      ),
      x.cached
    )
  })

  def disjointGraphsErrTrafo(names: Seq[Node]) : ErrTrafo = ErrTrafo({
    case x => OuroborosGraphSpecificactionError(
      names.head.toString(),
      x.offendingNode,
      NotDisjointGraphsReason(
        x.offendingNode,
        s"Graphs ${names.head} and ${names.last} might not be disjoint."
      )
    )
  })

  def closedGraphParametersErrTrafo(methodName: String, graph: Node, pre: Boolean): ErrTrafo = ErrTrafo(
    {
      case x if x.reason.isInstanceOf[AssertionFalse] => OuroborosClosedGraphSpecificactionError(
        graph.toString(),
        x.offendingNode,
        OpenGraphReason(
          x.offendingNode,
          if (pre) s"The union of the input of method $methodName might not be closed in the beginning."
          else
            s"The union of the input and output graphs of method $methodName might not be closed in the end."
        ),
        x.cached
      )
    }
  )

  def acyclicGraphErrTrafo(graph: Node) = ErrTrafo(
    {
      case x if x.reason.isInstanceOf[AssertionFalse] => OuroborosGraphSpecificactionError(
        graph.toString(),
        x.offendingNode,
        CyclicGraphReason(
          x.offendingNode,
          s"Graph $graph might not be acyclic."
        )
      )
      case x if x.reason.isInstanceOf[InsufficientPermission] => OuroborosInternalEncodingError(
        x.offendingNode,
        InsufficientGraphPermission(
          x.offendingNode,
          s"Might have insufficient permission to access all fields of $graph."
        )
      )
    }
  )

  def unlinkErrTrafo(fa: FieldAssign): ErrTrafo = {
    //TODO improve Error messages
    ErrTrafo({
      case x: PreconditionInCallFalse =>
        x.reason match {
          case r: InsufficientPermission => OuroborosAssignmentError(x.offendingNode,
            InsufficientGraphPermission(x.offendingNode, s"There might be insufficient permissiion to get read access to the ${fa.lhs.field.name} fields of all elements in ${x.offendingNode.args.head} " +
              s"and write access to the ${fa.lhs.field.name} field of ${x.offendingNode.args(1)}. Original message: " + x.reason.readableMessage),
            x.cached)

          case r: AssertionFalse => OuroborosAssignmentError(x.offendingNode,
            NotInGraphReason(x.offendingNode, s"${x.offendingNode.args(1)} might not be in ${x.offendingNode.args.head}" +
              s" or null might be in ${x.offendingNode.args.head}. Original message: " + x.reason.readableMessage),
            x.cached)

          case _ => OuroborosAssignmentError(x.offendingNode,
            InternalReason(x.offendingNode, "internal error in unlink: " + x.reason.readableMessage),
            x.cached)
        }
      case x => x
    })
  }

  def linkErrTrafo(fa: FieldAssign): ErrTrafo = {
    ErrTrafo({
      case x: PreconditionInCallFalse =>
        x.reason match {
          case r: AssertionFalse => OuroborosAssignmentError(x.offendingNode,
            NotInGraphReason(x.offendingNode, s"Assignment Error: ${x.offendingNode.args(2)} might not be in ${x.offendingNode.args.head}. " +
              s"Original Message: ${x.reason.readableMessage}"),
            x.cached)

          case xy => OuroborosAssignmentError(x.offendingNode,
            InternalReason(x.offendingNode, "internal error in link: " + x.reason.readableMessage),
            x.cached)
        }
      case x => x
    })
  }

  def wrongTypeErrTrafo(exp: Node, wantedType: Topology with Closedness): ErrTrafo = ErrTrafo({
    case x =>
      OuroborosTypeError(x.offendingNode,
        WrongTypeReason(x.offendingNode, s"The expression $exp might not be of wished Type $wantedType."), false)
  })

  def wrongTypeAfterCallErrTrafo(exp: Node, wantedType: Topology with Closedness): ErrTrafo = ErrTrafo({
    case x =>
      OuroborosTypeError(x.offendingNode,
        WrongTypeReason(x.offendingNode, s"The expression $exp might not be of wished Type $wantedType after the methodCall."), false)
  })

  def ZOPGCheckErrTrafo(exp: Node): ErrTrafo = ErrTrafo({
    case x =>
      OuroborosNotSupportedError(x.offendingNode,
        ZOPGCheckNotSupportedReason(x.offendingNode, s"Dynamically checking that $exp is of type ZOPG is not supported."), false)
  })

  def nodeNotInGraphErrTrafo(node: Node, graph: Node): ErrTrafo = ErrTrafo({
    case x =>
      OuroborosNodeCheckError(x.offendingNode,
        NotInGraphReason(x.offendingNode, s"The Node $node might not be in the declared Graph $graph."), false)
  })
}
