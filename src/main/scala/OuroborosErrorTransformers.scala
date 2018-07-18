package viper.silver.plugin

import viper.silver.ast.{ErrTrafo, Exp, Node}
import viper.silver.plugin.errors.OuroborosGraphSpecificactionError
import viper.silver.plugin.reasons.{InsufficientGraphPermission, NotDisjointGraphsReason, NullInGraphReason, OpenGraphReason}
import viper.silver.verifier.AbstractVerificationError
import viper.silver.verifier.errors.{ContractNotWellformed, LoopInvariantNotEstablished, LoopInvariantNotPreserved, PostconditionViolated}
import viper.silver.verifier.reasons.{AssertionFalse, InsufficientPermission}

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
        case r : InsufficientPermission => { //TODO maybe find out, for which field, we don't have enough permissions
          OuroborosGraphSpecificactionError(
            g,
            err.offendingNode,
            InsufficientGraphPermission(
              err.offendingNode,
              s"There might be insufficient permission to access all fields of nodes inside the graph $g."
            ),
            err.cached
          )
        }
        case r : AssertionFalse if r.readableMessage.contains(s"${OuroborosNames.getIdentifier("closed")}(")=> {
          OuroborosGraphSpecificactionError(
            g,
            err.offendingNode,
            OpenGraphReason(
              err.offendingNode,
              s"The graph $g might not be closed."
            ),
            err.cached
          )
        }

        case r : AssertionFalse if r.readableMessage.contains(s"${OuroborosNames.getIdentifier("NoNullInGraph")}(") => {
          OuroborosGraphSpecificactionError(
            g,
            err.offendingNode,
            NullInGraphReason(
              err.offendingNode,
               s"Null might be in the graph $g."
            ),
            err.cached
          )
        }

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
    case x: ContractNotWellformed if x.reason.isInstanceOf[AssertionFalse] => OuroborosGraphSpecificactionError(
      names.head.toString(),
      x.offendingNode,
      OpenGraphReason(
        x.offendingNode,
        s"There might not be enough permissions to check closedness of ${names.head}."
      ),
      x.cached
    )

    case x if x.reason.isInstanceOf[AssertionFalse] => OuroborosGraphSpecificactionError(
      names.head.toString(),
      x.offendingNode,
      OpenGraphReason(
        x.offendingNode,
        s"Graph ${names.head} might not be closed."
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
      case x if x.reason.isInstanceOf[AssertionFalse] => OuroborosGraphSpecificactionError(
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
}
