package viper.silver.plugin

import viper.silver.ast.{ErrTrafo, Exp, Node}
import viper.silver.plugin.errors.OuroborosGraphSpecificactionError
import viper.silver.plugin.reasons.{InsufficientGraphPermission, NotDisjointGraphsReason, NullInGraphReason, OpenGraphReason}
import viper.silver.verifier.errors.{ContractNotWellformed, PostconditionViolated}
import viper.silver.verifier.reasons.{AssertionFalse, InsufficientPermission}

object OuroborosErrorTransformers {

  def NullInGraphErrTrafo(names:Seq[Node]): ErrTrafo = ErrTrafo(
    {
      case err => OuroborosGraphSpecificactionError(
        err.offendingNode,
        NullInGraphReason(
          err.offendingNode,
          s"Null might be in Graph ${names.head}"
        )
      )
    }
  )
  val graphErrTrafo: ErrTrafo = ErrTrafo(
    {
      case err: PostconditionViolated => err.reason match {
        case r : InsufficientPermission => { //TODO maybe find out, for which field, we don't have enough permissions
          OuroborosGraphSpecificactionError(
            err.offendingNode,
            InsufficientGraphPermission(
              err.offendingNode,
              "There might be insufficient permission to access all fields of nodes inside the graph."
            ),
            err.cached
          )
        }
        case r : AssertionFalse if r.readableMessage.contains(s"${OuroborosNames.getIdentifier("closed")}(")=> {
          OuroborosGraphSpecificactionError(
            err.offendingNode,
            OpenGraphReason(
              err.offendingNode,
              "This graph might not be closed."
            ),
            err.cached
          )
        }

        case r : AssertionFalse if r.readableMessage.contains(s"${OuroborosNames.getIdentifier("NoNullInGraph")}(") => {
          OuroborosGraphSpecificactionError(
            err.offendingNode,
            NullInGraphReason(
              err.offendingNode,
              "Null might be in this graph."
            ),
            err.cached
          )
        }

        case _ => err
      }
      case err => err
    }
  )

  def closedGraphErrTrafo(names: Seq[Node]) : ErrTrafo = ErrTrafo({
    case x: ContractNotWellformed if x.reason.isInstanceOf[AssertionFalse] => OuroborosGraphSpecificactionError(
      x.offendingNode,
      OpenGraphReason(
        x.offendingNode,
        s"There might not be enough permissions to check closednes of ${names.head}."
      ),
      x.cached
    )

    case x if x.reason.isInstanceOf[AssertionFalse] => OuroborosGraphSpecificactionError(
      x.offendingNode,
      OpenGraphReason(
        x.offendingNode,
        s"Graph ${names.head} might not be closed."
      ),
      x.cached
    )
  })

  val qpsForRefFieldErrTrafo : ErrTrafo = ErrTrafo({
    case x => OuroborosGraphSpecificactionError(
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
      x.offendingNode,
      NotDisjointGraphsReason(
        x.offendingNode,
        s"Graphs ${names.head} and ${names.last} might not be disjoint."
      )
    )
  })
}
