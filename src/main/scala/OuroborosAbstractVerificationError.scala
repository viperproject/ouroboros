package viper.silver.plugin

import viper.silver.ast.utility.Rewriter.Rewritable
import viper.silver.ast.{Node, Position, Positioned, TransformableErrors}
import viper.silver.verifier.{AbstractVerificationError, AbstractError, AbstractErrorReason, ErrorReason}

abstract class OuroborosAbstractVerificationError extends AbstractVerificationError { }

object errors {
  type ErrorNode = Node with Positioned with TransformableErrors with Rewritable
  case class OuroborosGraphSpecificactionError(offendingNode: ErrorNode, reason: ErrorReason, override val cached: Boolean = false) extends OuroborosAbstractVerificationError {
    val id = "graph.specification"//TODO
    val text = "It could not be verified that this is a graph."
    def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = OuroborosGraphSpecificactionError(offendingNode, this.reason)
    def withReason(r: ErrorReason) = OuroborosGraphSpecificactionError(offendingNode, r)
  }

  case class OuroborosInternalEncodingError(offendingNode: ErrorNode, reason: ErrorReason, override val cached: Boolean = false) extends OuroborosAbstractVerificationError {
    val id = "internal"
    val text = "An internal error occurred."
    def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = OuroborosInternalEncodingError(offendingNode, this.reason)
    def withReason(r: ErrorReason) = OuroborosInternalEncodingError(offendingNode, r)
  }

  case class OuroborosAssignmentError(offendingNode: ErrorNode, reason: ErrorReason, override val cached: Boolean = false) extends OuroborosAbstractVerificationError {
    val id = "graph.assignment"//TODO
    val text = "Assignment failed."
    def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = OuroborosAssignmentError(offendingNode, this.reason)
    def withReason(r: ErrorReason) = OuroborosAssignmentError(offendingNode, r)
  }

}

object reasons {
  type ErrorNode = errors.ErrorNode
  case class NotInGraphReason(offendingNode: ErrorNode, explanation: String) extends AbstractErrorReason {
    val id = "node.not.in.graph"
    val readableMessage = explanation

    def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = NotInGraphReason(offendingNode, this.explanation)
  }

  case class InsufficientGraphPermission(offendingNode: ErrorNode, explanation: String) extends AbstractErrorReason {
    val id = "insufficient.graph.permissions"
    val readableMessage = explanation

    def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = InsufficientGraphPermission(offendingNode, this.explanation)
  }

  case class NullInGraphReason(offendingNode: ErrorNode, explanation: String) extends AbstractErrorReason {
    val id = "null.in.graph"
    val readableMessage = explanation

    def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = NullInGraphReason(offendingNode, this.explanation)
  }

  case class OpenGraphReason(offendingNode: ErrorNode, explanation: String) extends AbstractErrorReason {
    val id = "graph.not.closed"
    val readableMessage = explanation

    def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = OpenGraphReason(offendingNode, this.explanation)
  }

  case class NotDisjointGraphsReason(offendingNode: ErrorNode, explanation: String) extends AbstractErrorReason {
    val id = "graphs.not.disjoint"
    val readableMessage = explanation

    def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = NotDisjointGraphsReason(offendingNode, this.explanation)
  }
}

abstract class OuroborosAbstractError extends AbstractError { }

case class OuroborosInvalidIdentifierError(message: String, override val pos: Position) extends OuroborosAbstractError {
  def fullId = "invalid.identifier"
  def readableMessage: String = s"invalid Identifier: $message ($pos)"
}

