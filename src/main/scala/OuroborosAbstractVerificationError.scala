package viper.silver.plugin

import viper.silver.ast.utility.Rewriter.Rewritable
import viper.silver.ast.{Node, Position, Positioned, TransformableErrors}
import viper.silver.verifier.{AbstractError, AbstractVerificationError, ErrorReason, errors}
import viper.silver.verifier.errors.{ErrorNode, Internal}

abstract class OuroborosAbstractVerificationError extends AbstractVerificationError{
}
object errors {
  type ErrorNode = Node with Positioned with TransformableErrors with Rewritable
  case class OuroborosGraphSpecificactionError(offendingNode: ErrorNode, reason: ErrorReason, override val cached: Boolean = false) extends OuroborosAbstractVerificationError {
    val id = "Graph"//TODO
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

}

abstract class OuroborosAbstractError extends AbstractError {
}

case class OuroborosInvalidIdentifierError(message: String, override val pos: Position) extends OuroborosAbstractError {
  def fullId = "invalid.identifier"
  def readableMessage: String = s"invalid Identifier: $message ($pos)"
}

/*object errors {

}*/
