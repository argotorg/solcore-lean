import Solcore.Test.SourceCoreOperatorCallsFacts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates

/-! The exact original recursive expression tree includes both indirect calls.
Its source occurrences and ordered argument lists come from the checker graph. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreOperatorCalls
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (Syntax)

theorem ObservedProgram.identity_syntax {fixture : CompiledFixture} (observed : ObservedProgram fixture) :
    Syntax observed.identityRow.row.function.typedBody observed.identityShape.read.node.id :=
  .leaf (.read observed.identityShape.read.found observed.identityShape.read.form)

theorem ObservedProgram.select_syntax {fixture : CompiledFixture} (observed : ObservedProgram fixture) :
    Syntax observed.selectRow.row.function.typedBody observed.selectShape.expression.node.id := by
  apply Syntax.conditional observed.selectShape.expression.found observed.selectShape.expressionForm
  · exact .unary observed.selectShape.negation.found observed.selectShape.negationForm
      (.leaf (.read observed.selectShape.flagRead.found observed.selectShape.flagRead.form))
  · apply Syntax.binary observed.selectShape.sum.found observed.selectShape.sumForm
    · apply Syntax.call observed.selectShape.leftCall.found observed.selectShape.leftCall.form
        (.leaf (.read observed.selectShape.leftFunction.found observed.selectShape.leftFunction.form))
      intro child member
      have same := List.mem_singleton.mp member
      subst child
      exact .leaf (.read observed.selectShape.leftArgument.found observed.selectShape.leftArgument.form)
    · exact .leaf (.read observed.selectShape.leftValue.found observed.selectShape.leftValue.form)
  · apply Syntax.binary observed.selectShape.difference.found observed.selectShape.differenceForm
    · apply Syntax.call observed.selectShape.rightCall.found observed.selectShape.rightCall.form
        (.leaf (.read observed.selectShape.rightFunction.found observed.selectShape.rightFunction.form))
      intro child member
      have same := List.mem_singleton.mp member
      subst child
      exact .leaf (.read observed.selectShape.rightArgument.found observed.selectShape.rightArgument.form)
    · exact .leaf (.read observed.selectShape.rightValue.found observed.selectShape.rightValue.form)

end Tests.SourceCoreOperatorCalls
