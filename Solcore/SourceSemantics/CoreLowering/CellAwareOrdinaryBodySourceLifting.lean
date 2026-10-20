import Solcore.SourceSemantics.CoreLowering.CellAwareOrdinaryBodySourceConditional
import Solcore.SourceSemantics.CoreLowering.CellAwareOrdinaryBodyTree

/-! The actual finite lexical body certificate lifts ordinary Source success
and failure, with reached heaps and lexical scope restoration. No Core run or
body semantic law is required by this construction. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareOrdinaryBodySourceLifting
open Core Frontend SourceInference CellAwareOrdinaryBodySourceState

variable {program : Program} {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}

theorem lifts (wellFormed : ProgramWellFormed program)
    {checked : SourceCoreCompatibleCatalog.Checked}
    {layouts owner active frame globals onError values reasonAt context scope mode statements expected type code}
    (tree : CellAwareOrdinaryBodyTree.Tree layouts owner active frame globals onError values invocation.source
      (CellAwareLexicalBodyExpressions.StaticCertificate checked invocation.source reasonAt)
      context scope mode statements expected type code) :
    Lifts (program := program) (registry := registry) (invocation := invocation) context mode statements := by
  induction tree with
  | nil => exact CellAwareOrdinaryBodySourceState.nil
  | returnUnit rest found form => exact returnUnit found form
  | returnValue rest found form expressionFound _ certificate =>
      exact terminal wellFormed (.returning rest (lookupStatement?_sound found) form) certificate expressionFound
  | tail found form expressionFound _ certificate =>
      exact terminal wellFormed (.tail (lookupStatement?_sound found) form) certificate expressionFound
  | uninitialized found form mono extended _ _ _ _ _ _ ih =>
      exact absent found form mono extended ih
  | initialized found form mono extended _ initializerFound sourceType initial _ _ _ _ ih =>
      exact initialized wellFormed found form mono extended initializerFound sourceType initial ih
  | discard found form _ continuing expressionFound certificate _ ih =>
      exact discard wellFormed found form continuing expressionFound certificate ih
  | block found form _ _ inner remaining => exact block found form inner (.inl remaining)
  | ifThen found form conditionFound conditionType certificate _ _ _ thenLift elseLift remaining =>
      apply conditional wellFormed found form conditionFound conditionType certificate
      · intro truth; cases truth <;> assumption
      · exact .inl remaining
  | terminalBlock _ found form _ stops _ inner => exact block found form inner (.inr stops)
  | terminalIf _ found form conditionFound conditionType certificate _ _ thenStops elseStops _ thenLift elseLift =>
      apply conditional wellFormed found form conditionFound conditionType certificate
      · intro truth; cases truth <;> assumption
      · apply Or.inr
        intro truth; cases truth <;> assumption

end Solcore.SourceSemantics.CoreLowering.CellAwareOrdinaryBodySourceLifting
