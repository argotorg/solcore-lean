import Solcore.SourceSemantics.CoreLowering.CellAwareNamedDiagnosticIssuer
import Solcore.SourceSemantics.CoreLowering.CompatiblePublicContextualDiagnosticObservations
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionContextualReads
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicDecodedCallFaults

/-! Every ordinary read in the mixed named body uses its original issued
occurrence and token at the current public receiver. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareNamedReadDiagnostics
open Core Frontend SourceInference GeneralHeap CompatiblePayload

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {named : SourceCoreGeneralFunctions.Function}
  {reasonAt : ExpressionId → Word}
  (issuer : CellAwareNamedDiagnosticIssuer.Named compiled.indexed named reasonAt)
  (record : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan named.signature.key = .ok named.specialized)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)
  {invocation : Staging.Recursive.Scope}
  (sourceEq : invocation.source = CallableIndexedNamedGeneration.source named)
  (unique : NodeOccurrencesUnique invocation.source)

include issuer record receiver sourceEq unique in
/-- The actual read certificate fixes the binder; the selected compiler row
and retained issuer fix the diagnostic, including its original source span. -/
theorem uninitialized {fuel : Nat} {context : SourceSemantics.Context}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : CompatibleExpressionReads.LoweredRead fuel (.initial compiled.compatible.checked)
      invocation.source context reasonAt scope id lowered) (location : Dynamic.Location) :
    CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics
      (.uninitializedLocation location) (reasonAt id) := by
  obtain ⟨certificate, _type, _binding⟩ := receipt
  obtain ⟨issued, present, callback, own, ownFound⟩ := issuer
  have originalSource : invocation.source = named.specialized.function.typedBody := sourceEq
  have contains : ContainsExpression named.specialized.function.typedBody id certificate.node :=
    by simpa only [originalSource] using lookupExpression?_sound certificate.metadata.found
  have originalUnique : NodeOccurrencesUnique named.specialized.function.typedBody := by simpa only [originalSource] using unique
  obtain ⟨read, _expression, _binder, _span, token, _member, decoded⟩ :=
    CompatiblePublicContextualDiagnosticObservations.receiver_local_read_diagnostic compiled receiver present
      record originalUnique contains certificate.form ownFound
  apply CallableIndexedOwnedPublicDecodedCallFaults.of_assignment
  exact CallableIndexedOwnedPublicDecodedAssignmentFaults.of_decoded
    (by simpa only [callback, token] using decoded) (.readUninitialized location certificate.binder)

end Solcore.SourceSemantics.CoreLowering.CellAwareNamedReadDiagnostics
