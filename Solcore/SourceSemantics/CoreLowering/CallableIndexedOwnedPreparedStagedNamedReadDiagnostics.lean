import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicDiagnosticReceipts
import Solcore.SourceSemantics.CoreLowering.CompatiblePublicContextualDiagnosticObservations
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionContextualReads
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicDecodedStagedCallFaults

/-! The actual prepared named compiler and its receiving diagnostic table
supply fault interpretation only for certified local reads. The same read
certificate selects the original binder, occurrence and span. No blanket
interpretation for unrelated expressions or Source execution is assumed. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedReadDiagnostics
open Core Frontend SourceInference GeneralHeap CompatiblePayload
open CallableIndexedOwnedPublicFaultReceiverTables

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {row : SourceSpecialization.SpecializedFunction}
  (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
  (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared)
  {instantiation : DeclarationInstantiation}
  {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
    completion.result.extension completion.result.diagnostics)

include diagnostic aligned receiver in
/-- The complete issuer and exact receiver construct the diagnostic for this
accepted read. Its lexical Source binder and span come from the certificate. -/
theorem decoded_read {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {reason : Word} {code : Expr}
    (certificate : CompatibleExpressionReads.Certificate fuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      header.function.source scope id reason code)
    (token : reason = header.reasonAt id) :
    completion.result.diagnostics.diagnostic? reason = some {
      error := .uninitializedLocal certificate.binder
      site := .occurrence id.occurrence
      span := some certificate.node.span } := by
  obtain ⟨issued, present, lowered⟩ := diagnostic.actual
  have source : header.function.source = prepared.named.specialized.function.typedBody := by
    rw [aligned.function]
    rfl
  have unique : NodeOccurrencesUnique prepared.named.specialized.function.typedBody :=
    source ▸ header.unique
  have contains : ContainsExpression prepared.named.specialized.function.typedBody id certificate.node :=
    source ▸ lookupExpression?_sound certificate.metadata.found
  have sameBase : prepared.diagnostics.base = issued.program.base := by
    rw [lowered]
    cases compiled.indexed.base.callableContext <;> rfl
  have ownFound := prepared.compilation.diagnostic
  rw [sameBase] at ownFound
  have reasonEq : header.reasonAt id = issued.program.reasonAt prepared.named.signature.key id := by
    rw [aligned.reasonAt, lowered]
    cases compiled.indexed.base.callableContext <;> rfl
  obtain ⟨read, _expression, _binder, _span, readToken, _member, decoded⟩ :=
    CompatiblePublicContextualDiagnosticObservations.receiver_local_read_diagnostic
      compiled receiver present
      (CallableIndexedActualNamedSourceReceipts.cached_record compiled prepared.selected prepared.compilation.hook)
      unique contains certificate.form ownFound
  simpa only [← readToken, ← reasonEq, ← token] using decoded

include diagnostic aligned receiver in
/-- A certified read receives the concrete semantic fault interpretation.
The original Source fault retains its location in its independent trace. -/
theorem uninitialized {fuel : Nat} {context : SourceSemantics.Context}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : CompatibleExpressionReads.LoweredRead fuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      header.function.source context header.reasonAt scope id lowered)
    (location : Dynamic.Location) :
    CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics
      (.uninitializedLocation location) (header.reasonAt id) := by
  obtain ⟨certificate, _type, _binding⟩ := receipt
  apply CallableIndexedOwnedPublicDecodedCallFaults.of_assignment
  exact CallableIndexedOwnedPublicDecodedAssignmentFaults.of_decoded
    (decoded_read prepared diagnostic aligned receiver certificate rfl)
    (.readUninitialized location certificate.binder)

include diagnostic aligned receiver in
/-- The same concrete diagnostic keeps the semantic tag in recursive staging. -/
theorem staged_uninitialized {fuel : Nat} {context : SourceSemantics.Context}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : CompatibleExpressionReads.LoweredRead fuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      header.function.source context header.reasonAt scope id lowered)
    (location : Dynamic.Location) :
    CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics
      (.semantic (.uninitializedLocation location)) (header.reasonAt id) :=
  CallableIndexedOwnedPublicDecodedStagedCallFaults.of_semantic
    (uninitialized prepared diagnostic aligned receiver receipt location)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedReadDiagnostics
