import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedReceivingCallRejectionDiagnostics
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedScopedCallBoundaryReceipts

/-! A rejected first guard keeps its actual failing invocation and original
selected call row. The sealed before-arguments diagnostic reaches the literal
receiving table through its real rebuild and callable append. Its stage tag,
Source view, guard frame and callee endpoint remain attached to that lookup. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedReceivingFirstCallGateRejection
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedIndirectSourceAdapters
open CallableIndexedOwnedSelectedCallCodebookReceipts (Selected)
open CallableIndexedOwnedPreparedScopedCallBoundaryReceipts (CallView)
open CallableIndexedOwnedContextualDiagnosticSources (SourceView)
open CallableIndexedOwnedPublicFaultReceiverTables (IssuedAt)

/-- The view retains the actual failing scope and the forward relation to the
original row. A raw diagnostic alone cannot supply those Source coordinates. -/
inductive StageErrorView : Staging.Recursive.Scope → ExpressionId → Staging.CallGuard.Fault →
    SourceTypedRuntime.RuntimeError → Prop where
  | selected {invocation : Staging.Recursive.Scope} {sidecar : SourceCoreStageContracts.Sidecar}
      {site : SourceCoreCallableContracts.Callsite} {callee : ExpressionId} {ids : List ExpressionId}
      {originalNode actualNode : ExpressionNode} {originalMetadata metadata : IndirectCallResolution}
      {sourceValue : Dynamic.Value} {carrier : Value} {reason : Staging.CallGuard.Fault}
      (sourceView : SourceView sidecar.source invocation.source)
      (actualContains : ContainsExpression invocation.source site.call actualNode)
      (actualForm : actualNode.form = .call callee ids (.indirect metadata))
      (callView : CallView originalNode actualNode originalMetadata metadata)
      (guardFrame : invocation.guards = CallableLedger.frame sidecar)
      (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar)
        site site.call ids sourceValue carrier)
      (selected : Selected sidecar site callee ids originalMetadata originalNode dispatch.row)
      (rejected : Staging.CallBoundary.GuardRejects invocation.guards site.call ids sourceValue reason) :
      StageErrorView invocation site.call reason
        (CallStageGuard.error dispatch.guard.sidecar.caller dispatch.guard.node
          dispatch.guard.contract.owner reason)

/-- This first-gate relation keeps the complete stage failure. In particular,
the guard's arity fault still has its stage tag even when its raw error uses the
same count category as the semantic second-gate rejection. -/
def stagedFaults (table : SourceCoreFaultSites.Table) : RecursiveStageMeaning.FaultRep :=
  fun failure token => match failure with
    | .semantic _ => False
    | .stage invocation call reason => ∃ diagnostic,
        table.diagnostic? token = some diagnostic ∧ StageErrorView invocation call reason diagnostic.error

section OriginalRow
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  {native : SourceCoreGeneralFunctions.CallableContext}
  (prepared : Prepared compiler native)
  (stages : RecursiveNamedPreparedStageContracts.Prepared compiled native)
  {sidecar : SourceCoreStageContracts.Sidecar} {sourceValue : Dynamic.Value} {carrier : Value}
  (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar)
    prepared.site prepared.site.call ids sourceValue carrier)
  {originalNode : ExpressionNode} {originalMetadata : IndirectCallResolution}
  (selected : Selected sidecar prepared.site callee ids originalMetadata originalNode dispatch.row)
  {reason : Staging.CallGuard.Fault}

private theorem issued_reason {table : SourceCoreStageCodebook.Table}
    {caller : SourceSpecialization.SpecializationKey} {call : ExpressionId}
    {actualReason : SourceCoreCallableContracts.ReasonAt} {site : SourceCoreCallableContracts.Callsite}
    (issued : SourceCoreCallableContracts.prepareCallsite table caller call actualReason = .ok site) :
    site.reasonAt = actualReason := by
  unfold SourceCoreCallableContracts.prepareCallsite at issued
  split at issued
  · cases issued; rfl
  · cases issued

include stages selected in
/-- The original selected row and authentic rejection supply the sealed
before-arguments diagnostic at this exact prepared site. -/
theorem original_diagnostic
    (rejected : Staging.CallBoundary.GuardRejects (CallableLedger.frame sidecar)
      prepared.site.call ids sourceValue reason) :
    ∃ diagnostic, native.diagnostics.rootTable.diagnostic? (dispatch.reason reason) = some diagnostic ∧
      diagnostic.error = CallStageGuard.error dispatch.guard.sidecar.caller dispatch.guard.node
        dispatch.guard.contract.owner reason := by
  have member := List.mem_of_find?_eq_some selected.found
  change dispatch.row ∈ prepared.site.table.casesAt prepared.site.caller prepared.site.call at member
  have contained := (List.mem_filter.mp member).1
  rw [prepared.table] at contained
  obtain ⟨_issuer, _present, _callablePresent, allocated⟩ :=
    CallableIndexedOwnedPublicCallableDiagnostics.of_compiled compiled stages.present
  have decoded := CallableFaultDiagnosticPreparation.prepared_before_arguments allocated contained
    (dispatch.rejected rejected)
  simpa only [CallStageBoundary.Dispatch.reason, issued_reason prepared.prepared] using decoded

include stages selected in
/-- The same first-gate word is decoded in the actual public receiving table. -/
theorem receiving_diagnostic
    {completion : SourceCoreCallableIndexedPrograms.Completion compiled.indexed}
    (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
      completion.result.extension completion.result.diagnostics)
    (rejected : Staging.CallBoundary.GuardRejects (CallableLedger.frame sidecar)
      prepared.site.call ids sourceValue reason) :
    ∃ diagnostic, completion.result.diagnostics.diagnostic? (dispatch.reason reason) = some diagnostic ∧
      diagnostic.error = CallStageGuard.error dispatch.guard.sidecar.caller dispatch.guard.node
        dispatch.guard.contract.owner reason := by
  obtain ⟨diagnostic, decoded, error⟩ :=
    original_diagnostic compiler prepared stages dispatch selected rejected
  obtain ⟨_issued, _present, _callablePresent, allocated⟩ :=
    CallableIndexedOwnedPublicCallableDiagnostics.of_compiled compiled stages.present
  have high := CallableIndexedOwnedPreparedReceivingCallRejectionDiagnostics.reason_at_lower_bound
    (CallableFaultDiagnosticPreparation.prepare_receipt allocated)
    dispatch.row.caller dispatch.row.call dispatch.row.entry.id .beforeArguments
    (CallStageGuard.error dispatch.guard.sidecar.caller dispatch.guard.node dispatch.guard.contract.owner reason)
  rw [← issued_reason prepared.prepared] at high
  exact ⟨diagnostic,
    CallableIndexedOwnedPreparedReceivingCallRejectionDiagnostics.receiver_lookup
      compiled stages receiver high decoded, error⟩

include stages selected in
/-- The actual invocation and its reached callee state remain unchanged while
the original first-gate diagnostic is observed in the receiving table. -/
theorem receiving_staged_post
    {completion : SourceCoreCallableIndexedPrograms.Completion compiled.indexed}
    (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
      completion.result.extension completion.result.diagnostics)
    {invocation : Staging.Recursive.Scope}
    (sourceEq : invocation.source = source)
    (view : SourceView sidecar.source source)
    (callView : CallView originalNode compiler.original originalMetadata metadata)
    (guardFrame : invocation.guards = CallableLedger.frame sidecar)
    (rejected : Staging.CallBoundary.GuardRejects invocation.guards prepared.site.call ids sourceValue reason)
    {Records : Type} {protocol : ProtectedStateTransition.Protocol Records}
    {initialIndex : ProtectedStateTransition.Index} (initial : protocol.State initialIndex)
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    {canonical : Environment} {sourceResult : TypeSystem.Ty} {resultCore : Ty}
    (functions : FunctionModel compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
    (calleeState : protocol.State ⟨scope, mapping, world, heap, store, canonical⟩)
    (related : protocol.Relates initial calleeState)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked
      completion.result.context.registry functions mapping world heap store) :
    RecursiveStageMeaning.ResultRepresentsFor
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked
        completion.result.context.registry functions)
      mapping world sourceResult resultCore (stagedFaults completion.result.diagnostics)
      (.fault (.stage invocation prepared.site.call reason))
      (.inLeft resultCore (.word (dispatch.reason reason))) ∧
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked
      completion.result.context.registry functions mapping world heap store ∧
    ∃ reached : protocol.State ⟨scope, mapping, world, heap, store, canonical⟩,
      reached = calleeState ∧ protocol.Relates initial reached := by
  have actualRejected : Staging.CallBoundary.GuardRejects (CallableLedger.frame sidecar)
      prepared.site.call ids sourceValue reason := by
    rw [← guardFrame]
    exact rejected
  obtain ⟨diagnostic, decoded, error⟩ :=
    receiving_diagnostic compiler prepared stages dispatch selected receiver actualRejected
  have scopeView : SourceView sidecar.source invocation.source := by
    rw [sourceEq]
    exact view
  have actualContains : ContainsExpression invocation.source prepared.site.call compiler.original := by
    rw [sourceEq, prepared.call]
    exact lookupExpression?_sound compiler.found
  have errorView : StageErrorView invocation prepared.site.call reason diagnostic.error := by
    rw [error]
    exact .selected scopeView actualContains compiler.originalForm callView guardFrame dispatch selected rejected
  exact ⟨.fault ⟨diagnostic, decoded, errorView⟩, heaps, calleeState, rfl, related⟩

end OriginalRow
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedReceivingFirstCallGateRejection
