import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedReceivingCallRejectionDiagnostics
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedScopedCallBoundaryReceipts

/-! The original selected call row represents second-gate rejection against
the actual public receiving table. Original and substituted call metadata stay
distinct. A pure rejection retains the argument computation's exact dependent
caller state, record relation, heap and store. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedReceivingCallRejectionPosts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedIndirectSourceAdapters
open CallableIndexedOwnedSelectedCallCodebookReceipts (Selected)
open CallableIndexedOwnedContextualCalleeStageReceipts (BoundaryAt)
open CallableIndexedOwnedPublicFaultReceiverTables (IssuedAt)
open CallableIndexedOwnedPreparedSecondCallGateRejection (arityFaults stagedArityFaults)

/-- Each actual boundary retains its original generated request. -/
theorem selected_row {sidecar : SourceCoreStageContracts.Sidecar}
    {site : SourceCoreCallableContracts.Callsite} {callee : ExpressionId}
    {ids : List ExpressionId} {originalMetadata : IndirectCallResolution}
    {originalNode : ExpressionNode} {sourceValue : Dynamic.Value} {carrier : Value}
    (boundary : BoundaryAt sidecar site callee ids originalMetadata originalNode sourceValue carrier) :
    ∃ row, Selected sidecar site callee ids originalMetadata originalNode row := by
  cases boundary with
  | user dispatch selected => exact ⟨dispatch.row, selected⟩
  | builtin receipt => exact ⟨_, receipt.selected⟩

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
  {sidecar : SourceCoreStageContracts.Sidecar} {row : SourceCoreStageCodebook.Decision}
  {originalNode : ExpressionNode} {originalMetadata : IndirectCallResolution}
  (selected : Selected sidecar prepared.site callee ids originalMetadata originalNode row)
  {completion : SourceCoreCallableIndexedPrograms.Completion compiled.indexed}
  (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
    completion.result.extension completion.result.diagnostics)

include stages selected receiver in
theorem receiving_argument_post
    {Records : Type} {protocol : ProtectedStateTransition.Protocol Records}
    {initialIndex : ProtectedStateTransition.Index} (initial : protocol.State initialIndex)
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    {canonical : Environment} {sourceResult : TypeSystem.Ty} {resultCore : Ty}
    (functions : FunctionModel compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
    (argumentState : protocol.State ⟨scope, mapping, world, heap, store, canonical⟩)
    (related : protocol.Relates initial argumentState)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked
      completion.result.context.registry functions mapping world heap store)
    (different : row.entry.parameterCount ≠ ids.length) :
    FunctionCalls.ResultRepresents
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked
        completion.result.context.registry functions)
      mapping world sourceResult resultCore (arityFaults completion.result.diagnostics)
      (.fault (.argumentArityMismatch row.entry.parameterCount ids.length))
      (.inLeft resultCore (.word (prepared.site.reasonAt row.caller row.call row.entry.id
        .beforeApplication (.argumentArityMismatch row.entry.parameterCount ids.length)))) ∧
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked
      completion.result.context.registry functions mapping world heap store ∧
    ∃ reached : protocol.State ⟨scope, mapping, world, heap, store, canonical⟩,
      reached = argumentState ∧ protocol.Relates initial reached := by
  obtain ⟨diagnostic, decoded, error⟩ :=
    CallableIndexedOwnedPreparedReceivingCallRejectionDiagnostics.receiving_diagnostic
      compiler prepared stages selected receiver different
  exact ⟨.fault ⟨row.entry.parameterCount, ids.length, diagnostic, rfl, decoded, error⟩,
    heaps, argumentState, rfl, related⟩

include stages selected receiver in
theorem receiving_staged_argument_post
    {Records : Type} {protocol : ProtectedStateTransition.Protocol Records}
    {initialIndex : ProtectedStateTransition.Index} (initial : protocol.State initialIndex)
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    {canonical : Environment} {sourceResult : TypeSystem.Ty} {resultCore : Ty}
    (functions : FunctionModel compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
    (argumentState : protocol.State ⟨scope, mapping, world, heap, store, canonical⟩)
    (related : protocol.Relates initial argumentState)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked
      completion.result.context.registry functions mapping world heap store)
    (different : row.entry.parameterCount ≠ ids.length) :
    RecursiveStageMeaning.ResultRepresentsFor
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked
        completion.result.context.registry functions)
      mapping world sourceResult resultCore (stagedArityFaults completion.result.diagnostics)
      (.fault (.semantic (.argumentArityMismatch row.entry.parameterCount ids.length)))
      (.inLeft resultCore (.word (prepared.site.reasonAt row.caller row.call row.entry.id
        .beforeApplication (.argumentArityMismatch row.entry.parameterCount ids.length)))) ∧
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked
      completion.result.context.registry functions mapping world heap store ∧
    ∃ reached : protocol.State ⟨scope, mapping, world, heap, store, canonical⟩,
      reached = argumentState ∧ protocol.Relates initial reached := by
  obtain ⟨diagnostic, decoded, error⟩ :=
    CallableIndexedOwnedPreparedReceivingCallRejectionDiagnostics.receiving_diagnostic
      compiler prepared stages selected receiver different
  exact ⟨.fault ⟨row.entry.parameterCount, ids.length, diagnostic, rfl, decoded, error⟩,
    heaps, argumentState, rfl, related⟩

end OriginalRow

section ScopedRow
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  (prepared : Prepared compiler compiled.indexed.ancestry.graph.inputs.callable)
  {sidecar : SourceCoreStageContracts.Sidecar}

include compiler prepared in
/-- The actual Source view constructs the original selected row at the same
prepared site; both metadata records remain in the output. -/
theorem row_at_source_view
    (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
    (view : CallableIndexedOwnedContextualDiagnosticSources.SourceView sidecar.source source)
    (unique : NodeOccurrencesUnique sidecar.source)
    {sourceValue : Dynamic.Value} {carrier : Value}
    (actualOrigin : CallableLedger.OriginRep compiled.indexed.base.plan
      compiled.indexed.ancestry.graph.inputs.callable.table sourceValue carrier) :
    ∃ before originalMetadata row, ContainsExpression sidecar.source prepared.site.call before ∧
      before.form = .call callee ids (.indirect originalMetadata) ∧
      CallableIndexedOwnedPreparedScopedCallBoundaryReceipts.CallView
        before compiler.original originalMetadata metadata ∧
      Selected sidecar prepared.site callee ids originalMetadata before row := by
  obtain ⟨before, originalMetadata, contains, form, callView, boundary⟩ :=
    CallableIndexedOwnedPreparedScopedCallBoundaryReceipts.boundary_at_source_view
      compiler prepared caller view unique actualOrigin
  obtain ⟨row, selected⟩ := selected_row boundary
  exact ⟨before, originalMetadata, row, contains, form, callView, selected⟩

end ScopedRow
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedReceivingCallRejectionPosts
