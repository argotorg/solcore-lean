import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectStageBoundary
import Solcore.SourceSemantics.CoreLowering.CallableFaultDiagnosticPreparation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicCallableDiagnostics

/-! Actual public native presence supplies the same sealed callable diagnostic
factory. Only the genuine rejected beforeArguments row is interpreted; its
stage fault remains distinct from plain Dynamic faults. The complete boundary
receipt, callee pool and cumulative effects are retained unchanged. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectStageDiagnostics
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope id callee ids metadata reasonAt lowered)
  {native : SourceCoreGeneralFunctions.CallableContext} (prepared : Prepared compiler native)
  {sidecar : SourceCoreStageContracts.Sidecar} {sourceValue : Dynamic.Value} {calleeNative : Value}
  (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids sourceValue calleeNative)
  {reason : Staging.CallGuard.Fault}
  (rejected : Staging.CallBoundary.GuardRejects (CallableLedger.frame sidecar) prepared.site.call ids sourceValue reason)
  (stages : RecursiveNamedPreparedStageContracts.Prepared compiled native)

private theorem issued_reason {table : SourceCoreStageCodebook.Table}
    {caller : SourceSpecialization.SpecializationKey} {call : ExpressionId}
    {reasonAt : SourceCoreCallableContracts.ReasonAt} {site : SourceCoreCallableContracts.Callsite}
    (issued : SourceCoreCallableContracts.prepareCallsite table caller call reasonAt = .ok site) :
    site.reasonAt = reasonAt := by
  unfold SourceCoreCallableContracts.prepareCallsite at issued
  split at issued
  · cases issued; rfl
  · cases issued

include prepared dispatch in
private theorem actual_member : dispatch.row ∈ native.table.decisions := by
  have member := List.mem_of_find?_eq_some dispatch.found
  change dispatch.row ∈ prepared.site.table.casesAt prepared.site.caller prepared.site.call at member
  have contained := (List.mem_filter.mp member).1
  rwa [prepared.table] at contained

include rejected stages in
/-- The actual public factory decodes the exact rejected first-gate token. -/
theorem stage_diagnostic :
    ∃ diagnostic, native.diagnostics.rootTable.diagnostic? (dispatch.reason reason) = some diagnostic ∧
      diagnostic.error = CallStageGuard.error dispatch.guard.sidecar.caller dispatch.guard.node dispatch.guard.contract.owner reason := by
  obtain ⟨_diagnostics, _cached, _callableCached, generated⟩ :=
    CallableIndexedOwnedPublicCallableDiagnostics.of_compiled compiled stages.present
  have decoded := CallableFaultDiagnosticPreparation.prepared_before_arguments generated
    (actual_member compiler prepared dispatch) (dispatch.rejected rejected)
  simpa only [CallStageBoundary.Dispatch.reason, issued_reason prepared.prepared] using decoded

variable {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {calleeNode : ExpressionNode}
  {firstMap mapping : LocationMap} {firstWorld world : StoreTyping}
  {before calleeHeap : Dynamic.Heap} {firstStore store : Store}
  {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
  (first : callerProtocol.State ⟨scope, firstMap, firstWorld, before, firstStore, canonical⟩)
  {calleeSize : Nat}

include rejected stages in
/-- The entire staged result is retained verbatim beside its real table
observation; no semantic fault representation is invented. -/
theorem decoded_result {token : Word} {finalStore : Store}
    (result : CallableIndexedOwnedStoredIndirectStageBoundary.ResultAt
      (registry := registry) (faults := faults) (context := context) (evidence := evidence)
      (calleeNode := calleeNode) (mapping := mapping) (world := world) (calleeHeap := calleeHeap) (store := store)
      (environment := environment) (actual := actual) (ξ := ξ) (calleeSize := calleeSize)
      bridge profile compiler prepared first dispatch reason token finalStore) :
    CallableIndexedOwnedStoredIndirectStageBoundary.ResultAt
      (registry := registry) (faults := faults) (context := context) (evidence := evidence)
      (calleeNode := calleeNode) (mapping := mapping) (world := world) (calleeHeap := calleeHeap) (store := store)
      (environment := environment) (actual := actual) (ξ := ξ) (calleeSize := calleeSize)
      bridge profile compiler prepared first dispatch reason token finalStore ∧
    ∃ diagnostic, native.diagnostics.rootTable.diagnostic? token = some diagnostic ∧
      diagnostic.error = CallStageGuard.error dispatch.guard.sidecar.caller dispatch.guard.node dispatch.guard.contract.owner reason := by
  obtain ⟨diagnostic, decoded, error⟩ := stage_diagnostic compiler prepared dispatch rejected stages
  exact ⟨result, diagnostic, result.2.2.2.2.2.1.symm ▸ decoded, error⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectStageDiagnostics
