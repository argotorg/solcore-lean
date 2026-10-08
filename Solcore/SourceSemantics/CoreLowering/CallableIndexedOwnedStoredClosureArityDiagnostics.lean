import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredClosureArityBoundary
import Solcore.SourceSemantics.CoreLowering.CallableFaultDiagnosticPreparation

/-! The actual callable diagnostic factory interprets only the new arity
alternative at its exact beforeApplication token. An earlier argument fault
retains its original FaultRep. Every runtime state and effect remains the
frozen arity boundary's same result; no universal semantic decoder is assumed. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredClosureArityDiagnostics
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope id callee ids metadata reasonAt lowered)
  {native : SourceCoreGeneralFunctions.CallableContext} (prepared : Prepared compiler native)
  {sidecar : SourceCoreStageContracts.Sidecar} {function : Dynamic.Closure} {calleeNative : Value}
  (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids (.closure function) calleeNative)
  (selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar prepared.site callee ids metadata compiler.original dispatch.row)
  (different : function.parameters.length ≠ ids.length)
  {base : SourceCoreFaultSites.Table} {minimum : Nat}
  (diagnosticsPrepared : SourceCoreCallableFaultSites.prepare compiled.indexed.base.plan native.table base minimum = .ok native.diagnostics)

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

include selected different diagnosticsPrepared in
/-- The exact selected arity error decodes through its own real prepared table. -/
theorem arity_diagnostic :
    ∃ diagnostic,
      native.diagnostics.rootTable.diagnostic?
        (prepared.site.reasonAt dispatch.row.caller dispatch.row.call dispatch.row.entry.id .beforeApplication
          (.argumentArityMismatch function.parameters.length ids.length)) = some diagnostic ∧
      diagnostic.error = .argumentArityMismatch function.parameters.length ids.length := by
  have found := CallableFaultDiagnosticPreparation.prepared_after_arguments diagnosticsPrepared
    (actual_member compiler prepared dispatch)
    (CallableIndexedOwnedStoredClosureArityBoundary.rejected_row dispatch selected different)
  rw [issued_reason prepared.prepared]
  exact found

include selected different diagnosticsPrepared in
/-- Only the arity alternative adds a real table observation. Earlier child
fault representation is retained without an invented table law. -/
theorem decoded_fault {reason : Dynamic.SemanticFault} {token : Word}
    (observed : CallableIndexedOwnedStoredClosureArityBoundary.FaultToken (faults := faults) compiler prepared dispatch reason token) :
    faults reason token ∨ ∃ diagnostic,
      reason = .argumentArityMismatch function.parameters.length ids.length ∧
      native.diagnostics.rootTable.diagnostic? token = some diagnostic ∧
      diagnostic.error = .argumentArityMismatch function.parameters.length ids.length := by
  rcases observed with earlier | ⟨reasonEq, tokenEq⟩
  · exact Or.inl earlier
  · obtain ⟨diagnostic, found, error⟩ := arity_diagnostic compiler prepared dispatch selected different diagnosticsPrepared
    exact Or.inr ⟨diagnostic, reasonEq, tokenEq.symm ▸ found, error⟩

variable {context : SourceSemantics.Context}
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store} {canonical : Environment}
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)

include selected different diagnosticsPrepared in
/-- The complete runtime receipt is retained verbatim beside the actual table
observation. The returned pool and all cumulative effects remain identical. -/
theorem decoded_result {reason : Dynamic.SemanticFault} {after : Dynamic.Heap} {token : Word} {finalStore : Store}
    {finalMap : LocationMap} {finalWorld : StoreTyping}
    (result : CallableIndexedOwnedStoredClosureArityBoundary.ResultAt (registry := registry) (faults := faults)
      (context := context) bridge profile compiler prepared initial dispatch reason after token finalStore finalMap finalWorld) :
    CallableIndexedOwnedStoredClosureArityBoundary.ResultAt (registry := registry) (faults := faults)
      (context := context) bridge profile compiler prepared initial dispatch reason after token finalStore finalMap finalWorld ∧
    (faults reason token ∨ ∃ diagnostic,
      reason = .argumentArityMismatch function.parameters.length ids.length ∧
      native.diagnostics.rootTable.diagnostic? token = some diagnostic ∧
      diagnostic.error = .argumentArityMismatch function.parameters.length ids.length) :=
  ⟨result, decoded_fault compiler prepared dispatch selected different diagnosticsPrepared result.1⟩
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredClosureArityDiagnostics
