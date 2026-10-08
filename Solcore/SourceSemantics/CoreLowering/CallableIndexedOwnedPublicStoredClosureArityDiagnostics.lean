import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredClosureArityDiagnostics
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicCallableDiagnostics

/-! Actual public native presence retains the original callable diagnostic
factory internally. The selected row, physical mismatch and same runtime result
remain authentic receipts; no decoder or factory acceptance is an external law. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicStoredClosureArityDiagnostics
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
  (stages : RecursiveNamedPreparedStageContracts.Prepared compiled native)

include selected different stages in
/-- The public sealed compiler provides the same actual callable diagnostic factory. -/
theorem arity_diagnostic :
    ∃ diagnostic,
      native.diagnostics.rootTable.diagnostic?
        (prepared.site.reasonAt dispatch.row.caller dispatch.row.call dispatch.row.entry.id .beforeApplication
          (.argumentArityMismatch function.parameters.length ids.length)) = some diagnostic ∧
      diagnostic.error = .argumentArityMismatch function.parameters.length ids.length := by
  obtain ⟨_diagnostics, _cached, _callableCached, generated⟩ :=
    CallableIndexedOwnedPublicCallableDiagnostics.of_compiled compiled stages.present
  exact CallableIndexedOwnedStoredClosureArityDiagnostics.arity_diagnostic compiler prepared dispatch selected different generated

variable {context : SourceSemantics.Context}
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store} {canonical : Environment}
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)

include selected different stages in
/-- Public diagnostic provenance adds the exact table observation beside the
unchanged complete runtime result, including its real reached pool and effects. -/
theorem decoded_result {reason : Dynamic.SemanticFault} {after : Dynamic.Heap} {token : Word} {finalStore : Store}
    {finalMap : LocationMap} {finalWorld : StoreTyping}
    (result : CallableIndexedOwnedStoredClosureArityBoundary.ResultAt (registry := registry) (faults := faults)
      (context := context) bridge profile compiler prepared initial dispatch reason after token finalStore finalMap finalWorld) :
    CallableIndexedOwnedStoredClosureArityBoundary.ResultAt (registry := registry) (faults := faults)
      (context := context) bridge profile compiler prepared initial dispatch reason after token finalStore finalMap finalWorld ∧
    (faults reason token ∨ ∃ diagnostic,
      reason = .argumentArityMismatch function.parameters.length ids.length ∧
      native.diagnostics.rootTable.diagnostic? token = some diagnostic ∧
      diagnostic.error = .argumentArityMismatch function.parameters.length ids.length) := by
  obtain ⟨_diagnostics, _cached, _callableCached, generated⟩ :=
    CallableIndexedOwnedPublicCallableDiagnostics.of_compiled compiled stages.present
  exact CallableIndexedOwnedStoredClosureArityDiagnostics.decoded_result bridge profile compiler prepared dispatch selected
    different generated initial result

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicStoredClosureArityDiagnostics
