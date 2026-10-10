import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectStageBoundary

/-! Native reflection of a genuinely rejected first gate retains the exact
callee trace and complete receiving function model. The original two-bind
inversion keeps independent strict native child bounds. Its result is the
existing staged boundary outcome with the same callee admission and store. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedFunctionModelStageReflection
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters
open CallableIndexedOwnedStoredIndirectStageBoundary
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functionModel : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope id callee ids metadata reasonAt lowered)
  {native : SourceCoreGeneralFunctions.CallableContext} (prepared : Prepared compiler native)
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {calleeNode : ExpressionNode}
  {firstMap mapping : LocationMap} {firstWorld world : StoreTyping}
  {before calleeHeap : Dynamic.Heap} {firstStore store : Store}
  {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
  (first : callerProtocol.State ⟨scope, firstMap, firstWorld, before, firstStore, canonical⟩)
  {sourceValue : Dynamic.Value} {calleeNative : Value}
  (post : CallableIndexedOwnedStoredFunctionModelReceipts.ValuePost (registry := registry)
    (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context) bridge functionModel compiler first
    sourceValue calleeHeap calleeNative store mapping world)
  {sidecar : SourceCoreStageContracts.Sidecar}
  (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (sidecarSource : sidecar.source = source)
  (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids sourceValue calleeNative)
  {reason : Staging.CallGuard.Fault}
  (rejected : Staging.CallBoundary.GuardRejects (CallableLedger.frame sidecar) prepared.site.call ids sourceValue reason)
  {calleeSize : Nat}
  (calleeTrace : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) calleeSize
    context evidence source environment before callee sourceValue calleeHeap)

include caller sidecarSource post rejected calleeTrace in
/-- One authentic bounded completion uses the original first-gate inversion
and preservation producer at the same full function model. -/
theorem reflects_rejected (budget : Nat) {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual firstStore (lowered.expression.rename ξ) value finalStore)
    (within : size ≤ budget) :
    ∃ token, value = .inLeft compiler.resultType (.word token) ∧
      ForModel.ResultAt (registry := registry) (context := context) (evidence := evidence)
        (calleeNode := calleeNode) (mapping := mapping) (world := world) (calleeHeap := calleeHeap) (store := store)
        (environment := environment) (actual := actual) (ξ := ξ) (calleeSize := calleeSize)
        bridge functionModel compiler prepared first dispatch reason token finalStore ∧
      RejectedCompletion budget prepared.site native.diagnostics.unknown (compiler.calleeCode.expression.rename ξ)
        actual firstStore store calleeNative token := by
  have exactGate := gate_rejected dispatch rejected native.diagnostics.unknown actual store
  have full := completed
  rw [prepared.lowered_rename compiler ξ] at full
  obtain ⟨same, storeEq, bounds⟩ := completed_rejected post.1 exactGate full within
  subst finalStore
  exact ⟨dispatch.reason reason, same,
    ForModel.preserves_rejected bridge functionModel compiler prepared first post caller sidecarSource dispatch rejected calleeTrace,
    bounds⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedFunctionModelStageReflection
