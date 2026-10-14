import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageIndirectPrefixLifting
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageApplicationArity
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageNamedInvocationLifting
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedArgumentRows
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalProgramSupport

/-! The positive named payload selects the same actual cache entry, complete
source dictionary and captured physical frame at the reached argument heap. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2200000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageIndirectNamedLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPreparedStagedSelectedGeneralCallHeadBounds (Port)
open SelectedCompilationPhysicalProgramSupport (Support stages functions stagePrepared)
open SelectedCompilationStageBodyLiftBounds (NamedLiftsBelow)
open Staging.Recursive.Lifting (ApplicationLift)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {receiver : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (support : Support compiled headers keys receiver)
  {registry : SourceCoreRawMetadata.Registry}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (physical : ∀ {index}, callerProtocol.State index → CallableIndexedOwnedPhysicalGlobals.Authority compiled index.mapping index.store)
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation invocation.source scope
    id callee ids metadata reasonAt lowered)
  (port : Port (compiled := compiled) (invocation := invocation) compiler)
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
  (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
  {sourceTypes : List TypeSystem.Ty}
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (functions support)

include support physical runtime actualFunctionType in
theorem named_application (budget : Nat)
    (bodies : ∀ header, header ∈ headers → ∀ child,
      (stages compiled).Closure header.function child →
      NamedLiftsBelow (headers := headers) (keys := keys) header model (stages compiled) child budget)
    {function : Dynamic.GlobalFunction} {calleeHeap argumentsHeap after : Dynamic.Heap}
    {sources : List Dynamic.Value} {size argumentsSize : Nat} {callEvidence : Dynamic.EvidenceEnvironment}
    {outcome : Dynamic.ExpressionOutcome}
    (argumentsTrace : Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) (stages compiled)
      argumentsSize invocation context environment calleeHeap ids (.values sources) argumentsHeap)
    (prefixResult : SelectedCompilationIndirectValuesPrefix.ValuesPrefix
      (functionModel := functions support) (registry := registry)
      (bodyRegistry := receiver.result.context.registry)
      (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.result.diagnostics)
      (context := context) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeNode := port.calleeNode) (sidecar := port.sidecar)
      bridge support.profile compiler port.prepared initial (.global function) calleeHeap argumentsHeap sources)
    (called : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) size
      context invocation.evidence callEvidence argumentsHeap (.global function) sources outcome after)
    (within : size ≤ budget) :
    ApplicationLift (Program.ofChecked compiled.sourceProgram) (stages compiled) invocation context argumentsHeap
      (.global function) sources outcome after := by
  obtain ⟨parameter, result, functionType, bundle, _originalResult,
    _calleeStore, _calleeMap, _calleeWorld, carrier, values, _argumentsStore, finalMap, finalWorld,
    _originalNode, _originalMetadata, _calleePost, calleeTyped, _firstGate, _argumentsNative,
    represented, calleePayload, _callView, boundary, heaps, _maps, _worlds,
    _frame, _heapMetadata, argumentsTyped, argumentMetadata, reached, _related, admitted⟩ := prefixResult
  obtain ⟨rawType, ⟨association⟩, _nativeType⟩ :=
    CallableIndexedOwnedPhysicalCellOrigins.PayloadOrigins.named_member support.profile calleePayload function rfl
  let header := association.header
  let packet := support.bodies header association.member
  have certified := support.certificates header association.member
  by_cases arity : header.function.parameters.length = sources.length
  · have rawCallee : Dynamic.ValueHasType context calleeHeap (.global function) (.function parameter result) := by
      simpa only [functionType] using calleeTyped
    have certifiedAt := SelectedCompilationNamedArgumentRows.certified_at association.sourceAt support.bodyTyping
      packet.prepared packet.aligned
    cases boundary with
    | user dispatch selected =>
      have count : dispatch.row.entry.parameterCount = ids.length :=
        (CallableIndexedOwnedNamedPhysicalArityReceipts.named_parameter_count association.sourceAt
          port.caller dispatch selected).trans (arity.trans argumentsTrace.sound.length.symm)
      have secondAccepted : CallableContract.decision port.prepared.site.gates .beforeApplication
          compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown dispatch.contract = none := by
        rw [port.prepared.site.decision_known .beforeApplication
          compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown dispatch.contract dispatch.row dispatch.found]
        exact SourceCoreCallableContracts.reason_accepted dispatch.row port.prepared.site.reasonAt .beforeApplication
          (dispatch.row.afterArguments_ok (count.trans selected.argument_count.symm))
      obtain ⟨parameters, physicalArity, _result⟩ := SelectedCompilationNamedArgumentRows.accepted_rows
        association.sourceAt compiler certifiedAt actualFunctionType port.caller dispatch selected secondAccepted
        rawCallee association.type_eq represented bundle
      obtain ⟨headerHeap, headerArguments, _supports⟩ := SelectedCompilationNamedArgumentRows.arguments_at
        association.sourceAt certifiedAt certified runtime admitted.heap argumentsTyped
        (rawCallee.mono argumentMetadata) bundle physicalArity
      obtain ⟨⟨capture, _sameCapture⟩⟩ := association.at_store packet.prepared packet.aligned
        (support.owners association.owner) (physical reached)
      obtain ⟨sidecar, _prepared, _same, selectedScope, _declaration, _local, _evidence, _marker, _analysis⟩ :=
        CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts.selected association.sourceAt packet.prepared packet.aligned
          (stagePrepared compiled) association.descriptor
      rw [CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts.global_view association.sourceAt] at selectedScope
      exact SelectedCompilationStageNamedInvocationLifting.lifts_invocation (functions support) association.owner
        (bridge.pool reached) header capture association.sourceAt packet.layouts (physical reached) association.member
        support.bodyTyping.function_ids certified admitted.rows headerHeap headerArguments parameters heaps selectedScope
        budget (bodies header association.member _ selectedScope)
        (SelectedCompilationStageIndirectSourceTrace.call_with_global_evidence called) within
  · exact SelectedCompilationStageApplicationArity.global_mismatch support.bodyTyping.function_ids
      association.sourceAt.frame arity called

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageIndirectNamedLifting
