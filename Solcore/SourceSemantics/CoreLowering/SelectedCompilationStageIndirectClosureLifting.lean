import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageIndirectPrefixLifting
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageApplicationArity
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosurePacketLifting
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalClosureArgumentRows
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedArgumentRows
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalProgramSupport

/-! Positive closure payloads retain their actual selected body packet and
captures. Raw argument rows and the physical count are derived independently. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2200000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageIndirectClosureLifting
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
theorem closure_application (budget : Nat)
    (bodies : ∀ {mapping world function native bindings parameterCore resultCore}
      (association : CallableIndexedOwnedPreparedPhysicalClosureAssociation.Association headers keys
        receiver.result.context.registry
        (CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.result.diagnostics)
        mapping world function native bindings parameterCore resultCore),
      SelectedCompilationStageClosurePacketLifting.BelowFor model (stages compiled)
        association (support.closurePackets association) budget)
    {function : Dynamic.Closure} {calleeHeap argumentsHeap after : Dynamic.Heap}
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
      bridge support.profile compiler port.prepared initial (.closure function) calleeHeap argumentsHeap sources)
    (called : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) size
      context invocation.evidence callEvidence argumentsHeap (.closure function) sources outcome after)
    (within : size ≤ budget) :
    ApplicationLift (Program.ofChecked compiled.sourceProgram) (stages compiled) invocation context argumentsHeap
      (.closure function) sources outcome after := by
  by_cases arity : function.parameters.length = sources.length
  · obtain ⟨parameter, result, functionType, bundle, _originalResult,
      _calleeStore, _calleeMap, _calleeWorld, carrier, values, _argumentsStore, finalMap, finalWorld,
      _originalNode, _originalMetadata, _calleePost, calleeTyped, _firstGate, _argumentsNative,
      represented, calleePayload, _callView, boundary, heaps, _maps, _worlds,
      _frame, _heapMetadata, argumentsTyped, argumentMetadata, reached, _related, admitted⟩ := prefixResult
    have rawCallee : Dynamic.ValueHasType context calleeHeap (.closure function) (.function parameter result) := by
      simpa only [functionType] using calleeTyped
    have relatedCallee : CallableIndexedOwnedPreparedPhysicalCellOrigins.PayloadOrigins
        headers keys receiver.result.context.registry registry
        (CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.result.diagnostics)
        support.profile finalMap finalWorld (.function parameter result) (.closure function)
        carrier compiler.calleeCode.type := by
      change GenericHeap.PayloadModel.Represents model finalMap finalWorld
        (.function parameter result) (.closure function) carrier compiler.calleeCode.type
      simpa only [functionType] using calleePayload
    cases boundary with
    | user dispatch selected =>
      have count : dispatch.row.entry.parameterCount = ids.length :=
        (CallableIndexedOwnedStoredClosureArityBoundary.parameter_count dispatch selected).trans
          (arity.trans argumentsTrace.sound.length.symm)
      obtain ⟨raw, _valid, bindings, parameterCore, resultCore, member, _parameterEq, _resultEq, parameters⟩ :=
        SelectedCompilationPhysicalClosureArgumentRows.at_arguments bridge support.profile compiler reached dispatch
          selected count runtime argumentsTyped argumentMetadata rawCallee bundle admitted
          actualFunctionType relatedCallee represented argumentsTrace
      obtain ⟨association⟩ := member
      exact SelectedCompilationStageClosurePacketLifting.application_lifts support.profile association
        (support.closurePackets association) (support.closureSupport association) (bridge.pool reached)
        raw parameters heaps (physical reached) admitted.rows budget (bodies association) called within
  · exact SelectedCompilationStageApplicationArity.closure_mismatch arity called

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageIndirectClosureLifting
