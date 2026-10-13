import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPositiveFunctionModels
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationIndirectValuesPrefix
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBuiltinParentPreservation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectSecondGateBounds

/-! The constructed successful callee and argument prefix supplies builtin
parent preservation at its actual reached state. The selected physical count
is decided internally. A user callee retains the same full prefix for its
body producer. No complete application or body law is assumed. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationIndirectBuiltinPreservationDispatch
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPreparedStagedIndirectNativePrefix (CalleePost)
open CallableIndexedOwnedPreparedScopedCallBoundaryReceipts (CallView)
open CallableIndexedOwnedContextualCalleeStageReceipts (BoundaryAt)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {functionModel : CallableIndexedOwnedPositiveFunctionModels.Receiving
    headers keys bodyRegistry semanticFaults profile}
  [positive : CallableIndexedOwnedPositiveFunctionModels.ErasesToContextual
    headers keys bodyRegistry semanticFaults profile functionModel]
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry}
  {invocation : Staging.Recursive.Scope}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  (prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler
    compiled.indexed.ancestry.graph.inputs.callable)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  {sourceTypes : List TypeSystem.Ty} {calleeNode : ExpressionNode}
  {sidecar : SourceCoreStageContracts.Sidecar}

local notation "functions" => functionModel
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked
  completion.result.context.registry functions
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
  completion.result.diagnostics


/-- The exact original Source parent and its native result share the actual
reached caller endpoint. The two traces have independent sizes. -/
def ParentAt (sourceSize : Nat) (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap) : Prop :=
  Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages sourceSize
    invocation context environment before id outcome after ∧
  ∃ value finalStore finalMap finalWorld,
    Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
    RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
      compiler.original.type lowered.type callFaults outcome value ∧
    GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
    LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
    AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
    ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
      callerProtocol.Relates initial reached ∧
      CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context
        compiler.original.type outcome reached

variable (sourceParent : CallableIndexedOwnedIndirectSourceAdapters.SourceParent compiler)
  (occurrence : Staging.Recursive.Occurrence invocation id (.call callee ids (.indirect metadata)))
  (preparedStages : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    (functionModel) identities)

include positive sourceParent occurrence preparedStages receiver actualFunctionType observations in
/-- The authentic prefix is classified once. Successful builtin execution
uses its original primitive; physical mismatch uses the actual receiving
arity word. Both branches construct the whole native parent without replay. -/
theorem preserves_builtin_or_user
    {calleeSize argumentsSize applicationSize : Nat}
    {sourceValue : Dynamic.Value} {calleeHeap argumentsHeap after : Dynamic.Heap}
    {sources : List Dynamic.Value} {outcome : Staging.Recursive.Outcome}
    (calleeTrace : Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages calleeSize
      invocation context environment before callee (.value sourceValue) calleeHeap)
    (accepted : Staging.CallBoundary.GuardAccepts invocation.guards id ids sourceValue)
    (argumentsTrace : Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages argumentsSize
      invocation context environment calleeHeap ids (.values sources) argumentsHeap)
    (called : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) stages applicationSize
      invocation context argumentsHeap sourceValue sources outcome after)
    (prefixResult : SelectedCompilationIndirectValuesPrefix.ValuesPrefix (functionModel := functionModel)
      (registry := completion.result.context.registry) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeNode := calleeNode) (sidecar := sidecar)
      bridge profile compiler prepared initial sourceValue calleeHeap argumentsHeap sources) :
    (Staging.CallBoundary.UserCallable sourceValue ∧
      SelectedCompilationIndirectValuesPrefix.ValuesPrefix (functionModel := functionModel)
        (registry := completion.result.context.registry) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
        (context := context) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
        (calleeNode := calleeNode) (sidecar := sidecar)
        bridge profile compiler prepared initial sourceValue calleeHeap argumentsHeap sources) ∨
    ParentAt (functionModel := functionModel) (completion := completion) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (stages := stages) (invocation := invocation) (environment := environment)
      (actual := actual) (ξ := ξ) bridge profile compiler initial
      (Staging.Recursive.Size.stepSize [calleeSize, argumentsSize, applicationSize]) outcome after := by
  have originalPrefix := prefixResult
  obtain ⟨rawParameter, rawResult, functionType, bundle, resultType,
    calleeStore, calleeMap, calleeWorld, carrier, values, argumentsStore, finalMap, finalWorld,
    originalNode, originalMetadata, calleePost, valueTyped, _gate, argumentsNative,
    representedValues, representedCallee, _callView, boundary, finalHeaps, maps, worlds,
    frame, heapMetadata, _argumentsTyped, _argumentMetadata, reached, related, admitted⟩ := prefixResult
  cases boundary with
  | user dispatch selected =>
      exact .inl ⟨(CallableLedger.frame sidecar).userCallable dispatch.bound, originalPrefix⟩
  | builtin receipt =>
      rename_i function row
      by_cases count : row.entry.parameterCount = ids.length
      · rw [functionType] at valueTyped representedCallee
        have completeParent :
            Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages
              (Staging.Recursive.Size.stepSize [calleeSize, argumentsSize, applicationSize])
              invocation context environment before id outcome after ∧
            ∃ value,
              Evaluates actual store (lowered.expression.rename ξ) value argumentsStore ∧
              RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
                compiler.original.type lowered.type callFaults outcome value ∧
              after = argumentsHeap ∧
              GenericHeap.HeapRepresents model finalMap finalWorld argumentsHeap argumentsStore ∧
              LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
              AdministrativePreserved mapping store finalMap argumentsStore ∧
              Dynamic.HeapMetadataExtend before argumentsHeap ∧
              callerProtocol.Relates initial reached ∧
              CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context
                compiler.original.type outcome reached :=
          CallableIndexedOwnedPreparedStagedBuiltinParentPreservation.preserves_parent
            (headers := headers) (keys := keys) (bodyRegistry := bodyRegistry)
            (registry := completion.result.context.registry) (semanticFaults := semanticFaults)
            (profile := profile) (faults := callFaults)
            (context := context) (stages := stages) (invocation := invocation)
            (environment := environment) (actual := actual) (ξ := ξ)
            (mapping := mapping) (finalMap := finalMap) (world := world) (finalWorld := finalWorld)
            (before := before) (calleeHeap := calleeHeap) (argumentsHeap := argumentsHeap)
            (store := store) (argumentsStore := argumentsStore) (canonical := canonical)
            (identities := identities) (function := function) (carrier := carrier) (row := row)
            (sources := sources) (values := values) (sourceTypes := sourceTypes)
            (parameter := rawParameter) (result := rawResult) (sidecar := sidecar)
            (originalNode := originalNode) (originalMetadata := originalMetadata)
            (calleeSize := calleeSize) (argumentsSize := argumentsSize) (applicationSize := applicationSize)
            (outcome := outcome) (after := after) (calleeStore := calleeStore)
            bridge compiler prepared sourceParent occurrence initial reached related admitted
            finalHeaps maps worlds frame heapMetadata observations receipt count actualFunctionType
            valueTyped (representedCallee.map_functions (CallableIndexedOwnedPositiveFunctionModels.ErasesToContextual.erase (headers := headers) (keys := keys) (bodyRegistry := bodyRegistry) (faults := semanticFaults) (profile := profile))) representedValues bundle resultType calleeTrace argumentsTrace
            called calleePost.1 argumentsNative
        obtain ⟨parentSource, value, native, representation, sameHeap, heaps,
          keptMaps, keptWorlds, keptFrame, keptMetadata, keptRelated, post⟩ := completeParent
        cases sameHeap
        exact .inr ⟨parentSource, value, argumentsStore, finalMap, finalWorld,
          native, representation, heaps, keptMaps, keptWorlds, keptFrame, keptMetadata,
          reached, keptRelated, post⟩
      · have valuesCount := CallableIndexedOwnedPreparedSecondCallGateRejection.values_count argumentsTrace
        have physical : function.id.parameterTypes.length ≠ ids.length := by
          simpa only [receipt.parameter_count] using count
        cases called with
        | builtin primitive =>
            have originalCount := Dynamic.BuiltinApplies.argument_count primitive
            exact False.elim (physical (valuesCount.symm.trans originalCount).symm)
        | builtinType arity mismatch =>
            exact False.elim (physical (arity.trans valuesCount))
        | builtinArity mismatch =>
            have argumentsWeaken : Evaluates (.unit :: carrier :: actual) calleeStore
                (((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ).weakenAt 0 |>.weakenAt 0)
                (.inRight .word (DataPatternValues.packValues values)) argumentsStore := by
              simpa only [← GenericExpressionMeaning.rename_prefix, ← GenericExpressionMeaning.rename_prefix]
                using argumentsNative
            have native := CallableIndexedOwnedPreparedSecondCallGateRejection.builtin_native_preserves
              (unknown := compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown)
              (result := compiler.resultType) receipt physical calleePost.1 argumentsWeaken
            change Evaluates actual store
              (CallableContract.call prepared.site.gates
                compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown compiler.resultType
                (compiler.calleeCode.expression.rename ξ)
                ((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ)) _ argumentsStore at native
            rw [← prepared.lowered_rename compiler ξ] at native
            obtain ⟨represented, keptHeaps, keptState, sameState, _keptRelated⟩ :=
              CallableIndexedOwnedPreparedReceivingCallRejectionPosts.receiving_staged_argument_post
                compiler prepared preparedStages receipt.selected receiver initial functions reached related finalHeaps
                (sourceResult := compiler.original.type) (resultCore := lowered.type) count
            cases sameState
            have loweredType : lowered.type = compiler.resultType :=
              (congrArg (fun output => output.type) compiler.output).trans compiler.resultTypeEq.symm
            have faultRep := CallableIndexedOwnedPublicDecodedStagedCallFaults.arity_result model represented
            have post : CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context
                compiler.original.type
                (.fault (.semantic (.argumentArityMismatch function.id.parameterTypes.length sources.length))) reached :=
              ⟨admitted.rows, by intro value impossible; cases impossible⟩
            refine .inr ⟨.applied occurrence compiler.argumentCoercions calleeTrace accepted
              argumentsTrace sourceParent.arity (.builtinArity mismatch),
              .inLeft lowered.type (.word (prepared.site.reasonAt row.caller row.call row.entry.id
                .beforeApplication (.argumentArityMismatch row.entry.parameterCount ids.length))),
              argumentsStore, finalMap, finalWorld, ?_, ?_, keptHeaps, maps, worlds, frame,
              heapMetadata, reached, related, post⟩
            · simpa only [loweredType] using native
            · simpa only [receipt.parameter_count, valuesCount] using faultRep

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationIndirectBuiltinPreservationDispatch
