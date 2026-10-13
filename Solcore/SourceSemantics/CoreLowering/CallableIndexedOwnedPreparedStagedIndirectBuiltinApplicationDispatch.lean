import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPositiveFunctionModels
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectRetainedCalleeArgumentPrefix
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBuiltinParentBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectSecondGateBounds

/-! The actual retained argument prefix classifies its selected payload once.
Builtin physical mismatch produces the receiving semantic arity post; equal
count uses the original primitive at the same argument endpoint. A user
payload keeps its authentic callee, ordered arguments and application suffix.
The strict prefix producer remains responsible for constructing this input. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectBuiltinApplicationDispatch
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

/-- The user predicate concerns the same retained callee and suffix witness.
Its body, global provenance and physical-count decision remain future work. -/
def UserApplicationPrefix (budget : Nat) (value : Value) (finalStore : Store) : Prop :=
  ∃ sourceValue, Staging.CallBoundary.UserCallable sourceValue ∧
  ∃ rawParameter rawResult,
    calleeNode.type = .function rawParameter rawResult ∧
    TypeSystem.Ty.productMany sourceTypes = rawParameter ∧ compiler.original.type = rawResult ∧
  ∃ calleeSize argumentsSize calleeHeap calleeStore calleeMap calleeWorld sources values carrier
      argumentsHeap argumentsStore finalMap finalWorld originalNode originalMetadata,
    CalleePost (registry := completion.result.context.registry) (context := context)
      (actual := actual) (ξ := ξ) (calleeNode := calleeNode)
      bridge functions compiler initial sourceValue calleeHeap carrier calleeStore calleeMap calleeWorld ∧
    Dynamic.ValueHasType context calleeHeap sourceValue calleeNode.type ∧
    Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages calleeSize
      invocation context environment before callee (.value sourceValue) calleeHeap ∧
    Staging.CallBoundary.GuardAccepts invocation.guards id ids sourceValue ∧
    Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages argumentsSize
      invocation context environment calleeHeap ids (.values sources) argumentsHeap ∧
    DataExpressionSequence.Values model finalMap finalWorld sourceTypes (compiler.codes.map (·.type)) sources values ∧
    GenericHeap.PayloadModel.Represents model finalMap finalWorld calleeNode.type
      sourceValue carrier compiler.calleeCode.type ∧
    CallView originalNode compiler.original originalMetadata metadata ∧
    BoundaryAt sidecar prepared.site callee ids originalMetadata originalNode sourceValue carrier ∧
    GenericHeap.HeapRepresents model finalMap finalWorld argumentsHeap argumentsStore ∧
    LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
    AdministrativePreserved mapping store finalMap argumentsStore ∧ Dynamic.HeapMetadataExtend before argumentsHeap ∧
    (∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, argumentsHeap, argumentsStore, canonical⟩,
      callerProtocol.Relates initial reached ∧ Admission bridge context reached) ∧
    ∃ suffixSize, EvaluationSize suffixSize (DataPatternValues.packValues values :: .unit :: carrier :: actual)
      argumentsStore
      (LanguageResult.bind compiler.resultType
        (CallableContract.dispatch prepared.site.gates .beforeApplication
          compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown (.second (.var 2)))
        (.apply (.second (.first (.var 3))) (.var 1))) value finalStore ∧ suffixSize < budget

omit positive in
/-- Forgetting only the positive user classification keeps the original full
retained callee post and every transient argument effect. -/
theorem UserApplicationPrefix.to_retained {budget : Nat} {value : Value} {finalStore : Store}
    (user : UserApplicationPrefix (functionModel := functionModel) (completion := completion) (bodyRegistry := bodyRegistry)
      (semanticFaults := semanticFaults) (context := context) (stages := stages) (invocation := invocation)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeNode := calleeNode) (sidecar := sidecar) bridge profile compiler prepared initial budget value finalStore) :
    CallableIndexedOwnedPreparedStagedIndirectRetainedCalleeArgumentPrefix.ApplicationPrefix (functionModel := functionModel)
      (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (registry := completion.result.context.registry) (context := context) (stages := stages)
      (invocation := invocation) (environment := environment) (actual := actual) (ξ := ξ)
      (sourceTypes := sourceTypes) (calleeNode := calleeNode) (sidecar := sidecar)
      bridge profile compiler prepared initial budget value finalStore := by
  obtain ⟨sourceValue, _user, rawParameter, rawResult, functionType, bundle, resultType,
    calleeSize, argumentsSize, calleeHeap, calleeStore, calleeMap, calleeWorld, sources, values, carrier,
    argumentsHeap, argumentsStore, finalMap, finalWorld, originalNode, originalMetadata, tail⟩ := user
  exact ⟨rawParameter, rawResult, functionType, bundle, resultType, calleeSize, argumentsSize,
    sourceValue, calleeHeap, calleeStore, calleeMap, calleeWorld, sources, values, carrier,
    argumentsHeap, argumentsStore, finalMap, finalWorld, originalNode, originalMetadata, tail⟩

/-- Full parent meaning is constructed only after the actual builtin row has
been classified. The reached caller and both independent grades stay literal. -/
def ParentResult (value : Value) (finalStore : Store) : Prop :=
  ∃ sourceSize outcome after finalMap finalWorld,
    Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages sourceSize
      invocation context environment before id outcome after ∧
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

section Classification
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
/-- No callee or argument is replayed. The genuine prefix's selected BoundaryAt
either retains its user suffix, or decides builtin physical arity internally.
An accepted builtin uses the original complete parent reflection once. -/
theorem reflects_builtin_or_user {budget size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore)
    (retained : CallableIndexedOwnedPreparedStagedIndirectRetainedCalleeArgumentPrefix.ApplicationPrefix (functionModel := functionModel)
      (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (registry := completion.result.context.registry) (context := context) (stages := stages)
      (invocation := invocation) (environment := environment) (actual := actual) (ξ := ξ)
      (sourceTypes := sourceTypes) (calleeNode := calleeNode) (sidecar := sidecar)
      bridge profile compiler prepared initial budget value finalStore) :
    UserApplicationPrefix (functionModel := functionModel) (completion := completion) (bodyRegistry := bodyRegistry)
      (semanticFaults := semanticFaults) (context := context) (stages := stages) (invocation := invocation)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeNode := calleeNode) (sidecar := sidecar) bridge profile compiler prepared initial budget value finalStore ∨
    ParentResult (functionModel := functionModel) (completion := completion) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (stages := stages) (invocation := invocation) (environment := environment)
      (actual := actual) (ξ := ξ) bridge profile compiler initial value finalStore := by
  obtain ⟨rawParameter, rawResult, functionType, bundle, resultType, calleeSize, argumentsSize,
    sourceValue, calleeHeap, calleeStore, calleeMap, calleeWorld, sources, values, carrier,
    argumentsHeap, argumentsStore, finalMap, finalWorld, originalNode, originalMetadata,
    calleePost, valueTyped, child, accepted, arguments, representedValues, representedCallee,
    callView, boundary, finalHeaps, maps, worlds, frame, heapMetadata,
    ⟨reached, related, admitted⟩, suffixSize, suffix, strict⟩ := retained
  cases boundary with
  | user dispatch selected =>
    exact .inl ⟨sourceValue, (CallableLedger.frame sidecar).userCallable dispatch.bound,
      rawParameter, rawResult, functionType, bundle, resultType, calleeSize, argumentsSize,
      calleeHeap, calleeStore, calleeMap, calleeWorld, sources, values, carrier, argumentsHeap,
      argumentsStore, finalMap, finalWorld, originalNode, originalMetadata, calleePost, valueTyped,
      child, accepted, arguments, representedValues, representedCallee, callView, .user dispatch selected,
      finalHeaps, maps, worlds, frame, heapMetadata, ⟨reached, related, admitted⟩,
      suffixSize, suffix, strict⟩
  | builtin receipt =>
    rename_i function row
    by_cases count : row.entry.parameterCount = ids.length
    · rw [functionType] at valueTyped representedCallee
      obtain ⟨sourceResult, parentTrace, resultRep, sameStore, heaps, keptMaps, keptWorlds,
        keptFrame, keptMetadata, keptRelated, post⟩ :=
        CallableIndexedOwnedPreparedStagedBuiltinParentBounds.reflects_suffix
          bridge compiler prepared sourceParent occurrence initial reached related admitted
          finalHeaps maps worlds frame heapMetadata observations receipt count actualFunctionType
          valueTyped (representedCallee.map_functions (CallableIndexedOwnedPositiveFunctionModels.ErasesToContextual.erase (headers := headers) (keys := keys) (bodyRegistry := bodyRegistry) (faults := semanticFaults) (profile := profile))) representedValues bundle resultType child arguments suffix (Nat.le_of_lt strict)
      cases sameStore
      exact .inr ⟨Staging.Recursive.Size.stepSize [calleeSize, argumentsSize, Staging.Recursive.Size.stepSize []],
        .value sourceResult, argumentsHeap, finalMap, finalWorld, parentTrace, completed.sound, resultRep,
        heaps, keptMaps, keptWorlds, keptFrame, keptMetadata, reached, keptRelated, post⟩
    · obtain ⟨raw, shape⟩ := receipt.shape
      obtain ⟨sameValue, sameStore⟩ :=
        CallableIndexedOwnedPreparedStagedIndirectSecondGateBounds.rejected_suffix
          shape receipt.selected receipt.selected.found count suffix
      cases sameStore
      have physical : function.id.parameterTypes.length ≠ ids.length := by
        simpa only [receipt.parameter_count] using count
      have sourceFault := CallableIndexedOwnedPreparedSecondCallGateRejection.builtin_source
        occurrence compiler.argumentCoercions sourceParent.arity arguments child physical
      obtain ⟨represented, keptHeaps, keptState, sameState, _keptRelated⟩ :=
        CallableIndexedOwnedPreparedReceivingCallRejectionPosts.receiving_staged_argument_post
          compiler prepared preparedStages receipt.selected receiver initial functions reached related finalHeaps
          (sourceResult := compiler.original.type) (resultCore := lowered.type) count
      cases sameState
      have loweredType : lowered.type = compiler.resultType :=
        (congrArg (fun output => output.type) compiler.output).trans compiler.resultTypeEq.symm
      have valueShape : value = .inLeft lowered.type (.word
          (prepared.site.reasonAt row.caller row.call row.entry.id .beforeApplication
            (.argumentArityMismatch row.entry.parameterCount ids.length))) := by
        simpa only [loweredType] using sameValue
      have faultRep : RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
          compiler.original.type lowered.type callFaults
          (.fault (.semantic (.argumentArityMismatch row.entry.parameterCount ids.length))) value := by
        rw [valueShape]
        exact CallableIndexedOwnedPublicDecodedStagedCallFaults.arity_result model represented
      refine .inr ⟨Staging.Recursive.Size.stepSize [calleeSize, argumentsSize, Staging.Recursive.Size.stepSize []],
        .fault (.semantic (.argumentArityMismatch row.entry.parameterCount ids.length)), argumentsHeap,
        finalMap, finalWorld, ?_, completed.sound, faultRep, keptHeaps, maps, worlds, frame,
        heapMetadata, reached, related, ?_⟩
      · simpa only [receipt.parameter_count] using sourceFault
      · exact ⟨admitted.rows, by intro sourceValue impossible; cases impossible⟩

end Classification
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectBuiltinApplicationDispatch
