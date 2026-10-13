import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalNamedParentBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalIndirectGlobalPrefixes
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodies
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedPayloadReceipts

/-! Internal chosen-body dispatch for the eventual numeric body family.
The static factory selects one genuine packet; the body hypothesis belongs to
that packet alone. Existing failure, physical arity, parameter/body execution
and saved caller restoration proofs retain their original indices. Original
Source typing and compiler-policy transport remain separate static obligations.
-/
/-! A positive global payload retains its actual Header, Source instantiation,
dictionary and native captured code. The selected physical count is decided
at the real argument endpoint before this Header's body producer.
Static per-Header compiler coverage and numeric child coverage remain inputs. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalNamedGlobalDispatch
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedFunctionValues (Header NamedCapture NamedSourceAt)
open CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts (Receipt)
open CallableIndexedOwnedPreparedStagedPhysicalIndirectGlobalPrefixes (GlobalApplicationPrefix)
open CallableIndexedOwnedPreparedStagedPhysicalIndirectGlobalPrefixes (GlobalAppliedPrefix)
open CallableIndexedOwnedPreparedStagedIndirectBuiltinApplicationDispatch (ParentResult)
open CallableIndexedOwnedPreparedStagedIndirectBuiltinPreservationDispatch (ParentAt)
open CallableIndexedOwnedPreparedStagedNamedBodies (Body)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}

variable {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
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
  (physical : CallableIndexedOwnedPhysicalGlobals.Authority compiled mapping store)
  (owners : ∀ owner : CallableIndexedOwnedFunctionValues.OwnedKey keys,
    CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)
  {sourceTypes : List TypeSystem.Ty} {calleeNode : ExpressionNode}
  {sidecar : SourceCoreStageContracts.Sidecar}
  (sourceParent : CallableIndexedOwnedIndirectSourceAdapters.SourceParent compiler)
  (occurrence : Staging.Recursive.Occurrence invocation id (.call callee ids (.indirect metadata)))
  (preparedStages : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)
  (stageEq : stages = RecursiveNamedPreparedStageScopes.registry preparedStages)
  (callerPrepared : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
  (covers : invocation.evidence.Covers context)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  {certificate : GenericExpressionMeaning.Certificate}
  (sourceEq : invocation.source = source)
  (tree : DataExpressionSequence.Tree invocation.source certificate scope ids sourceTypes compiler.codes)
  (unique : NodeOccurrencesUnique invocation.source)
  (parentTyped : ExpressionHasType invocation.source context id compiler.original.type)
  (calleeFound : source.lookupExpression? callee = some calleeNode)
  (actualFunctionType : policy.callables.functionType = CallableContract.functionType)

local notation "functions" => CallableIndexedOwnedPhysicalCellOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked
  completion.result.context.registry functions
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics
local notation "poolBridge" => CallableIndexedOwnedBodyRestorationAdmission.bridge (headers := headers) (keys := keys)

include bridge profile compiler prepared initial physical owners sourceParent occurrence preparedStages stageEq callerPrepared receiver
  wellFormed runtime covers locals sourceEq tree unique parentTyped calleeFound actualFunctionType in
/-- The actual global prefix exposes its original Header before any execution
law is used. Physical mismatch returns the original arity parent; equal count
runs the retained named body producer at the real reached argument state. -/
theorem reflects_global
    (bodies : ∀ header, header ∈ headers → Body header)
    {budget size : Nat} {value : Value} {finalStore : Store}
    (children : ∀ header, ∀ _member : header ∈ headers,
      ∀ {child : Staging.Recursive.Scope},
        (RecursiveNamedPreparedStageScopes.registry preparedStages).Closure header.function child →
        CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.ReflectsBelow (headers := headers) (keys := keys)
        header model (RecursiveNamedPreparedStageScopes.registry preparedStages)
          child callFaults budget)
    (completed : EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore)
    (global : GlobalApplicationPrefix (completion := completion) (bodyRegistry := bodyRegistry)
      (semanticFaults := semanticFaults) (context := context) (stages := stages) (invocation := invocation)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeNode := calleeNode) (sidecar := sidecar) bridge profile compiler prepared initial budget value finalStore) :
    ParentResult (functionModel := functions) (completion := completion) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (stages := stages) (invocation := invocation) (environment := environment)
      (actual := actual) (ξ := ξ) bridge profile compiler initial value finalStore := by
  have originalTree : DataExpressionSequence.Tree source certificate scope ids sourceTypes compiler.codes := by
    simpa only [sourceEq] using tree
  have originalUnique : NodeOccurrencesUnique source := by simpa only [sourceEq] using unique
  have originalTyping : ExpressionHasType source context id compiler.original.type := by
    simpa only [sourceEq] using parentTyped
  obtain ⟨_parameter, _result, _calleeType, argumentsTyped, _bundle, _resultType⟩ :=
    CallableIndexedOwnedIndirectSourceTypeRows.original_rows compiler sourceParent
      originalTree originalUnique originalTyping calleeFound
  have typing : ExpressionsHaveTypes invocation.source context ids sourceTypes := by
    simpa only [sourceEq] using argumentsTyped
  obtain ⟨function, rawParameter, rawResult, functionType, bundle, originalResult,
    calleeSize, argumentsSize, calleeHeap, calleeStore, calleeMap, calleeWorld, sources, values, carrier,
    argumentsHeap, argumentsStore, finalMap, finalWorld, originalNode, originalMetadata,
    calleePost, calleeTyped, calleeTrace, accepted, argumentsTrace, represented, calleeRelated,
    _callView, boundary, heaps, maps, worlds, frame, heapMetadata, ⟨reached, related, admitted⟩,
    suffixSize, suffix, strict⟩ := global
  have origin : CallableIndexedOwnedPhysicalCellOrigins.PayloadOrigins headers keys bodyRegistry
      completion.result.context.registry semanticFaults profile finalMap finalWorld
      calleeNode.type (.global function) carrier compiler.calleeCode.type := by
    exact calleeRelated
  obtain ⟨originalType, ⟨association⟩, _runtimeType⟩ :=
    CallableIndexedOwnedPhysicalCellOrigins.PayloadOrigins.named_member profile origin function rfl
  let owner := association.owner
  let header := association.header
  let identity := association.identity
  let descriptor := association.descriptor
  have member : header ∈ headers := association.member
  have sourceAt := association.sourceAt
  have nativeType := association.type_eq
  let terminal := bodies header member
  have physicalAuthority := physical.extend frame
  obtain ⟨⟨capture, sameCapture⟩⟩ := association.at_store terminal.prepared terminal.aligned
    (owners owner) physicalAuthority
  have carrierEq : carrier = CallableIndexedOwnedPreparedStagedTerminalNamedApplicationBounds.carrier
      (owner := owner) header capture.named identity descriptor.id := by
    rw [sameCapture]
    exact association.native_eq
  cases boundary with
  | user dispatch selected =>
    by_cases count : dispatch.row.entry.parameterCount = ids.length
    · obtain ⟨_nativeCallee, _representedCallee, _calleeHeaps, _calleeMaps, _calleeWorlds,
        _calleeFrame, calleeMetadata, _calleeReached, _calleeRelated, calleeAdmission⟩ := calleePost
      have calleeHeapTyped := calleeAdmission.at_value.2.heap
      have rawCallee : Dynamic.ValueHasType context calleeHeap (.global function)
          (.function rawParameter rawResult) := by
        simpa only [functionType] using calleeTyped
      obtain ⟨sourceSize, outcome, after, returnedMap, returnedWorld, trace, resultRep, returnedHeaps,
        returnedMaps, returnedWorlds, returnedFrame, returnedMetadata, returned, returnedRelated, returnedPost⟩ :=
        CallableIndexedOwnedPreparedStagedPhysicalNamedParentBounds.reflects_suffix
          bridge functions compiler prepared sourceParent occurrence initial reached related admitted
          heaps maps worlds frame heapMetadata dispatch selected callerPrepared count accepted wellFormed runtime covers
          (locals.mono calleeMetadata) calleeHeapTyped typing rawCallee actualFunctionType represented bundle originalResult
          owner header capture physicalAuthority sourceAt identity descriptor.id carrierEq nativeType terminal.layouts member
          terminal.prepared terminal.aligned preparedStages descriptor stageEq
          budget (children header member) calleeTrace argumentsTrace suffix (Nat.le_of_lt strict)
      exact ⟨sourceSize, outcome, after, returnedMap, returnedWorld, trace, completed.sound,
        resultRep, returnedHeaps, returnedMaps, returnedWorlds, returnedFrame, returnedMetadata,
        returned, returnedRelated, returnedPost⟩
    · have physical := CallableIndexedOwnedNamedPhysicalArityReceipts.named_parameter_count
        sourceAt callerPrepared dispatch selected
      have valuesCount := CallableIndexedOwnedPreparedSecondCallGateRejection.values_count argumentsTrace
      have mismatch : header.function.parameters.length ≠ sources.length := by
        intro same
        exact count (physical.trans (same.trans valuesCount))
      have applied := CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts.arity_failure
        (actual := preparedStages) (caller := invocation) (context := context) (heap := argumentsHeap) sourceAt mismatch
      have called : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) stages
          (Staging.Recursive.Size.stepSize []) invocation context argumentsHeap (.global function) sources
          (.fault (.semantic (.argumentArityMismatch header.function.parameters.length sources.length))) argumentsHeap := by
        simpa only [stageEq] using applied
      have failedSource := Staging.Recursive.Size.Expression.applied occurrence compiler.argumentCoercions
        calleeTrace accepted argumentsTrace sourceParent.arity called
      have lowerType : lowered.type = compiler.resultType :=
        (congrArg (fun output => output.type) compiler.output).trans compiler.resultTypeEq.symm
      obtain ⟨sameValue, sameStore⟩ :=
        CallableIndexedOwnedPreparedStagedIndirectSecondGateBounds.rejected_suffix
          dispatch.shape selected dispatch.found count suffix
      cases sameStore
      obtain ⟨representedFault, keptHeaps, keptState, sameState, keptRelated⟩ :=
        CallableIndexedOwnedPreparedReceivingCallRejectionPosts.receiving_staged_argument_post
          compiler prepared preparedStages selected receiver initial functions reached related heaps
          (sourceResult := compiler.original.type) (resultCore := lowered.type) count
      cases sameState
      refine ⟨Staging.Recursive.Size.stepSize [calleeSize, argumentsSize, Staging.Recursive.Size.stepSize []],
        .fault (.semantic (.argumentArityMismatch dispatch.row.entry.parameterCount ids.length)),
        argumentsHeap, finalMap, finalWorld, ?_, completed.sound, ?_, keptHeaps, maps, worlds, frame,
        heapMetadata, reached, keptRelated, ?_⟩
      · simpa only [physical, valuesCount] using failedSource
      · have exactValue : value = .inLeft lowered.type
            (.word (prepared.site.reasonAt dispatch.row.caller dispatch.row.call dispatch.row.entry.id
              .beforeApplication (.argumentArityMismatch dispatch.row.entry.parameterCount ids.length))) := by
          simpa only [lowerType] using sameValue
        rw [exactValue]
        exact CallableIndexedOwnedPublicDecodedStagedCallFaults.arity_result model representedFault
      · change CallableIndexedOwnedSourceAdmission.PostAdmission bridge context compiler.original.type (.fault _) reached
        exact ⟨admitted.rows, by intro sourceValue impossible; cases impossible⟩

include bridge profile compiler prepared initial physical owners sourceParent occurrence preparedStages callerPrepared receiver
  wellFormed runtime covers locals sourceEq tree unique parentTyped calleeFound actualFunctionType in
/-- The genuine global Source suffix retains its original allocation and body
scope. The actual Header and physical row select body execution or arity
failure, and both branches preserve every reached caller effect. -/
theorem preserves_global
    (bodies : ∀ header, header ∈ headers → Body header)
    (guardFrame : invocation.guards = CallableLedger.frame sidecar)
    (budget : Nat)
    (children : ∀ header, ∀ _member : header ∈ headers,
      ∀ {child : Staging.Recursive.Scope}, stages.Closure header.function child →
        CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.PreservesBelow (headers := headers) (keys := keys)
        header model stages child callFaults budget)
    {calleeSize argumentsSize applicationSize : Nat}
    {sourceValue : Dynamic.Value} {calleeHeap argumentsHeap : Dynamic.Heap}
    {sources : List Dynamic.Value} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (global : GlobalAppliedPrefix (completion := completion) (bodyRegistry := bodyRegistry)
      (semanticFaults := semanticFaults) (context := context) (stages := stages) (invocation := invocation)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeNode := calleeNode) (sidecar := sidecar) bridge profile compiler prepared initial
      calleeSize argumentsSize applicationSize sourceValue calleeHeap argumentsHeap sources outcome after)
    (within : applicationSize ≤ budget) :
    ParentAt (functionModel := functions) (completion := completion) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (stages := stages) (invocation := invocation) (environment := environment)
      (actual := actual) (ξ := ξ) bridge profile compiler initial
      (Staging.Recursive.Size.stepSize [calleeSize, argumentsSize, applicationSize]) outcome after := by
  have originalTree : DataExpressionSequence.Tree source certificate scope ids sourceTypes compiler.codes := by
    simpa only [sourceEq] using tree
  have originalUnique : NodeOccurrencesUnique source := by simpa only [sourceEq] using unique
  have originalTyping : ExpressionHasType source context id compiler.original.type := by
    simpa only [sourceEq] using parentTyped
  obtain ⟨_parameter, _result, _calleeType, argumentsTyped, _bundle, _resultType⟩ :=
    CallableIndexedOwnedIndirectSourceTypeRows.original_rows compiler sourceParent
      originalTree originalUnique originalTyping calleeFound
  have typing : ExpressionsHaveTypes invocation.source context ids sourceTypes := by
    simpa only [sourceEq] using argumentsTyped
  obtain ⟨function, selectedFunction, calleeTrace, accepted, argumentsTrace, called, prefixResult⟩ := global
  cases selectedFunction
  obtain ⟨rawParameter, rawResult, functionType, bundle, originalResult,
    calleeStore, calleeMap, calleeWorld, carrier, values, argumentsStore, finalMap, finalWorld,
    originalNode, originalMetadata, calleePost, calleeTyped, firstGate, argumentsNative,
    represented, calleeRelated, _callView, boundary, heaps, maps, worlds,
    frame, heapMetadata, reached, related, admitted⟩ := prefixResult
  have origin : CallableIndexedOwnedPhysicalCellOrigins.PayloadOrigins headers keys bodyRegistry
      completion.result.context.registry semanticFaults profile finalMap finalWorld
      calleeNode.type (.global function) carrier compiler.calleeCode.type := by
    exact calleeRelated
  obtain ⟨originalType, ⟨association⟩, _runtimeType⟩ :=
    CallableIndexedOwnedPhysicalCellOrigins.PayloadOrigins.named_member profile origin function rfl
  let owner := association.owner
  let header := association.header
  let identity := association.identity
  let descriptor := association.descriptor
  have member : header ∈ headers := association.member
  have sourceAt := association.sourceAt
  have nativeType := association.type_eq
  let terminal := bodies header member
  have physicalAuthority := physical.extend frame
  obtain ⟨⟨capture, sameCapture⟩⟩ := association.at_store terminal.prepared terminal.aligned
    (owners owner) physicalAuthority
  have carrierEq : carrier = CallableIndexedOwnedPreparedStagedTerminalNamedApplicationBounds.carrier
      (owner := owner) header capture.named identity descriptor.id := by
    rw [sameCapture]
    exact association.native_eq
  cases boundary with
  | user dispatch selected =>
    by_cases count : dispatch.row.entry.parameterCount = ids.length
    · have calleeNative := calleePost.1
      obtain ⟨_nativeCallee, _representedCallee, _calleeHeaps, _calleeMaps, _calleeWorlds,
        _calleeFrame, calleeMetadata, _calleeReached, _calleeRelated, calleeAdmission⟩ := calleePost
      have calleeHeapTyped := calleeAdmission.at_value.2.heap
      have rawCallee : Dynamic.ValueHasType context calleeHeap (.global function)
          (.function rawParameter rawResult) := by
        simpa only [functionType] using calleeTyped
      exact CallableIndexedOwnedPreparedStagedPhysicalNamedParentBounds.preserves_parent
        bridge functions compiler prepared sourceParent occurrence initial reached related admitted
        heaps maps worlds frame heapMetadata dispatch selected callerPrepared count accepted wellFormed runtime covers
        (locals.mono calleeMetadata) calleeHeapTyped typing rawCallee actualFunctionType represented bundle originalResult
        owner header capture physicalAuthority sourceAt identity descriptor.id carrierEq nativeType terminal.layouts member
        budget (children header member)
        calleeTrace argumentsTrace called within calleeNative firstGate argumentsNative
    · have physical := CallableIndexedOwnedNamedPhysicalArityReceipts.named_parameter_count
        sourceAt callerPrepared dispatch selected
      have valuesCount := CallableIndexedOwnedPreparedSecondCallGateRejection.values_count argumentsTrace
      have different : header.function.parameters.length ≠ ids.length := by
        simpa only [physical] using count
      have bodyUnique : ∀ actualBody,
          Dynamic.FunctionInstantiates (Program.ofChecked compiled.sourceProgram) function.instantiation actualBody →
          RecursiveNamedCatalog.Header.sourceBody header = actualBody := by
        intro actualBody instantiated
        exact BuiltinNamedCalls.instantiation_unique_of_wellFormed wellFormed sourceAt.frame.instantiated instantiated
      cases called with
      | global instantiated _covers _roots _selected _parameters allocate _body _converted =>
        have same := bodyUnique _ instantiated
        cases same
        have actualCount := (congrArg List.length sourceAt.frame.parameters).trans
          (allocate.length_eq.trans valuesCount)
        exact False.elim (different actualCount)
      | globalArity instantiated mismatch =>
        have same := bodyUnique _ instantiated
        cases same
        have actualAccepted : Staging.CallBoundary.GuardAccepts (CallableLedger.frame sidecar)
            prepared.site.call ids (.global function) := by
          simpa only [guardFrame, prepared.call] using accepted
        have argumentsWeaken : Evaluates (.unit :: carrier :: actual) calleeStore
            (((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ).weakenAt 0 |>.weakenAt 0)
            (.inRight .word (DataPatternValues.packValues values)) argumentsStore := by
          simpa only [← GenericExpressionMeaning.rename_prefix, ← GenericExpressionMeaning.rename_prefix]
            using argumentsNative
        have native := CallableIndexedOwnedPreparedSecondCallGateRejection.user_native_preserves
          (result := compiler.resultType) dispatch selected actualAccepted count
          compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown calleePost.1 argumentsWeaken
        change Evaluates actual store
          (CallableContract.call prepared.site.gates
            compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown compiler.resultType
            (compiler.calleeCode.expression.rename ξ)
            ((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ)) _ argumentsStore at native
        rw [← prepared.lowered_rename compiler ξ] at native
        obtain ⟨representedFault, keptHeaps, keptState, sameState, keptRelated⟩ :=
          CallableIndexedOwnedPreparedReceivingCallRejectionPosts.receiving_staged_argument_post
            compiler prepared preparedStages selected receiver initial functions reached related heaps
            (sourceResult := compiler.original.type) (resultCore := lowered.type) count
        cases sameState
        have loweredType : lowered.type = compiler.resultType :=
          (congrArg (fun output => output.type) compiler.output).trans compiler.resultTypeEq.symm
        have faultRep := CallableIndexedOwnedPublicDecodedStagedCallFaults.arity_result model representedFault
        have post : CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context
            compiler.original.type
            (.fault (.semantic (.argumentArityMismatch
              (RecursiveNamedCatalog.Header.sourceBody header).source.inputs.length sources.length))) reached :=
          ⟨admitted.rows, by intro value impossible; cases impossible⟩
        refine ⟨.applied occurrence compiler.argumentCoercions calleeTrace accepted argumentsTrace sourceParent.arity
          (.globalArity instantiated mismatch),
          .inLeft lowered.type (.word (prepared.site.reasonAt dispatch.row.caller dispatch.row.call dispatch.row.entry.id
            .beforeApplication (.argumentArityMismatch dispatch.row.entry.parameterCount ids.length))),
          argumentsStore, finalMap, finalWorld, ?_, ?_, keptHeaps, maps, worlds, frame, heapMetadata,
          reached, keptRelated, post⟩
        · simpa only [loweredType] using native
        · simpa only [physical, sourceAt.frame.parameters, valuesCount] using faultRep

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalNamedGlobalDispatch
