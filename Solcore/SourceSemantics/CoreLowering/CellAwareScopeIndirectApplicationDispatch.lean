import Solcore.SourceSemantics.CoreLowering.SelectedStagedPostAdmission
import Solcore.SourceSemantics.CoreLowering.SelectedStagedArgumentTyping
import Solcore.SourceSemantics.CoreLowering.CellAwareScopeIndirectSourcePrefixDispatch
import Solcore.SourceSemantics.CoreLowering.CellAwareScopeIndirectApplicationParentBounds
import Solcore.SourceSemantics.CoreLowering.CellAwareScopeIndirectSecondGateBounds

/-! The materialization retained by the original callee determines the
application branch. Both real gates and every reached argument effect remain
part of the parent computation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareScopeIndirectApplicationDispatch
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
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
  [positive : SelectedCompilationCallableOrigins.Origins
    headers keys bodyRegistry semanticFaults profile functionModel]
  {named : SourceCoreGeneralFunctions.Function}
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : GenericExpressionMeaning.Certificate}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  (prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler
    compiled.indexed.ancestry.graph.inputs.callable)
  (sourceEq : invocation.source = source)
  (occurrence : Staging.Recursive.Occurrence invocation id (.call callee ids (.indirect metadata)))
  {calleeNode : ExpressionNode}
  (calleeCertificate : GeneralizedLocalNamedReadCompilation.Certificate compiled.indexed named
    invocation.source scope callee reasonAt compiler.calleeCode)
  (calleeRecipe : GeneralizedLocalNamedRecipeCompilation.Receipt calleeCertificate)
  (found : source.lookupExpression? callee = some calleeNode)
  (sourceTyped : ExpressionHasType source context callee calleeNode.type)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
  {canonical actual : Environment} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functionModel)
    (GeneralizedLocalInstanceValues.model compiled.indexed)) mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)
  (authority : CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model compiled.indexed)
    named.signature.key [] mapping world before store environment)
  (physical : CellAwareScopePhysical.Physical compiled named context scope canonical mapping world before store environment)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (ownerFrame : owner.key.frameLocation = physical.location)
  {sidecar : SourceCoreStageContracts.Sidecar}
  (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (view : CallableIndexedOwnedContextualDiagnosticSources.SourceView sidecar.source source)
  (originalUnique : NodeOccurrencesUnique sidecar.source)
  (guardFrame : invocation.guards = CallableLedger.frame sidecar)
  (sourceParent : CallableIndexedOwnedIndirectSourceAdapters.SourceParent compiler)
  {sourceTypes : List TypeSystem.Ty}
  (tree : DataExpressionSequence.Tree invocation.source certificate scope ids sourceTypes compiler.codes)
  (unique : NodeOccurrencesUnique invocation.source)
  (parentTyped : ExpressionHasType invocation.source context id compiler.original.type)
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)

local notation "functions" => functionModel
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

variable
  (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies (Program.ofChecked compiled.sourceProgram) stages)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
  (covers : invocation.evidence.Covers context)
  (actualFunctionType : policy.callables.functionType = CallableContract.functionType)

include prepared sourceEq occurrence found locals authority physical ownerFrame guardFrame sourceParent
  tree unique parentTyped stagePrepared receiver selectedBodies runtime covers actualFunctionType in
omit positive in
theorem preserves_application_selected (budget : Nat)
    (applicationMeaning : CellAwareScopeApplicationBounds.PreservesBelow
      bridge context model named stages invocation callFaults budget)
    {calleeSize argumentsSize applicationSize : Nat} {sourceValue : Dynamic.Value}
    {calleeHeap argumentsHeap after : Dynamic.Heap} {sources : List Dynamic.Value}
    {outcome : Staging.Recursive.Outcome}
    (calleeTrace : Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages calleeSize
      invocation context environment before callee (.value sourceValue) calleeHeap)
    (accepted : Staging.CallBoundary.GuardAccepts invocation.guards id ids sourceValue)
    (argumentsTrace : Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages argumentsSize
      invocation context environment calleeHeap ids (.values sources) argumentsHeap)
    (called : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) stages applicationSize
      invocation context argumentsHeap sourceValue sources outcome after)
    (within : applicationSize < budget)
    (prefixResult : CellAwareScopeIndirectValuesPrefix.ValuesPrefix (functionModel := functionModel)
      (registry := completion.result.context.registry) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeNode := calleeNode) (sidecar := sidecar)
      bridge profile compiler prepared initial owner sourceValue calleeHeap argumentsHeap sources) :
    CellAwareScopeIndirectSourcePrefixDispatch.NativeResultAt (functionModel := functionModel)
      (completion := completion) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (actual := actual) (ξ := ξ) bridge profile compiler initial outcome after := by
  obtain ⟨rawParameter, rawResult, functionType, bundle, originalResult,
    calleeStore, calleeMap, calleeWorld, carrier, values, argumentsStore, finalMap, finalWorld,
    originalNode, originalMetadata, calleePost, calleeTyped, firstGate, argumentsNative,
    represented, calleeRelated, strong, _callView, boundary, heaps, maps, worlds,
    frame, heapMetadata, effect, reached, related, admitted⟩ := prefixResult
  obtain ⟨function, native, bindings, parameterCore, resultCore, sourceValueEq, nativeEq, association, atFrame⟩ :=
    strong sourceValue rfl
  cases sourceValueEq
  have nativeSame := Value.inRight.inj nativeEq
  cases nativeSame.2
  have originalTree : DataExpressionSequence.Tree source certificate scope ids sourceTypes compiler.codes := by
    simpa only [sourceEq] using tree
  have originalUnique : NodeOccurrencesUnique source := by simpa only [sourceEq] using unique
  have originalTyping : ExpressionHasType source context id compiler.original.type := by
    simpa only [sourceEq] using parentTyped
  obtain ⟨_parameter, _result, _calleeType, argumentsTyped, _bundle, _resultType⟩ :=
    CallableIndexedOwnedIndirectSourceTypeRows.original_rows compiler sourceParent
      originalTree originalUnique originalTyping found
  have typing : ExpressionsHaveTypes invocation.source context ids sourceTypes := by
    simpa only [sourceEq] using argumentsTyped
  cases boundary with
  | user dispatch selected =>
    by_cases count : dispatch.row.entry.parameterCount = ids.length
    · have calleeNative := calleePost.1
      obtain ⟨_nativeCallee, _representedCallee, _strong, _calleeHeaps, _calleeMaps, _calleeWorlds,
        _calleeFrame, calleeMetadata, _calleeEffect, calleeReached, _calleeRelated, calleeAdmission⟩ := calleePost
      have rawCallee : Dynamic.ValueHasType context calleeHeap (.closure function)
          (.function rawParameter rawResult) := by simpa only [functionType] using calleeTyped
      have relatedCallee : GenericHeap.PayloadModel.Represents model finalMap finalWorld
          (.function rawParameter rawResult) (.closure function) carrier compiler.calleeCode.type := by
        simpa only [functionType] using calleeRelated
      obtain ⟨sourceValuesTyped, _heapTyped, argumentMetadata⟩ :=
        SelectedStagedArgumentTyping.values_at selectedBodies runtime covers
          (locals.mono calleeMetadata) calleeAdmission.at_value.2.heap typing argumentsTrace
      exact (CellAwareScopeIndirectApplicationParentBounds.preserves_parent
        bridge profile compiler prepared sourceParent occurrence initial reached related admitted heaps
        (authority.transport effect) (physical.transport effect frame) owner ownerFrame
        maps worlds frame heapMetadata effect dispatch selected count accepted sourceValuesTyped argumentMetadata
        runtime rawCallee actualFunctionType relatedCallee represented association atFrame bundle originalResult
        budget applicationMeaning calleeTrace argumentsTrace called within calleeNative firstGate argumentsNative).2
    · have physicalCount := CallableIndexedOwnedStoredClosureArityBoundary.parameter_count dispatch selected
      have valuesCount := CallableIndexedOwnedPreparedSecondCallGateRejection.values_count argumentsTrace
      have different : function.parameters.length ≠ ids.length := by simpa only [physicalCount] using count
      cases called with
      | closure selectedChild valid parameters allocate bodyTrace bodyResult =>
        exact False.elim (different (allocate.length_eq.trans valuesCount))
      | closureArity mismatch =>
        have actualAccepted : Staging.CallBoundary.GuardAccepts (CallableLedger.frame sidecar)
            prepared.site.call ids (.closure function) := by simpa only [guardFrame, prepared.call] using accepted
        have argumentsWeaken : Evaluates (.unit :: carrier :: actual) calleeStore
            (((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ).weakenAt 0 |>.weakenAt 0)
            (.inRight .word (DataPatternValues.packValues values)) argumentsStore := by
          simpa only [← GenericExpressionMeaning.rename_prefix, ← GenericExpressionMeaning.rename_prefix] using argumentsNative
        have evaluated := CallableIndexedOwnedPreparedSecondCallGateRejection.user_native_preserves
          (result := compiler.resultType) dispatch selected actualAccepted count
          compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown calleePost.1 argumentsWeaken
        change Evaluates actual store
          (CallableContract.call prepared.site.gates compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown
            compiler.resultType (compiler.calleeCode.expression.rename ξ)
            ((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ)) _ argumentsStore at evaluated
        rw [← prepared.lowered_rename compiler ξ] at evaluated
        obtain ⟨diagnostic, decoded, error⟩ :=
          CallableIndexedOwnedPreparedReceivingCallRejectionDiagnostics.receiving_diagnostic
            compiler prepared stagePrepared selected receiver count
        have received : RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld compiler.original.type lowered.type
            (CallableIndexedOwnedPreparedSecondCallGateRejection.stagedArityFaults completion.result.diagnostics)
            (.fault (.semantic (.argumentArityMismatch dispatch.row.entry.parameterCount ids.length)))
            (.inLeft lowered.type (.word (prepared.site.reasonAt dispatch.row.caller dispatch.row.call dispatch.row.entry.id
              .beforeApplication (.argumentArityMismatch dispatch.row.entry.parameterCount ids.length)))) :=
          .fault ⟨dispatch.row.entry.parameterCount, ids.length, diagnostic, rfl, decoded, error⟩
        have lowerType : lowered.type = compiler.resultType :=
          (congrArg (fun output => output.type) compiler.output).trans compiler.resultTypeEq.symm
        have faultRep := CallableIndexedOwnedPublicDecodedStagedCallFaults.arity_result model received
        refine ⟨.inLeft lowered.type (.word (prepared.site.reasonAt dispatch.row.caller dispatch.row.call dispatch.row.entry.id
            .beforeApplication (.argumentArityMismatch dispatch.row.entry.parameterCount ids.length))),
          argumentsStore, finalMap, finalWorld, ?_, ?_, heaps, maps, worlds, frame,
          heapMetadata, effect, reached, related, ?_⟩
        · simpa only [lowerType] using evaluated
        · simpa only [physicalCount, valuesCount] using faultRep
        · change CallableIndexedOwnedSourceAdmission.PostAdmission bridge context compiler.original.type (.fault _) reached
          exact ⟨admitted.rows, by intro value impossible; cases impossible⟩

/-- The real native suffix returns its independent Source grade and exact post. -/
def ReflectedResult (value : Value) (finalStore : Store) : Prop :=
  ∃ sourceSize outcome after finalMap finalWorld,
    Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages sourceSize
      invocation context environment before id outcome after ∧
    RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld compiler.original.type lowered.type
      callFaults outcome value ∧
    GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model
      (GeneralizedLocalInstanceValues.model compiled.indexed)) finalMap finalWorld after finalStore ∧
    LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
    AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
    CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model compiled.indexed)
      mapping world before store finalMap finalWorld after finalStore ∧
    ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
      callerProtocol.Relates initial reached ∧
      CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context compiler.original.type outcome reached

include prepared sourceEq occurrence found sourceTyped locals admitted authority physical ownerFrame sourceParent
  tree unique parentTyped stagePrepared receiver selectedBodies runtime covers actualFunctionType in
omit positive in
theorem reflects_application_selected (budget : Nat)
    (applicationMeaning : CellAwareScopeApplicationBounds.ReflectsBelow
      bridge context model named stages invocation callFaults budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (_completed : EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore)
    (prefixResult : CellAwareScopeIndirectArgumentPrefix.ApplicationPrefix (functionModel := functionModel)
      (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (registry := completion.result.context.registry) (context := context)
      (stages := stages) (invocation := invocation) (environment := environment)
      (actual := actual) (sourceTypes := sourceTypes) (calleeNode := calleeNode) (sidecar := sidecar)
      bridge profile compiler prepared initial owner budget value finalStore) :
    ReflectedResult (functionModel := functionModel) (completion := completion)
      (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) (context := context)
      (stages := stages) (invocation := invocation) (environment := environment)
      bridge profile compiler initial value finalStore := by
  obtain ⟨rawParameter, rawResult, functionType, bundle, originalResult,
    calleeSize, argumentsSize, sourceValue, calleeHeap, sources, values, carrier,
    argumentsHeap, argumentsStore, finalMap, finalWorld, originalNode, originalMetadata,
    calleeTrace, accepted, argumentsTrace, represented, calleeRelated, strong, _callView, boundary,
    heaps, maps, worlds, frame, heapMetadata, effect, ⟨reached, related, reachedAdmission⟩,
    suffixSize, suffix, strict⟩ := prefixResult
  obtain ⟨function, native, bindings, parameterCore, resultCore, sourceValueEq, nativeEq, association, atFrame⟩ :=
    strong sourceValue rfl
  cases sourceValueEq
  have nativeSame := Value.inRight.inj nativeEq
  cases nativeSame.2
  have originalTree : DataExpressionSequence.Tree source certificate scope ids sourceTypes compiler.codes := by
    simpa only [sourceEq] using tree
  have originalUnique : NodeOccurrencesUnique source := by simpa only [sourceEq] using unique
  have originalTyping : ExpressionHasType source context id compiler.original.type := by
    simpa only [sourceEq] using parentTyped
  obtain ⟨_parameter, _result, _calleeType, argumentsTyped, _bundle, _resultType⟩ :=
    CallableIndexedOwnedIndirectSourceTypeRows.original_rows compiler sourceParent originalTree originalUnique originalTyping found
  have typing : ExpressionsHaveTypes invocation.source context ids sourceTypes := by
    simpa only [sourceEq] using argumentsTyped
  have actualTyped : ExpressionHasType invocation.source context callee calleeNode.type := by
    simpa only [sourceEq] using sourceTyped
  have calleeSource := Staging.Recursive.SelectedPreservation.expression selectedBodies
    runtime covers locals admitted.heap actualTyped calleeTrace
  have rawCallee : Dynamic.ValueHasType context calleeHeap (.closure function) (.function rawParameter rawResult) := by
    simpa only [functionType] using calleeSource.value_typed _ rfl
  have relatedCallee : GenericHeap.PayloadModel.Represents model finalMap finalWorld
      (.function rawParameter rawResult) (.closure function) carrier compiler.calleeCode.type := by
    simpa only [functionType] using calleeRelated
  obtain ⟨sourceValuesTyped, _heapTyped, argumentMetadata⟩ :=
    SelectedStagedArgumentTyping.values_at selectedBodies runtime covers
      (locals.mono calleeSource.heap_extends) calleeSource.heap_typed typing argumentsTrace
  cases boundary with
  | user dispatch selected =>
    by_cases count : dispatch.row.entry.parameterCount = ids.length
    · exact CellAwareScopeIndirectApplicationParentBounds.reflects_suffix
        bridge profile compiler prepared sourceParent occurrence initial reached related reachedAdmission heaps
        (authority.transport effect) (physical.transport effect frame) owner ownerFrame
        maps worlds frame heapMetadata effect dispatch selected count accepted sourceValuesTyped argumentMetadata
        runtime rawCallee actualFunctionType relatedCallee represented association atFrame bundle originalResult
        budget applicationMeaning calleeTrace argumentsTrace suffix (Nat.le_of_lt strict)
    · have physicalCount := CallableIndexedOwnedStoredClosureArityBoundary.parameter_count dispatch selected
      have valuesCount := CallableIndexedOwnedPreparedSecondCallGateRejection.values_count argumentsTrace
      have mismatch : function.parameters.length ≠ sources.length := by simpa only [physicalCount, valuesCount] using count
      obtain ⟨valueEq, storeEq⟩ := CallableIndexedOwnedPreparedStagedIndirectSecondGateBounds.rejected_suffix
        dispatch.shape selected dispatch.found count suffix
      cases storeEq
      obtain ⟨diagnostic, decoded, error⟩ :=
        CallableIndexedOwnedPreparedReceivingCallRejectionDiagnostics.receiving_diagnostic
          compiler prepared stagePrepared selected receiver count
      have received : RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld compiler.original.type lowered.type
          (CallableIndexedOwnedPreparedSecondCallGateRejection.stagedArityFaults completion.result.diagnostics)
          (.fault (.semantic (.argumentArityMismatch dispatch.row.entry.parameterCount ids.length)))
          (.inLeft lowered.type (.word (prepared.site.reasonAt dispatch.row.caller dispatch.row.call dispatch.row.entry.id
            .beforeApplication (.argumentArityMismatch dispatch.row.entry.parameterCount ids.length)))) :=
        .fault ⟨dispatch.row.entry.parameterCount, ids.length, diagnostic, rfl, decoded, error⟩
      have lowerType : lowered.type = compiler.resultType :=
        (congrArg (fun output => output.type) compiler.output).trans compiler.resultTypeEq.symm
      have faultRep := CallableIndexedOwnedPublicDecodedStagedCallFaults.arity_result model received
      refine ⟨Staging.Recursive.Size.stepSize [calleeSize, argumentsSize, Staging.Recursive.Size.stepSize []],
        .fault (.semantic (.argumentArityMismatch function.parameters.length sources.length)),
        argumentsHeap, finalMap, finalWorld,
        .applied occurrence compiler.argumentCoercions calleeTrace accepted argumentsTrace sourceParent.arity (.closureArity mismatch),
        ?_, heaps, maps, worlds, frame, heapMetadata, effect, reached, related, ?_⟩
      · simpa only [valueEq, lowerType, physicalCount, valuesCount] using faultRep
      · change CallableIndexedOwnedSourceAdmission.PostAdmission bridge context compiler.original.type (.fault _) reached
        exact ⟨reachedAdmission.rows, by intro value impossible; cases impossible⟩

/- Compatibility adapters for callers with a whole-program receipt. -/
include prepared sourceEq occurrence found locals authority physical ownerFrame guardFrame sourceParent
  tree unique parentTyped stagePrepared receiver wellFormed runtime covers actualFunctionType in
omit positive in
theorem preserves_application (budget : Nat)
    (applicationMeaning : CellAwareScopeApplicationBounds.PreservesBelow
      bridge context model named stages invocation callFaults budget)
    {calleeSize argumentsSize applicationSize : Nat} {sourceValue : Dynamic.Value}
    {calleeHeap argumentsHeap after : Dynamic.Heap} {sources : List Dynamic.Value}
    {outcome : Staging.Recursive.Outcome}
    (calleeTrace : Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages calleeSize
      invocation context environment before callee (.value sourceValue) calleeHeap)
    (accepted : Staging.CallBoundary.GuardAccepts invocation.guards id ids sourceValue)
    (argumentsTrace : Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages argumentsSize
      invocation context environment calleeHeap ids (.values sources) argumentsHeap)
    (called : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) stages applicationSize
      invocation context argumentsHeap sourceValue sources outcome after)
    (within : applicationSize < budget)
    (prefixResult : CellAwareScopeIndirectValuesPrefix.ValuesPrefix (functionModel := functionModel)
      (registry := completion.result.context.registry) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeNode := calleeNode) (sidecar := sidecar)
      bridge profile compiler prepared initial owner sourceValue calleeHeap argumentsHeap sources) :
    CellAwareScopeIndirectSourcePrefixDispatch.NativeResultAt (functionModel := functionModel)
      (completion := completion) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (actual := actual) (ξ := ξ) bridge profile compiler initial outcome after := by
  apply preserves_application_selected (selectedBodies := Staging.Recursive.SelectedPreservation.SelectedBodies.of_program wellFormed) (prepared := prepared) (sourceEq := sourceEq) (occurrence := occurrence) (found := found) (locals := locals) (authority := authority) (physical := physical) (ownerFrame := ownerFrame) (guardFrame := guardFrame) (sourceParent := sourceParent) (tree := tree) (unique := unique) (parentTyped := parentTyped) (stagePrepared := stagePrepared) (receiver := receiver) (runtime := runtime) (covers := covers) (actualFunctionType := actualFunctionType) <;> assumption

include prepared sourceEq occurrence found sourceTyped locals admitted authority physical ownerFrame sourceParent
  tree unique parentTyped stagePrepared receiver wellFormed runtime covers actualFunctionType in
omit positive in
theorem reflects_application (budget : Nat)
    (applicationMeaning : CellAwareScopeApplicationBounds.ReflectsBelow
      bridge context model named stages invocation callFaults budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (_completed : EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore)
    (prefixResult : CellAwareScopeIndirectArgumentPrefix.ApplicationPrefix (functionModel := functionModel)
      (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (registry := completion.result.context.registry) (context := context)
      (stages := stages) (invocation := invocation) (environment := environment)
      (actual := actual) (sourceTypes := sourceTypes) (calleeNode := calleeNode) (sidecar := sidecar)
      bridge profile compiler prepared initial owner budget value finalStore) :
    ReflectedResult (functionModel := functionModel) (completion := completion)
      (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) (context := context)
      (stages := stages) (invocation := invocation) (environment := environment)
      bridge profile compiler initial value finalStore := by
  apply reflects_application_selected (selectedBodies := Staging.Recursive.SelectedPreservation.SelectedBodies.of_program wellFormed) (prepared := prepared) (sourceEq := sourceEq) (occurrence := occurrence) (found := found) (sourceTyped := sourceTyped) (locals := locals) (admitted := admitted) (authority := authority) (physical := physical) (ownerFrame := ownerFrame) (sourceParent := sourceParent) (tree := tree) (unique := unique) (parentTyped := parentTyped) (stagePrepared := stagePrepared) (receiver := receiver) (runtime := runtime) (covers := covers) (actualFunctionType := actualFunctionType) <;> assumption

end Solcore.SourceSemantics.CoreLowering.CellAwareScopeIndirectApplicationDispatch
