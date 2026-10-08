import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStoredIndirectParentPrefix
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryLambdaInvocation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredSourceBundleReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredSourceResultReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredCallSourcePrefix
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredApplicationProjection

/-! The actual prepared ordinary branch consumes the original successful
argument receipt and its intermediate effects. Native callable injectivity,
independent Source traces and actual physical arity construct its arguments.
Only strict children of the same expression family invoke the prepared body;
the original restoration returns the actual current caller pool. Prior
selections and principal population remain separate alternatives. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStoredIndirectApplication
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
  {native : SourceCoreGeneralFunctions.CallableContext}
  (prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler native)
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {certificate : GenericExpressionMeaning.Certificate} {calleeNode : ExpressionNode}
  (certified : certificate scope callee compiler.calleeCode)
  (found : source.lookupExpression? callee = some calleeNode)
  (sourceTyped : ExpressionHasType source context callee calleeNode.type)
  (parentTyped : ExpressionHasType source context id compiler.original.type)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
  (covers : evidence.Covers context)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
  {canonical actual : Environment} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)


variable {sidecar : SourceCoreStageContracts.Sidecar}
  (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (sidecarSource : sidecar.source = source)

variable {sourceTypes : List TypeSystem.Ty}
  (tree : DataExpressionSequence.Tree source certificate scope ids sourceTypes compiler.codes)
  (unique : NodeOccurrencesUnique source) (parent : SourceParent compiler)
  (actualFunctionType : policy.callables.functionType = CallableContract.functionType)

variable {function : Dynamic.Closure} {calleeHeap : Dynamic.Heap} {calleeStore : Store} {calleeNative : Value}
  {calleeMap : LocationMap} {calleeWorld : StoreTyping} {calleeSize : Nat}
  (calleeTrace : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) calleeSize
    context evidence source environment before callee (.closure function) calleeHeap)
  (post : CallableIndexedOwnedStoredFunctionModelReceipts.ValuePost (registry := registry)
    (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context)
    bridge (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) compiler initial (.closure function) calleeHeap calleeNative calleeStore calleeMap calleeWorld)
  (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids
    (.closure function) calleeNative)
  (selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar prepared.site callee ids metadata
    compiler.original dispatch.row)
  (accepted : Staging.CallBoundary.GuardAccepts (CallableLedger.frame sidecar) prepared.site.call ids (.closure function))
  {lambdaScope : SourceCoreLocalCell.Scope} {capturedActual : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (captured : CallableIndexedLambdaValues.Captures compiled.indexed calleeMap calleeWorld lambdaScope function.captured capturedActual)
  (code : CallableIndexedLambdaValues.Code compiled.indexed function lambdaScope captured.administrative)
  (history : CallableIndexedLambdaValues.History code)
  (support : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Support code)
  (seed : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.PreparedAt code support)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations 1 lambdaScope captured.canonical owner.key.frameLocation)
  (referenceIndex : code.referenceIndex = lambdaScope.length + 1 + compiled.indexed.base.globals.length)
  (sameNative : calleeNative = CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual)
  (selectedType : RuntimeValueHasType calleeWorld calleeNative
    (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) compiled.indexed.layouts.definitions)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) identities)
  {table : SourceCoreFaultSites.Table}
  (rebuilt : support.issued.diagnostics.tableForRegistry registry extension = .ok table)
  (operandIncluded : ∀ reason token, GenericAssignmentDiagnostics.OperandRep support.issued.assignments reason token → faults reason token)
  (unaryIncluded : ∀ reason token, EmittedDiagnosticTokenPlan.UnaryRep support.issued.assignments reason token → faults reason token)
  (interprets : ∀ context, CallableIndexedOwnedTypedLambdaBodyContinuations.Validity
      (program := Program.ofChecked compiled.sourceProgram) captured code context →
    CallableIndexedOwnedContextualLambdaAssignmentReadiness.ReachedInterpretations
      (context := context) (certificates := support.certificates support.body.readFuel function.source)
      (administrative := captured.administrative)
      (factory := CallableIndexedOwnedContextualLambdaJointStaticReceipts.trackedFactory
        support.diagnosticPolicy function.source support.issued.invalidOperand)
      (faults := faults) (registry := registry) support.issued
      (CallableIndexedOwnedParameterReadyContinuations.bridge (headers := headers) (keys := keys)) (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) table)

/-- Semantic callable outcomes retain their genuine staged counterpart.
Stage rejection is a separate earlier outcome. -/
def boundaryOutcome : Dynamic.ExpressionOutcome → Staging.CallBoundary.Outcome
  | .value value => .value value
  | .fault reason => .semanticFault reason

/-- The original successful prefix, actual intermediate effects and passed
fourth gate remain attached beside the complete Source and staged outcome. -/
def ResultAt (budget : Nat) (value : Value) (finalStore : Store) : Prop :=
    CallableIndexedOwnedStoredIndirectArgumentPrefix.ForModel.SuccessPrefix
      (registry := registry) (context := context) (evidence := evidence)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeHeap := calleeHeap) (calleeNative := calleeNative) (calleeStore := calleeStore)
      bridge (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) compiler prepared initial budget value finalStore ∧
    CallableIndexedOwnedStoredFunctionModelReceipts.SuccessStep
      (registry := registry) (context := context) (evidence := evidence)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeHeap := calleeHeap) (calleeNative := calleeNative) (calleeStore := calleeStore)
      (calleeMap := calleeMap) (calleeWorld := calleeWorld)
      bridge (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) compiler prepared initial budget value finalStore ∧
    CallableIndexedOwnedStoredIndirectApplicationPrefix.PassedAt (actual := actual)
      compiler prepared dispatch budget value finalStore ∧
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        context evidence source environment before id outcome after ∧
      Staging.CallBoundary.Executes (Program.ofChecked compiled.sourceProgram) (CallableLedger.frame sidecar)
        context evidence source environment before id callee ids metadata (boundaryOutcome outcome) after ∧
      CallableIndexedOwnedStoredFunctionModelReceipts.ParentResultAt (registry := registry) (faults := faults) (context := context)
        bridge (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) compiler initial outcome after value finalStore finalMap finalWorld

include parentTyped wellFormed runtime covers locals admitted tree unique parent actualFunctionType
  calleeTrace post accepted observed referenceIndex sameNative selectedType seed extension faithful observations
  rebuilt operandIncluded unaryIncluded interprets in
/-- The selected prepared packet constructs its own body continuation from
strict expression children, preserving the whole fourth-bind witness. -/
theorem reflects_selected (budget : Nat)
    (reflection : ∀ context, CallableIndexedOwnedTypedLambdaBodyContinuations.Validity
        (program := Program.ofChecked compiled.sourceProgram) captured code context →
      RecursiveNamedCatalogInvocationBounds.Below budget (fun size =>
        CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
          (CallableIndexedOwnedParameterReadyContinuations.bridge (headers := headers) (keys := keys))
          (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)) context function.evidence function.source
          (support.certificates support.body.readFuel function.source context) faults size))
    {value : Value} {finalStore : Store}
    (original : CallableIndexedOwnedStoredIndirectArgumentPrefix.ForModel.SuccessPrefix
      (registry := registry) (context := context) (evidence := evidence)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeHeap := calleeHeap) (calleeNative := calleeNative) (calleeStore := calleeStore)
      bridge (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) compiler prepared initial budget value finalStore)
    (step : CallableIndexedOwnedStoredFunctionModelReceipts.SuccessStep
      (registry := registry) (context := context) (evidence := evidence)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeHeap := calleeHeap) (calleeNative := calleeNative) (calleeStore := calleeStore)
      (calleeMap := calleeMap) (calleeWorld := calleeWorld)
      bridge (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) compiler prepared initial budget value finalStore)
    (passed : CallableIndexedOwnedStoredIndirectApplicationPrefix.PassedAt (actual := actual)
      compiler prepared dispatch budget value finalStore) :
    ResultAt (registry := registry) (faults := faults) (context := context) (evidence := evidence)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeHeap := calleeHeap) (calleeNative := calleeNative) (calleeStore := calleeStore)
      (calleeMap := calleeMap) (calleeWorld := calleeWorld) (sidecar := sidecar)
      bridge profile compiler prepared initial dispatch budget value finalStore := by
  refine ⟨original, step, passed, ?_⟩
  obtain ⟨_nativeSize, argumentSize, sources, values, middle, argumentStore, argumentMap, argumentWorld,
    _argumentsNative, _argumentsStrict, argumentsTrace, represented, argumentHeaps, stepMaps, stepWorlds, _stepFrame, _stepMetadata,
    maps, worlds, frame, metadataExtended, ⟨argumentState, related, argumentAdmission⟩,
    ⟨remainingSize, remaining, remainingStrict⟩⟩ := step
  have calleeRep := post.2.1
  have parameters := CallableIndexedLambdaEntryPrefix.parameters (values := .initial compiled.compatible.checked) code
  have sourceBinders : code.receipt.loweredParameters.map (fun binding => binding.1.scheme.body) =
      function.parameters.map (fun binding => binding.scheme.body) := by
    simpa only [List.map_map, Function.comp_def] using
      (congrArg (List.map (fun binding : TypedBinder => binding.scheme.body)) parameters).symm
  have sourceBundle := CallableIndexedOwnedStoredSourceBundleReceipts.source_bundle_of_trace
    unique compiler.found compiler.originalForm parentTyped tree compiler.argumentCoercions
    wellFormed runtime covers locals admitted.heap calleeTrace sourceBinders
  have actualType := calleeRep.runtime_hasType.type_eq
  have callableType := compiler.callableType
  rw [actualFunctionType] at callableType
  have nativeTypes := CallableIndexedOwnedStoredNativePackReceipts.callable_parameters
    (callableType.trans (actualType.symm.trans selectedType.type_eq))
  have nativeBundle := (CompatibleExpressionConstructorNativeTyping.packed_type compiler.codes).symm.trans
    (compiler.packedType.symm.trans nativeTypes.1)
  have nativeResult := nativeTypes.2
  have rawResult := congrArg SourceCoreRawMetadata.runtimeType
    (CallableIndexedOwnedStoredSourceResultReceipts.source_result_of_trace
      unique compiler.found compiler.originalForm parentTyped parent.coercions
      wellFormed runtime covers locals admitted.heap calleeTrace)
  have nativeCount : (compiler.codes.map (·.type)).length = function.parameters.length := by
    simpa only [List.length_map] using compiler.ordered_children.1.symm.trans passed.1.symm
  have arity : sources.length = function.parameters.length := represented.length.1.symm.trans nativeCount
  let futureCaptured := captured.extend stepMaps stepWorlds
  have representedArguments := CallableIndexedOwnedPreparedOrdinaryLambdaInvocation.arguments_of_bundles
    futureCaptured code support seed (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) profile represented arity.symm
    (by simpa only [sourceBinders] using sourceBundle) nativeBundle
  obtain ⟨parameter, sourceResult, rawTypes, _calleeTyping, argumentsTyping, application,
    calleeTyped, calleeHeapTyped, _calleeExtension, calleeLocals, rawTyped, _argumentHeapTyped,
    heapExtension, _argumentLocals, _fullExtension, rawArity, packed, packing, _packedTyped, raw⟩ :=
    CallableIndexedOwnedStoredCallSourcePrefix.from_admission_with_arity bridge initial wellFormed runtime covers locals admitted
      unique compiler.found compiler.originalForm parentTyped compiler.argumentCoercions arity calleeTrace argumentsTrace
  have rawArguments : Dynamic.ValuesHaveTypes function.context middle sources support.body.types := by
    simpa only [Dynamic.MonoBindersExtend.bodyTypes_eq support.body.extended] using raw.arguments
  have count : rawTypes.length = metadata.argumentCount := by
    cases application with | intro count _ _ _ => exact count.symm
  have argumentsCount := arguments_count_of_source_admission wellFormed runtime covers calleeLocals calleeHeapTyped
    argumentsTyping count argumentsTrace
  have read : Evaluates (DataPatternValues.packValues values :: .unit :: calleeNative :: actual) argumentStore
      (.second (.var 2)) (.word dispatch.contract) argumentStore :=
    .second (.var (by simpa only [List.getElem?_cons_succ, List.getElem?_cons_zero] using congrArg some dispatch.shape))
  have gate := prepared.site.dispatch_known .beforeApplication native.diagnostics.unknown
    dispatch.contract dispatch.row dispatch.found read
  rw [SourceCoreCallableContracts.reason_accepted dispatch.row prepared.site.reasonAt .beforeApplication passed.2.1] at gate
  cases CallableIndirectCallBounds.bind_completed remaining (Nat.le_of_lt remainingStrict) with
  | failed failed _strict =>
    have same := (evaluation_deterministic failed.sound gate).1
    cases same
  | continued acceptedGate applicationTrace _gateStrict applicationStrict =>
    obtain ⟨same, stores⟩ := evaluation_deterministic acceptedGate.sound gate
    cases same
    subst stores
    have payloadTrace := CallableIndexedOwnedStoredApplicationProjection.to_payload applicationTrace
    rw [sameNative] at payloadTrace
    obtain ⟨currentMetadata, currentCarried⟩ := argumentAdmission.rows owner.position
    have reference : futureCaptured.canonical[code.referenceIndex]? =
        some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
      rw [referenceIndex]
      exact observed.reference
    have call := CallableIndexedOwnedPreparedOrdinaryLambdaInvocation.application_reflects
        futureCaptured code support history (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) extension faithful observations wellFormed
        rebuilt operandIncluded unaryIncluded interprets representedArguments owner (bridge.pool argumentState)
        argumentHeaps raw.captures reference currentCarried (CallableIndexedLambdaTemplatePermission.lambda_allowed code history)
        raw.heaps rawArguments argumentAdmission.rows budget
        (CallableIndexedOwnedPreparedOrdinaryLambdaValues.runtime_views headers keys registry faults profile)
        reflection (callContext := context) (callerEvidence := evidence) payloadTrace (Nat.le_of_lt applicationStrict)
    obtain ⟨callSize, outcome, after, finalMap, finalWorld, called, resultRep, finalHeaps,
      lastMaps, lastWorlds, lastFrame, lastMetadata, transition⟩ := call
    obtain ⟨baseReached, baseRelated⟩ := transition
    obtain ⟨returned, samePool, lastRelated⟩ := bridge.restore argumentState baseReached
      lastMaps lastWorlds lastFrame lastMetadata baseRelated
    obtain ⟨sourceSize, sourceParent⟩ := SourceSuffix.to_expression compiler.found compiler.originalForm
      parent.requirements parent.coercions compiler.argumentCoercions parent.arity wellFormed runtime covers
      calleeLocals calleeHeapTyped argumentsTyping count calleeTrace
      (CallableIndexedOwnedIndirectExpressionHeads.SourceSuffix.called argumentsTrace called)
    have coercions : Dynamic.CoercionPathExecutes (Program.ofChecked compiled.sourceProgram) context evidence
        middle metadata.argumentCoercions packed packed middle := by
      rw [compiler.argumentCoercions]
      exact .nil
    have staged : Staging.CallBoundary.Executes (Program.ofChecked compiled.sourceProgram) (CallableLedger.frame sidecar)
        context evidence source environment before id callee ids metadata (boundaryOutcome outcome) after := by
      cases called with
      | value applied =>
        exact .applied calleeTrace.sound (by simpa only [prepared.call] using accepted) argumentsTrace.sound
          packing coercions packing parent.arity argumentsCount applied.sound
      | fault failed =>
        exact .applicationFault calleeTrace.sound (by simpa only [prepared.call] using accepted) argumentsTrace.sound
          packing coercions packing parent.arity argumentsCount failed.sound
    have loweredType : lowered.type = compiler.resultType :=
      (congrArg (fun output => output.type) compiler.output).trans compiler.resultTypeEq.symm
    have parentRep : GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)) finalMap finalWorld
        compiler.original.type lowered.type faults outcome value := by
      rw [loweredType, nativeResult]
      cases resultRep with
      | value relatedPayload => exact .value (.compatible rawResult relatedPayload)
      | fault matched => exact .fault matched
    exact ⟨sourceSize, outcome, after, finalMap, finalWorld, sourceParent, staged, parentRep, finalHeaps,
      maps.trans lastMaps, worlds.trans lastWorlds, frame.trans lastFrame, metadataExtended.trans lastMetadata,
      returned, callerProtocol.trans related lastRelated,
      after_expression_sized initial returned admitted wellFormed runtime covers locals parentTyped sourceParent
        (frame.trans lastFrame)⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStoredIndirectApplication
