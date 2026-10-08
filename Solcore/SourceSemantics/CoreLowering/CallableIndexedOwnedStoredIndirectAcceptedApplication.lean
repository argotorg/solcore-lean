import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectSuccessStep
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectApplicationPrefix
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaPackReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredSourceBundleReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredSourceResultReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredCallSourcePrefix
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredApplicationProjection

/-! The accepted application consumes the exact ordered argument receipt and
its retained callee-to-argument effects. The whole fourth-bind grade stays
unchanged; its pure reads give the actual payload application grade. Genuine
same-Code association and selected binder projection receipts remain static
inputs. Source traces derive raw callee and argument admission, while only the
strict shared-family body IH invokes the callable and restores the same caller
pool. Ordered argument reflection is not repeated. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectAcceptedApplication
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters
open CallableIndexedOwnedStoredClosureInvocation (Association)
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
    (CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile) mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)

local notation "functions" => CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions

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
  (post : CallableIndexedOwnedStoredIndirectCalleePost.ValuePost (registry := registry) (faults := faults)
    (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context)
    bridge profile compiler initial (.closure function) calleeHeap calleeNative calleeStore calleeMap calleeWorld)
  (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids
    (.closure function) calleeNative)
  (selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar prepared.site callee ids metadata
    compiler.original dispatch.row)
  (accepted : Staging.CallBoundary.GuardAccepts (CallableLedger.frame sidecar) prepared.site.call ids (.closure function))
  {bindings : List CallableIndexedParameterCertificates.Binding} {parameterCore resultCore : Ty}
  (association : Association headers keys registry faults calleeMap calleeWorld function calleeNative bindings parameterCore resultCore)
  (bindingPack : parameterCore = SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd))

/-- Semantic callable outcomes retain their genuine staged counterpart.
Stage rejection is a separate earlier outcome. -/
def boundaryOutcome : Dynamic.ExpressionOutcome → Staging.CallBoundary.Outcome
  | .value value => .value value
  | .fault reason => .semanticFault reason

variable {certificates : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}

/-- The original successful prefix, actual intermediate effects and passed
fourth gate remain attached beside the complete Source and staged outcome. -/
def ResultAt (budget : Nat) (value : Value) (finalStore : Store) : Prop :=
    CallableIndexedOwnedStoredIndirectArgumentPrefix.SuccessPrefix
      (registry := registry) (faults := faults) (context := context) (evidence := evidence)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeHeap := calleeHeap) (calleeNative := calleeNative) (calleeStore := calleeStore)
      bridge profile compiler prepared initial budget value finalStore ∧
    CallableIndexedOwnedStoredIndirectSuccessStep.SuccessStep
      (registry := registry) (faults := faults) (context := context) (evidence := evidence)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeHeap := calleeHeap) (calleeNative := calleeNative) (calleeStore := calleeStore)
      (calleeMap := calleeMap) (calleeWorld := calleeWorld)
      bridge profile compiler prepared initial budget value finalStore ∧
    CallableIndexedOwnedStoredIndirectApplicationPrefix.PassedAt (actual := actual)
      compiler prepared dispatch budget value finalStore ∧
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        context evidence source environment before id outcome after ∧
      Staging.CallBoundary.Executes (Program.ofChecked compiled.sourceProgram) (CallableLedger.frame sidecar)
        context evidence source environment before id callee ids metadata (boundaryOutcome outcome) after ∧
      CallableIndexedOwnedStoredIndirectCallBounds.ResultAt (registry := registry) (faults := faults) (context := context)
        bridge profile compiler initial outcome after value finalStore finalMap finalWorld

include parentTyped wellFormed runtime covers locals admitted tree unique parent actualFunctionType
  calleeTrace post accepted association bindingPack in
/-- The exact successful argument receipt supplies binding representations and
current admission internally. The strict payload grade selects only body IH;
all original prefix receipts are returned unchanged beside the whole result. -/
theorem reflects_selected (budget : Nat)
    (below : CallableIndexedOwnedExtendedJointReadyContinuations.ReflectingBelow
      (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax) functions wellFormed budget)
    {value : Value} {finalStore : Store}
    (original : CallableIndexedOwnedStoredIndirectArgumentPrefix.SuccessPrefix
      (registry := registry) (faults := faults) (context := context) (evidence := evidence)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeHeap := calleeHeap) (calleeNative := calleeNative) (calleeStore := calleeStore)
      bridge profile compiler prepared initial budget value finalStore)
    (step : CallableIndexedOwnedStoredIndirectSuccessStep.SuccessStep
      (registry := registry) (faults := faults) (context := context) (evidence := evidence)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeHeap := calleeHeap) (calleeNative := calleeNative) (calleeStore := calleeStore)
      (calleeMap := calleeMap) (calleeWorld := calleeWorld)
      bridge profile compiler prepared initial budget value finalStore)
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
  obtain ⟨_calleeEvaluation, calleeRep, _calleeHeaps, _calleeMaps, _calleeWorlds, _calleeFrame,
    _calleeMetadata, _calleeState, _calleeRelated, _calleePost⟩ := post
  have sourceBundle := CallableIndexedOwnedStoredSourceBundleReceipts.source_bundle_of_trace
    unique compiler.found compiler.originalForm parentTyped tree compiler.argumentCoercions
    wellFormed runtime covers locals admitted.heap calleeTrace
    (CallableIndexedOwnedStoredIndirectCallBounds.Association.source_binders association)
  have nativeBundle := (CallableIndexedOwnedStoredNativePackReceipts.compiler_parameter_pack
    compiler actualFunctionType association calleeRep).trans bindingPack
  have nativeResult := (CallableIndexedOwnedStoredNativePackReceipts.compiler_parameters
    compiler actualFunctionType association calleeRep).2
  have rawResult := congrArg SourceCoreRawMetadata.runtimeType
    (CallableIndexedOwnedStoredSourceResultReceipts.source_result_of_trace
      unique compiler.found compiler.originalForm parentTyped parent.coercions
      wellFormed runtime covers locals admitted.heap calleeTrace)
  have binderCount : ids.length = bindings.length := passed.1.symm.trans
    (CallableIndexedOwnedStoredIndirectCallBounds.Association.binding_count association).symm
  have nativeCount : (compiler.codes.map (·.type)).length = bindings.length := by
    simpa only [List.length_map] using compiler.ordered_children.1.symm.trans binderCount
  have valuesCount : sources.length = bindings.length := represented.length.1.symm.trans nativeCount
  have representedArguments := CallableIndexedOwnedStoredArgumentAlignment.arguments_of_bundles bindings represented
    valuesCount sourceBundle nativeBundle
  have future := association.extend stepMaps stepWorlds
  obtain ⟨parameter, sourceResult, rawTypes, _calleeTyping, argumentsTyping, application,
    calleeTyped, calleeHeapTyped, _calleeExtension, calleeLocals, rawTyped, _argumentHeapTyped,
    extension, _argumentLocals, _fullExtension, rawArity, packed, packing, _packedTyped, _raw⟩ :=
    CallableIndexedOwnedStoredCallSourcePrefix.from_admission bridge initial wellFormed runtime covers locals admitted
      unique compiler.found compiler.originalForm parentTyped compiler.argumentCoercions future representedArguments
      calleeTrace argumentsTrace
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
    obtain ⟨callSize, outcome, after, called, finalMap, finalWorld, resultRep, finalHeaps, lastMaps, lastWorlds,
      lastFrame, lastMetadata, _baseReached, _baseRelated, _stable, returned, _samePool, lastRelated⟩ :=
      CallableIndexedOwnedAdmittedStoredClosureInvocation.reflects_at bridge functions wellFormed runtime future
        argumentState argumentAdmission calleeTyped extension representedArguments argumentHeaps rawTyped packing
        (CallableIndexedOwnedStoredClosureArgumentReceipts.empty_bundle application compiler.argumentCoercions)
        rawArity budget below (callContext := context) (callerEvidence := evidence) payloadTrace (Nat.le_of_lt applicationStrict)
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
    have parentRep : GenericExpressionMeaning.ResultRepresents model finalMap finalWorld
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

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectAcceptedApplication
