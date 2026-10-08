import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectCallBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStoredIndirectApplication
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredClosureSourceArguments

/-! Forward prepared calls use the actual callee post and independently typed
argument vector. The shared ordered suffix core invokes a prepared body leaf
built internally from strict children, then restores the current caller once.
Prior selection and physical arity rejection remain separate alternatives. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3200000
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStoredIndirectPreservation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters CallableIndexedOwnedIndirectExpressionHeads CallableIndexedOwnedStoredClosureArgumentReceipts
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

include certified found sourceTyped environments heaps locals agrees typed admitted in
/-- The strict callee child constructs its actual value and reached state. -/
theorem preserves_callee_value (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      bridge (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)) context evidence source certificate faults size)
    {size : Nat} {sourceValue : Dynamic.Value} {after : Dynamic.Heap}
    (trace : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) size
      context evidence source environment before callee sourceValue after)
    (smaller : size < budget) :
    ∃ value finalStore finalMap finalWorld,
      CallableIndexedOwnedStoredFunctionModelReceipts.ValuePost (registry := registry)
        (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context)
        bridge (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) compiler initial sourceValue after value finalStore finalMap finalWorld := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, post⟩ :=
    children size smaller certified found sourceTyped environments heaps locals agrees typed initial admitted (.value trace)
  cases represented with
  | value represented =>
    exact ⟨_, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, post⟩

/-- Physical count is required only for the actual accepted application branch. -/
def PhysicalArity {argumentsSize callSize : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (suffix : SourceSuffix (Program.ofChecked compiled.sourceProgram) context evidence source environment calleeHeap ids function
      argumentsSize callSize outcome after) : Prop :=
  CallableIndexedOwnedStoredIndirectCallBounds.ForModel.CalledSuffix
    (context := context) (evidence := evidence) (environment := environment) suffix →
    function.parameters.length = ids.length

/-- The argument fault constructor needs no physical closure count. -/
theorem PhysicalArity.argumentFault {size : Nat} {reason : Dynamic.SemanticFault} {after : Dynamic.Heap}
    (failed : SourceExecutionSize.ExpressionsFault (Program.ofChecked compiled.sourceProgram) size
      context evidence source environment calleeHeap ids reason after) :
    PhysicalArity (context := context) (evidence := evidence) (source := source) (environment := environment)
      (function := function) (.argumentFault failed) := by
  rintro ⟨arguments, middle, argumentTrace, called, same⟩
  have positive := called.positive
  omega

/-- Accepted physical count is an independent actual compiler/closure receipt. -/
theorem PhysicalArity.called {argumentsSize callSize : Nat} {arguments : List Dynamic.Value}
    {middle after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}
    (argumentsTrace : SourceExecutionSize.ExpressionsEvaluate (Program.ofChecked compiled.sourceProgram) argumentsSize
      context evidence source environment calleeHeap ids arguments middle)
    (called : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) callSize
      context evidence function.evidence middle (.closure function) arguments outcome after)
    (count : function.parameters.length = ids.length) :
    PhysicalArity (context := context) (evidence := evidence) (source := source) (environment := environment)
      (.called argumentsTrace called) := fun _ => count

include parentTyped wellFormed runtime covers locals admitted unique parent calleeTrace accepted post in
/-- Genuine Source suffix witnesses construct their exact staged counterpart. -/
theorem staged_of_suffix {argumentsSize callSize : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (suffix : SourceSuffix (Program.ofChecked compiled.sourceProgram) context evidence source environment calleeHeap ids function
      argumentsSize callSize outcome after) :
    Staging.CallBoundary.Executes (Program.ofChecked compiled.sourceProgram) (CallableLedger.frame sidecar)
      context evidence source environment before id callee ids metadata
      (CallableIndexedOwnedPreparedStoredIndirectApplication.boundaryOutcome outcome) after := by
  cases suffix with
  | argumentFault failed =>
    exact .argumentsFault calleeTrace.sound (by simpa only [prepared.call] using accepted) failed.sound
  | called argumentsTrace called =>
    rename_i arguments middle
    obtain ⟨parameter, sourceResult, rawTypes, calleeTyping, argumentsTyping, application⟩ :=
      original_facts unique compiler.found compiler.originalForm parentTyped
    obtain ⟨_calleeTyped, calleeHeapTyped, _calleeExtension⟩ :=
      wellFormed.wholeLanguagePreservation.expression context evidence source environment before calleeHeap callee
        (.closure function) (.function parameter sourceResult) runtime covers locals admitted.heap calleeTyping calleeTrace.sound
    obtain ⟨packed, packing, _rawTyped, _heapTyped, _extension, _packedTyped⟩ :=
      after_trace wellFormed runtime covers (locals.mono post.2.2.2.2.2.2.1) calleeHeapTyped argumentsTyping argumentsTrace
    have count : rawTypes.length = metadata.argumentCount := by
      cases application with | intro count _ _ _ => exact count.symm
    have argumentsCount := arguments_count_of_source_admission wellFormed runtime covers
      (locals.mono post.2.2.2.2.2.2.1) calleeHeapTyped argumentsTyping count argumentsTrace
    have coercions : Dynamic.CoercionPathExecutes (Program.ofChecked compiled.sourceProgram) context evidence
        middle metadata.argumentCoercions packed packed middle := by
      rw [compiler.argumentCoercions]; exact .nil
    cases called with
    | value applied =>
      exact .applied calleeTrace.sound (by simpa only [prepared.call] using accepted) argumentsTrace.sound
        packing coercions packing parent.arity argumentsCount applied.sound
    | fault failed =>
      exact .applicationFault calleeTrace.sound (by simpa only [prepared.call] using accepted) argumentsTrace.sound
        packing coercions packing parent.arity argumentsCount failed.sound

include parentTyped wellFormed runtime covers locals admitted tree unique parent actualFunctionType
  environments agrees typed calleeTrace post accepted observed referenceIndex sameNative selectedType seed
  dispatch selected extension faithful observations rebuilt operandIncluded unaryIncluded interprets in
/-- The true Source suffix constructs its native execution. Prepared body
meaning uses only strict children at the genuine parameter entry. -/
theorem preserves_selected (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      bridge (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)) context evidence source certificate faults size)
    {argumentsSize callSize : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (suffix : SourceSuffix (Program.ofChecked compiled.sourceProgram) context evidence source environment calleeHeap ids function
      argumentsSize callSize outcome after)
    (physicalCount : PhysicalArity (context := context) (evidence := evidence) (source := source)
      (environment := environment) suffix)
    (argumentsWithin : argumentsSize ≤ budget) (callWithin : callSize ≤ budget)
    (meaning : CallableIndexedOwnedStoredIndirectCallBounds.ForModel.CalledSuffix
        (context := context) (evidence := evidence) (environment := environment) suffix → ∀ context, CallableIndexedOwnedTypedLambdaBodyContinuations.Validity
        (program := Program.ofChecked compiled.sourceProgram) captured code context →
      RecursiveNamedCatalogInvocationBounds.Below budget (fun size =>
        CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
          (CallableIndexedOwnedParameterReadyContinuations.bridge (headers := headers) (keys := keys))
          (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)) context function.evidence function.source
          (support.certificates support.body.readFuel function.source context) faults size)) :
    ∃ sourceSize value finalStore finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize context evidence source
        environment before id outcome after ∧
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      Staging.CallBoundary.Executes (Program.ofChecked compiled.sourceProgram) (CallableLedger.frame sidecar)
        context evidence source environment before id callee ids metadata
        (CallableIndexedOwnedPreparedStoredIndirectApplication.boundaryOutcome outcome) after ∧
      CallableIndexedOwnedStoredFunctionModelReceipts.ParentResultAt (registry := registry) (faults := faults) (context := context)
        bridge (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) compiler initial outcome after value finalStore finalMap finalWorld := by
  have calleePost := post
  obtain ⟨calleeEvaluation, calleeRep, calleeHeaps, calleeMaps, calleeWorlds, calleeFrame, calleeMetadata,
    calleeState, calleeRelated, _calleePost⟩ := post
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
  have application : CallableIndexedOwnedStoredIndirectCallBounds.ForModel.ApplicationPreserves
      (registry := registry) (faults := faults) bridge (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) compiler prepared
      (context := context) (evidence := evidence) (environment := environment) (canonical := canonical)
      (mapping := calleeMap) (world := calleeWorld) (calleeHeap := calleeHeap) (store := calleeStore)
      (function := function) (calleeNative := calleeNative) (sourceTypes := sourceTypes)
      (resultCore := code.receipt.resultCore) (dispatch := dispatch) budget suffix := by
    intro middleMap middleWorld middle middleStore arguments payloads types parameter sourceResult packed
      argumentState argumentAdmission stepMaps stepWorlds stepFrame stepMetadata calleeTyped heapExtension
      represented argumentHeaps rawTyped packing bundle argumentsSize callSize outcome after
      argumentsTrace called sameSuffix callWithin
    have physical := physicalCount sameSuffix
    have nativeCount : (compiler.codes.map (·.type)).length = function.parameters.length := by
      simpa only [List.length_map] using compiler.ordered_children.1.symm.trans physical.symm
    have arity : arguments.length = function.parameters.length := represented.length.1.symm.trans nativeCount
    let futureCaptured := captured.extend stepMaps stepWorlds
    have representedArguments := CallableIndexedOwnedPreparedOrdinaryLambdaInvocation.arguments_of_bundles
      futureCaptured code support seed (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) profile represented arity.symm
      (by simpa only [sourceBinders] using sourceBundle) nativeBundle
    obtain ⟨raw, stable⟩ := CallableIndexedOwnedStoredClosureSourceArguments.after_argument_extension
      bridge argumentState runtime argumentAdmission calleeTyped heapExtension rawTyped packing bundle arity
    have rawArguments : Dynamic.ValuesHaveTypes function.context middle arguments support.body.types := by
      simpa only [Dynamic.MonoBindersExtend.bodyTypes_eq support.body.extended] using raw.arguments
    obtain ⟨currentMetadata, currentCarried⟩ := argumentAdmission.rows owner.position
    have reference : futureCaptured.canonical[code.referenceIndex]? =
        some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
      rw [referenceIndex]
      exact observed.reference
    obtain ⟨result, finalStore, finalMap, finalWorld, evaluated, resultRep, finalHeaps,
      lastMaps, lastWorlds, lastFrame, lastMetadata, transition⟩ :=
      CallableIndexedOwnedPreparedOrdinaryLambdaInvocation.application_preserves
        futureCaptured code support history (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) extension faithful observations wellFormed
        rebuilt operandIncluded unaryIncluded interprets representedArguments owner (bridge.pool argumentState)
        argumentHeaps raw.captures reference currentCarried (CallableIndexedLambdaTemplatePermission.lambda_allowed code history)
        raw.heaps rawArguments stable budget (meaning sameSuffix) (callContext := context) (callerEvidence := evidence) called callWithin
    have evaluatedNative : Evaluates [calleeNative, DataPatternValues.packValues payloads]
        middleStore CallableIndexedLambdaCalls.applyPayload result finalStore := by
      simpa only [sameNative, futureCaptured, CallableIndexedLambdaValues.Captures.extend] using evaluated
    obtain ⟨baseReached, baseRelated⟩ := transition
    obtain ⟨returned, _samePool, lastRelated⟩ := bridge.restore argumentState baseReached
      lastMaps lastWorlds lastFrame lastMetadata baseRelated
    exact ⟨result, finalStore, finalMap, finalWorld,
      CallableIndexedOwnedStoredIndirectCallBounds.application_gate dispatch selected physical native.diagnostics.unknown,
      evaluatedNative, resultRep, finalHeaps, lastMaps, lastWorlds, lastFrame, lastMetadata, returned, lastRelated⟩
  obtain ⟨sourceSize, value, finalStore, finalMap, finalWorld, sourceParent, evaluated, result⟩ :=
    CallableIndexedOwnedStoredIndirectCallBounds.ForModel.preserves_selected_with_application
    bridge (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) compiler prepared parent tree unique parentTyped wellFormed runtime covers
    environments locals agrees typed initial admitted calleeState calleeRelated calleeMaps calleeWorlds calleeFrame calleeMetadata
    selectedType calleeHeaps rawResult nativeResult dispatch accepted calleeTrace calleeEvaluation
    selected budget children suffix argumentsWithin callWithin application
  exact ⟨sourceSize, value, finalStore, finalMap, finalWorld, sourceParent, evaluated,
    staged_of_suffix bridge profile compiler prepared parentTyped wellFormed runtime covers locals initial admitted unique parent
      calleeTrace calleePost accepted suffix, result⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStoredIndirectPreservation
