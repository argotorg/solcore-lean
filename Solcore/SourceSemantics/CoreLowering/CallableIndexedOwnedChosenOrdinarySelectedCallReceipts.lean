import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryReadMembers
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStoredIndirectApplication
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedIndirectCompilerReceipts

/-! The known chosen callee stays at one actual post and selected row.
Successful argument receipts extend that same positive index and retain the
current pool and complete fourth bind. Body construction remains in the
existing chosen continuation and invocation producers. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinarySelectedCallReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedNamedGeneration
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPreparedRuntimeFamilyMembers (OrdinaryIndex)
open CallableIndexedOwnedPreparedOrdinaryLambdaSupport
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedContextualCompilerPolicyProfiles (RootPolicyReceipt)
open CallableIndexedOwnedChosenOrdinaryFormedMembers (FactoryMember)
open CallableIndexedOwnedChosenOrdinaryStoredMembers
open CallableIndexedOwnedIndirectSourceAdapters
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {rootCompilation : Compilation compiled.indexed caller.named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) caller.named diagnostics namedCode rootCompilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  (expressionSyntax : TypedSource → ExpressionId → Prop)



/-- All payload equations and the chosen constructor belong to this known index. -/
def CalleeAt
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (i : OrdinaryIndex compiled) (history : History i.code)
    (raw : TypeSystem.Ty) (sourceValue : Dynamic.Value) (carrier : Value) (type : Ty) : Prop :=
  sourceValue = .closure i.function ∧
  carrier = CallableIndexedLambdaValues.value i.code i.captured.embedding history.native i.capturedActual ∧
  ChosenAt root expressionSyntax headers keys registry faults i history ∧
  CallableIndexedOwnedPreparedOrdinaryLambdaValues.Selected
    (headers := headers) (keys := keys) (registry := registry) (faults := faults)
    (mapping := i.mapping) (world := i.world) (raw := raw)
    (function := i.function) (native := carrier) (type := type)

section ReadPost
open CompatibleExpressionReads
variable {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {i : OrdinaryIndex compiled} {history : History i.code}
  {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id : ExpressionId} {reason : Word} {code : Expr}
  (certificate : Certificate fuel (.initial compiled.compatible.checked) source scope id reason code)
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {administrative : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
  {heap : Dynamic.Heap} {store : Store} {ξ : Renaming} {location : Dynamic.Location}
variable {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {childFuel : Nat}
  {compilation : SourceCoreFunctions.Context} {parentId : ExpressionId} {ids : List ExpressionId}
  {metadata : IndirectCallResolution} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body childFuel compilation source scope parentId id ids metadata reasonAt lowered)
  {calleeNode : ExpressionNode}
  (initial : callerProtocol.State ⟨scope, i.mapping, i.world, heap, store, canonical⟩)

theorem at_chosen_post
    (sameCode : compiler.calleeCode.expression = code)
    (sameNode : calleeNode = certificate.node)
    (sameType : compiler.calleeCode.type = certificate.type)
    (binding : StaticBinding certificate context) (unique : NodeOccurrencesUnique source)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      i.mapping i.world administrative scope environment canonical compiled.indexed.layouts.definitions)
    (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (stored : ChosenStoredAt root expressionSyntax headers keys registry faults i history heap store location)
    (lookup : Dynamic.Environment.LooksUp environment certificate.binder location)
    {sourceSize : Nat} {calleeValue : Dynamic.Value} {after : Dynamic.Heap}
    {carrier : Value} {calleeStore : Store} {calleeMap : LocationMap} {calleeWorld : StoreTyping}
    (sourceTrace : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) sourceSize
      context evidence source environment heap id calleeValue after)
    (post : CallableIndexedOwnedStoredFunctionModelReceipts.ValuePost (registry := registry)
      (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context)
      bridge (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)
      compiler initial calleeValue after carrier calleeStore calleeMap calleeWorld) :
    CallableIndexedOwnedStoredFunctionModelReceipts.ValuePost (registry := registry)
      (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context)
      bridge (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)
      compiler initial calleeValue after carrier calleeStore calleeMap calleeWorld ∧
    CalleeAt root expressionSyntax headers keys registry faults
      (extendIndex i post.2.2.2.1 post.2.2.2.2.1) history calleeNode.type calleeValue carrier compiler.calleeCode.type := by
  obtain ⟨samePost, sameSource, _sameHeap, sameNative, _sameStore, member⟩ :=
    CallableIndexedOwnedChosenOrdinaryReadMembers.at_value_post_chosen
      root expressionSyntax certificate bridge profile compiler initial sameCode binding unique
      environments locals agrees stored lookup sourceTrace post
  obtain ⟨sameSource, selected⟩ :=
    CallableIndexedOwnedChosenOrdinaryReadMembers.selected_at_callee_post
      (evidence := evidence) root expressionSyntax certificate bridge profile compiler initial
      sameNode sameType binding environments locals agrees stored lookup samePost sameSource sameNative member
  exact ⟨samePost, sameSource, sameNative, member, selected⟩
end ReadPost

section Gate
variable {sidecar : SourceCoreStageContracts.Sidecar} {site : SourceCoreCallableContracts.Callsite}
  {callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution} {node : ExpressionNode}
  {function : Dynamic.Closure} {carrier : Value}
  (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) site site.call ids (.closure function) carrier)
  (selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar site callee ids metadata node dispatch.row)

/-- Genuine stage acceptance and physical counts close only these two selected gates. -/
structure AcceptedAt (unknown : Word) : Prop where
  stage : Staging.CallBoundary.GuardAccepts (CallableLedger.frame sidecar) site.call ids (.closure function)
  physical : function.parameters.length = ids.length
  first : dispatch.row.beforeArguments = .ok ()
  fourth : dispatch.row.afterArguments = .ok ()
  beforeApplication : CallableContract.decision site.gates .beforeApplication unknown dispatch.contract = none

include selected in
/-- The original bound Source contract authenticates the same row counts. -/
theorem accepted_at_row (unknown : Word)
    (stage : Staging.CallBoundary.GuardAccepts (CallableLedger.frame sidecar) site.call ids (.closure function))
    (physical : function.parameters.length = ids.length) : AcceptedAt dispatch unknown :=
  ⟨stage, physical, dispatch.accepted stage,
    CallableIndexedOwnedStoredIndirectApplicationPrefix.accepted_row dispatch selected physical,
    CallableIndexedOwnedStoredIndirectCallBounds.application_gate dispatch selected physical unknown⟩

include selected in
/-- An actual passed fourth bind retains its physical count; stage acceptance stays independent. -/
theorem at_passed (unknown : Word)
    (stage : Staging.CallBoundary.GuardAccepts (CallableLedger.frame sidecar) site.call ids (.closure function))
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
    {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope id callee ids metadata reasonAt lowered)
    {native : SourceCoreGeneralFunctions.CallableContext} (prepared : Prepared compiler native)
    (same : prepared.site = site) {budget : Nat} {actual : Environment} {value : Value} {finalStore : Store}
    (passed : CallableIndexedOwnedStoredIndirectApplicationPrefix.PassedAt (actual := actual)
      compiler prepared (same.symm ▸ dispatch) budget value finalStore) : AcceptedAt dispatch unknown := by
  exact accepted_at_row dispatch selected unknown stage passed.1
end Gate

section Arguments
variable {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)

/-- The owner is the one retained by the actual positive constructor.
Every dynamic input is at this same argument heap, store and current row. -/
inductive ArgumentAt (i : OrdinaryIndex compiled) (history : History i.code)
    {callerScope : SourceCoreLocalCell.Scope} {canonical : Environment}
    {heap : Dynamic.Heap} {store : Store}
    (state : State headers keys ⟨callerScope, i.mapping, i.world, heap, store, canonical⟩)
    (sources : List Dynamic.Value) (payloads : List Value) : Prop where
  | ordinary
      (owner : OwnedKey keys) (factory : FactoryMember root expressionSyntax i)
      (origin : SourceOrigin i.support history)
      (prefixContext : i.captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
        (values := .initial compiled.compatible.checked) i.support.caller)
      (globals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
        (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
        headers owner.key.locations 1 i.scope i.captured.canonical owner.key.frameLocation)
      (referenceIndex : i.code.referenceIndex = i.scope.length + 1 + compiled.indexed.base.globals.length)
      (typed : RuntimeValueHasType i.world (CallableIndexedLambdaValues.value i.code i.captured.embedding history.native i.capturedActual)
        (CallableContract.functionType i.code.receipt.parameterCore i.code.receipt.resultCore) compiled.indexed.layouts.definitions)
      (represented : CallableIndexedParameterMeaning.Arguments
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
          (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile))
        i.mapping i.world i.code.receipt.loweredParameters sources payloads)
      (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) i.mapping i.world heap store)
      (raw : CallableIndexedOwnedStoredClosureSourceArguments.SourceArguments i.function heap sources)
      (argumentsTyped : Dynamic.ValuesHaveTypes i.function.context heap sources i.support.body.types)
      (stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows state)
      (reference : i.captured.canonical[i.code.referenceIndex]? =
        some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation))
      (currentMetadata : Option MetadataState)
      (currentCarried : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
        (state.rows owner.position).authority.current (state.rows owner.position).authority.ghost currentMetadata)
      (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed compiled.indexed.ancestry.graph.inputs
        history.metadata i.code.descriptor.id = true) : ArgumentAt i history state sources payloads

/-- This projection reconstructs the same positive constructor, without extracting data from Prop. -/
theorem ArgumentAt.chosen {i : OrdinaryIndex compiled} {history : History i.code}
    {callerScope : SourceCoreLocalCell.Scope} {canonical : Environment} {heap : Dynamic.Heap} {store : Store}
    {state : State headers keys ⟨callerScope, i.mapping, i.world, heap, store, canonical⟩}
    {sources : List Dynamic.Value} {payloads : List Value}
    (receipt : ArgumentAt (registry := registry) (faults := faults) root expressionSyntax profile i history state sources payloads) :
    ChosenAt root expressionSyntax headers keys registry faults i history := by
  cases receipt with
  | ordinary owner factory origin prefixContext globals referenceIndex typed represented heaps raw argumentsTyped stable reference currentMetadata currentCarried allowed =>
    exact .ordinary owner factory origin prefixContext globals referenceIndex typed

/-- The chosen compiler factory remains attached to the literal future index. -/
theorem ArgumentAt.factory {i : OrdinaryIndex compiled} {history : History i.code}
    {callerScope : SourceCoreLocalCell.Scope} {canonical : Environment} {heap : Dynamic.Heap} {store : Store}
    {state : State headers keys ⟨callerScope, i.mapping, i.world, heap, store, canonical⟩}
    {sources : List Dynamic.Value} {payloads : List Value}
    (receipt : ArgumentAt (registry := registry) (faults := faults) root expressionSyntax profile i history state sources payloads) :
    FactoryMember root expressionSyntax i :=
  ChosenAt.factory root expressionSyntax (ArgumentAt.chosen root expressionSyntax profile receipt)
end Arguments

section ParentArguments
variable {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope id callee ids metadata reasonAt lowered)
  {native : SourceCoreGeneralFunctions.CallableContext} (prepared : Prepared compiler native)
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {calleeNode : ExpressionNode}
  {firstMap : LocationMap} {firstWorld : StoreTyping} {before : Dynamic.Heap} {firstStore : Store}
  {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
  (first : callerProtocol.State ⟨scope, firstMap, firstWorld, before, firstStore, canonical⟩)
  {sourceTypes : List TypeSystem.Ty} {calleeHeap : Dynamic.Heap} {calleeStore : Store} {calleeNative : Value}
  (i : OrdinaryIndex compiled) (history : History i.code)

/-- This is the original complete argument tuple with one additional positive receipt. -/
def QualifiedSuccessStep (budget : Nat) (value : Value) (finalStore : Store) : Prop :=
  ∃ nativeSize sourceSize sources payloads middle argumentStore finalMap finalWorld,
    EvaluationSize nativeSize (.unit :: calleeNative :: actual) calleeStore
      ((((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ).weakenAt 0).weakenAt 0)
      (.inRight .word (DataPatternValues.packValues payloads)) argumentStore ∧ nativeSize < budget ∧
    SourceExecutionSize.ExpressionsEvaluate (Program.ofChecked compiled.sourceProgram) sourceSize
      context evidence source environment calleeHeap ids sources middle ∧
    DataExpressionSequence.Values
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile))
      finalMap finalWorld sourceTypes (compiler.codes.map (·.type)) sources payloads ∧
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
      (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) finalMap finalWorld middle argumentStore ∧
    ∃ stepMaps : LocationMap.Extends i.mapping finalMap, ∃ stepWorlds : WorldExtends i.world finalWorld,
    AdministrativePreserved i.mapping calleeStore finalMap argumentStore ∧ Dynamic.HeapMetadataExtend calleeHeap middle ∧
    LocationMap.Extends firstMap finalMap ∧ WorldExtends firstWorld finalWorld ∧
    AdministrativePreserved firstMap firstStore finalMap argumentStore ∧ Dynamic.HeapMetadataExtend before middle ∧
    ∃ argumentState : callerProtocol.State ⟨scope, finalMap, finalWorld, middle, argumentStore, canonical⟩,
    callerProtocol.Relates first argumentState ∧ Admission bridge context argumentState ∧
    ∃ remainingSize,
    EvaluationSize remainingSize (DataPatternValues.packValues payloads :: .unit :: calleeNative :: actual) argumentStore
      (LanguageResult.bind compiler.resultType
        (CallableContract.dispatch prepared.site.gates .beforeApplication native.diagnostics.unknown (.second (.var 2)))
        (.apply (.second (.first (.var 3))) (.var 1))) value finalStore ∧ remainingSize < budget ∧
    ArgumentAt (registry := registry) (faults := faults) root expressionSyntax profile (extendIndex i stepMaps stepWorlds) history (bridge.pool argumentState) sources payloads

variable {sidecar : SourceCoreStageContracts.Sidecar}
  (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids (.closure i.function) calleeNative)
  (selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar prepared.site callee ids metadata compiler.original dispatch.row)
  (stage : Staging.CallBoundary.GuardAccepts (CallableLedger.frame sidecar) prepared.site.call ids (.closure i.function))
  (member : ChosenAt root expressionSyntax headers keys registry faults i history)
  {calleeSize : Nat}
  (calleeTrace : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) calleeSize
    context evidence source environment before callee (.closure i.function) calleeHeap)
  (post : CallableIndexedOwnedStoredFunctionModelReceipts.ValuePost (registry := registry)
    (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context) bridge
    (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)
    compiler first (.closure i.function) calleeHeap calleeNative calleeStore i.mapping i.world)
  (sameNative : calleeNative = CallableIndexedLambdaValues.value i.code i.captured.embedding history.native i.capturedActual)
  (parentTyped : ExpressionHasType source context id compiler.original.type)
  {certificate : GenericExpressionMeaning.Certificate}
  (tree : DataExpressionSequence.Tree source certificate scope ids sourceTypes compiler.codes)
  (unique : NodeOccurrencesUnique source)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
  (covers : evidence.Covers context) (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (admitted : Admission bridge context first)
  (actualFunctionType : policy.callables.functionType = CallableContract.functionType)

include member calleeTrace post sameNative parentTyped tree unique wellFormed runtime covers locals admitted actualFunctionType in
/-- The same successful argument witness supplies all invocation inputs.
This endpoint invokes neither a callee/argument semantic producer nor a body. -/
theorem at_successful_arguments (budget : Nat) {value : Value} {finalStore : Store}
    (original : CallableIndexedOwnedStoredIndirectArgumentPrefix.ForModel.SuccessPrefix
      (registry := registry) (context := context) (evidence := evidence)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeHeap := calleeHeap) (calleeNative := calleeNative) (calleeStore := calleeStore)
      bridge (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) compiler prepared first budget value finalStore)
    (step : CallableIndexedOwnedStoredFunctionModelReceipts.SuccessStep
      (registry := registry) (context := context) (evidence := evidence)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeHeap := calleeHeap) (calleeNative := calleeNative) (calleeStore := calleeStore)
      (calleeMap := i.mapping) (calleeWorld := i.world)
      bridge (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) compiler prepared first budget value finalStore)
    (passed : CallableIndexedOwnedStoredIndirectApplicationPrefix.PassedAt (actual := actual)
      compiler prepared dispatch budget value finalStore) :
    CallableIndexedOwnedStoredIndirectArgumentPrefix.ForModel.SuccessPrefix
      (registry := registry) (context := context) (evidence := evidence)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeHeap := calleeHeap) (calleeNative := calleeNative) (calleeStore := calleeStore)
      bridge (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) compiler prepared first budget value finalStore ∧
    CallableIndexedOwnedStoredFunctionModelReceipts.SuccessStep
      (registry := registry) (context := context) (evidence := evidence)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeHeap := calleeHeap) (calleeNative := calleeNative) (calleeStore := calleeStore)
      (calleeMap := i.mapping) (calleeWorld := i.world)
      bridge (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) compiler prepared first budget value finalStore ∧
    CallableIndexedOwnedStoredIndirectApplicationPrefix.PassedAt (actual := actual)
      compiler prepared dispatch budget value finalStore ∧
    QualifiedSuccessStep (registry := registry) (faults := faults) (context := context) (evidence := evidence)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeHeap := calleeHeap) (calleeNative := calleeNative) (calleeStore := calleeStore)
      root expressionSyntax bridge profile compiler prepared first i history budget value finalStore := by
  refine ⟨original, step, passed, ?_⟩
  obtain ⟨nativeSize, sourceSize, sources, payloads, middle, argumentStore, finalMap, finalWorld,
    nativeTrace, strict, argumentsTrace, represented, argumentHeaps, stepMaps, stepWorlds, stepFrame, stepMetadata,
    maps, worlds, frame, metadataExtended, ⟨argumentState, related, argumentAdmission⟩,
    ⟨remainingSize, remaining, remainingStrict⟩⟩ := step
  have future := ChosenAt.extend root expressionSyntax member stepMaps stepWorlds
  cases future with
  | ordinary owner factory origin prefixContext globals referenceIndex typed =>
    have parameters := CallableIndexedLambdaEntryPrefix.parameters (values := .initial compiled.compatible.checked) i.code
    have sourceBinders : i.code.receipt.loweredParameters.map (fun binding => binding.1.scheme.body) =
        i.function.parameters.map (fun binding => binding.scheme.body) := by
      simpa only [List.map_map, Function.comp_def] using
        (congrArg (List.map (fun binding : TypedBinder => binding.scheme.body)) parameters).symm
    have sourceBundle := CallableIndexedOwnedStoredSourceBundleReceipts.source_bundle_of_trace
      unique compiler.found compiler.originalForm parentTyped tree compiler.argumentCoercions
      wellFormed runtime covers locals admitted.heap calleeTrace sourceBinders
    have selectedType : RuntimeValueHasType finalWorld calleeNative
        (CallableContract.functionType i.code.receipt.parameterCore i.code.receipt.resultCore) compiled.indexed.layouts.definitions := by
      rw [sameNative]
      exact typed
    have actualType := post.2.1.runtime_hasType.type_eq
    have callableType := compiler.callableType
    rw [actualFunctionType] at callableType
    have nativeTypes := CallableIndexedOwnedStoredNativePackReceipts.callable_parameters
      (callableType.trans (actualType.symm.trans selectedType.type_eq))
    have nativeBundle := (CompatibleExpressionConstructorNativeTyping.packed_type compiler.codes).symm.trans
      (compiler.packedType.symm.trans nativeTypes.1)
    have nativeCount : (compiler.codes.map (·.type)).length = i.function.parameters.length := by
      simpa only [List.length_map] using compiler.ordered_children.1.symm.trans passed.1.symm
    have arity : sources.length = i.function.parameters.length := represented.length.1.symm.trans nativeCount
    have representedArguments := CallableIndexedOwnedPreparedOrdinaryLambdaInvocation.arguments_of_bundles
      (i.captured.extend stepMaps stepWorlds) i.code i.support i.prepared
      (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) profile represented arity.symm
      (by simpa only [sourceBinders] using sourceBundle) nativeBundle
    obtain ⟨parameter, sourceResult, rawTypes, _calleeTyping, _argumentsTyping, _application,
      _calleeTyped, _calleeHeapTyped, _calleeExtension, _calleeLocals, _rawTyped, _argumentHeapTyped,
      _heapExtension, _argumentLocals, _fullExtension, _rawArity, _packed, _packing, _packedTyped, raw⟩ :=
      CallableIndexedOwnedStoredCallSourcePrefix.from_admission_with_arity bridge first wellFormed runtime covers locals admitted
        unique compiler.found compiler.originalForm parentTyped compiler.argumentCoercions arity calleeTrace argumentsTrace
    have rawArguments : Dynamic.ValuesHaveTypes i.function.context middle sources i.support.body.types := by
      simpa only [Dynamic.MonoBindersExtend.bodyTypes_eq i.support.body.extended] using raw.arguments
    have reference : i.captured.canonical[i.code.referenceIndex]? =
        some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
      have actualReferenceIndex : i.code.referenceIndex =
          i.scope.length + 1 + compiled.indexed.base.globals.length := referenceIndex
      rw [actualReferenceIndex]
      exact globals.reference
    obtain ⟨currentMetadata, currentCarried⟩ := argumentAdmission.rows owner.position
    exact ⟨nativeSize, sourceSize, sources, payloads, middle, argumentStore, finalMap, finalWorld,
      nativeTrace, strict, argumentsTrace, represented, argumentHeaps, stepMaps, stepWorlds, stepFrame, stepMetadata,
      maps, worlds, frame, metadataExtended, argumentState, related, argumentAdmission,
      remainingSize, remaining, remainingStrict,
      .ordinary owner factory origin prefixContext globals referenceIndex typed representedArguments argumentHeaps
        raw rawArguments argumentAdmission.rows reference currentMetadata currentCarried
        (CallableIndexedLambdaTemplatePermission.lambda_allowed i.code history)⟩
end ParentArguments

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinarySelectedCallReceipts
