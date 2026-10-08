import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryLambdaInvocation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinarySelectedCallReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStoredIndirectApplication

/-! Accepted stored parents consume the actual chosen callee and current
argument tuple. The body continuation is built internally; the original
invocation restores once and the caller protocol receives that same pool. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryAcceptedStoredParent
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedNamedGeneration
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters
open CallableIndexedOwnedIndirectExpressionHeads
open CallableIndexedOwnedPreparedRuntimeFamilyMembers (OrdinaryIndex)
open CallableIndexedOwnedContextualCompilerPolicyProfiles (RootPolicyReceipt)
open CallableIndexedOwnedPreparedMixedBodyCompilerFactory
open CallableIndexedOwnedPreparedMixedBodySiteInputs
open CallableIndexedOwnedChosenOrdinaryFormedMembers (FactoryMember)
open CallableIndexedOwnedChosenOrdinaryStoredMembers (ChosenAt extendIndex)
open CallableIndexedOwnedChosenOrdinaryLambdaInvocation (ChosenFor Validity)
open CallableIndexedOwnedChosenOrdinarySelectedCallReceipts (ArgumentAt)
open RecursiveNamedCatalogInvocationBounds (Below)
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {owning : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {rootCompilation : Compilation compiled.indexed owning.named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) owning.named diagnostics namedCode rootCompilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  (expressionSyntax : TypedSource → ExpressionId → Prop)

variable (i : OrdinaryIndex compiled) (history : History i.code)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (member : ChosenFor (headers := headers) root expressionSyntax owner i history)

include member in
/-- Only proof facets extend; the same known owner, Code, factory and history remain. -/
theorem extend_chosen {futureMap : LocationMap} {futureWorld : StoreTyping}
    (maps : LocationMap.Extends i.mapping futureMap) (worlds : WorldExtends i.world futureWorld) :
    ChosenFor (headers := headers) root expressionSyntax owner (extendIndex i maps worlds) history := by
  obtain ⟨factory, origin, prefixContext, globals, referenceIndex, typed⟩ := member
  exact ⟨FactoryMember.extend root expressionSyntax factory maps worlds,
    origin, prefixContext, globals, referenceIndex, typed.weaken worlds⟩

include member in
/-- This is the same positive constructor, with no relation or value inverse. -/
theorem chosen_at : ChosenAt root expressionSyntax headers keys registry faults i history :=
  .ordinary owner member.factory member.origin member.prefixContext member.globals member.referenceIndex member.typed

/-- Actual static domains and diagnostic policies of this literal selected Support. -/
structure RuntimeInputs where
  domains : ∀ context, Validity i context → ∀ childScope,
    DomainAt root expressionSyntax i.support.body.readFuel context i.function.evidence childScope headers
  wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)
  sameLayouts : ∀ header, header ∈ headers → header.layouts = compiled.indexed.layouts
  complete : RecursiveNamedCatalogNativeContexts.Complete (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers
  globals : owning.globals = compiled.indexed.base.globals.length
  slots : ∀ header, header ∈ headers → header.slot < compiled.indexed.base.globals.length
  prefixZero : owner.key.capturePrefix = 0
  noIndirect : CallableIndexedOwnedPreparedMixedBodyRuntimeBounds.NoIndirect (CallableIndexedNamedGeneration.source owning.named)
  extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry
  identities : Dynamic.Value → Word → Prop
  faithful : DataEquality.IdentityFaithful identities
  observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) identities
  uninitialized : ∀ id location, faults (.uninitializedLocation location) (rootReasonAt id)
  missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((rootReasonAt id).add tag)
  table : SourceCoreFaultSites.Table
  rebuilt : i.support.issued.diagnostics.tableForRegistry registry extension = .ok table
  operandIncluded : ∀ reason token, GenericAssignmentDiagnostics.OperandRep i.support.issued.assignments reason token → faults reason token
  unaryIncluded : ∀ reason token, EmittedDiagnosticTokenPlan.UnaryRep i.support.issued.assignments reason token → faults reason token
  interprets : ∀ context, Validity i context →
    CallableIndexedOwnedContextualLambdaAssignmentReadiness.ReachedInterpretations
      (context := context) (certificates := i.support.certificates i.support.body.readFuel i.function.source)
      (administrative := i.captured.administrative)
      (factory := CallableIndexedOwnedContextualLambdaJointStaticReceipts.trackedFactory i.support.diagnosticPolicy i.function.source i.support.issued.invalidOperand)
      (faults := faults) (registry := registry) i.support.issued
      (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner owning)
      (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) table

variable (inputs : RuntimeInputs (headers := headers) (registry := registry) (faults := faults) root expressionSyntax i profile owner)

/-- Map/world extension retains these exact static inputs and their actual factory. -/
def RuntimeInputs.extend {futureMap : LocationMap} {futureWorld : StoreTyping}
    (maps : LocationMap.Extends i.mapping futureMap) (worlds : WorldExtends i.world futureWorld) :
    RuntimeInputs (headers := headers) (registry := registry) (faults := faults)
      root expressionSyntax (extendIndex i maps worlds) profile owner := {
  domains := inputs.domains, wellFormed := inputs.wellFormed, sameLayouts := inputs.sameLayouts
  complete := inputs.complete, globals := inputs.globals, slots := inputs.slots, prefixZero := inputs.prefixZero
  noIndirect := inputs.noIndirect, extension := inputs.extension, identities := inputs.identities, faithful := inputs.faithful
  observations := inputs.observations, uninitialized := inputs.uninitialized, missing := inputs.missing
  table := inputs.table, rebuilt := inputs.rebuilt, operandIncluded := inputs.operandIncluded
  unaryIncluded := inputs.unaryIncluded, interprets := inputs.interprets }

variable {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope id callee ids metadata reasonAt lowered)
  {native : SourceCoreGeneralFunctions.CallableContext} (prepared : Prepared compiler native)
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {calleeNode : ExpressionNode}
  {firstMap : LocationMap} {firstWorld : StoreTyping} {before : Dynamic.Heap} {firstStore : Store}
  {administrative actualContext : Core.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
  (initial : callerProtocol.State ⟨scope, firstMap, firstWorld, before, firstStore, canonical⟩)
  {sourceTypes : List TypeSystem.Ty} {calleeHeap : Dynamic.Heap} {calleeStore : Store} {calleeNative : Value}
  {calleeSize : Nat}
  (calleeTrace : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) calleeSize
    context evidence source environment before callee (.closure i.function) calleeHeap)
  (post : CallableIndexedOwnedStoredFunctionModelReceipts.ValuePost (registry := registry)
    (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context) bridge
    (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)
    compiler initial (.closure i.function) calleeHeap calleeNative calleeStore i.mapping i.world)
  (sameNative : calleeNative = value i.code i.captured.embedding history.native i.capturedActual)
  (parentTyped : ExpressionHasType source context id compiler.original.type)
  {certificate : GenericExpressionMeaning.Certificate}
  (tree : DataExpressionSequence.Tree source certificate scope ids sourceTypes compiler.codes)
  (unique : NodeOccurrencesUnique source) (parent : SourceParent compiler)
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
  (covers : evidence.Covers context) (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (admitted : Admission bridge context initial)
  (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
  {sidecar : SourceCoreStageContracts.Sidecar}
  (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids (.closure i.function) calleeNative)
  (selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar prepared.site callee ids metadata compiler.original dispatch.row)
  (accepted : CallableIndexedOwnedChosenOrdinarySelectedCallReceipts.AcceptedAt dispatch native.diagnostics.unknown)

include member post actualFunctionType sameNative in
/-- The actual native callable type fixes only the genuine parameter and result projections. -/
theorem native_bundle :
    SourceCoreCompatibleCatalog.packTypes (compiler.codes.map (·.type)) = i.code.receipt.parameterCore ∧
    compiler.resultType = i.code.receipt.resultCore := by
  have nativeTyped : RuntimeValueHasType i.world calleeNative
      (CallableContract.functionType i.code.receipt.parameterCore i.code.receipt.resultCore) compiled.indexed.layouts.definitions := by
    rw [sameNative]
    exact member.typed
  have actualType := post.2.1.runtime_hasType.type_eq
  have callableType := compiler.callableType
  rw [actualFunctionType] at callableType
  have fields := CallableIndexedOwnedStoredNativePackReceipts.callable_parameters
    (callableType.trans (actualType.symm.trans nativeTyped.type_eq))
  exact ⟨(CompatibleExpressionConstructorNativeTyping.packed_type compiler.codes).symm.trans
    (compiler.packedType.symm.trans fields.1), fields.2⟩

include calleeTrace parentTyped tree unique runtime covers locals admitted inputs in
/-- The independently typed Source row supplies this exact original parameter bundle. -/
theorem source_bundle :
    TypeSystem.Ty.productMany sourceTypes = TypeSystem.Ty.productMany (i.code.receipt.loweredParameters.map (fun binding => binding.1.scheme.body)) := by
  have parameters := CallableIndexedLambdaEntryPrefix.parameters (values := .initial compiled.compatible.checked) i.code
  have sourceBinders : i.code.receipt.loweredParameters.map (fun binding => binding.1.scheme.body) =
      i.function.parameters.map (fun binding => binding.scheme.body) := by
    simpa only [List.map_map, Function.comp_def] using
      (congrArg (List.map (fun binding : TypedBinder => binding.scheme.body)) parameters).symm
  exact CallableIndexedOwnedStoredSourceBundleReceipts.source_bundle_of_trace
    unique compiler.found compiler.originalForm parentTyped tree compiler.argumentCoercions
    inputs.wellFormed runtime covers locals admitted.heap calleeTrace sourceBinders

include calleeTrace parentTyped unique runtime covers locals admitted inputs parent in
/-- Empty original output coercions preserve the real Source result type. -/
theorem raw_result : SourceCoreRawMetadata.runtimeType compiler.original.type = SourceCoreRawMetadata.runtimeType i.function.resultType :=
  congrArg SourceCoreRawMetadata.runtimeType
    (CallableIndexedOwnedStoredSourceResultReceipts.source_result_of_trace
      unique compiler.found compiler.originalForm parentTyped parent.coercions
      inputs.wellFormed runtime covers locals admitted.heap calleeTrace)


local notation "functions" => CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions

variable
  (owners : ((Program.ofChecked compiled.sourceProgram).functions.map (fun definition => definition.body.owner)).Nodup)
  (idsUnique : ∀ context, Validity i context → RequirementIdsUnique context)

include member inputs calleeTrace post sameNative parentTyped tree unique runtime covers locals admitted
  actualFunctionType accepted owners idsUnique in
/-- The parent core supplies its actual argument state. This finite leaf
constructs raw arguments and the chosen continuation internally at that state. -/
theorem application_preserves (outer budget : Nat) (withinOuter : budget ≤ outer)
    (ih : ∀ index, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults) functions owner index))
    {suffixArgumentsSize suffixCallSize : Nat} {suffixOutcome : Dynamic.ExpressionOutcome} {suffixAfter : Dynamic.Heap}
    (suffix : SourceSuffix (Program.ofChecked compiled.sourceProgram) context evidence source environment calleeHeap ids i.function
      suffixArgumentsSize suffixCallSize suffixOutcome suffixAfter) :
    CallableIndexedOwnedStoredIndirectCallBounds.ForModel.ApplicationPreserves (registry := registry) (faults := faults)
      bridge functions compiler prepared (native := native) (context := context) (evidence := evidence)
      (environment := environment) (scope := scope) (canonical := canonical) (calleeHeap := calleeHeap)
      (mapping := i.mapping) (world := i.world) (store := calleeStore) (function := i.function)
      (calleeNative := calleeNative) (sourceTypes := sourceTypes) (resultCore := i.code.receipt.resultCore)
      (dispatch := dispatch) budget suffix := by
  have nativeFields := native_bundle root expressionSyntax i history profile owner member bridge compiler initial post sameNative actualFunctionType
  have rawBundle := source_bundle root expressionSyntax i profile owner inputs bridge compiler initial calleeTrace parentTyped tree unique runtime covers locals admitted
  have parameters := CallableIndexedLambdaEntryPrefix.parameters (values := .initial compiled.compatible.checked) i.code
  have sourceBinders : i.code.receipt.loweredParameters.map (fun binding => binding.1.scheme.body) =
      i.function.parameters.map (fun binding => binding.scheme.body) := by
    simpa only [List.map_map, Function.comp_def] using
      (congrArg (List.map (fun binding : TypedBinder => binding.scheme.body)) parameters).symm
  intro middleMap middleWorld middle middleStore arguments payloads types parameter sourceResult packed
    argumentState argumentAdmission maps worlds frame metadata calleeTyped heapExtension represented argumentHeaps
    rawTyped packing bundle argumentsSize callSize outcome after argumentsTrace called _calledSuffix callWithin
  have nativeCount : (compiler.codes.map (·.type)).length = i.function.parameters.length := by
    simpa only [List.length_map] using compiler.ordered_children.1.symm.trans accepted.physical.symm
  have arity : arguments.length = i.function.parameters.length := represented.length.1.symm.trans nativeCount
  let future := extendIndex i maps worlds
  have futureMember := extend_chosen root expressionSyntax i history owner member maps worlds
  have actualArguments := CallableIndexedOwnedPreparedOrdinaryLambdaInvocation.arguments_of_bundles
    future.captured future.code future.support future.prepared functions profile represented arity.symm
    (by simpa only [sourceBinders, future, extendIndex] using rawBundle) nativeFields.1
  have raw := CallableIndexedOwnedStoredClosureSourceArguments.at_arguments runtime
    (calleeTyped.mono heapExtension) argumentAdmission.heap rawTyped packing bundle arity
  have actualRaw : Dynamic.ValuesHaveTypes i.function.context middle arguments i.support.body.types := by
    simpa only [Dynamic.MonoBindersExtend.bodyTypes_eq i.support.body.extended] using raw.arguments
  obtain ⟨value, finalStore, finalMap, finalWorld, application, resultRep, finalHeaps,
    lastMaps, lastWorlds, lastFrame, lastMetadata, baseReached, baseRelated⟩ :=
    CallableIndexedOwnedChosenOrdinaryLambdaInvocation.application_preserves_chosen
      root expressionSyntax future history profile owner futureMember
      inputs.domains inputs.wellFormed inputs.sameLayouts owners idsUnique inputs.complete inputs.globals inputs.slots
      inputs.prefixZero inputs.noIndirect inputs.extension inputs.faithful inputs.observations inputs.uninitialized inputs.missing
      inputs.rebuilt inputs.operandIncluded inputs.unaryIncluded inputs.interprets
      (bridge.pool argumentState) raw.heaps actualRaw argumentAdmission.rows actualArguments argumentHeaps raw.captures
      outer budget withinOuter ih called callWithin
  obtain ⟨returned, _samePool, related⟩ := bridge.restore argumentState baseReached lastMaps lastWorlds lastFrame lastMetadata baseRelated
  refine ⟨value, finalStore, finalMap, finalWorld, accepted.beforeApplication, ?_, resultRep, finalHeaps,
    lastMaps, lastWorlds, lastFrame, lastMetadata, returned, related⟩
  simpa only [future, extendIndex, Captures.extend, sameNative] using application

variable
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    firstMap firstWorld administrative scope environment canonical compiled.indexed.layouts.definitions)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes firstWorld actual actualContext compiled.indexed.layouts.definitions)

include member inputs calleeTrace post sameNative parentTyped tree unique parent runtime covers locals admitted
  actualFunctionType selected accepted owners idsUnique environments agrees typed in
/-- Ordered arguments and the whole Source parent use the original core once;
the chosen application leaf is constructed internally rather than supplied. -/
theorem preserves_accepted (outer budget : Nat) (withinOuter : budget ≤ outer)
    (ih : ∀ index, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults) functions owner index))
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      bridge model context evidence source certificate faults size)
    {argumentsSize callSize : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (suffix : SourceSuffix (Program.ofChecked compiled.sourceProgram) context evidence source environment calleeHeap ids i.function
      argumentsSize callSize outcome after)
    (argumentsWithin : argumentsSize ≤ budget) (callWithin : callSize ≤ budget) :
    ∃ sourceSize value finalStore finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize context evidence source
        environment before id outcome after ∧
      Evaluates actual firstStore (lowered.expression.rename ξ) value finalStore ∧
      CallableIndexedOwnedStoredFunctionModelReceipts.ParentResultAt (registry := registry) (faults := faults)
        (context := context) bridge functions compiler initial outcome after value finalStore finalMap finalWorld := by
  obtain ⟨calleeState, calleeRelated, calleeAdmission⟩ := post.2.2.2.2.2.2.2
  have calleeHeaps := post.2.2.1
  have calleeMaps := post.2.2.2.1
  have calleeWorlds := post.2.2.2.2.1
  have calleeFrame := post.2.2.2.2.2.1
  have calleeMetadata := post.2.2.2.2.2.2.1
  have nativeTyped : RuntimeValueHasType i.world calleeNative
      (CallableContract.functionType i.code.receipt.parameterCore i.code.receipt.resultCore) compiled.indexed.layouts.definitions := by
    rw [sameNative]; exact member.typed
  have rawResult := raw_result root expressionSyntax i profile owner inputs bridge compiler initial calleeTrace parentTyped unique parent runtime covers locals admitted
  have nativeFields := native_bundle root expressionSyntax i history profile owner member bridge compiler initial post sameNative actualFunctionType
  have leaf : CallableIndexedOwnedStoredIndirectCallBounds.ForModel.ApplicationPreserves (registry := registry) (faults := faults)
      bridge functions compiler prepared (native := native) (context := context) (evidence := evidence)
      (environment := environment) (scope := scope) (canonical := canonical) (calleeHeap := calleeHeap)
      (mapping := i.mapping) (world := i.world) (store := calleeStore) (function := i.function)
      (calleeNative := calleeNative) (sourceTypes := sourceTypes) (resultCore := i.code.receipt.resultCore)
      (dispatch := dispatch) budget suffix := application_preserves root expressionSyntax i history profile owner member inputs bridge compiler prepared initial
    calleeTrace post sameNative parentTyped tree unique runtime covers locals admitted actualFunctionType dispatch accepted owners idsUnique
    outer budget withinOuter ih suffix
  exact CallableIndexedOwnedStoredIndirectCallBounds.ForModel.preserves_selected_with_application
    bridge functions compiler prepared parent tree unique parentTyped inputs.wellFormed runtime covers environments locals agrees typed
    initial admitted calleeState calleeRelated calleeMaps calleeWorlds calleeFrame calleeMetadata nativeTyped calleeHeaps
    rawResult nativeFields.2 dispatch accepted.stage calleeTrace post.1 selected budget children suffix argumentsWithin callWithin leaf

/-- The complete original accepted application receipts remain alongside the
independent Source grade, staged outcome and exact returned caller pool. -/
def ReflectedAt (budget : Nat) (value : Value) (finalStore : Store) : Prop :=
  CallableIndexedOwnedPreparedStoredIndirectApplication.ResultAt
    (registry := registry) (faults := faults) (context := context) (evidence := evidence)
    (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
    (calleeHeap := calleeHeap) (calleeNative := calleeNative) (calleeStore := calleeStore)
    (calleeMap := i.mapping) (calleeWorld := i.world) (sidecar := sidecar)
    bridge profile compiler prepared initial dispatch budget value finalStore

include member inputs calleeTrace post sameNative parentTyped tree unique parent runtime covers locals admitted
  actualFunctionType accepted in
/-- Reflection consumes the authentic whole fourth bind at its own argument
store, then the same chosen application and finite caller-pool lift once. -/
theorem reflects_accepted (outer budget : Nat) (withinOuter : budget ≤ outer)
    (ih : ∀ index, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults) functions owner index))
    {value : Value} {finalStore : Store}
    (original : CallableIndexedOwnedStoredIndirectArgumentPrefix.ForModel.SuccessPrefix
      (registry := registry) (context := context) (evidence := evidence)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeHeap := calleeHeap) (calleeNative := calleeNative) (calleeStore := calleeStore)
      bridge functions compiler prepared initial budget value finalStore)
    (step : CallableIndexedOwnedStoredFunctionModelReceipts.SuccessStep
      (registry := registry) (context := context) (evidence := evidence)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeHeap := calleeHeap) (calleeNative := calleeNative) (calleeStore := calleeStore)
      (calleeMap := i.mapping) (calleeWorld := i.world)
      bridge functions compiler prepared initial budget value finalStore)
    (passed : CallableIndexedOwnedStoredIndirectApplicationPrefix.PassedAt (actual := actual)
      compiler prepared dispatch budget value finalStore) :
    ReflectedAt (registry := registry) (faults := faults) (context := context) (evidence := evidence)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeHeap := calleeHeap) (calleeNative := calleeNative) (calleeStore := calleeStore)
      i profile bridge compiler prepared initial dispatch budget value finalStore := by
  obtain ⟨_original, _step, _passed, qualified⟩ :=
    CallableIndexedOwnedChosenOrdinarySelectedCallReceipts.at_successful_arguments
      root expressionSyntax bridge profile compiler prepared initial i history dispatch
      (chosen_at root expressionSyntax i history owner member) calleeTrace post sameNative parentTyped tree unique
      inputs.wellFormed runtime covers locals admitted actualFunctionType budget original step passed
  refine ⟨original, step, passed, ?_⟩
  obtain ⟨nativeSize, argumentsSize, arguments, payloads, middle, argumentStore, middleMap, middleWorld,
    _argumentsNative, _argumentsStrict, argumentsTrace, represented, argumentHeaps, stepMaps, stepWorlds, _stepFrame, _stepMetadata,
    maps, worlds, frame, metadataExtended, argumentState, related, argumentAdmission,
    remainingSize, remaining, remainingStrict, argumentReceipt⟩ := qualified
  cases argumentReceipt with
  | ordinary _owner _factory _origin _prefixContext _globals _referenceIndex _typed actualArguments _heaps raw actualRaw stable _reference _currentMetadata _currentCarried _allowed =>
    have read : Evaluates (DataPatternValues.packValues payloads :: .unit :: calleeNative :: actual) argumentStore
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
      let future := extendIndex i stepMaps stepWorlds
      have futureMember := extend_chosen root expressionSyntax i history owner member stepMaps stepWorlds
      obtain ⟨callSize, outcome, after, finalMap, finalWorld, called, resultRep, finalHeaps,
        lastMaps, lastWorlds, lastFrame, lastMetadata, baseReached, baseRelated⟩ :=
        CallableIndexedOwnedChosenOrdinaryLambdaInvocation.application_reflects_chosen
          root expressionSyntax future history profile owner futureMember
          inputs.domains inputs.wellFormed inputs.sameLayouts inputs.complete inputs.globals inputs.slots
          inputs.prefixZero inputs.noIndirect inputs.extension inputs.faithful inputs.observations inputs.uninitialized inputs.missing
          inputs.rebuilt inputs.operandIncluded inputs.unaryIncluded inputs.interprets
          (bridge.pool argumentState) raw.heaps actualRaw stable actualArguments argumentHeaps raw.captures
          outer budget withinOuter ih payloadTrace (Nat.le_of_lt applicationStrict)
      obtain ⟨returned, _samePool, lastRelated⟩ := bridge.restore argumentState baseReached
        lastMaps lastWorlds lastFrame lastMetadata baseRelated
      have nativeCount : (compiler.codes.map (·.type)).length = i.function.parameters.length := by
        simpa only [List.length_map] using compiler.ordered_children.1.symm.trans passed.1.symm
      have arity : arguments.length = i.function.parameters.length := represented.length.1.symm.trans nativeCount
      obtain ⟨parameter, sourceResult, rawTypes, _calleeTyping, argumentsTyping, application,
        _calleeTyped, calleeHeapTyped, _calleeExtension, calleeLocals, _rawTyped, _argumentHeapTyped,
        _heapExtension, _argumentLocals, _fullExtension, _rawArity, packed, packing, _packedTyped, _raw⟩ :=
        CallableIndexedOwnedStoredCallSourcePrefix.from_admission_with_arity bridge initial inputs.wellFormed runtime covers locals admitted
          unique compiler.found compiler.originalForm parentTyped compiler.argumentCoercions arity
          calleeTrace argumentsTrace
      have count : rawTypes.length = metadata.argumentCount := by
        cases application with | intro count _ _ _ => exact count.symm
      have argumentsCount := arguments_count_of_source_admission inputs.wellFormed runtime covers calleeLocals calleeHeapTyped
        argumentsTyping count argumentsTrace
      obtain ⟨sourceSize, sourceParent⟩ := SourceSuffix.to_expression compiler.found compiler.originalForm
        parent.requirements parent.coercions compiler.argumentCoercions parent.arity inputs.wellFormed runtime covers
        calleeLocals calleeHeapTyped argumentsTyping count calleeTrace (SourceSuffix.called argumentsTrace called)
      have coercions : Dynamic.CoercionPathExecutes (Program.ofChecked compiled.sourceProgram) context evidence
          middle metadata.argumentCoercions packed packed middle := by
        rw [compiler.argumentCoercions]; exact .nil
      have staged : Staging.CallBoundary.Executes (Program.ofChecked compiled.sourceProgram) (CallableLedger.frame sidecar)
          context evidence source environment before id callee ids metadata
          (CallableIndexedOwnedPreparedStoredIndirectApplication.boundaryOutcome outcome) after := by
        cases called with
        | value applied =>
          exact .applied calleeTrace.sound (by simpa only [prepared.call] using accepted.stage)
            argumentsTrace.sound packing coercions packing parent.arity argumentsCount applied.sound
        | fault failed =>
          exact .applicationFault calleeTrace.sound (by simpa only [prepared.call] using accepted.stage)
            argumentsTrace.sound packing coercions packing parent.arity argumentsCount failed.sound
      have rawResult := raw_result root expressionSyntax i profile owner inputs bridge compiler initial calleeTrace parentTyped unique parent runtime covers locals admitted
      have nativeFields := native_bundle root expressionSyntax i history profile owner member bridge compiler initial post sameNative actualFunctionType
      have parentRep := CallableIndexedOwnedStoredIndirectCallBounds.ForModel.parent_result
        functions compiler rawResult nativeFields.2 resultRep
      exact ⟨sourceSize, outcome, after, finalMap, finalWorld, sourceParent, staged, parentRep, finalHeaps,
        maps.trans lastMaps, worlds.trans lastWorlds, frame.trans lastFrame, metadataExtended.trans lastMetadata,
        returned, callerProtocol.trans related lastRelated,
        after_expression_sized initial returned admitted inputs.wellFormed runtime covers locals parentTyped sourceParent
          (frame.trans lastFrame)⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryAcceptedStoredParent
