import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualInitializedClosureReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectCallBounds

/-! Positive ordinary or principal stored members construct their actual
callable origin and initialized callee post. The same selected carrier tag,
ordered argument receipts and genuine strict joint continuations feed the
original whole-call proofs. The member's hidden code is never reclassified. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualStoredMemberCallBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads
open CallableIndexedOwnedIndirectSourceAdapters
open CallableIndexedOwnedStoredClosureArgumentReceipts
open CallableIndexedOwnedContextualStoredClosureAssociationReceipts (Member)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

/-- Only the positive constructor is projected. Its actual Source authority,
code and history produce origin for exactly its retained native carrier. -/
theorem member_stage_origin {mapping : LocationMap} {world : StoreTyping}
    {function : Dynamic.Closure} {native : Core.Value}
    {bindings : List CallableIndexedParameterCertificates.Binding} {parameter result : Ty}
    (member : Member headers keys registry faults mapping world function native bindings parameter result) :
    CallableLedger.OriginRep compiled.indexed.base.plan compiled.indexed.ancestry.graph.inputs.callable.table
      (.closure function) native := by
  cases member with
  | ordinary _ captured code history support _ _ _ _ _ _ _ =>
    exact CallableIndexedOwnedOrdinaryLambdaSupport.Support.stage_origin captured code support history
  | principal _ captured code history support _ _ _ _ _ _ _ =>
    exact CallableIndexedOwnedMethodLambdaSupport.Support.stage_origin captured code support history

variable {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  (prepared : Prepared compiler compiled.indexed.ancestry.graph.inputs.callable)
  {certificate : GenericExpressionMeaning.Certificate}
  {mapping : LocationMap} {world : StoreTyping}
  {function : Dynamic.Closure} {captureScope : SourceCoreLocalCell.Scope} {capturedActual : Environment}
  (captured : Captures compiled.indexed mapping world captureScope function.captured capturedActual)
  (code : Code compiled.indexed function captureScope captured.administrative)
  (history : History code)
  (selected : CallableIndexedOwnedSelectedIndirectHeads.Selection (faults := faults)
    (certificate := certificate) compiler prepared code)

local notation "carrier" => CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual
local notation "functions" => CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions

section Static
variable {context : SourceSemantics.Context}
  (unique : NodeOccurrencesUnique source)
  (parentTyped : ExpressionHasType source context id compiler.original.type)

include selected unique parentTyped in
/-- The original Source row and selected physical vector retain ordered
binder equality, count and native packing independently of any body law. -/
theorem argument_rows :
    ExpressionsHaveTypes source context ids (code.receipt.loweredParameters.map (fun binding => binding.1.scheme.body)) ∧
    ids.length = code.receipt.loweredParameters.length ∧
    SourceCoreCompatibleCatalog.packTypes (compiler.codes.map (·.type)) =
      SourceCoreCompatibleCatalog.packTypes (code.receipt.loweredParameters.map Prod.snd) := by
  obtain ⟨_parameter, _result, _types, _calleeTyped, argumentsTyped, _application⟩ :=
    original_facts unique compiler.found compiler.originalForm parentTyped
  have row := CallableIndexedOwnedContextualInitializedClosureReceipts.source_types_at_tree
    unique selected.children argumentsTyped
  have counts := congrArg List.length selected.nativeTypes
  simp only [List.length_map] at counts
  exact ⟨row ▸ argumentsTyped, compiler.ordered_children.1.trans counts,
    congrArg SourceCoreCompatibleCatalog.packTypes selected.nativeTypes⟩

variable {sidecar : SourceCoreStageContracts.Sidecar}
  (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (sidecarSource : sidecar.source = source)
  (member : Member headers keys registry faults mapping world function
    (CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual)
    code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore)

include member caller in
/-- Caller preparation transports the retained positive member origin to the
same exact plan and table used by the original callsite. -/
theorem member_origin_at_caller :
    CallableLedger.OriginRep sidecar.plan prepared.site.table (.closure function) carrier := by
  have plan := (CallContractCertificates.sidecar_of_accepted caller).1
  simpa only [plan, prepared.table] using (member_stage_origin member)

include member selected caller sidecarSource in
/-- Original codebook rows construct Dispatch. Its actual carrier word fixes
only the descriptor ID, preserving the member's distinct hidden code. The
same selected first decision reconstructs the authentic Source guard. -/
theorem dispatch_at_member :
    ∃ _dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site
        prepared.site.call ids (.closure function) carrier,
      Staging.CallBoundary.GuardAccepts (CallableLedger.frame sidecar) prepared.site.call ids (.closure function) := by
  have stages := RecursiveNamedPreparedStageContracts.of_compiled compiled
    compiled.indexed.ancestry.graph.inputs.callableSelected
  have atSite := stages.accepted
  rw [← prepared.table] at atSite
  have contains : ContainsExpression sidecar.source prepared.site.call compiler.original := by
    rw [sidecarSource, prepared.call]
    exact lookupExpression?_sound compiler.found
  have rows := CallCodebookCertificates.rows_of_prepareWithProjection atSite caller contains compiler.originalForm
  have origin := member_origin_at_caller (prepared := prepared) (member := member) (caller := caller)
  have binding : ∃ contract, (CallableLedger.frame sidecar).Binds (.closure function) contract := by
    generalize carrier_eq : carrier = native at origin
    cases origin with
    | closure _ _ _ actualOrigin => exact ⟨_, actualOrigin.binds⟩
  obtain ⟨_contract, bound⟩ := binding
  obtain ⟨dispatch⟩ := CallableLedger.dispatch rows origin bound
  have descriptor : dispatch.contract = code.descriptor.id :=
    (Core.Value.word.inj (Core.Value.pair.inj dispatch.shape).2).symm
  have decision : CallableContract.decision prepared.site.gates .beforeArguments
      compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown dispatch.contract = none := by
    rw [descriptor]
    exact selected.stageAccepted
  have noReason := (prepared.site.decision_known .beforeArguments
    compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown
    dispatch.contract dispatch.row dispatch.found).symm.trans decision
  have passed : dispatch.row.beforeArguments = .ok () := by
    cases answer : dispatch.row.beforeArguments with
    | ok accepted => cases accepted; rfl
    | error error =>
      have rejected := SourceCoreCallableContracts.reason_rejected dispatch.row prepared.site.reasonAt
        .beforeArguments error answer
      rw [rejected] at noReason
      cases noReason
  exact ⟨dispatch, dispatch.accepted_iff.mp passed⟩
end Static

section LiveCallee
variable {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {heap : Dynamic.Heap} {store : Store} {location : Dynamic.Location}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
  {canonical actual : Environment} {ξ : Renaming}
  (stored : CallableIndexedOwnedContextualInitializedClosureReceipts.StoredAt headers keys registry faults
    mapping world heap store location function
    (CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual) code.receipt.loweredParameters
    code.receipt.parameterCore code.receipt.resultCore)
  {readFuel : Nat} {readReason : Word} {readCode : Expr}
  (read : CompatibleExpressionReads.Certificate readFuel (.initial compiled.compatible.checked)
    source scope callee readReason readCode)
  (sameCode : compiler.calleeCode.expression = readCode)
  (sameType : compiler.calleeCode.type = read.type)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  (binding : CompatibleExpressionReads.StaticBinding read context)
  (unique : NodeOccurrencesUnique source)
  (parentTyped : ExpressionHasType source context id compiler.original.type)
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    (CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile) mapping world heap store)
  (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (lookup : Dynamic.Environment.LooksUp environment read.binder location)
  (initial : callerProtocol.State ⟨scope, mapping, world, heap, store, canonical⟩)
  (admitted : Admission bridge context initial)

include stored read sameCode sameType extension binding unique parentTyped environments heaps locals agrees lookup admitted in
/-- The actual initialized read derives its own Source trace, full ValuePost
and retained positive association at the identical caller tuple. -/
theorem callee_at_stored :
    ∃ sourceSize,
      SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) sourceSize
        context evidence source environment heap callee (.closure function) heap ∧
      CallableIndexedOwnedStoredFunctionModelReceipts.ValuePost (registry := registry)
        (actual := actual) (ξ := ξ) (calleeNode := read.node) (context := context)
        bridge functions compiler initial (.closure function) heap carrier store mapping world ∧
      CallableIndexedOwnedStoredClosureInvocation.Association headers keys registry faults mapping world
        function carrier code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore := by
  obtain ⟨_parameter, _result, _types, calleeTyped, _argumentsTyped, _application⟩ :=
    original_facts unique compiler.found compiler.originalForm parentTyped
  have reported := CallableIndexedOwnedContextualInitializedClosureReceipts.reported_type_at
    unique read.metadata.found calleeTyped
  have readTyped : ExpressionHasType source context callee read.node.type := by
    rw [reported]
    exact calleeTyped
  obtain ⟨sourceSize, sourceTrace, post, association, _selection, _stored⟩ :=
    CallableIndexedOwnedContextualInitializedClosureReceipts.callee_post
      (certificate := read) (bridge := bridge) (compiler := compiler) (initial := initial) (evidence := evidence)
      (profile := profile) (extension := extension) (binding := binding) (unique := unique)
      (environments := environments) (heaps := heaps) (locals := locals) (agrees := agrees)
      (stored := stored) (lookup := lookup) (sameCode := sameCode) (sameNode := rfl)
      (sameType := sameType) (sourceTyped := readTyped) (admitted := admitted)
  exact ⟨sourceSize, sourceTrace, post, association⟩

variable (parent : SourceParent compiler)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
  (covers : evidence.Covers context)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  {sidecar : SourceCoreStageContracts.Sidecar}
  (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (sidecarSource : sidecar.source = source)
  {certificates : Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}

include selected stored read sameCode sameType extension binding unique parentTyped environments heaps locals agrees lookup admitted
  parent wellFormed runtime covers typed caller sidecarSource in
/-- Both positive member alternatives feed one original whole preservation
proof at their actual callee post. Strict argument and body continuations
remain universal inputs; the returned pool, effects and admission stay causal. -/
theorem preserves_at_stored (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      bridge model context evidence source certificate faults size)
    (below : CallableIndexedOwnedExtendedJointReadyContinuations.PreservingBelow
      (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax) functions wellFormed budget)
    {argumentsSize callSize : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (suffix : SourceSuffix (Program.ofChecked compiled.sourceProgram) context evidence source environment heap ids function
      argumentsSize callSize outcome after)
    (argumentsWithin : argumentsSize ≤ budget) (callWithin : callSize ≤ budget) :
    ∃ sourceSize value finalStore finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize context evidence source
        environment heap id outcome after ∧
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      CallableIndexedOwnedStoredIndirectCallBounds.ResultAt (registry := registry) (faults := faults) (context := context)
        bridge profile compiler initial outcome after value finalStore finalMap finalWorld := by
  obtain ⟨_sourceSize, sourceTrace, post, association⟩ := callee_at_stored
    (bridge := bridge) (profile := profile) (compiler := compiler)
    (stored := stored) (read := read) (sameCode := sameCode) (sameType := sameType) (extension := extension)
    (binding := binding) (unique := unique) (parentTyped := parentTyped) (environments := environments)
    (heaps := heaps) (locals := locals) (agrees := agrees) (lookup := lookup)
    (initial := initial) (admitted := admitted)
  obtain ⟨calleeEvaluation, _represented, calleeHeaps, maps, worlds, frame, metadata,
    reached, related, _calleeAdmission⟩ := post
  obtain ⟨_sourceArguments, binderCount, nativeBundle⟩ := argument_rows
    (compiler := compiler) (prepared := prepared) (code := code) (selected := selected)
    (unique := unique) (parentTyped := parentTyped)
  obtain ⟨dispatch, accepted⟩ := dispatch_at_member
    (compiler := compiler) (prepared := prepared) (captured := captured) (code := code)
    (history := history) (selected := selected) (member := stored.1)
    (caller := caller) (sidecarSource := sidecarSource)
  have stages := RecursiveNamedPreparedStageContracts.of_compiled compiled
    compiled.indexed.ancestry.graph.inputs.callableSelected
  exact CallableIndexedOwnedStoredIndirectCallBounds.preserves_selected
    bridge profile compiler prepared parent selected.children unique parentTyped wellFormed runtime covers
    environments locals agrees typed initial admitted reached related maps worlds frame metadata
    association calleeHeaps binderCount rfl nativeBundle selected.rawResult selected.nativeResult
    stages caller sidecarSource dispatch accepted sourceTrace calleeEvaluation
    budget children below suffix argumentsWithin callWithin

include selected stored read sameCode sameType extension binding unique parentTyped environments heaps locals agrees lookup admitted
  parent wellFormed runtime covers typed caller sidecarSource in
/-- Finite native whole-call reflection retains its actual application grade
and returns an independent Source grade with the same caller post. -/
theorem reflects_at_stored (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      bridge model context evidence source certificate faults size)
    (below : CallableIndexedOwnedExtendedJointReadyContinuations.ReflectingBelow
      (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax) functions wellFormed budget)
    {size : Nat} {value : Core.Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize context evidence source
        environment heap id outcome after ∧
      CallableIndexedOwnedStoredIndirectCallBounds.ResultAt (registry := registry) (faults := faults) (context := context)
        bridge profile compiler initial outcome after value finalStore finalMap finalWorld := by
  obtain ⟨_sourceSize, sourceTrace, post, association⟩ := callee_at_stored
    (bridge := bridge) (profile := profile) (compiler := compiler)
    (stored := stored) (read := read) (sameCode := sameCode) (sameType := sameType) (extension := extension)
    (binding := binding) (unique := unique) (parentTyped := parentTyped) (environments := environments)
    (heaps := heaps) (locals := locals) (agrees := agrees) (lookup := lookup)
    (initial := initial) (admitted := admitted)
  obtain ⟨calleeEvaluation, _represented, calleeHeaps, maps, worlds, frame, metadata,
    reached, related, _calleeAdmission⟩ := post
  obtain ⟨_sourceArguments, binderCount, nativeBundle⟩ := argument_rows
    (compiler := compiler) (prepared := prepared) (code := code) (selected := selected)
    (unique := unique) (parentTyped := parentTyped)
  obtain ⟨dispatch, accepted⟩ := dispatch_at_member
    (compiler := compiler) (prepared := prepared) (captured := captured) (code := code)
    (history := history) (selected := selected) (member := stored.1)
    (caller := caller) (sidecarSource := sidecarSource)
  have stages := RecursiveNamedPreparedStageContracts.of_compiled compiled
    compiled.indexed.ancestry.graph.inputs.callableSelected
  exact CallableIndexedOwnedStoredIndirectCallBounds.reflects_selected
    bridge profile compiler prepared parent selected.children unique parentTyped wellFormed runtime covers
    environments locals agrees typed initial admitted reached related maps worlds frame metadata
    association calleeHeaps binderCount rfl nativeBundle selected.rawResult selected.nativeResult
    stages caller sidecarSource dispatch accepted sourceTrace calleeEvaluation
    budget children below completed within
end LiveCallee
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualStoredMemberCallBounds
