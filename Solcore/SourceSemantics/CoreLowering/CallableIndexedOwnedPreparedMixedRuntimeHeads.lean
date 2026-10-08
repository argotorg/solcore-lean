import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedMixedCompilerHeads
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedExpressionRuntimeBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicPreparedNamedFamilyClosure
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryLambdaInvocation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedRuntimeFamilyMembers
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryFormedMembers
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStoredIndirectParentPrefix
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStoredIndirectApplication
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStoredIndirectPreservation

/-! Finite runtime branches retain their actual named parameter receipt or
prepared ordinary index. Strict family members supply the existing body
continuations internally. Indirect global/prior classification and qualified
value storage remain separate from these constructor-specific adapters. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedMixedRuntimeHeads
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open RecursiveNamedBoundedContracts (Below)
open CallableIndexedOwnedPreparedRuntimeFamilyMembers (OrdinaryIndex)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

section NamedMembers
variable (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed)) (owner : OwnedKey keys)

/-- A genuine strict named family member gives the Source continuation at
that exact allocated parameter receipt, including its original agreement. -/
theorem named_source_bodies (outer budget : Nat) (within : budget ≤ outer)
    (ih : ∀ i, Below outer
      (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
        (headers := headers) (registry := registry) (faults := faults) functions owner i))
    (header : Header compiled (Program.ofChecked compiled.sourceProgram)) (member : header ∈ headers) :
    CallableIndexedOwnedPreparedNamedParameterReceipts.SourceBodiesFor
      (headers := headers) (functions := functions) (owner := owner) (registry := registry) (faults := faults) header budget := by
  intro initial argumentsPool arguments receipt _agreement child strict
  exact (ih ⟨header, member, initial, argumentsPool, arguments, receipt⟩ child
    (Nat.lt_of_lt_of_le strict within)).1

/-- Native members keep their measured parameter prefix and restoration
receipt, while selecting the independent native conjunct at the true child. -/
theorem named_native_bodies (outer budget : Nat) (within : budget ≤ outer)
    (ih : ∀ i, Below outer
      (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
        (headers := headers) (registry := registry) (faults := faults) functions owner i))
    (header : Header compiled (Program.ofChecked compiled.sourceProgram)) (member : header ∈ headers) :
    CallableIndexedOwnedPreparedNamedParameterReceipts.NativeBodiesFor
      (headers := headers) (functions := functions) (owner := owner) (registry := registry) (faults := faults) header budget := by
  intro initial argumentsPool arguments receipt prefixSize bodyStore value finalStore
    _prefix _prefixStrict _restored child strict
  exact (ih ⟨header, member, initial, argumentsPool, arguments, receipt⟩ child
    (Nat.lt_of_lt_of_le strict within)).2

end NamedMembers

section NamedHeads
variable (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (owner : OwnedKey keys) (caller : Header compiled (Program.ofChecked compiled.sourceProgram))
  (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context
    (CallableIndexedNamedGeneration.source caller.named))
  (covers : evidence.Covers context)
  (unique : NodeOccurrencesUnique (CallableIndexedNamedGeneration.source caller.named))
  (owners : ((Program.ofChecked compiled.sourceProgram).functions.map (fun definition => definition.body.owner)).Nodup)
  (idsUnique : RequirementIdsUnique context)
  (sameLayouts : ∀ header, header ∈ headers → header.layouts = compiled.indexed.layouts)
  {certificate : GenericExpressionMeaning.Certificate}

include wellFormed runtime covers unique owners idsUnique sameLayouts in
/-- The mixed named constructor uses actual ordered child expressions and
body members at their genuine parameter input, without a completed body law. -/
private theorem named_preserves (outer budget size : Nat) (headWithin : size ≤ budget) (within : budget ≤ outer)
    (children : Below budget (CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots
        (CallableIndexedOwnedNestedCallerProtocol.carrier (headers := headers) owner caller))
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile))
      context evidence (CallableIndexedNamedGeneration.source caller.named) certificate faults))
    (ih : ∀ i, Below outer
      (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family (headers := headers)
        (registry := registry) (faults := faults)
        (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) owner i)) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots
        (CallableIndexedOwnedNestedCallerProtocol.carrier (headers := headers) owner caller))
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile))
      context evidence (CallableIndexedNamedGeneration.source caller.named)
      (RecursiveNamedCallEvidenceHeads.Head (prepared := compiled.indexed.ancestry)
        (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        headers (CallableIndexedNamedGeneration.context compiled.indexed caller.named)
        (CallableIndexedNamedGeneration.source caller.named) context evidence certificate) faults size := by
  exact CallableIndexedOwnedPreparedNamedExpressionRuntimeBounds.preserves_head
    (compilation := CallableIndexedNamedGeneration.context compiled.indexed caller.named) (certificate := certificate)
    (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)
    owner (CallableIndexedOwnedNestedCallerProtocol.carrier (headers := headers) owner caller)
    evidence wellFormed runtime covers unique owners idsUnique sameLayouts budget size headWithin children
    (named_source_bodies _ owner outer budget within ih)

include wellFormed runtime covers unique sameLayouts in
/-- The native named constructor preserves its own argument/body grades and
reconstructs the independent Source outcome at the real restored caller. -/
private theorem named_reflects (outer budget size : Nat) (headWithin : size ≤ budget) (within : budget ≤ outer)
    (children : Below budget (CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots
        (CallableIndexedOwnedNestedCallerProtocol.carrier (headers := headers) owner caller))
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile))
      context evidence (CallableIndexedNamedGeneration.source caller.named) certificate faults))
    (ih : ∀ i, Below outer
      (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family (headers := headers)
        (registry := registry) (faults := faults)
        (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) owner i)) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots
        (CallableIndexedOwnedNestedCallerProtocol.carrier (headers := headers) owner caller))
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile))
      context evidence (CallableIndexedNamedGeneration.source caller.named)
      (RecursiveNamedCallEvidenceHeads.Head (prepared := compiled.indexed.ancestry)
        (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        headers (CallableIndexedNamedGeneration.context compiled.indexed caller.named)
        (CallableIndexedNamedGeneration.source caller.named) context evidence certificate) faults size := by
  exact CallableIndexedOwnedPreparedNamedExpressionRuntimeBounds.reflects_head
    (compilation := CallableIndexedNamedGeneration.context compiled.indexed caller.named) (certificate := certificate)
    (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)
    owner (CallableIndexedOwnedNestedCallerProtocol.carrier (headers := headers) owner caller)
    evidence wellFormed runtime covers unique sameLayouts budget size headWithin children
    (named_native_bodies _ owner outer budget within ih)

end NamedHeads

section FormationHeads
variable (caller : Header compiled (Program.ofChecked compiled.sourceProgram))
  (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
  (owner : OwnedKey keys) (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (globals : caller.globals = compiled.indexed.base.globals.length)
  (slots : ∀ header, header ∈ headers → header.slot < compiled.indexed.base.globals.length)
  (prefixZero : owner.key.capturePrefix = 0)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context
    (CallableIndexedNamedGeneration.source caller.named)) (covers : evidence.Covers context)

include complete globals slots prefixZero wellFormed runtime covers in
/-- A literal mixed lambda Formation runs once at identity inclusion of the
full prepared model. Its existing result does not promise a stored sidecar. -/
private theorem formation_preserves (size : Nat) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile))
      context evidence (CallableIndexedNamedGeneration.source caller.named)
      (CallableIndexedOwnedPreparedOrdinaryLambdaInvocation.Certificate caller context evidence) faults size := by
  exact CallableIndexedOwnedPreparedOrdinaryLambdaInvocation.preserves_head_at caller context evidence owner profile
    (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)
    (fun related => related) complete globals slots prefixZero wellFormed runtime covers rfl size

include complete globals slots prefixZero wellFormed runtime covers in
/-- Native formation keeps the original caller packet and an independent
Source grade; all prior model alternatives remain unchanged. -/
private theorem formation_reflects (size : Nat) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile))
      context evidence (CallableIndexedNamedGeneration.source caller.named)
      (CallableIndexedOwnedPreparedOrdinaryLambdaInvocation.Certificate caller context evidence) faults size := by
  exact CallableIndexedOwnedPreparedOrdinaryLambdaInvocation.reflects_head_at caller context evidence owner profile
    (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)
    (fun related => related) complete globals slots prefixZero wellFormed runtime covers rfl size

end FormationHeads

/-- Exact selection keeps the actual prior alternative or the known formed
constructor. This finite split never upgrades an opaque prior relation. -/
theorem selection_cases {mapping : LocationMap} {world : StoreTyping}
    {raw : TypeSystem.Ty} {source : Dynamic.Value} {native : Value} {type : Ty}
    (selected : CallableIndexedOwnedPreparedOrdinaryLambdaValues.Selection
      headers keys registry faults mapping world raw source native type) :
    CallableIndexedOwnedGeneralFunctionSelection.Selection headers keys registry faults mapping world raw source native type ∨
      CallableIndexedOwnedPreparedOrdinaryFormedMembers.FormedAt headers keys registry faults mapping world raw source native type := by
  cases selected with
  | prior original => exact Or.inl original
  | @prepared_ordinary function scope actual owner captured code history support origin prefixContext globals referenceIndex typed prepared =>
    right
    let i : OrdinaryIndex compiled := {
      function := function, mapping := mapping, world := world, scope := scope, capturedActual := actual
      captured := captured, code := code, support := support, prepared := prepared }
    exact .ordinary i owner history origin prefixContext globals referenceIndex typed

section Applications
open CallableIndexedOwnedIndirectSourceAdapters CallableIndexedOwnedIndirectExpressionHeads

variable
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
  (unique : NodeOccurrencesUnique source) (parent : CallableIndexedOwnedIndirectSourceAdapters.SourceParent compiler)
  (actualFunctionType : policy.callables.functionType = CallableContract.functionType)

include prepared certified found sourceTyped parentTyped wellFormed runtime covers
  environments heaps locals agrees typed admitted caller sidecarSource tree unique parent in
/-- The actual indirect compiler branch produces one callee post. Its global,
prior and classifier alternatives remain in the original conditional prefix. -/
theorem indirect_reflects_prefix (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      bridge (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)) context evidence source certificate faults size)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore)
    (within : size ≤ budget) :
    SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar ∧
    sidecar.source = source ∧
    (CallableIndexedOwnedStoredIndirectNativePrefix.ForModel.FaultPrefix
        (registry := registry) (faults := faults) (context := context) (evidence := evidence)
        (environment := environment) (actual := actual) (ξ := ξ) (sidecar := sidecar)
        bridge (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) compiler initial budget value finalStore ∨
      CallableIndexedOwnedPreparedStoredIndirectParentPrefix.ValuePrefix (registry := registry) (faults := faults) (context := context) (evidence := evidence)
        (environment := environment) (actual := actual) (ξ := ξ) (calleeNode := calleeNode)
        (sourceTypes := sourceTypes) (sidecar := sidecar) bridge profile compiler prepared initial budget value finalStore) := by
  exact CallableIndexedOwnedPreparedStoredIndirectParentPrefix.reflects_parent
    (bridge := bridge) (profile := profile) (compiler := compiler) (prepared := prepared)
    (certified := certified) (found := found) (sourceTyped := sourceTyped) (parentTyped := parentTyped)
    (wellFormed := wellFormed) (runtime := runtime) (covers := covers)
    (environments := environments) (heaps := heaps) (locals := locals) (agrees := agrees) (typed := typed)
    (initial := initial) (admitted := admitted) (caller := caller) (sidecarSource := sidecarSource)
    (tree := tree) (unique := unique) (parent := parent) budget children completed within

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

include parentTyped wellFormed runtime covers locals admitted tree unique parent actualFunctionType
  calleeTrace post accepted observed referenceIndex sameNative selectedType seed extension faithful observations
  rebuilt operandIncluded unaryIncluded interprets in
/-- The known selected ordinary index supplies its strict native expression
members. The original whole fourth bind and current caller restore run once. -/
theorem prepared_application_reflects (budget : Nat)
    (outer : Nat) (within : budget ≤ outer)
    (ih : ∀ i, RecursiveNamedCatalogInvocationBounds.Below outer
      (CallableIndexedOwnedPreparedRuntimeFamilyMembers.Family (headers := headers) (keys := keys)
        (registry := registry) (faults := faults)
        (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) i))
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
    CallableIndexedOwnedPreparedStoredIndirectApplication.ResultAt (registry := registry) (faults := faults) (context := context) (evidence := evidence)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeHeap := calleeHeap) (calleeNative := calleeNative) (calleeStore := calleeStore)
      (calleeMap := calleeMap) (calleeWorld := calleeWorld) (sidecar := sidecar)
      bridge profile compiler prepared initial dispatch budget value finalStore := by
  let i : OrdinaryIndex compiled := {
    function := function, mapping := calleeMap, world := calleeWorld, scope := lambdaScope
    capturedActual := capturedActual, captured := captured, code := code, support := support, prepared := seed }
  exact CallableIndexedOwnedPreparedStoredIndirectApplication.reflects_selected
    (bridge := bridge) (profile := profile) (compiler := compiler) (prepared := prepared)
    (parentTyped := parentTyped) (wellFormed := wellFormed) (runtime := runtime) (covers := covers)
    (locals := locals) (initial := initial) (admitted := admitted) (tree := tree) (unique := unique)
    (parent := parent) (actualFunctionType := actualFunctionType) (calleeTrace := calleeTrace) (post := post)
    (dispatch := dispatch) (accepted := accepted) (owner := owner)
    (captured := captured) (code := code) (history := history) (support := support) (seed := seed)
    (observed := observed) (referenceIndex := referenceIndex) (sameNative := sameNative) (selectedType := selectedType)
    (extension := extension) (faithful := faithful) (observations := observations) (rebuilt := rebuilt)
    (operandIncluded := operandIncluded) (unaryIncluded := unaryIncluded) (interprets := interprets)
    budget (CallableIndexedOwnedPreparedRuntimeFamilyMembers.reflects_below
      (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)
      outer budget within ih i) original step passed

include parentTyped wellFormed runtime covers locals admitted tree unique parent actualFunctionType
  environments agrees typed calleeTrace post accepted observed referenceIndex sameNative selectedType seed
  dispatch selected extension faithful observations rebuilt operandIncluded unaryIncluded interprets in
/-- Only the actual called suffix requests ordinary strict expression members.
An argument fault has no physical count or body-child demand. -/
theorem prepared_selected_preserves (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      bridge (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)) context evidence source certificate faults size)
    {argumentsSize callSize : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (suffix : SourceSuffix (Program.ofChecked compiled.sourceProgram) context evidence source environment calleeHeap ids function
      argumentsSize callSize outcome after)
    (physicalCount : CallableIndexedOwnedPreparedStoredIndirectPreservation.PhysicalArity (context := context) (evidence := evidence) (source := source)
      (environment := environment) suffix)
    (argumentsWithin : argumentsSize ≤ budget) (callWithin : callSize ≤ budget)
    (outer : Nat) (within : budget ≤ outer)
    (ih : CallableIndexedOwnedStoredIndirectCallBounds.ForModel.CalledSuffix
        (context := context) (evidence := evidence) (environment := environment) suffix →
      ∀ i, RecursiveNamedCatalogInvocationBounds.Below outer
        (CallableIndexedOwnedPreparedRuntimeFamilyMembers.Family (headers := headers) (keys := keys)
          (registry := registry) (faults := faults)
          (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) i)) :
    ∃ sourceSize value finalStore finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize context evidence source
        environment before id outcome after ∧
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      Staging.CallBoundary.Executes (Program.ofChecked compiled.sourceProgram) (CallableLedger.frame sidecar)
        context evidence source environment before id callee ids metadata
        (CallableIndexedOwnedPreparedStoredIndirectApplication.boundaryOutcome outcome) after ∧
      CallableIndexedOwnedStoredFunctionModelReceipts.ParentResultAt (registry := registry) (faults := faults) (context := context)
        bridge (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) compiler initial outcome after value finalStore finalMap finalWorld := by
  let i : OrdinaryIndex compiled := {
    function := function, mapping := calleeMap, world := calleeWorld, scope := lambdaScope
    capturedActual := capturedActual, captured := captured, code := code, support := support, prepared := seed }
  exact CallableIndexedOwnedPreparedStoredIndirectPreservation.preserves_selected
    (bridge := bridge) (profile := profile) (compiler := compiler) (prepared := prepared)
    (parentTyped := parentTyped) (wellFormed := wellFormed) (runtime := runtime) (covers := covers)
    (locals := locals) (initial := initial) (admitted := admitted) (tree := tree) (unique := unique)
    (parent := parent) (actualFunctionType := actualFunctionType) (calleeTrace := calleeTrace) (post := post)
    (dispatch := dispatch) (selected := selected) (accepted := accepted) (owner := owner)
    (captured := captured) (code := code) (history := history) (support := support) (seed := seed)
    (observed := observed) (referenceIndex := referenceIndex) (sameNative := sameNative) (selectedType := selectedType)
    (extension := extension) (faithful := faithful) (observations := observations) (rebuilt := rebuilt)
    (operandIncluded := operandIncluded) (unaryIncluded := unaryIncluded) (interprets := interprets)
    (environments := environments) (agrees := agrees) (typed := typed)
    budget children suffix physicalCount argumentsWithin callWithin
    (fun called => CallableIndexedOwnedPreparedRuntimeFamilyMembers.preserves_below
      (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)
      outer budget within (ih called) i)

end Applications

/-- This certificate names one actual scope/id/code, so a finite branch
consumer cannot silently apply to a different compiled occurrence. -/
def Point (scope : SourceCoreLocalCell.Scope) (id : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr) :
    GenericExpressionMeaning.Certificate :=
  fun requestedScope requestedId requestedCode =>
    requestedScope = scope ∧ requestedId = id ∧ requestedCode = lowered

section Restrict
variable {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  {bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol}
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
  {model : GenericHeap.PayloadModel catalog projects definitions}
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
  {certificate : GenericExpressionMeaning.Certificate} {scope : SourceCoreLocalCell.Scope}
  {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {size : Nat}

private theorem preserves_point
    (meaning : CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge model context evidence source certificate faults size)
    (member : certificate scope id lowered) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge model context evidence source (Point scope id lowered) faults size := by
  intro requestedScope requestedId requestedCode same
  obtain ⟨rfl, rfl, rfl⟩ := same
  exact meaning member

private theorem reflects_point
    (meaning : CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge model context evidence source certificate faults size)
    (member : certificate scope id lowered) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge model context evidence source (Point scope id lowered) faults size := by
  intro requestedScope requestedId requestedCode same
  obtain ⟨rfl, rfl, rfl⟩ := same
  exact meaning member
end Restrict

section MixedBranches
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedContextualCompilerPolicyProfiles
variable {caller : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : Compilation compiled.indexed caller.named diagnostics namedCode}
  {rootFuel : Nat} {rootScope : SourceCoreLocalCell.Scope} {rootId : ExpressionId}
  {reasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) caller.named diagnostics namedCode compilation
    rootFuel (source caller.named) rootScope rootId reasonAt rootLowered)
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  (factory : CallableIndexedOwnedIndirectCompilerReceipts.Factory caller diagnostics namedCode compilation
    (source caller.named) context evidence rootScope
    (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller) certificates)
  {children : GenericExpressionMeaning.Certificate} {scope : SourceCoreLocalCell.Scope}
  {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}

/-- The static mixed Head remains attached to its literal runtime certificate.
This definition does not classify an arbitrary Head or an actual Source value. -/
def At (_head : CallableIndexedOwnedPreparedMixedCompilerHeads.Head root factory headers children scope id lowered) :
    GenericExpressionMeaning.Certificate := Point scope id lowered

variable (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (owner : OwnedKey keys) (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context (source caller.named))
  (covers : evidence.Covers context) (unique : NodeOccurrencesUnique (source caller.named))
  (sameLayouts : ∀ header, header ∈ headers → header.layouts = compiled.indexed.layouts)
  (owners : ((Program.ofChecked compiled.sourceProgram).functions.map (fun definition => definition.body.owner)).Nodup)
  (idsUnique : RequirementIdsUnique context)

include wellFormed runtime covers unique sameLayouts owners idsUnique in
/-- Use the actual mixed named constructor with strict named family members
and ordered admitted children at that same root/caller occurrence. -/
theorem named_branch_preserves
    (named : RecursiveNamedCallEvidenceHeads.Calls (some evidence) headers
      (CallableIndexedNamedGeneration.context compiled.indexed caller.named) (source caller.named) context children scope id lowered)
    (outer budget size : Nat) (headWithin : size ≤ budget) (within : budget ≤ outer)
    (arguments : Below budget (CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots
        (CallableIndexedOwnedNestedCallerProtocol.carrier (headers := headers) owner caller))
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile))
      context evidence (source caller.named) children faults))
    (ih : ∀ i, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults)
      (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) owner i)) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots
        (CallableIndexedOwnedNestedCallerProtocol.carrier (headers := headers) owner caller))
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile))
      context evidence (source caller.named)
      (At root factory (CallableIndexedOwnedPreparedMixedCompilerHeads.Head.named named)) faults size := by
  exact preserves_point
    (named_preserves profile owner caller context evidence wellFormed runtime covers unique owners idsUnique sameLayouts
      outer budget size headWithin within arguments ih) named

include wellFormed runtime covers unique sameLayouts in
/-- The actual mixed named native branch keeps the original measured children
and current restored pool, with an independent Source witness. -/
theorem named_branch_reflects
    (named : RecursiveNamedCallEvidenceHeads.Calls (some evidence) headers
      (CallableIndexedNamedGeneration.context compiled.indexed caller.named) (source caller.named) context children scope id lowered)
    (outer budget size : Nat) (headWithin : size ≤ budget) (within : budget ≤ outer)
    (arguments : Below budget (CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots
        (CallableIndexedOwnedNestedCallerProtocol.carrier (headers := headers) owner caller))
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile))
      context evidence (source caller.named) children faults))
    (ih : ∀ i, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults)
      (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) owner i)) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots
        (CallableIndexedOwnedNestedCallerProtocol.carrier (headers := headers) owner caller))
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile))
      context evidence (source caller.named)
      (At root factory (CallableIndexedOwnedPreparedMixedCompilerHeads.Head.named named)) faults size := by
  exact reflects_point
    (named_reflects profile owner caller context evidence wellFormed runtime covers unique sameLayouts
      outer budget size headWithin within arguments ih) named

variable
  (complete : RecursiveNamedCatalogNativeContexts.Complete (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (globals : caller.globals = compiled.indexed.base.globals.length)
  (slots : ∀ header, header ∈ headers → header.slot < compiled.indexed.base.globals.length)
  (prefixZero : owner.key.capturePrefix = 0)

include complete globals slots prefixZero wellFormed runtime covers in
/-- The actual compiled lambda receipt supplies Formation literally. No
qualification is recovered from its broad runtime ResultAt after formation. -/
theorem formation_branch_preserves
    {childFuel : Nat} {node : ExpressionNode} {parameters : List TypedBinder}
    {result : TypeSystem.Ty} {statements : List StatementId} {reported : Ty}
    (found : (source caller.named).lookupExpression? id = some node)
    (form : node.form = .lambda parameters result statements)
    (certificate : CallableIndexedLambdaCertificates.Certificate root.selected.policy root.selected.lowerBody childFuel
      (CallableIndexedNamedGeneration.context compiled.indexed caller.named) (source caller.named)
      rootScope id node parameters result statements reported reasonAt lowered)
    (receipt : CallableIndexedOwnedPreparedOrdinaryLambdaCompilerReceipts.Receipt caller diagnostics namedCode compilation
      context evidence rootScope id lowered)
    (samePolicy : receipt.formation.produced.site.code.policy = root.selected.policy)
    (sameBody : receipt.formation.produced.site.code.lowerBody = root.selected.lowerBody)
    (sameFuel : receipt.formation.produced.site.code.fuel = childFuel)
    (sameView : receipt.formation.produced.site.code.view = source caller.named)
    (sameReason : receipt.formation.produced.site.code.reasonAt = reasonAt)
    (sameCertificate : HEq receipt.formation.produced.site.code.receipt certificate)
    (metadata : CompatibleExpressionReads.Metadata compiled.compatible.checked (source caller.named) id node lowered.type)
    (size : Nat) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile))
      context evidence (source caller.named)
      (At (headers := headers) (children := children) root factory (CallableIndexedOwnedPreparedMixedCompilerHeads.Head.prepared_lambda
        found form certificate receipt samePolicy sameBody sameFuel sameView sameReason sameCertificate metadata)) faults size := by
  exact preserves_point
    (formation_preserves caller context evidence owner profile complete globals slots prefixZero wellFormed runtime covers size)
    ⟨receipt.formation⟩

include complete globals slots prefixZero wellFormed runtime covers in
/-- Native formation consumes the same literal compiled receipt and owning
caller frame at its actual mixed lambda constructor. -/
theorem formation_branch_reflects
    {childFuel : Nat} {node : ExpressionNode} {parameters : List TypedBinder}
    {result : TypeSystem.Ty} {statements : List StatementId} {reported : Ty}
    (found : (source caller.named).lookupExpression? id = some node)
    (form : node.form = .lambda parameters result statements)
    (certificate : CallableIndexedLambdaCertificates.Certificate root.selected.policy root.selected.lowerBody childFuel
      (CallableIndexedNamedGeneration.context compiled.indexed caller.named) (source caller.named)
      rootScope id node parameters result statements reported reasonAt lowered)
    (receipt : CallableIndexedOwnedPreparedOrdinaryLambdaCompilerReceipts.Receipt caller diagnostics namedCode compilation
      context evidence rootScope id lowered)
    (samePolicy : receipt.formation.produced.site.code.policy = root.selected.policy)
    (sameBody : receipt.formation.produced.site.code.lowerBody = root.selected.lowerBody)
    (sameFuel : receipt.formation.produced.site.code.fuel = childFuel)
    (sameView : receipt.formation.produced.site.code.view = source caller.named)
    (sameReason : receipt.formation.produced.site.code.reasonAt = reasonAt)
    (sameCertificate : HEq receipt.formation.produced.site.code.receipt certificate)
    (metadata : CompatibleExpressionReads.Metadata compiled.compatible.checked (source caller.named) id node lowered.type)
    (size : Nat) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile))
      context evidence (source caller.named)
      (At (headers := headers) (children := children) root factory (CallableIndexedOwnedPreparedMixedCompilerHeads.Head.prepared_lambda
        found form certificate receipt samePolicy sameBody sameFuel sameView sameReason sameCertificate metadata)) faults size := by
  exact reflects_point
    (formation_reflects caller context evidence owner profile complete globals slots prefixZero wellFormed runtime covers size)
    ⟨receipt.formation⟩

end MixedBranches

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedMixedRuntimeHeads
