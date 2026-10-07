import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSelectedIndirectBodies
import Solcore.Test.SourceCoreClosedOwnedLexicalBody

/-! A literal lambda call uses its authentic formation receipt and caller packet.
The lambda-only child family and selected anonymous body continuations are closed
here from static receipts. Empty arguments, empty parameters and a nil Unit body
construct the complete Source parent; native reflection retains its own Source
grade and the exact actual returned pool. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
namespace Tests.SourceCoreOwnedSelectedLiteralCall
open Solcore Core Frontend SourceInference
open SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedIndirectExpressionHeads CallableIndexedOwnedIndirectSourceAdapters
open CallableIndexedLambdaNestedRuntimeBodyMeaning
open RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds
open SourceCoreCallableIndexedFrames
open Tests.SourceCoreClosedOwnedLexicalBody (reached_pool_observations)
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : SourceSemantics.Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (prefixZero : owner.key.capturePrefix = 0)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (globals : ∀ header, header ∈ headers → header.globals = compiled.indexed.base.globals.length)
  (slots : ∀ header, header ∈ headers → header.slot < compiled.indexed.base.globals.length)
  (sameLayouts : ∀ header, header ∈ headers → header.layouts = compiled.indexed.layouts)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
variable
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) identities)
  (functionTypes : FunctionRuntimeViews (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  (uninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (missing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header ∈ headers, faults .controlEscapedFunction header.escaped)
  (ranks : CallableIndexedOwnedFunctionValues.Header compiled program → Nat)
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled program → ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}

variable (profiles : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location} {current : NativeFrame} {ghost : GhostFrame},
      (entry : BodyState (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        headers owner.key.locations owner.key.capturePrefix (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost) →
      (CallableIndexedOwnedNamedCanonicalEntries.condition (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) owner header) entry →
      MatchProfileWith (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (fun context => RecursiveNamedCatalogMutualMeaning.ContextFor true header.solved context header.function.evidence)
        (CallableIndexedOwnedNestedNamedFamilyClosure.certificates (headers := headers) (registry := registry) (faults := faults) ranks header)
        diagnosticPolicy header (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)

variable (caller : CallableIndexedOwnedFunctionValues.Header compiled program)
  (callerGlobals : caller.globals = compiled.indexed.base.globals.length)
  {source : TypedSource} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  (sameSource : source = CallableIndexedNamedGeneration.source caller.named)

/-- Every child receipt is a genuine original lambda occurrence. -/
def lambdaChildren : GenericExpressionMeaning.Certificate := fun scope id lowered =>
  ∃ rank, Nonempty (LambdaAt (values := .initial compiled.compatible.checked)
    headers caller registry faults rank source context evidence scope id lowered)

include prefixZero complete callerGlobals slots sameSource in
/-- The lambda child family is proved by the real formation leaf producer. -/
private theorem children_preserve (size : Nat) (unique : NodeOccurrencesUnique source) :
    ProtectedStateTransition.PreservesAt
      (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      program context evidence source (lambdaChildren (headers := headers) (registry := registry) (faults := faults) (source := source) (context := context) (evidence := evidence) caller) faults size := by
  intro scope id lowered certified
  obtain ⟨rank, child⟩ := certified
  exact CallableIndexedOwnedNestedCanonicalState.formation_preserves_at owner caller prefixZero profile complete
    callerGlobals slots sameSource size unique child

include prefixZero complete callerGlobals slots sameSource in
/-- Native lambda completion retains the same reached packet and Source grade. -/
private theorem children_reflect (size : Nat) :
    ProtectedStateTransition.ReflectsAt
      (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      program context evidence source (lambdaChildren (headers := headers) (registry := registry) (faults := faults) (source := source) (context := context) (evidence := evidence) caller) faults size := by
  intro scope id lowered certified
  obtain ⟨rank, child⟩ := certified
  exact CallableIndexedOwnedNestedCanonicalState.formation_reflects_at owner caller prefixZero profile complete
    callerGlobals slots sameSource size child

section Parent
variable {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  (head : CallableIndexedOwnedSelectedIndirectHeads.Receipt (headers := headers)
    (registry := registry) (faults := faults) (source := source) (context := context) (evidence := evidence)
    caller (lambdaChildren (headers := headers) (registry := registry) (faults := faults) (source := source) (context := context) (evidence := evidence) caller) scope id lowered)
  (noArguments : head.ids = []) (noParameters : head.formation.parameters = [])
  (emptyBody : head.formation.statements = []) (unitResult : head.formation.result = .unit)
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
  {canonical actual : Environment} {administrative actualContext : Core.Context}
  {environment : Dynamic.Environment} {ξ : Renaming}
  (initial : (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller).State
    ⟨scope, mapping, world, heap, store, canonical⟩)
  (related : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (stored : RuntimeStoreHasTypes world store compiled.indexed.layouts.definitions)

private def bridge := CallableIndexedOwnedIndirectCallerProtocol.forget_slots
  (CallableIndexedOwnedNestedCallerProtocol.carrier (headers := headers) owner caller)

private def selectedClosure :=
  CallableIndexedOwnedSelectedIndirectHeads.formedReceipt owner caller prefixZero profile complete callerGlobals slots head
    (bridge owner caller) initial initial.property related agrees typed stored


variable (bodyUninitialized : ∀ id location, faults (.uninitializedLocation location) ((actualCode head.formation environment).reasonAt id))
  (bodyMissing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) (((actualCode head.formation environment).reasonAt id).add tag))

include prefixZero profile initial complete globals slots sameLayouts extension faithful observations functionTypes owners
  uninitialized missing escaped profiles callerGlobals related agrees typed stored bodyUninitialized bodyMissing in
/-- The exact argument post selects the internally closed authentic body. -/
private theorem closed_source (budget : Nat) :
    SourceContinuations (source := source) (context := context) (evidence := evidence)
      (environment := environment) (ids := head.ids) profile (selectedClosure owner prefixZero profile complete slots caller callerGlobals head initial related agrees typed stored) (head.selected environment).escaped
      (bridge owner caller) initial budget := by
  exact CallableIndexedOwnedSelectedIndirectBodies.source_continuations owner prefixZero profile complete globals slots sameLayouts
    extension faithful observations functionTypes owners uninitialized missing escaped ranks profiles (selectedClosure owner prefixZero profile complete slots caller callerGlobals head initial related agrees typed stored) rfl rfl
    callerGlobals bodyUninitialized bodyMissing (head.selected environment).escaped (bridge owner caller) initial budget

include prefixZero profile initial complete globals slots sameLayouts extension faithful observations functionTypes
  uninitialized missing escaped profiles callerGlobals related agrees typed stored bodyUninitialized bodyMissing in
private theorem closed_native (budget : Nat) :
    NativeContinuations (source := source) (context := context) (evidence := evidence)
      (environment := environment) (ids := head.ids) profile (selectedClosure owner prefixZero profile complete slots caller callerGlobals head initial related agrees typed stored) (head.selected environment).escaped
      (bridge owner caller) initial budget := by
  exact CallableIndexedOwnedSelectedIndirectBodies.native_continuations owner prefixZero profile complete globals slots sameLayouts
    extension faithful observations functionTypes uninitialized missing escaped ranks profiles (selectedClosure owner prefixZero profile complete slots caller callerGlobals head initial related agrees typed stored) rfl rfl
    callerGlobals bodyUninitialized bodyMissing (head.selected environment).escaped (bridge owner caller) initial budget


variable
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) mapping world heap store)
  (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
  (heapTyped : Dynamic.HeapWellTyped context heap)
  (stable : StableRows initial.val)
  (wellFormed : ProgramWellFormed program)
  (runtime : Dynamic.SourceRuntimeValid program context source)
  (covers : evidence.Covers context)
  (unique : NodeOccurrencesUnique source)

include prefixZero profile complete callerGlobals slots initial related agrees typed stored wellFormed runtime covers locals heapTyped noArguments noParameters emptyBody unitResult in
/-- The complete original Source parent is constructed from genuine formation,
empty ordered arguments, actual empty parameters and the nil Unit body. -/
theorem actual_source :
    ∃ size, RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment heap id
      (.value .unit) heap := by
  let closure := (selectedClosure owner prefixZero profile complete slots caller callerGlobals head initial related agrees typed stored)
  obtain ⟨calleeSource, _native⟩ := CallableIndexedOwnedSelectedIndirectHeads.formed_receipts owner caller prefixZero
    profile complete callerGlobals slots head (bridge owner caller) initial initial.property related agrees typed stored
  obtain ⟨calleeSize, calleeTrace⟩ := SourceExecutionSize.ExpressionEvaluates.has_size calleeSource
  have arguments : SourceExecutionSize.ExpressionsEvaluate program (SourceExecutionSize.stepSize [])
      context evidence source environment heap head.ids [] heap := by
    rw [noArguments]; exact .nil
  have parameters : (formed head.formation environment).parameters = [] := noParameters
  have body : (formed head.formation environment).body = [] := emptyBody
  have result : (formed head.formation environment).resultType = .unit := unitResult
  have allocated : Dynamic.BindersAllocate (formed head.formation environment).captured heap
      (formed head.formation environment).parameters [] (formed head.formation environment).captured heap := by
    rw [parameters]; exact .nil _ _
  have executed : SourceExecutionSize.FunctionStatementsExecute program (SourceExecutionSize.stepSize [])
      closure.inputs.context (formed head.formation environment).evidence (formed head.formation environment).source
      (formed head.formation environment).captured heap (formed head.formation environment).body closure.inputs.context
      (.fallthrough (formed head.formation environment).captured) heap := by
    have nilTrace : SourceExecutionSize.FunctionStatementsExecute program (SourceExecutionSize.stepSize [])
        closure.inputs.context (formed head.formation environment).evidence (formed head.formation environment).source
        (formed head.formation environment).captured heap [] closure.inputs.context
        (.fallthrough (formed head.formation environment).captured) heap := .nil
    exact Eq.mp (congrArg (fun statements => SourceExecutionSize.FunctionStatementsExecute program (SourceExecutionSize.stepSize [])
      closure.inputs.context (formed head.formation environment).evidence (formed head.formation environment).source
      (formed head.formation environment).captured heap statements closure.inputs.context
      (.fallthrough (formed head.formation environment).captured) heap) body.symm) nilTrace
  have called : RecursiveNamedCallBounds.CallOutcome program
      (SourceExecutionSize.stepSize [SourceExecutionSize.stepSize []]) context evidence
      (formed head.formation environment).evidence heap (.closure (formed head.formation environment)) [] (.value .unit) heap :=
    .value (.closureUnit rfl (closure.bodyOrigin (head.selected environment).escaped).frame result
      closure.inputs.extended allocated executed ⟨_, rfl⟩)
  exact SourceSuffix.to_expression head.compiler.found head.compiler.originalForm head.parent.requirements
    head.parent.coercions head.compiler.argumentCoercions head.parent.arity wellFormed runtime covers locals heapTyped
    head.sourceArguments head.sourceCount calleeTrace (SourceSuffix.of_call arguments called)


/-- Observations refer to every real reached row, retaining duplicate records. -/
def observationsAt {firstIndex reachedIndex : ProtectedStateTransition.Index}
    (first : State headers keys firstIndex) (reached : State headers keys reachedIndex) : Prop :=
  (∀ row, RecordPrefix (records first row) (records reached row)) ∧
  (∀ row record, record ∈ records reached row → CallableIndexedSnapshots.Holds
    compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
    compiled.indexed.ancestry.layout.frame reachedIndex.mapping reachedIndex.store record) ∧
  (∀ row record, record ∈ records first row → record ∈ records reached row)


/-- The same transition witness supplies every row's ordered prefix and real
snapshot interpretation at its own final map and store. -/
theorem observe_transition {firstIndex finalIndex : ProtectedStateTransition.Index}
    (first : (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller).State firstIndex)
    (transition : ProtectedStateTransition.Transition
      (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller) first finalIndex) :
    ∃ reached : (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller).State finalIndex,
      (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller).Relates first reached ∧
      observationsAt (compiled := compiled) (program := program) (headers := headers) (keys := keys) first.val reached.val := by
  obtain ⟨reached, related⟩ := transition
  exact ⟨reached, related,
    reached_pool_observations (compiled := compiled) (program := program) (headers := headers) (keys := keys)
      (initial := first.val) (final := reached.val) related⟩

include prefixZero profile initial complete globals slots sameLayouts extension faithful observations functionTypes owners
  uninitialized missing escaped profiles callerGlobals sameSource related agrees typed stored heaps locals heapTyped stable
  wellFormed runtime covers unique bodyUninitialized bodyMissing noArguments noParameters emptyBody unitResult in
/-- This whole literal call has no expression or body execution law as input.
The same actual callee, argument and body posts supply the restored caller pool. -/
theorem literal_call_source_post :
    ∃ sourceSize,
      RecursiveNamedCallBounds.ExpressionOutcome program sourceSize context evidence source environment heap id
        (.value .unit) heap ∧
      ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
        finalMap finalWorld head.compiler.original.type lowered.type faults (.value .unit) value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) finalMap finalWorld heap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend heap heap ∧
      ProtectedStateTransition.Transition (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller)
        initial ⟨scope, finalMap, finalWorld, heap, finalStore, canonical⟩ := by
  obtain ⟨sourceSize, sourceTrace⟩ := actual_source
    (owner := owner) (prefixZero := prefixZero) (profile := profile) (complete := complete)
    (slots := slots) (caller := caller) (callerGlobals := callerGlobals) (head := head)
    (initial := initial) (related := related) (agrees := agrees) (typed := typed) (stored := stored)
    (wellFormed := wellFormed) (runtime := runtime) (covers := covers) (locals := locals) (heapTyped := heapTyped)
    (noArguments := noArguments) (noParameters := noParameters) (emptyBody := emptyBody) (unitResult := unitResult)
  have bodies : SourceContinuations (source := source) (context := context) (evidence := evidence)
      (environment := environment) (ids := head.ids) profile (selectedClosure owner prefixZero profile complete slots caller callerGlobals head initial related agrees typed stored) (head.selected environment).escaped
      (bridge owner caller) initial sourceSize := closed_source (owner := owner) (prefixZero := prefixZero) (profile := profile) (complete := complete)
    (globals := globals) (slots := slots) (sameLayouts := sameLayouts) (extension := extension) (faithful := faithful)
    (observations := observations) (functionTypes := functionTypes) (owners := owners) (uninitialized := uninitialized)
    (missing := missing) (escaped := escaped) (ranks := ranks) (profiles := profiles) (caller := caller)
    (callerGlobals := callerGlobals) (head := head) (initial := initial) (related := related) (agrees := agrees)
    (typed := typed) (stored := stored) (bodyUninitialized := bodyUninitialized) (bodyMissing := bodyMissing) sourceSize
  refine ⟨sourceSize, sourceTrace, ?_⟩
  exact CallableIndexedOwnedSelectedIndirectHeads.preserves_bounded
      (owner := owner) (caller := caller) (prefixZero := prefixZero) (profile := profile) (complete := complete)
      (globals := callerGlobals) (slots := slots) (head := head) (bridge := bridge owner caller) (initial := initial)
      (packet := initial.property) (related := related) (agrees := agrees) (typed := typed) (stored := stored)
      (heaps := heaps) (locals := locals) (heapTyped := heapTyped) (stable := stable) (wellFormed := wellFormed)
      (runtime := runtime) (covers := covers) (unique := unique) (budget := sourceSize)
      (arguments := fun child _ => children_preserve (owner := owner) (prefixZero := prefixZero) (profile := profile)
        (complete := complete) (caller := caller) (callerGlobals := callerGlobals) (slots := slots)
        (sameSource := sameSource) child unique)
      (bodies := bodies) sourceTrace (Nat.le_refl _)

include prefixZero profile initial complete globals slots sameLayouts extension faithful observations functionTypes
  uninitialized missing escaped profiles callerGlobals sameSource related agrees typed stored heaps locals heapTyped stable
  wellFormed runtime covers bodyUninitialized bodyMissing in
/-- Native completion follows the same actual selection and body family and
returns a genuine independently graded whole Source parent at the real post. -/
theorem literal_call_native_post {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome program sourceSize context evidence source environment heap id outcome after ∧
      GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
        finalMap finalWorld head.compiler.original.type lowered.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
      ProtectedStateTransition.Transition (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller)
        initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  have bodies : NativeContinuations (source := source) (context := context) (evidence := evidence)
      (environment := environment) (ids := head.ids) profile (selectedClosure owner prefixZero profile complete slots caller callerGlobals head initial related agrees typed stored) (head.selected environment).escaped
      (bridge owner caller) initial size := closed_native (owner := owner) (prefixZero := prefixZero) (profile := profile) (complete := complete)
    (globals := globals) (slots := slots) (sameLayouts := sameLayouts) (extension := extension) (faithful := faithful)
    (observations := observations) (functionTypes := functionTypes) (uninitialized := uninitialized)
    (missing := missing) (escaped := escaped) (ranks := ranks) (profiles := profiles) (caller := caller)
    (callerGlobals := callerGlobals) (head := head) (initial := initial) (related := related) (agrees := agrees)
    (typed := typed) (stored := stored) (bodyUninitialized := bodyUninitialized) (bodyMissing := bodyMissing) size
  exact CallableIndexedOwnedSelectedIndirectHeads.reflects_bounded
      (owner := owner) (caller := caller) (prefixZero := prefixZero) (profile := profile) (complete := complete)
      (globals := callerGlobals) (slots := slots) (head := head) (bridge := bridge owner caller) (initial := initial)
      (packet := initial.property) (related := related) (agrees := agrees) (typed := typed) (stored := stored)
      (heaps := heaps) (locals := locals) (heapTyped := heapTyped) (stable := stable) (wellFormed := wellFormed)
      (runtime := runtime) (covers := covers) (budget := size)
      (arguments := fun child _ => children_reflect (owner := owner) (prefixZero := prefixZero) (profile := profile)
        (complete := complete) (caller := caller) (callerGlobals := callerGlobals) (slots := slots)
        (sameSource := sameSource) child)
      (bodies := bodies) completed (Nat.le_refl _)

end Parent
end Tests.SourceCoreOwnedSelectedLiteralCall
