import Solcore.Test.SourceCoreClosedOwnedCoercionStep
import Solcore.SourceSemantics.CoreLowering.ProtectedCoercionPathMeaning
import Solcore.SourceSemantics.CoreLowering.CallablePreparedOperatorSourceBounds

/-! Actual ordered Coerce methods retain their full compiled rows and saved
captures. Each closed body produces the real next pool; only the capture reads
are transported through its actual effects. The shared path folds keep every
record-producing post, including success and faults. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
namespace Tests.SourceCoreClosedOwnedCoercionPath
open Solcore Core Frontend SourceInference
open SourceSemantics SourceSemantics.CoreLowering GeneralHeap CoreProof ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallablePreparedMethodRuntimeMeaning
open CallableIndexedOwnedMethodCaptureReceipts
open Tests.SourceCoreClosedOwnedMethodBootstrap (TypedCapture)
open Tests.SourceCoreClosedOwnedLexicalBody (reached_pool_observations)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (profileFlag : compiled.compatible.checked.catalog.callableContracts = true)
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {project : SourceCoreEvidence.Projector} {compilation : SourceCoreFunctions.Context}
  {caller : SourceSpecialization.SpecializedFunction} {available : SourceCompilationPlan.EvidenceEnvironment}
  {scope : SourceCoreBasic.Scope} {node : ExpressionNode} {policy : SourceCoreFunctions.CallablePolicy}

/-- Each actual row retains the original compiler Step, checked method/cache,
full independent Source selector/dictionary, typed bootstrap and builtin profile. -/
structure CheckedRow where
  method : ExecutableImplMethods.CheckedMethod
  cached : CallablePreparedMethodSelection.Cached compiled method.specialized
  dictionary : Dynamic.EvidenceEnvironment
  bootstrap : TypedCapture (headers := headers) (keys := keys) (registry := registry) (faults := faults) cached dictionary profileFlag
  profile : Profile cached.compilation (.initial compiled.compatible.checked) (CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (sourceBody (compiled := compiled) (method := method)) dictionary bootstrap.capture.administrative registry faults
  step : CoercionStep
  call : CallableCoercionSpine.Call
  selected : Tests.SourceCoreClosedOwnedCoercionStep.Selected (step := step) (call := call) (context := context) (evidence := evidence)
    cached dictionary profileFlag bootstrap
  owner : CallableIndexedOwnedFunctionValues.OwnedKey keys
  physical : owner.key.frameLocation = 0
  inputCode : SourceCoreBasic.LoweredExpr
  outputCode : SourceCoreBasic.LoweredExpr
  emission : CallableCoercionSpine.Step compiled.sourceProgram project compilation caller available scope node policy inputCode step outputCode call
  sameMethod : emission.method = method

variable (row : CheckedRow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
  (context := context) (evidence := evidence) (project := project) (compilation := compilation)
  (caller := caller) (available := available) (scope := scope) (node := node) (policy := policy) profileFlag)

/-- This is the same complete original method row used for strict child inversion. -/
def CheckedRow.method_row := Tests.SourceCoreClosedOwnedCoercionStep.method_row
  row.cached row.dictionary profileFlag row.bootstrap row.profile row.selected

def CheckedRow.coercion_row : CallableCoercionPathMeaning.Row :=
  ⟨row.step, row.call, sourceBody (compiled := compiled) (method := row.method), row.dictionary⟩

/-- The saved native capture belongs to this actual state, with the exact
physical owner and selected global slot. It stores no body meaning. -/
structure Saved (index : ProtectedStateTransition.Index) where
  installed : Installed row.cached.compilation (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (sourceBody := sourceBody (compiled := compiled) (method := row.method))
    (administrative := row.bootstrap.capture.administrative) (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag)
    index.mapping index.world index.heap index.store index.canonical
  sameFrame : installed.frameLocation = row.owner.key.frameLocation
  sameIndex : installed.globalIndex = row.call.index

/-- Captures extend from real effects. Ordered records remain in the actual
returned pool and are never reconstructed by this operation. -/
def Saved.extend {index : ProtectedStateTransition.Index} (saved : Saved profileFlag row index)
    {mapping world heap store}
    (maps : LocationMap.Extends index.mapping mapping) (worlds : WorldExtends index.world world)
    (frame : AdministrativePreserved index.mapping index.store mapping store)
    (metadata : Dynamic.HeapMetadataExtend index.heap heap) :
    Saved profileFlag row (index.extend mapping world heap store) :=
  ⟨saved.installed.extend maps worlds frame metadata, saved.sameFrame, saved.sameIndex⟩

variable (rows : List (CheckedRow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
  (context := context) (evidence := evidence) (project := project) (compilation := compilation)
  (caller := caller) (available := available) (scope := scope) (node := node) (policy := policy) profileFlag))

/-- The same complete Owned pool is accompanied by actual saved reads for
these finite checked rows. The relation observes only the genuine pool records. -/
def pathProtocol : ProtectedStateTransition.Protocol (Records keys) where
  State := fun index => { _pool : State headers keys index // ∀ row, row ∈ rows → Nonempty (Saved profileFlag row index) }
  records := fun state => records state.val
  Relates := fun first last => Relates first.val last.val
  refl := fun state => Relates.refl state.val
  trans := fun first last => first.trans last

/-- One actual post is wrapped with captures extended through exactly its true
effects. The complete pool and record vector are retained verbatim. -/
def wrap_post {index : ProtectedStateTransition.Index}
    (initial : (pathProtocol profileFlag rows).State index) {mapping world heap store}
    (reached : State headers keys (index.extend mapping world heap store))
    (maps : LocationMap.Extends index.mapping mapping) (worlds : WorldExtends index.world world)
    (frame : AdministrativePreserved index.mapping index.store mapping store)
    (metadata : Dynamic.HeapMetadataExtend index.heap heap) :
    (pathProtocol profileFlag rows).State (index.extend mapping world heap store) :=
  ⟨reached, by
    intro other member
    obtain ⟨saved⟩ := initial.property other member
    exact ⟨Saved.extend profileFlag other saved maps worlds frame metadata⟩⟩

theorem wrapped_pool {index : ProtectedStateTransition.Index}
    (initial : (pathProtocol profileFlag rows).State index) {mapping world heap store}
    (reached : State headers keys (index.extend mapping world heap store))
    (maps : LocationMap.Extends index.mapping mapping) (worlds : WorldExtends index.world world)
    (frame : AdministrativePreserved index.mapping index.store mapping store)
    (metadata : Dynamic.HeapMetadataExtend index.heap heap) :
    (wrap_post profileFlag rows initial reached maps worlds frame metadata).val = reached := rfl

variable (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) identities)
  (functionTypes : FunctionRuntimeViews (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag))
  (escaped : ∀ row, row ∈ rows → faults .controlEscapedFunction row.cached.compilation.own.table.escapedReason)
  (uninitialized : ∀ row, row ∈ rows → ∀ id location,
    faults (.uninitializedLocation location) (row.cached.diagnostics.reasonAt row.cached.named.signature.key id))
  (missing : ∀ row, row ∈ rows → ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((row.cached.diagnostics.reasonAt row.cached.named.signature.key id).add tag))

include extension faithful observations functionTypes escaped uninitialized missing in
/-- Every method callback is derived here from the actual captured slot and
proved closed builtin body family; it is never a semantic hypothesis. -/
private theorem steps_preserve (reason : Word) :
    ProtectedCoercionPathMeaning.StepPreserves (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (row := CheckedRow.coercion_row profileFlag) (registry := registry) (faults := faults)
      (caller := (RecursiveNamedCatalogPreparedInitialization.environment compiled)) (reason := reason) (pathProtocol profileFlag rows) [] (RecursiveNamedCatalogPreparedInitialization.environment compiled) (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) (SourceSemantics.Program.ofChecked compiled.sourceProgram) rows := by
  intro current mapping world before after store input native outcome member initial heaps represented trace
  obtain ⟨saved⟩ := initial.property current member
  change ValueRep compiled.compatible.checked registry (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) mapping world current.step.source input native current.call.signature.parameterType at represented
  change CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) mapping world before store at heaps
  have arguments : CallableIndexedParameterMeaning.Arguments
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag))
      mapping world current.cached.named.inputs [input] [native] := by
    rw [current.selected.bindings]
    apply CallableIndexedParameterMeaning.Arguments.cons _ .nil
    change ValueRep _ _ _ _ _ current.selected.binder.scheme.body _ _ _
    simpa only [current.selected.inputType] using represented
  change NamedCalls.BodyOutcome (SourceSemantics.Program.ofChecked compiled.sourceProgram) (sourceBody (compiled := compiled) (method := current.method)) current.dictionary before [input] outcome after at trace
  obtain ⟨sourceSize, actualTrace⟩ := RecursiveNamedCallBounds.BodyOutcome.has_size trace
  have produced :=
    CallableIndexedOwnedMethodBuiltinBounds.invocation_preserves
      (compiled := compiled) (program := (SourceSemantics.Program.ofChecked compiled.sourceProgram)) (headers := headers) (keys := keys)
      (registry := registry) (faults := faults)
      (named := current.cached.named) (diagnostics := current.cached.diagnostics) (code := current.cached.code)
      (sourceBody := sourceBody (compiled := compiled) (method := current.method))
      (dictionary := current.dictionary) (administrative := current.bootstrap.capture.administrative)
      (mapping := mapping) (world := world) (before := before) (store := store)
      (callerEnvironment := (RecursiveNamedCatalogPreparedInitialization.environment compiled)) (callerScope := []) (callerCanonical := (RecursiveNamedCatalogPreparedInitialization.environment compiled))
      current.cached.compilation current.profile (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag)
      extension faithful observations functionTypes (escaped current member) (uninitialized current member) (missing current member)
      saved.installed arguments current.owner initial.val saved.sameFrame heaps actualTrace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, related, finalHeaps, maps, worlds, frame, metadata, reached, poolRelated⟩ := produced
  have reference := saved.installed.globalReference
  rw [saved.sameIndex] at reference
  refine ⟨value, finalStore, finalMap, finalWorld, .applied reference saved.installed.globalRead evaluated,
    ?_, finalHeaps, maps, worlds, frame, metadata,
    wrap_post profileFlag rows initial reached maps worlds frame metadata, poolRelated⟩
  simpa only [SourceCoreCompatibleValues.Context.initial, CheckedRow.coercion_row, current.selected.result, current.selected.signature] using related

include extension faithful observations functionTypes escaped uninitialized missing in
/-- The original InvokeSized child remains native-strict, while the closed
reflection independently supplies the Source outcome and actual reached pool. -/
private theorem steps_reflect (budget : Nat) (reason : Word) :
    ProtectedCoercionPathMeaning.StepReflects (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (row := CheckedRow.coercion_row profileFlag) (registry := registry) (faults := faults)
      (pathProtocol profileFlag rows) [] (RecursiveNamedCatalogPreparedInitialization.environment compiled) (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) (SourceSemantics.Program.ofChecked compiled.sourceProgram) (CallableCoercionSpine.InvokeSized budget (RecursiveNamedCatalogPreparedInitialization.environment compiled) reason) rows := by
  intro current mapping world before store finalStore input native value member initial heaps represented completed
  obtain ⟨saved⟩ := initial.property current member
  change ValueRep compiled.compatible.checked registry (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) mapping world current.step.source input native current.call.signature.parameterType at represented
  change CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) mapping world before store at heaps
  have arguments : CallableIndexedParameterMeaning.Arguments
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag))
      mapping world current.cached.named.inputs [input] [native] := by
    rw [current.selected.bindings]
    apply CallableIndexedParameterMeaning.Arguments.cons _ .nil
    change ValueRep _ _ _ _ _ current.selected.binder.scheme.body _ _ _
    simpa only [current.selected.inputType] using represented
  change CallableCoercionSpine.InvokeSized budget (RecursiveNamedCatalogPreparedInitialization.environment compiled) reason current.call store (.inRight .word native) value finalStore at completed
  let captured : CallablePreparedOperatorSuffixMeaning.Capture (current.method_row profileFlag) (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) (RecursiveNamedCatalogPreparedInitialization.environment compiled) mapping world before store :=
    ⟨saved.installed, saved.sameIndex⟩
  obtain ⟨bodySize, _strict, body⟩ := CallablePreparedOperatorSuffixMeaning.Capture.completed_sized
    (method := current.method_row profileFlag) (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) captured completed
  have produced :=
    CallableIndexedOwnedMethodBuiltinBounds.invocation_reflects
      (compiled := compiled) (program := (SourceSemantics.Program.ofChecked compiled.sourceProgram)) (headers := headers) (keys := keys)
      (registry := registry) (faults := faults)
      (named := current.cached.named) (diagnostics := current.cached.diagnostics) (code := current.cached.code)
      (sourceBody := sourceBody (compiled := compiled) (method := current.method))
      (dictionary := current.dictionary) (administrative := current.bootstrap.capture.administrative)
      (mapping := mapping) (world := world) (before := before) (store := store)
      (callerEnvironment := (RecursiveNamedCatalogPreparedInitialization.environment compiled)) (callerScope := []) (callerCanonical := (RecursiveNamedCatalogPreparedInitialization.environment compiled))
      current.cached.compilation current.profile (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag)
      extension faithful observations functionTypes (escaped current member) (uninitialized current member) (missing current member)
      saved.installed arguments current.owner initial.val saved.sameFrame heaps body
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, actualTrace, related, finalHeaps, maps, worlds, frame, metadata, reached, poolRelated⟩ := produced
  refine ⟨outcome, after, finalMap, finalWorld, actualTrace.sound, ?_, finalHeaps, maps, worlds, frame, metadata,
    wrap_post profileFlag rows initial reached maps worlds frame metadata, poolRelated⟩
  simpa only [SourceCoreCompatibleValues.Context.initial, CheckedRow.coercion_row, current.selected.result, current.selected.signature] using related


section Pair
variable (first second : CheckedRow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
  (context := context) (evidence := evidence) (project := project) (compilation := compilation)
  (caller := caller) (available := available) (scope := scope) (node := node) (policy := policy) profileFlag)

/-- Both true bootstrap receipts have the same entire store, so their actual
worlds agree. The pool and the two ordered capture rows are retained directly. -/
def initial_pair
    (pool : State headers keys ⟨[], [], first.bootstrap.world, ⟨[]⟩, (RecursiveNamedCatalogPreparedInitialization.store compiled), (RecursiveNamedCatalogPreparedInitialization.environment compiled)⟩) :
    (pathProtocol profileFlag [first, second]).State
      ⟨[], [], first.bootstrap.world, ⟨[]⟩, (RecursiveNamedCatalogPreparedInitialization.store compiled), (RecursiveNamedCatalogPreparedInitialization.environment compiled)⟩ :=
  ⟨pool, by
    intro current member
    rcases List.mem_cons.mp member with same | member
    · subst current
      exact ⟨⟨first.bootstrap.capture.installed,
        first.bootstrap.capture.frame_eq.trans first.physical.symm, first.selected.index⟩⟩
    · have same := List.mem_singleton.mp member
      subst current
      have saved : Saved profileFlag second
          ⟨[], [], second.bootstrap.world, ⟨[]⟩, (RecursiveNamedCatalogPreparedInitialization.store compiled), (RecursiveNamedCatalogPreparedInitialization.environment compiled)⟩ :=
        ⟨second.bootstrap.capture.installed,
          second.bootstrap.capture.frame_eq.trans second.physical.symm, second.selected.index⟩
      have same : second.bootstrap.world = first.bootstrap.world :=
        second.bootstrap.typed.world_eq.trans first.bootstrap.typed.world_eq.symm
      exact ⟨same ▸ saved⟩⟩

/-- Raw Source types and native types join separately; their projection alone
is never used to identify the original Source path. -/
theorem pair_chain (sourceJoin : first.step.target = second.step.source)
    (nativeJoin : first.call.signature.resultType = second.call.signature.parameterType) :
    CallableCoercionPathMeaning.ChainFor (CheckedRow.coercion_row profileFlag)
      first.step.source first.call.signature.parameterType [first, second]
      second.step.target second.call.signature.resultType := by
  apply CallableCoercionPathMeaning.ChainFor.cons
  change CallableCoercionPathMeaning.ChainFor _ first.step.target first.call.signature.resultType
    [second] second.step.target second.call.signature.resultType
  rw [sourceJoin, nativeJoin]
  exact .cons (.nil _ _)

/-- The actual compiler steps compose in their recorded order, retaining full
method/dictionary/global receipts and the real emitted suffix. -/
theorem emitted_pair (codeJoin : first.outputCode = second.inputCode) :
    CallableCoercionSpine.Spine compiled.sourceProgram project compilation caller available scope node policy
      first.inputCode [first.step, second.step] second.outputCode [first.call, second.call] := by
  apply CallableCoercionSpine.Spine.cons first.emission
  rw [codeJoin]
  exact .cons second.emission .nil

private theorem ordinary_pair {before after : Dynamic.Heap} {input : Dynamic.Value}
    {outcome : Dynamic.ExpressionOutcome}
    (trace : CallableCoercionPathMeaning.SelectedTraceFor (CheckedRow.coercion_row profileFlag)
      (SourceSemantics.Program.ofChecked compiled.sourceProgram) [first, second] before input outcome after) :
    CallableCoercionExpressionMeaning.Path (SourceSemantics.Program.ofChecked compiled.sourceProgram) context evidence before
      [first.step, second.step] input outcome after := by
  cases trace with
  | fault failed => exact .head (.method first.selected.selector failed)
  | cons invoked tail =>
    cases tail with
    | fault failed => exact .tail (.method first.selected.selector invoked) (.head (.method second.selected.selector failed))
    | cons called tail =>
      cases tail
      exact .cons (.method first.selected.selector invoked) (.cons (.method second.selected.selector called) .nil)

/-- The independent original Source grade is obtained from the same genuine
selected path, reusing existing Source grading rather than a new induction. -/
theorem graded_pair {before after : Dynamic.Heap} {input : Dynamic.Value}
    {outcome : Dynamic.ExpressionOutcome}
    (trace : CallableCoercionPathMeaning.SelectedTraceFor (CheckedRow.coercion_row profileFlag)
      (SourceSemantics.Program.ofChecked compiled.sourceProgram) [first, second] before input outcome after) :
    ∃ sourceSize, CallablePreparedOperatorSourceBounds.PathAt (SourceSemantics.Program.ofChecked compiled.sourceProgram) sourceSize context evidence
      before [first.step, second.step] input outcome after := by
  have source := ordinary_pair profileFlag first second trace
  cases outcome with
  | value value => exact SourceExecutionSize.CoercionPathExecutes.has_size source
  | fault reason => exact SourceExecutionSize.CoercionPathFaults.has_size source

variable (sourceJoin : first.step.target = second.step.source)
  (nativeJoin : first.call.signature.resultType = second.call.signature.parameterType)
  (codeJoin : first.outputCode = second.inputCode)
  (pool : State headers keys ⟨[], [], first.bootstrap.world, ⟨[]⟩, (RecursiveNamedCatalogPreparedInitialization.store compiled), (RecursiveNamedCatalogPreparedInitialization.environment compiled)⟩)
  (pairEscaped : ∀ row, row ∈ [first, second] → faults .controlEscapedFunction row.cached.compilation.own.table.escapedReason)
  (pairUninitialized : ∀ row, row ∈ [first, second] → ∀ id location,
    faults (.uninitializedLocation location) (row.cached.diagnostics.reasonAt row.cached.named.signature.key id))
  (pairMissing : ∀ row, row ∈ [first, second] → ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((row.cached.diagnostics.reasonAt row.cached.named.signature.key id).add tag))

include extension faithful observations functionTypes pairEscaped pairUninitialized pairMissing sourceJoin nativeJoin codeJoin pool in
/-- Two closed checked methods use the actual first post as the second input.
Both success and faults return the true final pool and the same ordered source
path; every retained record still has its live snapshot observation. -/
theorem pair_preserves {input : Dynamic.Value} {native : Value} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (represented : ValueRep compiled.compatible.checked registry
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag)
      [] first.bootstrap.world first.step.source input native first.call.signature.parameterType)
    (trace : CallableCoercionPathMeaning.SelectedTraceFor (CheckedRow.coercion_row profileFlag)
      (SourceSemantics.Program.ofChecked compiled.sourceProgram) [first, second] ⟨[]⟩ input outcome after) (reason : Word) :
    ∃ sourceSize value finalStore finalMap finalWorld,
      CallableCoercionSpine.Spine compiled.sourceProgram project compilation caller available scope node policy
        first.inputCode [first.step, second.step] second.outputCode [first.call, second.call] ∧
      CallablePreparedOperatorSourceBounds.PathAt (SourceSemantics.Program.ofChecked compiled.sourceProgram) sourceSize context evidence ⟨[]⟩ [first.step, second.step] input outcome after ∧
      CallableCoercionSpine.Runs (RecursiveNamedCatalogPreparedInitialization.environment compiled) reason (RecursiveNamedCatalogPreparedInitialization.store compiled) (.inRight .word native) [first.call, second.call] value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag)) finalMap finalWorld
        second.step.target second.call.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) finalMap finalWorld after finalStore ∧
      LocationMap.Extends [] finalMap ∧ WorldExtends first.bootstrap.world finalWorld ∧
      AdministrativePreserved [] (RecursiveNamedCatalogPreparedInitialization.store compiled) finalMap finalStore ∧ Dynamic.HeapMetadataExtend ⟨[]⟩ after ∧
      ∃ reached : State headers keys ⟨[], finalMap, finalWorld, after, finalStore, (RecursiveNamedCatalogPreparedInitialization.environment compiled)⟩,
        Relates pool reached ∧ (∀ row, RecordPrefix (records pool row) (records reached row)) ∧
        (∀ row record, record ∈ records reached row → CallableIndexedSnapshots.Holds compiled.indexed.ancestry.graph.inputs
          compiled.indexed.ancestry.graph.table compiled.indexed.ancestry.layout.frame finalMap finalStore record) ∧
        (∀ row record, record ∈ records pool row → record ∈ records reached row) := by
  have step : ProtectedCoercionPathMeaning.StepPreserves
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (row := CheckedRow.coercion_row profileFlag) (registry := registry) (faults := faults)
      (caller := (RecursiveNamedCatalogPreparedInitialization.environment compiled)) (reason := reason) (pathProtocol profileFlag [first, second]) [] (RecursiveNamedCatalogPreparedInitialization.environment compiled)
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) (SourceSemantics.Program.ofChecked compiled.sourceProgram) [first, second] :=
    steps_preserve profileFlag [first, second] extension faithful observations functionTypes
    pairEscaped pairUninitialized pairMissing reason
  obtain ⟨value, finalStore, finalMap, finalWorld, runs, related, heaps, maps, worlds, frame, metadata, reached, poolRelated⟩ :=
    ProtectedCoercionPathMeaning.preserves
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (row := CheckedRow.coercion_row profileFlag) (registry := registry) (faults := faults)
      (caller := (RecursiveNamedCatalogPreparedInitialization.environment compiled)) (reason := reason) (pathProtocol profileFlag [first, second]) [] (RecursiveNamedCatalogPreparedInitialization.environment compiled)
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) (SourceSemantics.Program.ofChecked compiled.sourceProgram) step
      (pair_chain profileFlag first second sourceJoin nativeJoin)
      (initial_pair profileFlag first second pool) first.bootstrap.heaps represented trace
  obtain ⟨sourceSize, graded⟩ := graded_pair profileFlag first second trace
  exact ⟨sourceSize, value, finalStore, finalMap, finalWorld, emitted_pair profileFlag first second codeJoin,
    graded, runs, related, heaps, maps, worlds, frame, metadata, reached.val, poolRelated, reached_pool_observations poolRelated⟩

include extension faithful observations functionTypes pairEscaped pairUninitialized pairMissing sourceJoin nativeJoin codeJoin pool in
/-- Actual measured native invocations reflect the same two selected Source
methods. Source grading remains independent of the native budget, and final
records come only from the returned state of the shared ordered fold. -/
theorem pair_reflects {input : Dynamic.Value} {native value : Value} {budget : Nat} {reason : Word} {finalStore : Store}
    (represented : ValueRep compiled.compatible.checked registry
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag)
      [] first.bootstrap.world first.step.source input native first.call.signature.parameterType)
    (runs : CallableCoercionSpine.RunsFor (CallableCoercionSpine.InvokeSized budget (RecursiveNamedCatalogPreparedInitialization.environment compiled) reason)
      (RecursiveNamedCatalogPreparedInitialization.store compiled) (.inRight .word native) [first.call, second.call] value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      CallableCoercionSpine.Spine compiled.sourceProgram project compilation caller available scope node policy
        first.inputCode [first.step, second.step] second.outputCode [first.call, second.call] ∧
      CallableCoercionPathMeaning.SelectedTraceFor (CheckedRow.coercion_row profileFlag)
        (SourceSemantics.Program.ofChecked compiled.sourceProgram) [first, second] ⟨[]⟩ input outcome after ∧
      CallablePreparedOperatorSourceBounds.PathAt (SourceSemantics.Program.ofChecked compiled.sourceProgram) sourceSize context evidence ⟨[]⟩ [first.step, second.step] input outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag)) finalMap finalWorld
        second.step.target second.call.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) finalMap finalWorld after finalStore ∧
      LocationMap.Extends [] finalMap ∧ WorldExtends first.bootstrap.world finalWorld ∧
      AdministrativePreserved [] (RecursiveNamedCatalogPreparedInitialization.store compiled) finalMap finalStore ∧ Dynamic.HeapMetadataExtend ⟨[]⟩ after ∧
      ∃ reached : State headers keys ⟨[], finalMap, finalWorld, after, finalStore, (RecursiveNamedCatalogPreparedInitialization.environment compiled)⟩,
        Relates pool reached ∧ (∀ row, RecordPrefix (records pool row) (records reached row)) ∧
        (∀ row record, record ∈ records reached row → CallableIndexedSnapshots.Holds compiled.indexed.ancestry.graph.inputs
          compiled.indexed.ancestry.graph.table compiled.indexed.ancestry.layout.frame finalMap finalStore record) ∧
        (∀ row record, record ∈ records pool row → record ∈ records reached row) := by
  have step : ProtectedCoercionPathMeaning.StepReflects
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (row := CheckedRow.coercion_row profileFlag) (registry := registry) (faults := faults)
      (pathProtocol profileFlag [first, second]) [] (RecursiveNamedCatalogPreparedInitialization.environment compiled)
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) (SourceSemantics.Program.ofChecked compiled.sourceProgram)
      (CallableCoercionSpine.InvokeSized budget (RecursiveNamedCatalogPreparedInitialization.environment compiled) reason) [first, second] :=
    steps_reflect profileFlag [first, second] extension faithful observations functionTypes
    pairEscaped pairUninitialized pairMissing budget reason
  obtain ⟨outcome, after, finalMap, finalWorld, trace, related, heaps, maps, worlds, frame, metadata, reached, poolRelated⟩ :=
    ProtectedCoercionPathMeaning.reflects
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (row := CheckedRow.coercion_row profileFlag) (registry := registry) (faults := faults)
      (caller := (RecursiveNamedCatalogPreparedInitialization.environment compiled)) (reason := reason) (pathProtocol profileFlag [first, second]) [] (RecursiveNamedCatalogPreparedInitialization.environment compiled)
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) (SourceSemantics.Program.ofChecked compiled.sourceProgram)
      (fun completed => completed.forget) step (pair_chain profileFlag first second sourceJoin nativeJoin)
      (initial_pair profileFlag first second pool) first.bootstrap.heaps represented (by simpa only [List.map_cons, List.map_nil, CheckedRow.coercion_row] using runs)
  obtain ⟨sourceSize, graded⟩ := graded_pair profileFlag first second trace
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, emitted_pair profileFlag first second codeJoin,
    trace, graded, related, heaps, maps, worlds, frame, metadata, reached.val, poolRelated, reached_pool_observations poolRelated⟩
end Pair

end Tests.SourceCoreClosedOwnedCoercionPath
