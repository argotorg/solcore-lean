import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodInvocationEntries
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalCanonicalState
import Solcore.SourceSemantics.CoreLowering.RecursiveStageMeaning
import Solcore.SourceSemantics.Staging.RecursiveTraceSize

/-! Staged method invocation enters the actual marked parameter prefix and
restores the caller from the body's reached pool. Both callbacks receive the
real complete cache and slot layout, and preserve semantic and stage faults. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodInvocationBounds
open Core Frontend SourceInference GeneralHeap CoreProof ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedParameterCertificates CallableIndexedParameterMeaning SourceCoreCallableIndexedFrames
open CallableIndexedOwnedFunctionState CallablePreparedMethodRuntimeMeaning
open CallableIndexedOwnedMethodInvocationBounds (ParameterEntry)
open CallableIndexedOwnedPreparedStagedMethodInvocationEntries

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program}
  {code : Expr} (generation : CallableIndexedNamedGeneration.Compilation compiled.indexed named diagnostics code)
  {sourceBody : Dynamic.BodyInstance} {dictionary : Dynamic.EvidenceEnvironment}
  {administrative : Core.Context} {registry : SourceCoreRawMetadata.Registry}
  (sourceAt : CallablePreparedMethodRuntimeProfileFactory.SourceAt generation
    (.initial compiled.compatible.checked) sourceBody dictionary)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {callerEnvironment : Environment} {arguments : List Dynamic.Value} {payloads : List Value}
  (installed : Installed generation (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (sourceBody := sourceBody)
    (administrative := administrative) functions mapping world before store callerEnvironment)
  (represented : Arguments (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    mapping world named.inputs arguments payloads)
  {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (sameFrame : installed.frameLocation = owner.key.frameLocation)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world before store)


variable {stages : Staging.Recursive.Registry} {child : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}
  (physical : CallableIndexedOwnedPhysicalGlobals.Authority compiled mapping store)
  (slots : CallableIndexedOwnedPhysicalGlobals.Slots compiled 0 [] installed.canonical)

/-- The Source body callback starts at the exact parameter-produced state. -/
def SourceBodyAt (budget : Nat)
    {initialStore : Store} {location : Location} {native : NativeFrame}
    {actualContext : Core.Context} {actual : Environment} {ξ : Renaming}
    (entry : ParameterEntry compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
      location native (.initial compiled.compatible.checked) functions registry
      (methodFunction generation sourceBody dictionary) sourceAt.context named.inputs arguments before initialStore mapping world
      administrative actualContext actual ξ generation.parameterCode generation.body)
    (reached : State headers keys ⟨named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)),
      entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩) : Prop :=
  ∀ {size finalContext bodyOutcome outcome after},
    Staging.Recursive.Size.StatementsIn program stages true size child sourceAt.context entry.environment
      entry.heap generation.statements finalContext bodyOutcome after →
    Staging.Recursive.BodyResult sourceBody.resultType bodyOutcome outcome → size < budget →
    ∃ value finalStore finalMap finalWorld,
      Evaluates entry.actualBody entry.store (generation.body.rename entry.embedding) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld sourceBody.resultType named.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends entry.mapping finalMap ∧ WorldExtends entry.world finalWorld ∧
      AdministrativePreserved entry.mapping entry.store finalMap finalStore ∧ Dynamic.HeapMetadataExtend entry.heap after ∧
      ProtectedStateTransition.Transition (protocol headers keys) reached
        ⟨named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)), finalMap, finalWorld, after, finalStore, entry.canonical⟩

/-- Reflection uses the native body's independent strict grade. -/
def NativeBodyAt (budget : Nat)
    {initialStore : Store} {location : Location} {native : NativeFrame}
    {actualContext : Core.Context} {actual : Environment} {ξ : Renaming}
    {prefixSize : Nat} {value : Value} {finalStore : Store}
    (entry : Prefix compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
      location native (.initial compiled.compatible.checked) functions registry
      (methodFunction generation sourceBody dictionary) sourceAt.context named.inputs arguments before initialStore mapping world
      administrative actualContext actual ξ generation.parameterCode generation.body prefixSize value finalStore)
    (reached : State headers keys ⟨named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)),
      entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩) : Prop :=
  entry.childSize < budget →
    ∃ sourceSize finalContext bodyOutcome outcome after finalMap finalWorld,
      Staging.Recursive.Size.StatementsIn program stages true sourceSize child sourceAt.context entry.environment
        entry.heap generation.statements finalContext bodyOutcome after ∧
      Staging.Recursive.BodyResult sourceBody.resultType bodyOutcome outcome ∧
      RecursiveStageMeaning.ResultRepresentsFor (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld sourceBody.resultType named.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends entry.mapping finalMap ∧ WorldExtends entry.world finalWorld ∧
      AdministrativePreserved entry.mapping entry.store finalMap finalStore ∧ Dynamic.HeapMetadataExtend entry.heap after ∧
      ProtectedStateTransition.Transition (protocol headers keys) reached
        ⟨named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)), finalMap, finalWorld, after, finalStore, entry.canonical⟩

def SourceContinuation (budget : Nat) : Prop :=
  ∀ (originId : Word) (index : Int) (metadata : MetadataState)
    (_selected : compiled.indexed.ancestry.graph.inputs.callable.table.idAt?
      (.named named.signature.key) = some originId)
    (_history : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      (.state index) (.named originId) (some metadata))
    (_emitted : generation.output = withFrame (.var (compiled.indexed.base.globals.length + 1))
      (SourceCoreCallableIndexedDispatch.literal compiled.indexed.ancestry.layout.frame (.state index)) generation.parameterCode)
    (entry : ParameterEntry compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
      owner.key.frameLocation (.state index) (.initial compiled.compatible.checked) functions registry
      (methodFunction generation sourceBody dictionary) sourceAt.context named.inputs arguments before
      (store.set owner.key.frameLocation (encode compiled.indexed.ancestry.layout.frame (.state index))) mapping world
      administrative (.unit :: compiled.indexed.ancestry.layout.frame.type :: named.signature.parameterType :: installed.capturedContext)
      (.unit :: encode compiled.indexed.ancestry.layout.frame (caller.rows owner.position).authority.current ::
        DataPatternValues.packValues payloads :: installed.captured)
      (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) installed.embedding.lift))
      generation.parameterCode generation.body)
    (added : Environment), added.length = named.inputs.length →
    entry.canonical = added ++ DataPatternValues.packValues payloads :: installed.canonical →
  ∀ (reached : State headers keys ⟨named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)),
      entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩),
    Relates caller reached →
    CallableIndexedOwnedPhysicalGlobals.Authority compiled entry.mapping entry.store →
    CallableIndexedOwnedPhysicalGlobals.Slots compiled 1
      (named.inputs.reverse.map (fun binding => (binding.1.id, binding.2))) entry.canonical →
    SourceBodyAt (stages := stages) (child := child) (faults := faults)
      generation sourceAt functions budget entry reached

def NativeContinuation (budget : Nat) : Prop :=
  ∀ (originId : Word) (index : Int) (metadata : MetadataState) (prefixSize : Nat) (bodyStore : Store)
    (_selected : compiled.indexed.ancestry.graph.inputs.callable.table.idAt?
      (.named named.signature.key) = some originId)
    (_history : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      (.state index) (.named originId) (some metadata))
    (_prefixWithin : prefixSize < budget)
    {value : Value} {finalStore : Store}
    (_restored : finalStore = bodyStore.set owner.key.frameLocation
      (encode compiled.indexed.ancestry.layout.frame (caller.rows owner.position).authority.current))
    (entry : Prefix compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
      owner.key.frameLocation (.state index) (.initial compiled.compatible.checked) functions registry
      (methodFunction generation sourceBody dictionary) sourceAt.context named.inputs arguments before
      (store.set owner.key.frameLocation (encode compiled.indexed.ancestry.layout.frame (.state index))) mapping world
      administrative (.unit :: compiled.indexed.ancestry.layout.frame.type :: named.signature.parameterType :: installed.capturedContext)
      (.unit :: encode compiled.indexed.ancestry.layout.frame (caller.rows owner.position).authority.current ::
        DataPatternValues.packValues payloads :: installed.captured)
      (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) installed.embedding.lift))
      generation.parameterCode generation.body prefixSize value bodyStore)
    (added : Environment), added.length = named.inputs.length →
    entry.canonical = added ++ DataPatternValues.packValues payloads :: installed.canonical →
  ∀ (reached : State headers keys ⟨named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)),
      entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩),
    Relates caller reached →
    CallableIndexedOwnedPhysicalGlobals.Authority compiled entry.mapping entry.store →
    CallableIndexedOwnedPhysicalGlobals.Slots compiled 1
      (named.inputs.reverse.map (fun binding => (binding.1.id, binding.2))) entry.canonical →
    NativeBodyAt (stages := stages) (child := child) (faults := faults)
      generation sourceAt functions budget entry reached

include sourceAt installed represented sameFrame heaps physical slots in
theorem preserves (budget : Nat)
    (bodyMeaning : SourceContinuation (registry := registry) (program := program) (headers := headers) (keys := keys)
      (owner := owner) (caller := caller) (arguments := arguments) (payloads := payloads)
      (stages := stages) (child := child) (faults := faults) generation sourceAt functions installed budget)
    {bodySize : Nat} {environment : Dynamic.Environment} {bound after : Dynamic.Heap}
    {finalContext : SourceSemantics.Context} {bodyOutcome : Staging.Recursive.BodyOutcome}
    {outcome : Staging.Recursive.Outcome}
    (allocated : Dynamic.BindersAllocate [] before (methodFunction generation sourceBody dictionary).parameters
      arguments environment bound)
    (bodyTrace : Staging.Recursive.Size.StatementsIn program stages true bodySize child sourceAt.context environment
      bound generation.statements finalContext bodyOutcome after)
    (matched : Staging.Recursive.BodyResult sourceBody.resultType bodyOutcome outcome)
    (within : bodySize < budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (DataPatternValues.packValues payloads :: installed.captured) store
        (generation.output.rename installed.embedding.lift) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld sourceBody.resultType named.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition (protocol headers keys) caller
        ⟨callerScope, finalMap, finalWorld, after, finalStore, callerCanonical⟩ := by
  obtain ⟨originId, index, metadata, owned, history, emitted, entry, added, length, spine, parameterState, parameterRelated⟩ :=
    parameters_with_state generation sourceAt functions installed represented owner caller sameFrame heaps
  obtain ⟨sameEnvironment, sameHeap⟩ := FunctionCallBody.allocations_same entry.allocation allocated
  rw [← sameEnvironment, ← sameHeap] at bodyTrace
  let physicalEntry := CallableIndexedOwnedPhysicalCanonicalState.of_parameter_spine physical
    (by
      have same : (caller.rows owner.position).authority.frameLocation = owner.key.frameLocation :=
        (caller.rows owner.position).frame_eq
      simpa only [same] using (caller.rows owner.position).authority.frame.read)
    (.state index) entry.frame parameterState slots (DataPatternValues.packValues payloads)
    (by simpa only [List.length_map, List.length_reverse] using length) spine
  obtain ⟨value, bodyStore, finalMap, finalWorld, bodyEvaluation, result, finalHeaps,
    bodyMaps, bodyWorlds, bodyFrame, bodyMetadata, bodyState, bodyRelated⟩ :=
    bodyMeaning originId index metadata owned history emitted entry added length spine parameterState parameterRelated
      physicalEntry.physical physicalEntry.base.property bodyTrace matched within
  have prefixEvaluation := entry.agreement.wrap bodyEvaluation
  rw [rename_prefix] at prefixEvaluation
  let authority := (caller.rows owner.position).authority
  have physical : authority.frameLocation = owner.key.frameLocation := (caller.rows owner.position).frame_eq
  have read : store.read? owner.key.frameLocation = some (encode compiled.indexed.ancestry.layout.frame authority.current) := by
    simpa only [physical] using authority.frame.read
  have reference : (DataPatternValues.packValues payloads :: installed.captured)[installed.embedding.lift
      (compiled.indexed.base.globals.length + 1)]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
    simpa only [sameFrame, Renaming.lift, Nat.succ_sub_one, List.getElem?_cons_succ] using installed.capturedReference
  have evaluated := CallableContextFrames.withFrame_evaluates (.var reference) read
    (next_evaluates index (DataPatternValues.packValues payloads :: installed.captured) store
      (encode compiled.indexed.ancestry.layout.frame authority.current)) prefixEvaluation
  have renamed : generation.output.rename installed.embedding.lift = withFrame
      (.var (installed.embedding.lift (compiled.indexed.base.globals.length + 1)))
      (SourceCoreCallableIndexedDispatch.literal compiled.indexed.ancestry.layout.frame (.state index))
      (generation.parameterCode.rename installed.embedding.lift) := by
    rw [emitted, NamedCalls.withFrame_rename, Expr.rename, CallableIndexedRenaming.literal]
  have maps := entry.maps.trans bodyMaps
  have worlds := entry.worlds.trans bodyWorlds
  have frame := entry.frame.trans bodyFrame
  have sourceMetadata := entry.metadata.trans bodyMetadata
  have related : Relates caller bodyState := parameterRelated.trans bodyRelated
  obtain ⟨restoredHeaps, restoredFrame, _cell, _bodyRelated, _callerRelated, _records, returned⟩ :=
    CallableIndexedOwnedBodyRestoration.restore_return caller bodyState owner.position (CallableIndexedAmbient.frame_registered compiled.indexed)
      finalHeaps worlds frame related
  refine ⟨value, _, finalMap, finalWorld, ?_, result, restoredHeaps, maps, worlds, restoredFrame, sourceMetadata, returned⟩
  exact renamed.symm ▸ evaluated

include sourceAt installed represented sameFrame heaps physical slots in
theorem reflects (budget : Nat)
    (bodyMeaning : NativeContinuation (registry := registry) (program := program) (headers := headers) (keys := keys)
      (owner := owner) (caller := caller) (arguments := arguments) (payloads := payloads)
      (stages := stages) (child := child) (faults := faults) generation sourceAt functions installed budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size (DataPatternValues.packValues payloads :: installed.captured) store
      (generation.output.rename installed.embedding.lift) value finalStore) (within : size ≤ budget) :
    ∃ sourceSize environment bound finalContext bodyOutcome outcome after finalMap finalWorld,
      Dynamic.BindersAllocate [] before (methodFunction generation sourceBody dictionary).parameters arguments environment bound ∧
      Staging.Recursive.Size.StatementsIn program stages true sourceSize child sourceAt.context environment
        bound generation.statements finalContext bodyOutcome after ∧
      Staging.Recursive.BodyResult sourceBody.resultType bodyOutcome outcome ∧
      RecursiveStageMeaning.ResultRepresentsFor (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld sourceBody.resultType named.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition (protocol headers keys) caller
        ⟨callerScope, finalMap, finalWorld, after, finalStore, callerCanonical⟩ := by
  obtain ⟨originId, index, metadata, prefixSize, bodyStore, owned, history, strict, restored,
    entry, added, length, spine, parameterState, parameterRelated⟩ :=
    body_prefix_with_state generation sourceAt functions installed represented owner caller sameFrame heaps completed
  let physicalEntry := CallableIndexedOwnedPhysicalCanonicalState.of_parameter_spine physical
    (by
      have same : (caller.rows owner.position).authority.frameLocation = owner.key.frameLocation :=
        (caller.rows owner.position).frame_eq
      simpa only [same] using (caller.rows owner.position).authority.frame.read)
    (.state index) entry.frame parameterState slots (DataPatternValues.packValues payloads)
    (by simpa only [List.length_map, List.length_reverse] using length) spine
  obtain ⟨sourceSize, finalContext, bodyOutcome, outcome, after, finalMap, finalWorld, bodyTrace, matched, result, finalHeaps,
    bodyMaps, bodyWorlds, bodyFrame, bodyMetadata, bodyState, bodyRelated⟩ :=
    bodyMeaning originId index metadata prefixSize bodyStore owned history
      (Nat.lt_of_lt_of_le strict within) restored entry added length spine parameterState parameterRelated
      physicalEntry.physical physicalEntry.base.property
      (Nat.lt_of_le_of_lt entry.bounded (Nat.lt_of_lt_of_le strict within))
  have maps := entry.maps.trans bodyMaps
  have worlds := entry.worlds.trans bodyWorlds
  have frame := entry.frame.trans bodyFrame
  have sourceMetadata := entry.metadata.trans bodyMetadata
  have related : Relates caller bodyState := parameterRelated.trans bodyRelated
  obtain ⟨restoredHeaps, restoredFrame, _cell, _bodyRelated, _callerRelated, _records, returned⟩ :=
    CallableIndexedOwnedBodyRestoration.restore_return caller bodyState owner.position (CallableIndexedAmbient.frame_registered compiled.indexed)
      finalHeaps worlds frame related
  subst finalStore
  exact ⟨sourceSize, entry.environment, entry.heap, finalContext, bodyOutcome, outcome, after, finalMap, finalWorld,
    entry.allocation, bodyTrace, matched, result, restoredHeaps, maps, worlds, restoredFrame, sourceMetadata, returned⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodInvocationBounds
