import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodInvocationBounds
import Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodRuntimeProfileFactory

/-! Actual method hook and marked parameter entry, using only the original
Source frame and compiler prefix. The body has no execution contract here. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodInvocationEntries
open Core Frontend SourceInference GeneralHeap CoreProof ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedParameterCertificates CallableIndexedParameterMeaning SourceCoreCallableIndexedFrames
open CallableIndexedOwnedFunctionState CallablePreparedMethodRuntimeMeaning
open CallableIndexedOwnedMethodInvocationBounds (ParameterEntry parameter_entry_with_state parameter_prefix_with_state)

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

theorem rename_prefix (body : Expr) (ξ : Renaming) :
    body.rename (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ)) =
      ((body.rename ξ).weakenAt 0).weakenAt 0 := by
  rw [GenericExpressionMeaning.rename_prefix, GenericExpressionMeaning.rename_prefix]

theorem next_evaluates (index : Int) (actual : Environment) (initialStore : Store) (saved : Value) :
    Evaluates (saved :: actual) initialStore
      ((SourceCoreCallableIndexedDispatch.literal compiled.indexed.ancestry.layout.frame (.state index)).weakenAt 0)
      (encode compiled.indexed.ancestry.layout.frame (.state index)) initialStore := by
  rw [← Expr.rename_insertion, CallableIndexedRenaming.literal]
  exact CallableIndexedContextFrames.literal_evaluates _ _ _ _

include sourceAt in
theorem accepted_parameters : SourceCoreSourceCells.bindParameters
    (CallableIndexedNamedGeneration.allocator compiled.indexed named) sourceBody.source [] named.inputs
    named.signature.resultType SourceCoreFunctions.argumentProjection generation.body = .ok generation.parameterCode := by
  rw [sourceAt.sameSource]
  exact generation.parametersCompiled

include sameFrame in
/-- Both original reads refer to the same physical cell. Its saved native
frame therefore agrees with the actual selected pool row; no ghost-history
substitution or equality of record lists is assumed. -/
theorem installed_current_eq : installed.current = (caller.rows owner.position).authority.current := by
  have physical : (caller.rows owner.position).authority.frameLocation = owner.key.frameLocation := (caller.rows owner.position).frame_eq
  have poolRead : store.read? owner.key.frameLocation = some
      (encode compiled.indexed.ancestry.layout.frame (caller.rows owner.position).authority.current) := by
    simpa only [physical] using (caller.rows owner.position).authority.frame.read
  have originalRead : store.read? owner.key.frameLocation = some
      (encode compiled.indexed.ancestry.layout.frame installed.current) := by
    simpa only [sameFrame] using installed.caller.read
  have encoded := Option.some.inj (originalRead.symm.trans poolRead)
  have decoded := congrArg (decode compiled.indexed.ancestry.layout.frame) encoded
  rw [decode_encode, decode_encode] at decoded
  exact Option.some.inj decoded

include sourceAt installed represented sameFrame heaps in
/-- The actual pool is installed at the method's real physical frame before
shared marked parameters allocate every snapshot. Complete method captures and
ordered canonical spines accompany the actual parameter post witness. -/
theorem parameters_with_state :
    ∃ originId index metadata,
      compiled.indexed.ancestry.graph.inputs.callable.table.idAt? (.named named.signature.key) = some originId ∧
      Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table (.state index) (.named originId) (some metadata) ∧
      generation.output = withFrame (.var (compiled.indexed.base.globals.length + 1))
        (SourceCoreCallableIndexedDispatch.literal compiled.indexed.ancestry.layout.frame (.state index)) generation.parameterCode ∧
    ∃ entry : ParameterEntry compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
      owner.key.frameLocation (.state index) (.initial compiled.compatible.checked) functions registry
      (methodFunction generation sourceBody dictionary) sourceAt.context named.inputs arguments before
      (store.set owner.key.frameLocation (encode compiled.indexed.ancestry.layout.frame (.state index))) mapping world
      administrative (.unit :: compiled.indexed.ancestry.layout.frame.type :: named.signature.parameterType :: installed.capturedContext)
      (.unit :: encode compiled.indexed.ancestry.layout.frame (caller.rows owner.position).authority.current ::
        DataPatternValues.packValues payloads :: installed.captured)
      (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) installed.embedding.lift))
      generation.parameterCode generation.body,
    ∃ added : Environment, added.length = named.inputs.length ∧
      entry.canonical = added ++ DataPatternValues.packValues payloads :: installed.canonical ∧
      ProtectedStateTransition.Transition (protocol headers keys) caller
        ⟨named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)),
          entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩ := by
  obtain ⟨originId, index, metadata, owned, history, emitted⟩ :=
    CallableIndexedFormation.namedBody_history compiled.indexed.ancestry generation.hook
  let authority := (caller.rows owner.position).authority
  have physical : authority.frameLocation = owner.key.frameLocation := (caller.rows owner.position).frame_eq
  have read : store.read? owner.key.frameLocation = some (encode compiled.indexed.ancestry.layout.frame authority.current) := by
    simpa only [physical] using authority.frame.read
  have unmapped : owner.key.frameLocation ∉ mapping := by simpa only [physical] using authority.unmapped
  have typed : world[owner.key.frameLocation]? = some compiled.indexed.ancestry.layout.frame.type := by
    simpa only [physical] using authority.typed
  let installedPool := install caller owner.position (.stable history)
  let initial : State headers keys ⟨[], mapping, world, before,
      store.set owner.key.frameLocation (encode compiled.indexed.ancestry.layout.frame (.state index)), installed.canonical⟩ := installedPool
  obtain ⟨installedHeaps, nextCell⟩ := CallableIndexedBodyFrames.install (CallableIndexedAmbient.frame_registered compiled.indexed) heaps unmapped typed
    (show CellState compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      compiled.indexed.ancestry.layout.frame owner.key.frameLocation authority.current authority.ghost store from
      by simpa only [physical] using authority.frame) (.stable history)
  let producer := CallableIndexedOwnedMarkedAllocation.producer headers keys
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
  have readyAt : ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary owner.key.frameLocation (.state index) :=
    CallableIndexedOwnedAllocationProducer.readyAt_of_stable_read
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) owner.position history
  have packTyped : RuntimeValueHasType world (DataPatternValues.packValues payloads) named.signature.parameterType
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions :=
    sourceAt.parameterType.symm ▸ CallableIndexedParameters.Arguments.pack_typed represented
  have actualTyped := RuntimeEnvironmentHasTypes.cons
    (RuntimeValueHasType.unit (definitions := (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions))
    (.cons (encode_runtime_typed world (CallableIndexedAmbient.frame_registered compiled.indexed) authority.current) (.cons packTyped installed.captureTyped))
  have actualLayout : EnvironmentsAgree
      (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) installed.embedding.lift))
      (DataPatternValues.packValues payloads :: installed.canonical)
      (.unit :: encode compiled.indexed.ancestry.layout.frame authority.current :: DataPatternValues.packValues payloads :: installed.captured) :=
    GenericExpressionMeaning.agree_prefix
    (GenericExpressionMeaning.agree_prefix (ReadOnly.EnvironmentsAgree.lift installed.captureLayout (DataPatternValues.packValues payloads))
      (encode compiled.indexed.ancestry.layout.frame authority.current)) .unit
  obtain ⟨entry, added, length, spine, reached, related⟩ := parameter_entry_with_state
    (compiled := compiled) (program := program) (headers := headers) (keys := keys)
    (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (registry := registry) (layouts := compiled.indexed.layouts) (owner := named.signature.key) (active := [])
    (layout := compiled.indexed.ancestry.layout.frame) (globals := compiled.indexed.base.globals.length)
    (function := methodFunction generation sourceBody dictionary) functions
    (fun error => .sourceAllocation (reprStr error)) (accepted_parameters generation sourceAt)
    sourceAt.parameters sourceAt.parameters sourceAt.extended rfl (CallableIndexedAmbient.frame_registered compiled.indexed) represented
    installed.environments installedHeaps installed.locals actualLayout actualTyped
    (by simpa only [sameFrame] using installed.canonicalReference) nextCell.read unmapped producer initial readyAt
  exact ⟨originId, index, metadata, owned, history, emitted, entry, added, length, spine, reached,
    (install_related caller owner.position (.stable history)).trans related⟩

include sourceAt installed represented sameFrame heaps in
/-- Original native hook inversion selects its strict parameter child; the
shared parameter fold produces the actual body pool and keeps the exact final
saved-frame write from that same completion. -/
theorem body_prefix_with_state {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size (DataPatternValues.packValues payloads :: installed.captured) store
      (generation.output.rename installed.embedding.lift) value finalStore) :
    ∃ originId index metadata prefixSize bodyStore,
      compiled.indexed.ancestry.graph.inputs.callable.table.idAt? (.named named.signature.key) = some originId ∧
      Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table (.state index) (.named originId) (some metadata) ∧
      prefixSize < size ∧
      finalStore = bodyStore.set owner.key.frameLocation
        (encode compiled.indexed.ancestry.layout.frame (caller.rows owner.position).authority.current) ∧
    ∃ entry : Prefix compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
      owner.key.frameLocation (.state index) (.initial compiled.compatible.checked) functions registry
      (methodFunction generation sourceBody dictionary) sourceAt.context named.inputs arguments before
      (store.set owner.key.frameLocation (encode compiled.indexed.ancestry.layout.frame (.state index))) mapping world
      administrative (.unit :: compiled.indexed.ancestry.layout.frame.type :: named.signature.parameterType :: installed.capturedContext)
      (.unit :: encode compiled.indexed.ancestry.layout.frame (caller.rows owner.position).authority.current ::
        DataPatternValues.packValues payloads :: installed.captured)
      (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) installed.embedding.lift))
      generation.parameterCode generation.body prefixSize value bodyStore,
    ∃ added : Environment, added.length = named.inputs.length ∧
      entry.canonical = added ++ DataPatternValues.packValues payloads :: installed.canonical ∧
      ProtectedStateTransition.Transition (protocol headers keys) caller
        ⟨named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)),
          entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩ := by
  let authority := (caller.rows owner.position).authority
  have physical : authority.frameLocation = owner.key.frameLocation := (caller.rows owner.position).frame_eq
  have read : store.read? owner.key.frameLocation = some (encode compiled.indexed.ancestry.layout.frame authority.current) := by
    simpa only [physical] using authority.frame.read
  have unmapped : owner.key.frameLocation ∉ mapping := by simpa only [physical] using authority.unmapped
  have typed : world[owner.key.frameLocation]? = some compiled.indexed.ancestry.layout.frame.type := by
    simpa only [physical] using authority.typed
  have reference : (DataPatternValues.packValues payloads :: installed.captured)[installed.embedding.lift
      (compiled.indexed.base.globals.length + 1)]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
    simpa only [sameFrame, Renaming.lift, Nat.succ_sub_one, List.getElem?_cons_succ] using installed.capturedReference
  obtain ⟨originId, index, metadata, owned, history, emitted⟩ :=
    CallableIndexedFormation.namedBody_history compiled.indexed.ancestry generation.hook
  have renamed : generation.output.rename installed.embedding.lift = withFrame
      (.var (installed.embedding.lift (compiled.indexed.base.globals.length + 1)))
      (SourceCoreCallableIndexedDispatch.literal compiled.indexed.ancestry.layout.frame (.state index))
      (generation.parameterCode.rename installed.embedding.lift) := by
    rw [emitted, NamedCalls.withFrame_rename, Expr.rename, CallableIndexedRenaming.literal]
  rw [renamed] at completed
  obtain ⟨nextSize, prefixSize, nextValue, nextStore, bodyStore, nextCompletion, prefixCompletion,
    _sizeBound, smaller, restored⟩ := RecursiveNamedCallBounds.with_frame (.var reference) read completed
  obtain ⟨nextEq, nextStoreEq⟩ := evaluation_deterministic nextCompletion.sound
    (next_evaluates index (DataPatternValues.packValues payloads :: installed.captured) store
      (encode compiled.indexed.ancestry.layout.frame authority.current))
  rw [nextEq, nextStoreEq, ← rename_prefix] at prefixCompletion
  let installedPool := install caller owner.position (.stable history)
  let initial : State headers keys ⟨[], mapping, world, before,
      store.set owner.key.frameLocation (encode compiled.indexed.ancestry.layout.frame (.state index)), installed.canonical⟩ := installedPool
  obtain ⟨installedHeaps, nextCell⟩ := CallableIndexedBodyFrames.install (CallableIndexedAmbient.frame_registered compiled.indexed) heaps unmapped typed
    (show CellState compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      compiled.indexed.ancestry.layout.frame owner.key.frameLocation authority.current authority.ghost store from
      by simpa only [physical] using authority.frame) (.stable history)
  let producer := CallableIndexedOwnedMarkedAllocation.producer headers keys
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
  have readyAt : ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary owner.key.frameLocation (.state index) :=
    CallableIndexedOwnedAllocationProducer.readyAt_of_stable_read
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) owner.position history
  have packTyped : RuntimeValueHasType world (DataPatternValues.packValues payloads) named.signature.parameterType
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions :=
    sourceAt.parameterType.symm ▸ CallableIndexedParameters.Arguments.pack_typed represented
  have actualTyped := RuntimeEnvironmentHasTypes.cons
    (RuntimeValueHasType.unit (definitions := (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions))
    (.cons (encode_runtime_typed world (CallableIndexedAmbient.frame_registered compiled.indexed) authority.current) (.cons packTyped installed.captureTyped))
  have actualLayout : EnvironmentsAgree
      (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) installed.embedding.lift))
      (DataPatternValues.packValues payloads :: installed.canonical)
      (.unit :: encode compiled.indexed.ancestry.layout.frame authority.current :: DataPatternValues.packValues payloads :: installed.captured) :=
    GenericExpressionMeaning.agree_prefix
    (GenericExpressionMeaning.agree_prefix (ReadOnly.EnvironmentsAgree.lift installed.captureLayout (DataPatternValues.packValues payloads))
      (encode compiled.indexed.ancestry.layout.frame authority.current)) .unit
  obtain ⟨entry, added, length, spine, reached, related⟩ := parameter_prefix_with_state
    (compiled := compiled) (program := program) (headers := headers) (keys := keys)
    (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (registry := registry) (layouts := compiled.indexed.layouts) (owner := named.signature.key) (active := [])
    (layout := compiled.indexed.ancestry.layout.frame) (globals := compiled.indexed.base.globals.length)
    (function := methodFunction generation sourceBody dictionary) functions
    (fun error => .sourceAllocation (reprStr error)) (accepted_parameters generation sourceAt)
    sourceAt.parameters sourceAt.parameters sourceAt.extended rfl (CallableIndexedAmbient.frame_registered compiled.indexed) represented
    installed.environments installedHeaps installed.locals actualLayout actualTyped
    (by simpa only [sameFrame] using installed.canonicalReference) nextCell.read unmapped producer initial readyAt prefixCompletion
  exact ⟨originId, index, metadata, prefixSize, bodyStore, owned, history, smaller, restored,
    entry, added, length, spine, reached, (install_related caller owner.position (.stable history)).trans related⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodInvocationEntries
