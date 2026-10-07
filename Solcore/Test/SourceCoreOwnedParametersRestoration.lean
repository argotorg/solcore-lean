import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedInvocationBounds

/-! Concrete parameter prefixes produce their reached pool with real marked
allocation receipts. Restoring that same post preserves its exact ordered
rows, the original protected records, and the captured callable read. -/
set_option autoImplicit false
namespace Tests.SourceCoreOwnedParametersRestoration
open Solcore Core Frontend SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory SourceCoreCallableIndexedFrames
open CallableIndexedOwnedFunctionState RecursiveNamedCatalog
open RecursiveNamedCatalogInvocationBounds CallableIndexedParameterMeaning

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : SourceSemantics.Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
  {registry : SourceCoreRawMetadata.Registry}

/-- Exact reached-row restoration and prefix retention are separate facts. -/
def ReturnedObservations {caller body : ProtectedStateTransition.Index}
    (saved : State headers keys caller) (reached : State headers keys body) (selected : Fin keys.length) : Prop :=
  let final := CallableIndexedOwnedBodyRestoration.finalIndex (body := body) saved selected
  let returned := CallableIndexedOwnedBodyRestoration.returned saved reached selected
  CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions
    body.mapping body.world body.heap final.store ∧
  AdministrativePreserved caller.mapping caller.store body.mapping final.store ∧
  CellState compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
    compiled.indexed.ancestry.layout.frame keys[selected.val].frameLocation
    (saved.rows selected).authority.current (saved.rows selected).authority.ghost final.store ∧
  records returned = records reached ∧ Relates saved returned ∧
  (∀ row, RecordPrefix (records saved row) (records returned row)) ∧
  (∀ row record, record ∈ records saved row → record ∈ records returned row) ∧
  (∀ row record, record ∈ records reached row →
    CallableIndexedSnapshots.Holds compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      compiled.indexed.ancestry.layout.frame body.mapping final.store record) ∧
  (∀ row : Fin keys.length, keys[row.val].frameLocation = keys[selected.val].frameLocation →
    (returned.rows row).authority.current = (saved.rows selected).authority.current ∧
    (returned.rows row).authority.ghost = (saved.rows selected).authority.ghost) ∧
  (∀ row : Fin keys.length, keys[row.val].frameLocation ≠ keys[selected.val].frameLocation →
    (returned.rows row).authority.current = (reached.rows row).authority.current ∧
    (returned.rows row).authority.ghost = (reached.rows row).authority.ghost) ∧
  ProtectedStateTransition.Transition (protocol headers keys) saved final

private theorem set_of_read {store : Store} {location : Location} {value : Value}
    (read : store.read? location = some value) : store.set location value = store := by
  obtain ⟨bound, same⟩ := List.getElem_of_getElem? read
  rw [← same]
  exact List.set_getElem_self bound

private theorem restore_actual_prefix {caller body : ProtectedStateTransition.Index}
    (saved : State headers keys caller) (reached : State headers keys body) (selected : Fin keys.length)
    (registered : compiled.indexed.ancestry.layout.frame.Registered compiled.indexed.layouts.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions
      body.mapping body.world body.heap body.store)
    (worlds : WorldExtends caller.world body.world)
    (frame : AdministrativePreserved caller.mapping caller.store body.mapping body.store)
    (related : Relates saved reached) : ReturnedObservations (functions := functions) (registry := registry) saved reached selected := by
  have read := (saved.rows selected).authority.frame.read
  rw [(saved.rows selected).frame_eq] at read
  have same := set_of_read read
  have installedFrame : AdministrativePreserved caller.mapping
      (caller.store.set keys[selected.val].frameLocation
        (encode compiled.indexed.ancestry.layout.frame (saved.rows selected).authority.current)) body.mapping body.store := by
    exact Eq.mp (congrArg (fun original => AdministrativePreserved caller.mapping original body.mapping body.store) same.symm) frame
  obtain ⟨finalHeaps, finalFrame, cell, _fromReached, fromSaved, exactRecords, transition⟩ :=
    CallableIndexedOwnedBodyRestoration.restore_return saved reached selected registered heaps worlds installedFrame related
  refine ⟨finalHeaps, finalFrame, cell, exactRecords, fromSaved, fromSaved, ?_, ?_, ?_, ?_, transition⟩
  · intro row record member
    obtain ⟨suffix, appended⟩ := fromSaved row
    rw [appended]
    exact List.mem_append_left _ member
  · exact CallableIndexedOwnedBodyRestoration.returned_snapshot saved reached selected
  · exact CallableIndexedOwnedBodyRestoration.returned_same_frame saved reached selected
  · exact CallableIndexedOwnedBodyRestoration.returned_other_frame saved reached selected

private theorem readyAt_layout
    {first second : SourceCoreAllocationLayouts.Prepared}
    {frame : SourceCoreCallableIndexedFrames.Layout}
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects definitions}
    (same : first = second)
    (producer : ProtectedStateTransition.MarkedAllocation.Producer (protocol headers keys) second frame model)
    {location : Location} {native : NativeFrame}
    (ready : ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary location native) :
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt ((same.symm ▸ producer).toOrdinary) location native := by
  cases same
  exact ready

section Parameters
variable {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
  {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
  (saved : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
  (selected : Fin keys.length)
  {header : CallableIndexedOwnedFunctionValues.Header compiled program}
  (sameLayouts : header.layouts = compiled.indexed.layouts)
  (capture : Capture (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    headers keys[selected.val].locations keys[selected.val].capturePrefix
    (saved.rows selected).authority.frameLocation header mapping world heap store)
  {metadata : Option MetadataState}
  (history : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
    (saved.rows selected).authority.current (saved.rows selected).authority.ghost metadata)
  {arguments : List Dynamic.Value} {payloads : List Value}
  (represented : Arguments (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    mapping world header.bindings arguments payloads)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world heap store)
  {actual : Environment} {actualContext : Core.Context} {ξ : Renaming}
  (agrees : EnvironmentsAgree ξ (DataPatternValues.packValues payloads :: capture.canonical) actual)
  (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)

private def concreteProducer : ProtectedStateTransition.MarkedAllocation.Producer (protocol headers keys)
    header.layouts compiled.indexed.ancestry.layout.frame
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) :=
  sameLayouts.symm ▸ CallableIndexedOwnedMarkedAllocation.producer headers keys
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)

include history in
private theorem concreteReady : ProtectedStateTransition.OrdinaryAllocation.ReadyAt
    (concreteProducer (headers := headers) (keys := keys) (functions := functions) (registry := registry) sameLayouts).toOrdinary
    (saved.rows selected).authority.frameLocation (saved.rows selected).authority.current := by
  have seed : CallableIndexedOwnedAllocationProducer.StableOwner keys
      (saved.rows selected).authority.frameLocation (saved.rows selected).authority.current :=
    ⟨selected, (saved.rows selected).authority.ghost, metadata, (saved.rows selected).frame_eq.symm, history⟩
  intro index reached read
  exact (readyAt_layout (headers := headers) (keys := keys) sameLayouts
    (CallableIndexedOwnedMarkedAllocation.producer headers keys
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions))
    (CallableIndexedOwnedAllocationProducer.readyAt_of_stableOwner (headers := headers)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) seed)) reached read

include sameLayouts capture represented heaps agrees actualTyped history in
/-- This source prefix needs no body execution or body meaning premise. -/
theorem parameters_restore_actual_pool :
    ∃ entry : BodyState (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers keys[selected.val].locations keys[selected.val].capturePrefix functions registry header arguments heap store mapping world
      capture.administrative actualContext actual ξ (saved.rows selected).authority.frameLocation
      (saved.rows selected).authority.current (saved.rows selected).authority.ghost,
    ∃ reached : State headers keys ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
      entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩,
      Relates saved reached ∧
      ContinuationAgreement actual store (header.parameterCode.rename ξ) entry.actualBody entry.store (header.body.rename entry.embedding) ∧
      ReturnedObservations (functions := functions) (registry := registry) saved reached selected ∧
      (CallableIndexedOwnedBodyRestoration.finalIndex
        (body := ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)), entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩)
        saved selected).store.read? (keys[selected.val].locations header) = some (.inRight .unit
          (.closure header.named.signature.parameterType (LanguageResult.resultType header.named.signature.resultType)
            (header.code.rename capture.embedding.lift) capture.captured)) := by
  let initial : State headers keys ⟨[], mapping, world, heap, store, capture.canonical⟩ := saved
  obtain ⟨entry, transition, agreement⟩ := CallableIndexedOwnedInvocationBounds.parameters_with_state
    (saved.rows selected).authority capture.environments capture.locals capture.reference capture.coherent represented heaps agrees actualTyped
    (concreteProducer sameLayouts) initial (concreteReady saved selected sameLayouts history)
  obtain ⟨reached, related⟩ := transition
  have observations := restore_actual_prefix saved reached selected (CallableIndexedAmbient.frame_registered compiled.indexed)
    entry.heaps entry.worlds entry.frame related
  refine ⟨entry, reached, related, agreement, observations, ?_⟩
  exact (observations.2.1 _ capture.unmapped (List.getElem?_eq_some_iff.mp capture.read).1).2.trans capture.read

include sameLayouts capture represented heaps agrees actualTyped history in
/-- Native prefix inversion supplies its original body grade and the same real
parameter post. Source and native grades remain independent. -/
theorem parameters_native_restore_actual_pool (member : header ∈ headers)
    {size : Nat} {result : Value} {afterStore : Store}
    (completed : EvaluationSize size actual store (header.parameterCode.rename ξ) result afterStore) :
    ∃ entry : BodyState (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers keys[selected.val].locations keys[selected.val].capturePrefix functions registry header arguments heap store mapping world
      capture.administrative actualContext actual ξ (saved.rows selected).authority.frameLocation
      (saved.rows selected).authority.current (saved.rows selected).authority.ghost,
    ∃ child, EvaluationSize child entry.actualBody entry.store (header.body.rename entry.embedding) result afterStore ∧
      child ≤ size ∧ (header.bindings ≠ [] → child < size) ∧
    ∃ reached : State headers keys ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
      entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩,
      Relates saved reached ∧ ReturnedObservations (functions := functions) (registry := registry) saved reached selected ∧
      (CallableIndexedOwnedBodyRestoration.finalIndex
        (body := ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)), entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩)
        saved selected).store.read? (keys[selected.val].locations header) = some (.inRight .unit
          (.closure header.named.signature.parameterType (LanguageResult.resultType header.named.signature.resultType)
            (header.code.rename capture.embedding.lift) capture.captured)) := by
  let initial : State headers keys ⟨[], mapping, world, heap, store, capture.canonical⟩ := saved
  obtain ⟨entry, child, bodyCompletion, childLe, childStrict, transition⟩ := CallableIndexedOwnedInvocationBounds.parameters_sized_with_state
    (saved.rows selected).authority member capture represented heaps agrees actualTyped completed
    (concreteProducer sameLayouts) initial (concreteReady saved selected sameLayouts history)
  obtain ⟨reached, related⟩ := transition
  have observations := restore_actual_prefix saved reached selected (CallableIndexedAmbient.frame_registered compiled.indexed)
    entry.heaps entry.worlds entry.frame related
  refine ⟨entry, child, bodyCompletion, childLe, childStrict, reached, related, observations, ?_⟩
  exact (observations.2.1 _ capture.unmapped (List.getElem?_eq_some_iff.mp capture.read).1).2.trans capture.read

end Parameters
end Tests.SourceCoreOwnedParametersRestoration
