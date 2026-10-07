import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedFunctionState

/-! Actual pool transitions retain ordered record lists in each original row.
The allocator's reached witness is passed to restoration and to the next
transition; administrative transport preserves its complete observation. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallableIndexedOwnedFunctionState
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CallableIndexedHistory SourceCoreCallableIndexedFrames
open CallableIndexedOwnedFunctionValues CallableIndexedOwnedFunctionEntries CallableIndexedOwnedFunctionState

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : SourceSemantics.Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {initial middle finalIndex : ProtectedStateTransition.Index}

/-- Every retained snapshot is an actual old store cell, so the allocator's
next fresh location cannot already be registered in any input row. -/
theorem fresh_location_unregistered (pool : State headers keys initial)
    (record : CallableIndexedSnapshots.Record)
    (fresh : record.location = initial.store.length) :
    ¬ CallableIndexedAuthorityPool.Pool.Registered pool record := by
  rintro ⟨row, member⟩
  exact fresh_record_absent pool row fresh member

/-- Ordered prefix inclusion retains every original position, including
multiple occurrences of the same snapshot; it permits only an appended suffix. -/
theorem relates_keeps_ordered_row_prefix
    {before : State headers keys initial} {after : State headers keys middle}
    (related : Relates before after) (row : Fin keys.length) :
    (records after row).take (records before row).length = records before row ∧
    ∀ position, position < (records before row).length →
      (records after row)[position]? = (records before row)[position]? := by
  obtain ⟨suffix, appended⟩ := related row
  constructor
  · rw [appended]; simp
  · intro position bound
    rw [appended, List.getElem?_append_left bound]

section AdministrativeEffects
variable {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}

/-- Legacy administrative lifting uses this exact transport. Its complete
record observation is unchanged, even if the reached store has new cells. -/
theorem administrative_extension_keeps_observation
    (pool : State headers keys initial)
    (maps : LocationMap.Extends initial.mapping mapping) (worlds : WorldExtends initial.world world)
    (frame : AdministrativePreserved initial.mapping initial.store mapping store)
    (metadata : Dynamic.HeapMetadataExtend initial.heap heap)
    (record : CallableIndexedSnapshots.Record) (fresh : record.location = initial.store.length) :
    let extended := (administrativeTransport headers keys).extend pool maps worlds frame metadata
    records extended = records pool ∧ ¬ CallableIndexedAuthorityPool.Pool.Registered extended record := by
  dsimp only
  have observed := administrative_records pool maps worlds frame metadata
  refine ⟨observed, ?_⟩
  rintro ⟨row, member⟩
  have atRow := congrFun observed row
  change record ∈ records ((administrativeTransport headers keys).extend pool maps worlds frame metadata) row at member
  rw [atRow] at member
  exact fresh_record_absent pool row fresh member

/-- The allocator's appended occurrence cannot be recovered by lifting a
legacy contract through administrative transport. This also detects an
appended duplicate, because the complete list observation keeps multiplicity. -/
theorem actual_append_cannot_be_administrative_post
    (pool : State headers keys initial) (post : State headers keys middle)
    (selected : Fin keys.length) (record : CallableIndexedSnapshots.Record)
    (appended : records post selected = records pool selected ++ [record])
    (maps : LocationMap.Extends initial.mapping mapping) (worlds : WorldExtends initial.world world)
    (frame : AdministrativePreserved initial.mapping initial.store mapping store)
    (metadata : Dynamic.HeapMetadataExtend initial.heap heap) :
    records post ≠ records ((administrativeTransport headers keys).extend pool maps worlds frame metadata) := by
  intro equal
  have sameRow := congrFun (equal.trans (administrative_records pool maps worlds frame metadata)) selected
  have lengths := congrArg List.length sameRow
  rw [appended, List.length_append, List.length_singleton] at lengths
  omega
end AdministrativeEffects

section SnapshotAndRestoration
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {request : SourceCoreSourceCells.Request} {globals : Nat}
  {allocate : SourceCoreSourceCells.Allocator}
  {environment : Environment} {location : Location} {native : NativeFrame} {ghost : GhostFrame}
  {metadata : Option MetadataState} {payload : Option Value} {futureWorld : StoreTyping} {after : Dynamic.Heap}
  {next : NativeFrame} {nextGhost : GhostFrame}

/-- Real three-cell allocation supplies the first post-witness. An
authenticated mutable-frame write and restoration consume that witness in
sequence. The selected row keeps its appended snapshot, a different row
sharing the frame keeps its own ordered records, and a distinct frame keeps
its reached history. No callable body law is needed for these protocol atoms. -/
theorem actual_snapshot_write_and_restore
    (pool : State headers keys initial) (selected duplicate other : Fin keys.length)
    (duplicateRow : duplicate ≠ selected)
    (sameFrame : keys[duplicate.val].frameLocation = keys[selected.val].frameLocation)
    (differentFrame : keys[other.val].frameLocation ≠ keys[selected.val].frameLocation)
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active request)
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated compiled.indexed.ancestry.layout.frame
      globals allocate request)
    (same : annotation.original = allocation.expression)
    (reference : environment[SourceCoreCallableIndexedAllocationFrames.referenceIndex globals request]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type location))
    (read : initial.store.read? location = some (encode compiled.indexed.ancestry.layout.frame native))
    (history : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table native ghost metadata)
    (bounded : ∀ target ∈ initial.mapping, target < initial.store.length)
    (slots : ∀ position binding, request.scope[position]? = some binding → ∃ target,
      environment[request.references position]? = some (.cellRef (OptionalCell.cellType binding.2) target))
    (payloadAt : CallableIndexedAllocationCompletion.PayloadAt request environment payload)
    (worlds : WorldExtends initial.world futureWorld) (sourceMetadata : Dynamic.HeapMetadataExtend initial.heap after)
    (bodyHistory : Current compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table next nextGhost) :
    ∃ captured,
      let allocatedIndex := initial.extend (initial.mapping ++ [initial.store.length + 2]) futureWorld after
        (initial.store ++ [encode compiled.indexed.ancestry.layout.frame native,
          SourceCoreHeapMarkers.markerValue allocation.entry.layout captured,
          CallableIndexedAllocationCompletion.optionalValue request.payloadType payload])
      let writtenIndex := allocatedIndex.extend allocatedIndex.mapping allocatedIndex.world allocatedIndex.heap
        (allocatedIndex.store.set keys[selected.val].frameLocation (encode compiled.indexed.ancestry.layout.frame next))
      let restoredIndex := writtenIndex.extend writtenIndex.mapping writtenIndex.world writtenIndex.heap
        (writtenIndex.store.set keys[selected.val].frameLocation
          (encode compiled.indexed.ancestry.layout.frame (pool.rows selected).authority.current))
      Evaluates environment initial.store annotation.expression
        (.cellRef (OptionalCell.cellType request.payloadType) (initial.store.length + 2)) allocatedIndex.store ∧
      ∃ reached : State headers keys allocatedIndex,
        Relates pool reached ∧
        let written := install reached selected bodyHistory
        let final := restored pool written selected
        Relates pool final ∧ records final = records reached ∧
        records final selected = records pool selected ++ [⟨initial.store.length, native, ghost, metadata⟩] ∧
        records final duplicate = records pool duplicate ∧ records final other = records pool other ∧
        (final.rows duplicate).authority.current = (pool.rows selected).authority.current ∧
        (final.rows duplicate).authority.ghost = (pool.rows selected).authority.ghost ∧
        (final.rows other).authority.current = (written.rows other).authority.current ∧
        CallableIndexedSnapshots.Holds compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
          compiled.indexed.ancestry.layout.frame restoredIndex.mapping restoredIndex.store
          ⟨initial.store.length, native, ghost, metadata⟩ ∧
        ProtectedStateTransition.Transition (protocol headers keys) pool restoredIndex := by
  obtain ⟨captured, evaluated, reached, related, appended, unchanged, _⟩ :=
    CallableIndexedOwnedFunctionState.completed_snapshot pool selected allocation annotation same
      reference read history bounded slots payloadAt worlds sourceMetadata
  refine ⟨captured, ?_⟩
  dsimp only
  refine ⟨evaluated, reached, related, ?_⟩
  let written := install reached selected bodyHistory
  let final := restored pool written selected
  have recordsEq : records final = records reached :=
    (CallableIndexedOwnedFunctionState.restored_records pool written selected).trans
      (install_records reached selected bodyHistory)
  have finalRelated : Relates pool final := Relates.trans related
    (Relates.trans (install_related reached selected bodyHistory)
      (restored_related pool written selected))
  have otherRow : other ≠ selected := by
    intro equal
    subst other
    exact differentFrame rfl
  have finalMember : (⟨initial.store.length, native, ghost, metadata⟩ : CallableIndexedSnapshots.Record) ∈ records final selected := by
    rw [recordsEq, appended]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  obtain ⟨duplicateCurrent, duplicateGhost⟩ :=
    CallableIndexedOwnedFunctionState.restored_same_frame pool written selected duplicate sameFrame
  have otherCurrent := (CallableIndexedOwnedFunctionState.restored_other_frame pool written selected other differentFrame).1
  refine ⟨finalRelated, recordsEq, ?_, ?_, ?_, duplicateCurrent, duplicateGhost, otherCurrent,
    record_snapshot final selected finalMember, ?_⟩
  · rw [recordsEq]; exact appended
  · rw [recordsEq]; exact unchanged duplicate duplicateRow
  · rw [recordsEq]; exact unchanged other otherRow
  · have first := ProtectedStateTransition.Transition.of_related (protocol headers keys) related
    have second := ProtectedStateTransition.Transition.then (protocol headers keys) first
      (fun actualPost _ => install_transition actualPost selected bodyHistory)
    exact ProtectedStateTransition.Transition.then (protocol headers keys) second
      (fun actualPost _ => restored_transition pool actualPost selected)
end SnapshotAndRestoration

end Tests.SourceCoreCallableIndexedOwnedFunctionState
