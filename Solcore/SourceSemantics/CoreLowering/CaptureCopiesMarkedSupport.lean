import Solcore.SourceSemantics.CoreLowering.CaptureCopies
import Solcore.SourceSemantics.CoreLowering.CallableIndexedAllocationRenaming
import Solcore.SourceSemantics.CoreLowering.GenericCellHeap

/-! Support for the marked copies of a closure's captured cells. The copy chain
walks a suffix of the scope head first, counting the copies made so far, while
the renaming of the body is fixed over the whole scope. The bookkeeping here
relates the two: the copied slots of a suffix, the renaming's value on the
slot being copied or skipped, and a pending agreement that sends the processed
slots past the copies still to be made. One marked copy evaluates under the
actual renaming by transporting the allocator's receipts. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CaptureCopies
open Core Frontend Frontend.SourceInference GeneralHeap CoreProof ReadOnly
open SourceSemantics.CaptureBinders (copiedBinder?)
open CallableIndexedAllocationCompletion (PayloadAt optionalValue)

/-! ## The copy renaming -/

/-- A position outside the copied ones moves past every copy. -/
theorem copyRenaming_not_mem {positions : List Nat} {index : Nat} (absent : index ∉ positions) :
    SourceCoreSourceCells.copyRenaming positions index = index + positions.length := by
  have none : positions.findIdx? (fun position => decide (position = index)) = none := by
    rw [List.findIdx?_eq_none_iff]
    intro position mem
    simp only [decide_eq_false_iff_not]
    intro same
    exact absent (same ▸ mem)
  simp [SourceCoreSourceCells.copyRenaming, none]

/-- The copy of a position lies below the copies made after it. -/
theorem copyRenaming_mem {done remaining : List Nat} {index : Nat} (fresh : index ∉ done) :
    SourceCoreSourceCells.copyRenaming (done ++ index :: remaining) index = remaining.length := by
  have none : done.findIdx? (fun position => decide (position = index)) = none := by
    rw [List.findIdx?_eq_none_iff]
    intro position mem
    simp only [decide_eq_false_iff_not]
    intro same
    exact fresh (same ▸ mem)
  simp only [SourceCoreSourceCells.copyRenaming, List.findIdx?_append, none, List.findIdx?_cons,
    decide_true, ↓reduceIte, Option.none_or, Option.map_some, List.length_append, List.length_cons]
  omega

/-! ## Copied slots of a scope suffix -/

/-- The copied slots of the suffix `rest` of a scope, whose first slot has
scope index `index`. -/
def copiedSlotsFrom (source : TypedSource) (rest : SourceCoreLocalCell.Scope) (index : Nat) :
    List (Nat × TypedBinder × Core.Ty) :=
  (rest.zipIdx index).filterMap fun ((id, type), index) =>
    (copiedBinder? source id).map fun binder => (index, binder, type)

theorem copiedSlots_eq (source : TypedSource) (scope : SourceCoreLocalCell.Scope) :
    SourceCoreSourceCells.copiedSlots source scope = copiedSlotsFrom source scope 0 := rfl

theorem copiedSlotsFrom_nil (source : TypedSource) (index : Nat) :
    copiedSlotsFrom source [] index = [] := rfl

theorem copiedSlotsFrom_shared {source : TypedSource} {id : Resolved.LocalId} {type : Core.Ty}
    (rest : SourceCoreLocalCell.Scope) (index : Nat) (uncopied : copiedBinder? source id = none) :
    copiedSlotsFrom source ((id, type) :: rest) index = copiedSlotsFrom source rest (index + 1) := by
  simp [copiedSlotsFrom, uncopied]

theorem copiedSlotsFrom_copied {source : TypedSource} {id : Resolved.LocalId} {type : Core.Ty}
    {binder : TypedBinder} (rest : SourceCoreLocalCell.Scope) (index : Nat)
    (copied : copiedBinder? source id = some binder) :
    copiedSlotsFrom source ((id, type) :: rest) index =
      (index, binder, type) :: copiedSlotsFrom source rest (index + 1) := by
  simp [copiedSlotsFrom, copied]

/-- Every copied slot of a suffix lies at or past its first index. -/
theorem copiedSlotsFrom_le (source : TypedSource) :
    ∀ (rest : SourceCoreLocalCell.Scope) (index : Nat) (slot : Nat × TypedBinder × Core.Ty),
      slot ∈ copiedSlotsFrom source rest index → index ≤ slot.1
  | [], _, _, mem => by simp [copiedSlotsFrom] at mem
  | (id, type) :: rest, index, slot, mem => by
      cases copied : copiedBinder? source id with
      | none =>
          rw [copiedSlotsFrom_shared rest index copied] at mem
          exact Nat.le_of_succ_le (copiedSlotsFrom_le source rest (index + 1) slot mem)
      | some binder =>
          rw [copiedSlotsFrom_copied rest index copied, List.mem_cons] at mem
          rcases mem with same | mem
          · subst same; exact Nat.le_refl _
          · exact Nat.le_of_succ_le (copiedSlotsFrom_le source rest (index + 1) slot mem)

/-- The copies the chain over `rest` still makes. -/
def pendingCopies (source : TypedSource) (rest : SourceCoreLocalCell.Scope) (index : Nat) : Nat :=
  (copiedSlotsFrom source rest index).length

/-- The body renaming seen from a chain state: `done` holds the positions
already copied, `rest` at `index` the slots still to process. -/
def chainRenaming (source : TypedSource) (preLength : Nat) (done : List Nat)
    (rest : SourceCoreLocalCell.Scope) (index : Nat) : Renaming :=
  SourceCoreSourceCells.copyRenaming
    (done ++ (copiedSlotsFrom source rest index).map fun slot => slot.1 + preLength)

theorem chainRenaming_scope (source : TypedSource) (scope : SourceCoreLocalCell.Scope) (preLength : Nat) :
    chainRenaming source preLength [] scope 0 = SourceCoreSourceCells.scopeCopyRenaming source scope (· + preLength) :=
  rfl

theorem chainRenaming_shared {source : TypedSource} {id : Resolved.LocalId} {type : Core.Ty}
    (preLength : Nat) (done : List Nat) (rest : SourceCoreLocalCell.Scope) (index : Nat)
    (uncopied : copiedBinder? source id = none) :
    chainRenaming source preLength done ((id, type) :: rest) index =
      chainRenaming source preLength done rest (index + 1) := by
  simp only [chainRenaming, copiedSlotsFrom_shared rest index uncopied]

theorem chainRenaming_copied {source : TypedSource} {id : Resolved.LocalId} {type : Core.Ty}
    {binder : TypedBinder} (preLength : Nat) (done : List Nat) (rest : SourceCoreLocalCell.Scope)
    (index : Nat) (copied : copiedBinder? source id = some binder) :
    chainRenaming source preLength done ((id, type) :: rest) index =
      chainRenaming source preLength (done ++ [index + preLength]) rest (index + 1) := by
  simp only [chainRenaming, copiedSlotsFrom_copied rest index copied, List.map_cons, List.append_assoc,
    List.singleton_append]

theorem pendingCopies_shared {source : TypedSource} {id : Resolved.LocalId} {type : Core.Ty}
    (rest : SourceCoreLocalCell.Scope) (index : Nat) (uncopied : copiedBinder? source id = none) :
    pendingCopies source ((id, type) :: rest) index = pendingCopies source rest (index + 1) := by
  simp only [pendingCopies, copiedSlotsFrom_shared rest index uncopied]

theorem pendingCopies_copied {source : TypedSource} {id : Resolved.LocalId} {type : Core.Ty}
    {binder : TypedBinder} (rest : SourceCoreLocalCell.Scope) (index : Nat)
    (copied : copiedBinder? source id = some binder) :
    pendingCopies source ((id, type) :: rest) index = pendingCopies source rest (index + 1) + 1 := by
  simp only [pendingCopies, copiedSlotsFrom_copied rest index copied, List.length_cons]

/-- A position outside the earlier copies and the suffix's copied slots
moves past every copy. -/
theorem chainRenaming_not_mem {source : TypedSource} {preLength : Nat} {done : List Nat}
    {rest : SourceCoreLocalCell.Scope} {index position : Nat}
    (fresh : position ∉ done)
    (outside : ∀ slot ∈ copiedSlotsFrom source rest index, slot.1 + preLength ≠ position) :
    chainRenaming source preLength done rest index position = position + (done.length + pendingCopies source rest index) := by
  unfold chainRenaming
  rw [copyRenaming_not_mem, List.length_append, List.length_map]
  · rfl
  intro mem
  rw [List.mem_append] at mem
  rcases mem with mem | mem
  · exact fresh mem
  · rw [List.mem_map] at mem
    obtain ⟨slot, mem, same⟩ := mem
    exact outside slot mem same

/-- A position below the suffix and outside the earlier copies moves past
every copy. -/
theorem chainRenaming_below {source : TypedSource} {preLength : Nat} {done : List Nat}
    {rest : SourceCoreLocalCell.Scope} {index position : Nat}
    (fresh : position ∉ done) (below : position < index + preLength) :
    chainRenaming source preLength done rest index position = position + (done.length + pendingCopies source rest index) := by
  apply chainRenaming_not_mem fresh
  intro slot mem
  have := copiedSlotsFrom_le source rest index slot mem
  omega

/-- The slot being copied is sent below the copies still to be made. -/
theorem chainRenaming_copy {source : TypedSource} {preLength : Nat} {done : List Nat}
    {rest : SourceCoreLocalCell.Scope} {index : Nat}
    (doneBelow : ∀ position ∈ done, position < index + preLength) :
    chainRenaming source preLength (done ++ [index + preLength]) rest (index + 1) (index + preLength) =
      pendingCopies source rest (index + 1) := by
  unfold chainRenaming
  rw [List.append_assoc, List.singleton_append, copyRenaming_mem, List.length_map]
  · rfl
  intro mem
  have := doneBelow _ mem
  omega

/-! ## Pending agreement -/

/-- The entries of `source` are sent by `σ` past `pending` copies still to be
made, onto slots of `target` holding the same entries. -/
def Pending {α : Type} (σ : Renaming) (pending : Nat) (source target : List α) : Prop :=
  ∀ {index : Nat} {entry : α}, source[index]? = some entry →
    ∃ slot, σ index = slot + pending ∧ target[slot]? = some entry

namespace Pending

variable {α : Type} {σ : Renaming} {pending : Nat} {source target : List α}

/-- One more copy made: every earlier slot moves up by one. -/
theorem push (related : Pending σ (pending + 1) source target) (entry : α) :
    Pending σ pending source (entry :: target) := by
  intro index found selected
  obtain ⟨slot, same, selected⟩ := related selected
  exact ⟨slot + 1, by omega, by simpa using selected⟩

/-- The copy of the next slot is the entry just pushed. -/
theorem copied (related : Pending σ (pending + 1) source target)
    (position : σ source.length = pending) (entry : α) :
    Pending σ pending (source ++ [entry]) (entry :: target) := by
  intro index found selected
  rcases Nat.lt_or_ge index source.length with below | above
  · rw [List.getElem?_append_left below] at selected
    exact related.push entry selected
  · have same : index = source.length := by
      have bound := (List.getElem?_eq_some_iff.mp selected).1
      simp only [List.length_append, List.length_singleton] at bound
      omega
    subst same
    rw [List.getElem?_concat_length] at selected
    obtain rfl := Option.some.inj selected
    exact ⟨0, by simpa using position, rfl⟩

/-- A slot that keeps its entry is sent to that entry's current slot. -/
theorem shared (related : Pending σ pending source target) {slot : Nat} {entry : α}
    (position : σ source.length = slot + pending) (selected : target[slot]? = some entry) :
    Pending σ pending (source ++ [entry]) target := by
  intro index found found
  rcases Nat.lt_or_ge index source.length with below | above
  · rw [List.getElem?_append_left below] at found
    exact related found
  · have same : index = source.length := by
      have bound := (List.getElem?_eq_some_iff.mp found).1
      simp only [List.length_append, List.length_singleton] at bound
      omega
    subst same
    rw [List.getElem?_concat_length] at found
    obtain rfl := Option.some.inj found
    exact ⟨slot, position, selected⟩

/-- With no copy pending, composing with an agreement of the target gives an
agreement of the source. -/
theorem agree {ρ : Renaming} {final : List α} (related : Pending σ 0 source target)
    (agrees : ∀ {index : Nat} {entry : α}, target[index]? = some entry → final[ρ index]? = some entry)
    {index : Nat} {entry : α} (found : source[index]? = some entry) :
    final[Renaming.comp ρ σ index]? = some entry := by
  obtain ⟨slot, same, selected⟩ := related found
  show final[ρ (σ index)]? = some entry
  rw [same, Nat.add_zero]
  exact agrees selected

end Pending

/-! ## List bookkeeping -/

/-- An agreement of environments transfers along an equality of sources. -/
theorem agree_of_eq {ρ : Renaming} {source source' target : Environment} (same : source = source')
    (agrees : EnvironmentsAgree ρ source target) : EnvironmentsAgree ρ source' target := same ▸ agrees

/-- A renaming respecting a context respects an equal context. -/
theorem respects_of_eq {ρ : Renaming} {source source' target : Core.Context} (same : source = source')
    (respects : Renaming.Respects ρ source target) : Renaming.Respects ρ source' target := same ▸ respects

/-- Indexing past a prefix of known length. -/
theorem getElem?_append_shift {α : Type} {prefixList rest : List α} {count index : Nat}
    (length : prefixList.length = count) : (prefixList ++ rest)[index + count]? = rest[index]? := by
  rw [List.getElem?_append_right (by omega)]
  congr 1
  omega

/-! ## Scope environments -/

/-- The scope part of a represented environment, with no administrative tail. -/
theorem scope_environments {catalog : SourceCoreDataCatalog.Catalog} {definitions : DataEnvironment}
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {scope : SourceCoreLocalCell.Scope} {environment : Dynamic.Environment} {canonical : Environment}
    (related : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical
      definitions) :
    DataHeap.EnvRepresents catalog mapping world [] scope environment (canonical.take scope.length) definitions := by
  induction related with
  | nil _ => exact .nil .nil
  | cons reference _ ih => exact .cons reference ih
  | internal typed absent _ ih => exact .internal typed absent ih

/-- A copy of the lexical environment binds no identifier the original does
not bind. -/
theorem copies_absent {source : TypedSource} {environment copies : Dynamic.Environment}
    {heap after : Dynamic.Heap} (copy : Dynamic.EnvironmentCopies source environment heap copies after)
    {id : Resolved.LocalId} (absent : ∀ location, ¬ Dynamic.Environment.LooksUp environment id location) :
    ∀ location, ¬ Dynamic.Environment.LooksUp copies id location := by
  intro location lookup
  obtain ⟨original, originalLookup, _⟩ := copy.looksUp lookup
  exact absent original originalLookup

/-! ## Optional payloads -/

/-- A typed optional cell value is an optional payload. -/
theorem optional_of_typed {world : StoreTyping} {definitions : DataEnvironment} {value : Value} {type : Ty}
    (typed : RuntimeValueHasType world value (OptionalCell.cellType type) definitions) :
    ∃ payload, value = optionalValue type payload := by
  unfold OptionalCell.cellType at typed
  cases typed with
  | inLeft unitTyped => cases unitTyped; exact ⟨none, rfl⟩
  | inRight _ => exact ⟨some _, rfl⟩

/-- A represented optional cell value is an optional payload. -/
theorem optional_of_cell {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
    {mapping : LocationMap} {world : StoreTyping} {cell : Dynamic.Cell} {value : Value} {type : Ty}
    (represented : GenericHeap.CellRepresents model mapping world cell value type) :
    ∃ payload, value = optionalValue type payload := by
  cases represented with
  | uninitialized _ => exact ⟨none, rfl⟩
  | initialized _ => exact ⟨some _, rfl⟩

/-! ## Chain inversions -/

theorem copyChain_shared (allocator : Option SourceCoreSourceCells.Allocator) {source : TypedSource}
    (scope : SourceCoreLocalCell.Scope) (base : Nat → Nat) {id : Resolved.LocalId} {type : Core.Ty}
    (rest : SourceCoreLocalCell.Scope) (index ordinal : Nat) (body : Expr)
    (uncopied : copiedBinder? source id = none) :
    SourceCoreSourceCells.copyChain allocator source scope base ((id, type) :: rest) index ordinal body =
      SourceCoreSourceCells.copyChain allocator source scope base rest (index + 1) ordinal body := by
  simp only [SourceCoreSourceCells.copyChain, uncopied]

theorem copyChain_copied {allocator : Option SourceCoreSourceCells.Allocator} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {base : Nat → Nat} {id : Resolved.LocalId} {type : Core.Ty}
    {binder : TypedBinder} {rest : SourceCoreLocalCell.Scope} {index ordinal : Nat} {body emitted : Expr}
    (copied : copiedBinder? source id = some binder)
    (accepted : SourceCoreSourceCells.copyChain allocator source scope base ((id, type) :: rest) index ordinal
      body = .ok emitted) :
    ∃ copy continuation,
      SourceCoreSourceCells.copyCell allocator source scope
        (SourceCoreSourceCells.copyReferences source scope binder base ordinal) binder type
        (.var (base index + ordinal)) = .ok copy ∧
      SourceCoreSourceCells.copyChain allocator source scope base rest (index + 1) (ordinal + 1) body =
        .ok continuation ∧
      emitted = .letE copy continuation := by
  simp only [SourceCoreSourceCells.copyChain, copied] at accepted
  cases copyAccepted : SourceCoreSourceCells.copyCell allocator source scope
      (SourceCoreSourceCells.copyReferences source scope binder base ordinal) binder type
      (.var (base index + ordinal)) with
  | error error => simp [copyAccepted, bind, Except.bind] at accepted
  | ok copy =>
    cases chainAccepted : SourceCoreSourceCells.copyChain allocator source scope base rest (index + 1)
        (ordinal + 1) body with
    | error error => simp [copyAccepted, chainAccepted, bind, Except.bind] at accepted
    | ok continuation =>
      simp only [copyAccepted, chainAccepted, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at accepted
      exact ⟨copy, continuation, rfl, rfl, accepted.symm⟩

theorem copyChain_nil (allocator : Option SourceCoreSourceCells.Allocator) (source : TypedSource)
    (scope : SourceCoreLocalCell.Scope) (base : Nat → Nat) (index ordinal : Nat) {body emitted : Expr}
    (accepted : SourceCoreSourceCells.copyChain allocator source scope base [] index ordinal body = .ok emitted) :
    emitted = body := by
  simp only [SourceCoreSourceCells.copyChain, pure, Except.pure, Except.ok.injEq] at accepted
  exact accepted.symm

theorem copyCell_some {allocate : SourceCoreSourceCells.Allocator} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {references : Renaming} {binder : TypedBinder}
    {type : Core.Ty} {reference copy : Expr}
    (accepted : SourceCoreSourceCells.copyCell (some allocate) source scope references binder type reference =
      .ok copy) :
    ∃ absent present,
      allocate ⟨source, scope, Renaming.comp (Renaming.insertion 0) references, binder, type, none⟩ =
        .ok absent ∧
      allocate ⟨source, scope, Renaming.comp (Renaming.insertion 0) references, binder, type, some (.var 0)⟩ =
        .ok present ∧
      copy = .caseE (.loadCell reference) absent present := by
  simp only [SourceCoreSourceCells.copyCell] at accepted
  cases absentAccepted : allocate ⟨source, scope, Renaming.comp (Renaming.insertion 0) references, binder, type,
      none⟩ with
  | error error => simp [absentAccepted, bind, Except.bind] at accepted
  | ok absent =>
    cases presentAccepted : allocate ⟨source, scope, Renaming.comp (Renaming.insertion 0) references, binder,
        type, some (.var 0)⟩ with
    | error error => simp [absentAccepted, presentAccepted, bind, Except.bind] at accepted
    | ok present =>
      simp only [absentAccepted, presentAccepted, bind, Except.bind, pure, Except.pure,
        Except.ok.injEq] at accepted
      exact ⟨absent, present, rfl, rfl, accepted.symm⟩

/-! ## Administrative copies -/

/-- Three appended administrative cells preserve every earlier one. -/
theorem administrative_append (mapping : LocationMap) (store : Store) (first second third : Value) :
    AdministrativePreserved mapping store mapping (store ++ [first, second, third]) := by
  have steps := (AdministrativePreserved.allocate_administrative mapping store first).trans
    ((AdministrativePreserved.allocate_administrative mapping (store ++ [first]) second).trans
      (AdministrativePreserved.allocate_administrative mapping (store ++ [first] ++ [second]) third))
  simpa [List.append_assoc] using steps

/-- A copy of an internal slot: the snapshot, marker and payload cells are
all administrative, and the payload cell keeps the slot's type. -/
theorem heap_allocate_administrative {definitions : DataEnvironment} {cells : GenericHeap.CellModel definitions}
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    {snapshot marker payload : Value} {snapshotType markerType payloadType : Ty}
    (heaps : GenericHeap.CellHeapRepresents cells mapping world heap store)
    (snapshotTyped : RuntimeValueHasType world snapshot snapshotType definitions)
    (markerTyped : RuntimeValueHasType world marker markerType definitions)
    (payloadTyped : RuntimeValueHasType world payload (OptionalCell.cellType payloadType) definitions) :
    GenericHeap.CellHeapRepresents cells mapping
      (world ++ [snapshotType, markerType, OptionalCell.cellType payloadType])
      heap (store ++ [snapshot, marker, payload]) ∧
    (world ++ [snapshotType, markerType, OptionalCell.cellType payloadType])[store.length + 2]? =
      some (OptionalCell.cellType payloadType) := by
  have snapshotHeaps := heaps.allocate_administrative snapshotTyped
  have markerHeaps := snapshotHeaps.allocate_administrative
    (markerTyped.weaken (show WorldExtends world (world ++ [snapshotType]) from ⟨_, rfl⟩))
  have payloadHeaps := markerHeaps.allocate_administrative (payloadTyped.weaken
    (show WorldExtends world ((world ++ [snapshotType]) ++ [markerType]) from ⟨[snapshotType, markerType], by simp⟩))
  refine ⟨by simpa [Store.allocate, List.append_assoc] using payloadHeaps, ?_⟩
  have lengthEq := heaps.runtime_hasTypes.length_eq
  rw [List.getElem?_append_right (by omega)]
  have same : store.length + 2 - world.length = 2 := by omega
  rw [same]
  rfl

/-- A mapped copy of a source cell in any cell model: the snapshot and marker
cells are administrative, and the payload cell represents the copied cell as
the original does. -/
theorem heap_allocate_copy {definitions : DataEnvironment} {cells : GenericHeap.CellModel definitions}
    {mapping : LocationMap} {world : StoreTyping}
    {before after : Dynamic.Heap} {store : Store} {copied : Dynamic.Cell} {sourceLocation : Dynamic.Location}
    {snapshot marker payload : Value} {snapshotType markerType payloadType : Ty}
    (heaps : GenericHeap.CellHeapRepresents cells mapping world before store)
    (snapshotTyped : RuntimeValueHasType world snapshot snapshotType definitions)
    (markerTyped : RuntimeValueHasType world marker markerType definitions)
    (cell : cells.Represents mapping world copied payload payloadType)
    (allocated : Dynamic.Heap.AllocatesCopy before copied sourceLocation after) :
    GenericHeap.CellHeapRepresents cells (mapping ++ [store.length + 2])
      (world ++ [snapshotType, markerType, OptionalCell.cellType payloadType])
      after (store ++ [snapshot, marker, payload]) ∧
      ReferenceRepresents (mapping ++ [store.length + 2])
        (world ++ [snapshotType, markerType, OptionalCell.cellType payloadType])
        sourceLocation (store.length + 2) payloadType := by
  have snapshotHeaps := heaps.allocate_administrative snapshotTyped
  have markerHeaps := snapshotHeaps.allocate_administrative
    (markerTyped.weaken (show WorldExtends world (world ++ [snapshotType]) from ⟨_, rfl⟩))
  have extended := cells.extend cell (LocationMap.Extends.refl mapping)
    (show WorldExtends world ((world ++ [snapshotType]) ++ [markerType]) from ⟨[snapshotType, markerType], by simp⟩)
  cases allocated
  simpa [Store.allocate, List.append_assoc, Nat.add_assoc] using markerHeaps.append extended

/-! ## One renamed marked copy -/

/-- The frame reference of a copy's request: every copy counts the packed
argument like a named input's own allocation. -/
theorem copyReferences_frame (source : TypedSource) (scope : SourceCoreLocalCell.Scope)
    (binder : TypedBinder) (base : Nat → Nat) (ordinal globals : Nat) :
    SourceCoreSourceCells.copyReferences source scope binder base ordinal
      (scope.length + (if source.inputs.any (fun input => decide (input.id = binder.id)) then 0 else 1) + globals) =
      base (scope.length + 1 + globals) + ordinal := by
  unfold SourceCoreSourceCells.copyReferences
  cases named : source.inputs.any (fun input => decide (input.id = binder.id))
  · simp
  · simp only [↓reduceIte, Nat.add_zero]
    rw [if_neg (by omega)]
    congr 2
    omega

/-- One branch of a marked copy, transported under the actual renaming: the
frame snapshot, a typed marker over the scope's original slots and the
payload cell. -/
theorem branch_evaluates {catalog : SourceCoreDataCatalog.Catalog} {definitions : DataEnvironment}
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {request : SourceCoreSourceCells.Request}
    {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {allocate : SourceCoreSourceCells.Allocator}
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active request)
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated layout globals allocate request)
    (same : annotation.original = allocation.expression)
    (sameDefinitions : layouts.definitions = definitions)
    (payloadShape : request.payload = none ∨ request.payload = some (.var 0))
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment}
    {canonical layoutEnvironment current : Environment} {store : Store} {contextLocation : Location}
    {native : CallableIndexedHistory.NativeFrame} {payload : Option Value} {ρ : Renaming}
    (environments : DataHeap.EnvRepresents catalog mapping world [] request.scope environment canonical definitions)
    (agrees : EnvironmentsAgree request.references canonical layoutEnvironment)
    (reference : layoutEnvironment[SourceCoreCallableIndexedAllocationFrames.referenceIndex globals request]? =
      some (.cellRef layout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native))
    (payloadAt : PayloadAt request layoutEnvironment payload)
    (actual : EnvironmentsAgree ρ layoutEnvironment current) :
    ∃ marker markerType,
      RuntimeValueHasType world marker markerType definitions ∧
      Evaluates current store (annotation.expression.rename ρ)
        (.cellRef (OptionalCell.cellType request.payloadType) (store.length + 2))
        (store ++ [SourceCoreCallableIndexedFrames.encode layout native, marker,
          optionalValue request.payloadType payload]) := by
  obtain ⟨captured, selected, typed⟩ := CallableIndexedOrdinaryAllocation.captures_typed environments agrees
  have captureType : allocation.entry.layout.captureType = SourceCoreSourceCells.captureType request.scope := by
    change SourceCoreSourceCells.captureType allocation.entry.key.scope =
      SourceCoreSourceCells.captureType request.scope
    rw [allocation.keyExact]
    rfl
  have markerRegistered : allocation.entry.layout.Registered definitions := sameDefinitions ▸ allocation.registered
  refine ⟨SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, allocation.entry.layout.type,
    .constructed markerRegistered.payloadLookup (captureType.symm ▸ typed), ?_⟩
  exact CallableIndexedAllocationRenaming.transport allocation annotation same payloadShape
    (CallableIndexedAllocationCompletion.evaluates allocation annotation same reference read selected payloadAt)
    actual

/-- A marked copy of a slot, under the actual renaming: it reads the slot's
cell and returns a reference to a fresh payload cell holding the same
optional value, after the frame snapshot and a typed marker. -/
theorem copy_evaluates {catalog : SourceCoreDataCatalog.Catalog} {definitions : DataEnvironment}
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {binder : TypedBinder} {type : Ty}
    {base : Nat → Nat} {ordinal slot : Nat} {copy : Expr}
    (accepted : SourceCoreSourceCells.copyCell
      (some (SourceCoreCallableIndexedAllocationFrames.allocator layout globals
        (layouts.allocatorAt owner active onError)))
      source scope (SourceCoreSourceCells.copyReferences source scope binder base ordinal) binder type
      (.var slot) = .ok copy)
    (sameDefinitions : layouts.definitions = definitions)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment}
    {canonical layoutEnvironment current : Environment} {store : Store}
    {contextLocation target : Location} {native : CallableIndexedHistory.NativeFrame}
    {payload : Option Value} {ρ : Renaming}
    (environments : DataHeap.EnvRepresents catalog mapping world [] scope environment
      (canonical.take scope.length) definitions)
    (slots : ∀ index, index < scope.length → layoutEnvironment[base index + ordinal]? = canonical[index]?)
    (frame : layoutEnvironment[base (scope.length + 1 + globals) + ordinal]? =
      some (.cellRef layout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native))
    (found : layoutEnvironment[slot]? = some (.cellRef (OptionalCell.cellType type) target))
    (cell : store.read? target = some (optionalValue type payload))
    (agrees : EnvironmentsAgree ρ layoutEnvironment current) :
    ∃ marker markerType,
      RuntimeValueHasType world marker markerType definitions ∧
      Evaluates current store (copy.rename ρ) (.cellRef (OptionalCell.cellType type) (store.length + 2))
        (store ++ [SourceCoreCallableIndexedFrames.encode layout native, marker, optionalValue type payload]) := by
  obtain ⟨absent, present, absentAccepted, presentAccepted, rfl⟩ := copyCell_some accepted
  obtain ⟨absentAllocation, absentAnnotation, absentSame, rfl⟩ :=
    CallableIndexedAllocationCompletion.accepted_receipts onError absentAccepted
  obtain ⟨presentAllocation, presentAnnotation, presentSame, rfl⟩ :=
    CallableIndexedAllocationCompletion.accepted_receipts onError presentAccepted
  have scrutinee : Evaluates current store ((Expr.loadCell (.var slot)).rename ρ) (optionalValue type payload) store :=
    .loadCell (.var (agrees found)) cell
  have shifted : ∀ value : Value,
      EnvironmentsAgree (Renaming.comp (Renaming.insertion 0)
        (SourceCoreSourceCells.copyReferences source scope binder base ordinal))
        (canonical.take scope.length) (value :: layoutEnvironment) := by
    intro value index entry selected
    have below : index < scope.length := by
      have bound := (List.getElem?_eq_some_iff.mp selected).1
      simp only [List.length_take] at bound
      omega
    rw [List.getElem?_take_of_lt below] at selected
    show (value :: layoutEnvironment)[Renaming.insertion 0
      (SourceCoreSourceCells.copyReferences source scope binder base ordinal index)]? = some entry
    simp only [Renaming.insertion, Nat.zero_le, ↓reduceIte, List.getElem?_cons_succ,
      SourceCoreSourceCells.copyReferences, below]
    rw [slots index below]
    exact selected
  have frameAt : ∀ (value : Value) (payloadExpression : Option Expr),
      (value :: layoutEnvironment)[SourceCoreCallableIndexedAllocationFrames.referenceIndex globals
        ⟨source, scope, Renaming.comp (Renaming.insertion 0)
          (SourceCoreSourceCells.copyReferences source scope binder base ordinal), binder, type,
          payloadExpression⟩]? = some (.cellRef layout.type contextLocation) := by
    intro value payloadExpression
    have named : SourceCoreCallableIndexedAllocationFrames.isNamedInput
        ⟨source, scope, Renaming.comp (Renaming.insertion 0)
          (SourceCoreSourceCells.copyReferences source scope binder base ordinal), binder, type,
          payloadExpression⟩ = source.inputs.any (fun input => decide (input.id = binder.id)) := rfl
    show (value :: layoutEnvironment)[Renaming.insertion 0
      (SourceCoreSourceCells.copyReferences source scope binder base ordinal
        (scope.length + (if SourceCoreCallableIndexedAllocationFrames.isNamedInput
          ⟨source, scope, Renaming.comp (Renaming.insertion 0)
            (SourceCoreSourceCells.copyReferences source scope binder base ordinal), binder, type,
            payloadExpression⟩ then 0 else 1) + globals))]? =
      some (.cellRef layout.type contextLocation)
    rw [named, copyReferences_frame]
    simp only [Renaming.insertion, Nat.zero_le, ↓reduceIte, List.getElem?_cons_succ]
    exact frame
  cases payload with
  | none =>
    obtain ⟨marker, markerType, markerTyped, evaluated⟩ := branch_evaluates absentAllocation absentAnnotation
      absentSame sameDefinitions (Or.inl rfl) environments (shifted .unit) (frameAt .unit none)
      read (.absent rfl) (agrees.lift .unit)
    exact ⟨marker, markerType, markerTyped, .caseLeft scrutinee evaluated⟩
  | some value =>
    obtain ⟨marker, markerType, markerTyped, evaluated⟩ := branch_evaluates presentAllocation presentAnnotation
      presentSame sameDefinitions (Or.inr rfl) environments (shifted value)
      (frameAt value (some (.var 0))) read (.initialized rfl rfl) (agrees.lift value)
    exact ⟨marker, markerType, markerTyped, .caseRight scrutinee evaluated⟩

end Solcore.SourceSemantics.CoreLowering.CaptureCopies
