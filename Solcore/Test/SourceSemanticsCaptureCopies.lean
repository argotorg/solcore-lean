import Solcore.SourceSemantics.Dynamic.Typing

/-! The copies a closure makes of a captured environment, computed. A binding
whose identifier the closure's source copies (`CaptureBinders.copiedBinder?`)
gets a fresh cell at the end of the heap holding a copy of its cell; every
other binding keeps its location. When every binding holds a cell this is the
source semantics' `EnvironmentCopies`, so a hand-built trace can state its exact
heap over the copies made by a generalized `let` and by each closure call. -/
set_option autoImplicit false
namespace Tests.SourceSemanticsCaptureCopies
open Solcore Frontend SourceInference SourceSemantics

/-- Every binding of `environment` holds a cell of `heap`. -/
def Readable (heap : Dynamic.Heap) (environment : Dynamic.Environment) : Prop :=
  ∀ binding ∈ environment, ∃ cell, Dynamic.Heap.Reads heap binding.2 cell

/-- The cell copied for one binding: its cell, when the source copies the
identifier and the location holds a cell. -/
def copiedCell? (source : TypedSource) (id : Resolved.LocalId) (heap : Dynamic.Heap)
    (location : Dynamic.Location) : Option Dynamic.Cell :=
  if (CaptureBinders.copiedBinder? source id).isSome then heap.cells[location.index]? else none

/-- The copies of `environment` made from `heap`, most recent binding first,
and the heap after them. -/
def copies (source : TypedSource) : Dynamic.Environment → Dynamic.Heap → Dynamic.Environment × Dynamic.Heap
  | [], heap => ([], heap)
  | (id, location) :: rest, heap =>
    match copiedCell? source id heap location with
    | some cell =>
      ((id, ⟨heap.cells.length⟩) :: (copies source rest ⟨heap.cells ++ [cell]⟩).1,
        (copies source rest ⟨heap.cells ++ [cell]⟩).2)
    | none => ((id, location) :: (copies source rest heap).1, (copies source rest heap).2)

theorem cellAt_iff : ∀ {cells : List Dynamic.Cell} {index : Nat} {cell : Dynamic.Cell},
    Dynamic.Heap.CellAt cells index cell ↔ cells[index]? = some cell
  | [], _, _ => by
    constructor
    · intro selected; cases selected
    · intro found; simp at found
  | _ :: _, 0, _ => by
    constructor
    · intro selected; cases selected; rfl
    · intro found
      simp only [List.getElem?_cons_zero, Option.some.injEq] at found
      subst found
      exact .head
  | _ :: _, _ + 1, _ => by
    constructor
    · intro selected
      cases selected with
      | tail rest => simpa only [List.getElem?_cons_succ] using cellAt_iff.mp rest
    · intro found
      exact .tail (cellAt_iff.mpr (by simpa only [List.getElem?_cons_succ] using found))

theorem reads_iff {heap : Dynamic.Heap} {location : Dynamic.Location} {cell : Dynamic.Cell} :
    Dynamic.Heap.Reads heap location cell ↔ heap.cells[location.index]? = some cell :=
  ⟨fun | .intro selected => cellAt_iff.mp selected, fun found => .intro (cellAt_iff.mpr found)⟩

namespace Readable

theorem tail {heap : Dynamic.Heap} {binding : Resolved.LocalId × Dynamic.Location}
    {environment : Dynamic.Environment} (readable : Readable heap (binding :: environment)) :
    Readable heap environment :=
  fun other member => readable other (List.mem_cons_of_mem _ member)

theorem mono {before after : Dynamic.Heap} {environment : Dynamic.Environment}
    (readable : Readable before environment) (extension : Dynamic.HeapMetadataExtend before after) :
    Readable after environment := by
  intro binding member
  obtain ⟨cell, read⟩ := readable binding member
  obtain ⟨updated, updatedRead, _, _⟩ := extension _ _ read
  exact ⟨updated, updatedRead⟩

/-- A lexically agreeing environment holds a cell for every binding. -/
theorem of_agrees {heap : Dynamic.Heap} {scope : Resolved.LocalScope TypeSystem.Scheme}
    {environment : Dynamic.Environment} (agrees : Dynamic.EnvironmentAgrees heap scope environment) :
    Readable heap environment := by
  induction agrees with
  | nil => intro _ member; cases member
  | cons read _ _ _ ih =>
    intro binding member
    rcases List.mem_cons.mp member with same | rest
    · subst same; exact ⟨_, read⟩
    · exact ih binding rest

/-- The copies hold a cell for every binding: a copy holds its fresh cell and a
shared binding keeps its cell. -/
theorem of_copies {source : TypedSource} {environment copied : Dynamic.Environment}
    {before after : Dynamic.Heap} (copy : Dynamic.EnvironmentCopies source environment before copied after)
    (readable : Readable before environment) : Readable after copied := by
  induction copy with
  | nil => exact readable
  | shared _ tail ih =>
    intro binding member
    rcases List.mem_cons.mp member with same | rest
    · subst same
      obtain ⟨cell, read⟩ := readable _ List.mem_cons_self
      exact ⟨cell, tail.preserves_read read⟩
    · exact ih readable.tail binding rest
  | copied _ _ allocate tail ih =>
    intro binding member
    rcases List.mem_cons.mp member with same | rest
    · subst same
      exact ⟨_, tail.preserves_read allocate.reads_new⟩
    · exact ih (readable.tail.mono (Dynamic.HeapMetadataExtend.of_copy allocate)) binding rest

end Readable

/-- Copying only appends cells. -/
theorem appends_of_copies {source : TypedSource} {environment copied : Dynamic.Environment}
    {before after : Dynamic.Heap} (copy : Dynamic.EnvironmentCopies source environment before copied after) :
    ∃ added, after.cells = before.cells ++ added := by
  induction copy with
  | nil => exact ⟨[], by simp⟩
  | shared _ _ ih => exact ih
  | @copied _ _ _ _ cell _ _ _ _ _ _ _ allocate _ ih =>
    obtain ⟨added, same⟩ := ih
    cases allocate
    exact ⟨cell :: added, by simp [same]⟩

/-- A lookup in the copies reads an exact copy of the cell the original lookup
reads: copying never changes what a captured binding holds. -/
theorem copy_reads {source : TypedSource} {environment copied : Dynamic.Environment}
    {before after : Dynamic.Heap} (copy : Dynamic.EnvironmentCopies source environment before copied after)
    {id : Resolved.LocalId} {location : Dynamic.Location} {cell : Dynamic.Cell}
    (lookup : Dynamic.Environment.LooksUp environment id location) (read : Dynamic.Heap.Reads before location cell) :
    ∃ copyLocation, Dynamic.Environment.LooksUp copied id copyLocation ∧ Dynamic.Heap.Reads after copyLocation cell := by
  induction copy generalizing location with
  | nil => cases lookup
  | shared _ tail ih =>
    cases lookup with
    | head => exact ⟨_, .head, tail.preserves_read read⟩
    | tail different rest =>
      obtain ⟨copyLocation, found, copyRead⟩ := ih rest read
      exact ⟨copyLocation, .tail different found, copyRead⟩
  | copied _ original allocate tail ih =>
    cases lookup with
    | head =>
      have same := original.functional read
      subst same
      exact ⟨_, .head, tail.preserves_read allocate.reads_new⟩
    | tail different rest =>
      obtain ⟨copyLocation, found, copyRead⟩ := ih rest (allocate.preserves_read read)
      exact ⟨copyLocation, .tail different found, copyRead⟩

theorem copies_some {source : TypedSource} {id : Resolved.LocalId} {location : Dynamic.Location}
    {rest : Dynamic.Environment} {heap : Dynamic.Heap} {cell : Dynamic.Cell}
    (found : copiedCell? source id heap location = some cell) :
    copies source ((id, location) :: rest) heap =
      ((id, ⟨heap.cells.length⟩) :: (copies source rest ⟨heap.cells ++ [cell]⟩).1,
        (copies source rest ⟨heap.cells ++ [cell]⟩).2) := by
  rw [copies, found]

theorem copies_none {source : TypedSource} {id : Resolved.LocalId} {location : Dynamic.Location}
    {rest : Dynamic.Environment} {heap : Dynamic.Heap}
    (absent : copiedCell? source id heap location = none) :
    copies source ((id, location) :: rest) heap =
      ((id, location) :: (copies source rest heap).1, (copies source rest heap).2) := by
  rw [copies, absent]

/-- When every binding holds a cell, the computed copies are the source
semantics' copies. -/
theorem copies_spec (source : TypedSource) : ∀ {environment : Dynamic.Environment} {heap : Dynamic.Heap},
    Readable heap environment →
      Dynamic.EnvironmentCopies source environment heap (copies source environment heap).1
        (copies source environment heap).2
  | [], heap, _ => .nil heap
  | (id, location) :: rest, heap, readable => by
    cases decision : CaptureBinders.copiedBinder? source id with
    | none =>
      have absent : copiedCell? source id heap location = none := by simp [copiedCell?, decision]
      rw [copies_none absent]
      exact .shared decision (copies_spec source readable.tail)
    | some binder =>
      obtain ⟨cell, read⟩ := readable (id, location) List.mem_cons_self
      have found : copiedCell? source id heap location = some cell := by
        simpa [copiedCell?, decision] using reads_iff.mp read
      rw [copies_some found]
      have allocate : Dynamic.Heap.AllocatesCopy heap cell ⟨heap.cells.length⟩ ⟨heap.cells ++ [cell]⟩ := .append
      exact .copied decision read allocate
        (copies_spec source (readable.tail.mono (Dynamic.HeapMetadataExtend.of_copy allocate)))

/-- Copying only appends cells. -/
theorem copies_appends (source : TypedSource) : ∀ (environment : Dynamic.Environment) (heap : Dynamic.Heap),
    ∃ added, (copies source environment heap).2.cells = heap.cells ++ added
  | [], heap => ⟨[], by simp [copies]⟩
  | (id, location) :: rest, heap => by
    cases found : copiedCell? source id heap location with
    | none =>
      rw [copies_none found]
      exact copies_appends source rest heap
    | some cell =>
      rw [copies_some found]
      obtain ⟨added, same⟩ := copies_appends source rest ⟨heap.cells ++ [cell]⟩
      exact ⟨cell :: added, by simp [same]⟩

/-- A substitution instance of a source copies the same bindings. -/
theorem copiedCell?_applySubstitution (substitution : TypeSystem.Substitution) (source : TypedSource)
    (id : Resolved.LocalId) (heap : Dynamic.Heap) (location : Dynamic.Location) :
    copiedCell? (source.applySubstitution substitution) id heap location = copiedCell? source id heap location := by
  simp only [copiedCell?, CaptureBinders.copied_isSome_applySubstitution]

theorem copies_applySubstitution (substitution : TypeSystem.Substitution) (source : TypedSource) :
    ∀ (environment : Dynamic.Environment) (heap : Dynamic.Heap),
      copies (source.applySubstitution substitution) environment heap = copies source environment heap
  | [], _ => rfl
  | (id, location) :: rest, heap => by
    cases found : copiedCell? source id heap location with
    | none =>
      rw [copies_none found, copies_none ((copiedCell?_applySubstitution substitution source id heap location).trans found),
        copies_applySubstitution substitution source rest heap]
    | some cell =>
      rw [copies_some found, copies_some ((copiedCell?_applySubstitution substitution source id heap location).trans found),
        copies_applySubstitution substitution source rest]

/-- The copies a call of an instantiated closure makes over a substituted source
are those of the original source. -/
theorem copies_spec_applySubstitution (substitution : TypeSystem.Substitution) (source : TypedSource)
    {environment : Dynamic.Environment} {heap : Dynamic.Heap} (readable : Readable heap environment) :
    Dynamic.EnvironmentCopies (source.applySubstitution substitution) environment heap
      (copies source environment heap).1 (copies source environment heap).2 := by
  rw [← copies_applySubstitution substitution source]
  exact copies_spec _ readable

end Tests.SourceSemanticsCaptureCopies
