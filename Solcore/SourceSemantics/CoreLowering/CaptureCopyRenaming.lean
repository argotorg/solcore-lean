import Solcore.Frontend.SourceCoreSourceCells

/-! The renaming that redirects a scope's copied slots to their copies, one
copy at a time. A copy chain copies its slots at the positions
`chainPositions` lists, in copy order. Each further copy at a fresh position
moves that position to the newest slot and every other index one slot
further, so a lookup agreement through the earlier copies extends to the
next one. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CaptureCopyRenaming
open Core Frontend Frontend.SourceInference
open SourceSemantics.CaptureBinders (copiedBinder?)
open Frontend.SourceCoreSourceCells (copyRenaming scopeCopyRenaming)

/-- The positions a copy chain copies, in copy order, for the remaining slots
`rest` starting at scope index `index`. -/
def chainPositions (source : TypedSource) (base : Nat → Nat) : SourceCoreLocalCell.Scope → Nat → List Nat
  | [], _ => []
  | (id, _) :: rest, index =>
      match copiedBinder? source id with
      | none => chainPositions source base rest (index + 1)
      | some _ => base index :: chainPositions source base rest (index + 1)

private theorem chainPositions_eq_filterMap (source : TypedSource) (base : Nat → Nat) :
    ∀ (rest : SourceCoreLocalCell.Scope) (index : Nat),
      chainPositions source base rest index =
        ((rest.zipIdx index).filterMap fun ((id, type), position) =>
          (copiedBinder? source id).map fun binder => (position, binder, type)).map fun slot => base slot.1
  | [], _ => rfl
  | (id, type) :: rest, index => by
      rw [List.zipIdx_cons, List.filterMap_cons]
      cases copied : copiedBinder? source id with
      | none => simp [chainPositions, copied, chainPositions_eq_filterMap source base rest (index + 1)]
      | some binder => simp [chainPositions, copied, chainPositions_eq_filterMap source base rest (index + 1)]

/-- A scope's copy renaming is the copy renaming of its chain positions. -/
theorem scopeCopyRenaming_eq (source : TypedSource) (scope : SourceCoreLocalCell.Scope) (base : Nat → Nat) :
    scopeCopyRenaming source scope base = copyRenaming (chainPositions source base scope 0) := by
  rw [chainPositions_eq_filterMap]
  rfl

theorem copyRenaming_nil (index : Nat) : copyRenaming [] index = index := by
  simp [copyRenaming]

private theorem findIdx?_none {positions : List Nat} {index : Nat} (absent : index ∉ positions) :
    positions.findIdx? (fun position => decide (position = index)) = none := by
  rw [List.findIdx?_eq_none_iff]
  intro position member
  simp only [decide_eq_false_iff_not]
  rintro rfl
  exact absent member

/-- An uncopied index moves past every copy. -/
theorem copyRenaming_of_not_mem {positions : List Nat} {index : Nat} (absent : index ∉ positions) :
    copyRenaming positions index = index + positions.length := by
  simp only [copyRenaming, findIdx?_none absent]

/-- The newest copy of a fresh position is the first slot. -/
theorem copyRenaming_snoc_self {positions : List Nat} {position : Nat} (fresh : position ∉ positions) :
    copyRenaming (positions ++ [position]) position = 0 := by
  simp [copyRenaming, List.findIdx?_append, findIdx?_none fresh]

private theorem copyRenaming_snoc_of_found {positions : List Nat} {position index ordinal : Nat}
    (found : positions.findIdx? (fun position => decide (position = index)) = some ordinal) :
    copyRenaming (positions ++ [position]) index = copyRenaming positions index + 1 := by
  have bound : ordinal < positions.length := (List.findIdx?_eq_some_iff_findIdx_eq.mp found).1
  simp only [copyRenaming, List.findIdx?_append, found, Option.some_or, List.length_append,
    List.length_singleton]
  omega

/-- A further copy moves an index that already has a copy one slot further. -/
theorem copyRenaming_snoc_of_mem {positions : List Nat} {position index : Nat} (member : index ∈ positions) :
    copyRenaming (positions ++ [position]) index = copyRenaming positions index + 1 := by
  cases found : positions.findIdx? (fun position => decide (position = index)) with
  | none =>
      rw [List.findIdx?_eq_none_iff] at found
      simpa using found index member
  | some ordinal => exact copyRenaming_snoc_of_found found

/-- A further copy of another position moves every index one slot further. -/
theorem copyRenaming_snoc_of_ne {positions : List Nat} {position index : Nat} (different : index ≠ position) :
    copyRenaming (positions ++ [position]) index = copyRenaming positions index + 1 := by
  cases found : positions.findIdx? (fun position => decide (position = index)) with
  | none =>
      have other : [position].findIdx? (fun position => decide (position = index)) = none := by
        simp [Ne.symm different]
      simp only [copyRenaming, List.findIdx?_append, found, other, Option.none_or, Option.map_none,
        List.length_append, List.length_singleton]
      omega
  | some ordinal => exact copyRenaming_snoc_of_found found

/-- Lookup agreement along a renaming. `ReadOnly.EnvironmentsAgree` and
`Renaming.Respects` are this relation on environments and contexts. -/
def Agrees {α : Type} (mapping : Renaming) (source target : List α) : Prop :=
  ∀ ⦃index : Nat⦄ ⦃value : α⦄, source[index]? = some value → target[mapping index]? = some value

namespace Agrees

theorem respects {mapping : Renaming} {source target : Core.Context} :
    Agrees mapping source target ↔ Renaming.Respects mapping source target :=
  ⟨fun agree _ _ found => agree found, fun respects _ _ found => respects found⟩

private theorem getElem?_replace {α : Type} {before after : List α} {old new : α} {index : Nat}
    (different : index ≠ before.length) :
    ((before ++ [new]) ++ after)[index]? = (before ++ old :: after)[index]? := by
  rcases Nat.lt_or_gt_of_ne different with lower | upper
  · rw [List.append_assoc, List.getElem?_append_left lower, List.getElem?_append_left lower]
  · obtain ⟨offset, shifted⟩ : ∃ offset, index = before.length + (offset + 1) :=
      ⟨index - before.length - 1, by omega⟩
    subst shifted
    rw [List.append_assoc, List.singleton_append, List.getElem?_append_right (by omega),
      List.getElem?_append_right (by omega)]
    simp

/-- The first unprocessed slot is read at its own position past the earlier
copies. -/
theorem read {α : Type} {mapping : Renaming} {done : List Nat} {before after target : List α} {old : α}
    (agree : Agrees (Renaming.comp mapping (copyRenaming done)) (before ++ old :: after) target)
    (fresh : before.length ∉ done) :
    target[mapping (before.length + done.length)]? = some old := by
  have found := agree (index := before.length) (value := old) (by simp)
  simpa only [Renaming.comp, copyRenaming_of_not_mem fresh] using found

/-- Copying the first unprocessed slot: the copy becomes the newest value
and takes that slot's place. -/
theorem copy {α : Type} {mapping : Renaming} {done : List Nat} {before after target : List α} {old : α}
    (agree : Agrees (Renaming.comp mapping (copyRenaming done)) (before ++ old :: after) target)
    (fresh : before.length ∉ done) (new : α) :
    Agrees (Renaming.comp mapping.lift (copyRenaming (done ++ [before.length])))
      ((before ++ [new]) ++ after) (new :: target) := by
  intro index value found
  by_cases same : index = before.length
  · subst index
    simp only [Renaming.comp, copyRenaming_snoc_self fresh, Renaming.lift]
    simpa using found
  · simp only [Renaming.comp, copyRenaming_snoc_of_ne same, Renaming.lift, List.getElem?_cons_succ]
    exact agree (by rwa [← getElem?_replace (new := new) same])

/-- Skipping the first unprocessed slot moves it into the processed prefix. -/
theorem skip {α : Type} {mapping : Renaming} {before after target : List α} {old : α}
    (agree : Agrees mapping (before ++ old :: after) target) :
    Agrees mapping ((before ++ [old]) ++ after) target := by
  intro index value found
  exact agree (by simpa only [List.append_assoc, List.singleton_append] using found)

end Agrees

end Solcore.SourceSemantics.CoreLowering.CaptureCopyRenaming
