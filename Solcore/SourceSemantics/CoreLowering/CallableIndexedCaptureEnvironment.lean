import Solcore.SourceSemantics.CoreLowering.CallableIndexedAllocationCompletion
import Solcore.SourceSemantics.CoreLowering.DataEnvironment
import Solcore.SourceSemantics.CoreLowering.ReadOnlyRenaming

/-! Capture slots come from the existing lexical environment, including hidden
match cells and a closure's copies of them. Administrative insertion changes
their reference indices, not their values or aliases. These facts concern the
compiler's actual capture selector; an arbitrary closure may retain additional
unused native slots. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedCaptureEnvironment
open Core Frontend GeneralHeap CallableIndexedAllocationCompletion

/-- An indexed scope lookup selects a typed cell reference, even when that slot
is an internal match binding with no corresponding source lexical name. -/
theorem scope_slot {catalog : SourceCoreDataCatalog.Catalog} {mapping : LocationMap}
    {world : StoreTyping} {administrative : Core.Context} {scope : SourceCoreLocalCell.Scope}
    {source : Dynamic.Environment} {canonical : Environment}
    (related : DataHeap.EnvRepresents catalog mapping world administrative scope source canonical)
    {index : Nat} {binding : Resolved.LocalId × Ty} (found : scope[index]? = some binding) :
    ∃ target : Location, world[target]? = some (OptionalCell.cellType binding.2) ∧
      canonical[index]? = some (.cellRef (OptionalCell.cellType binding.2) target) := by
  induction related generalizing index with
  | nil => simp at found
  | @cons scope source canonical id location target payload reference tail ih =>
    cases index with
    | zero =>
      have same : (id, payload) = binding := Option.some.inj found
      subst binding
      exact ⟨target, reference.typed, rfl⟩
    | succ index => exact ih found
  | @internal scope source canonical id target payload typed absent tail ih =>
    cases index with
    | zero =>
      have same : (id, payload) = binding := Option.some.inj found
      subst binding
      exact ⟨target, typed, rfl⟩
    | succ index => exact ih found

/-- Real renamed lexical references remain typed cell references; no
assumption about the types of unrelated administrative slots is needed. -/
theorem selected_slots {catalog : SourceCoreDataCatalog.Catalog} {mapping : LocationMap}
    {world : StoreTyping} {administrative : Core.Context} {scope : SourceCoreLocalCell.Scope}
    {source : Dynamic.Environment} {canonical actual : Environment} {references : Renaming}
    (related : DataHeap.EnvRepresents catalog mapping world administrative scope source canonical)
    (agrees : ReadOnly.EnvironmentsAgree references canonical actual) :
    ∀ index binding, scope[index]? = some binding → ∃ target,
      world[target]? = some (OptionalCell.cellType binding.2) ∧
      actual[references index]? = some (.cellRef (OptionalCell.cellType binding.2) target) := by
  intro index binding found
  obtain ⟨target, typed, selected⟩ := scope_slot related found
  exact ⟨target, typed, agrees selected⟩

theorem captures {catalog : SourceCoreDataCatalog.Catalog} {mapping : LocationMap}
    {world : StoreTyping} {administrative : Core.Context} {scope : SourceCoreLocalCell.Scope}
    {source : Dynamic.Environment} {canonical actual : Environment} {references : Renaming}
    (related : DataHeap.EnvRepresents catalog mapping world administrative scope source canonical)
    (agrees : ReadOnly.EnvironmentsAgree references canonical actual) :
    ∃ captured, Captures actual references scope captured := by
  apply Captures.of_slots
  intro index binding found
  obtain ⟨target, _, selected⟩ := selected_slots related agrees index binding found
  exact ⟨target, selected⟩

/-- A protected snapshot is not among the values selected by an authenticated
capture slot, even if an unrelated native environment slot holds its reference:
every selected slot is an optional cell, and the snapshot is not. -/
theorem excludes_snapshot {catalog : SourceCoreDataCatalog.Catalog} {mapping : LocationMap}
    {world : StoreTyping} {administrative : Core.Context} {scope : SourceCoreLocalCell.Scope}
    {source : Dynamic.Environment} {canonical actual : Environment} {references : Renaming}
    (related : DataHeap.EnvRepresents catalog mapping world administrative scope source canonical)
    (agrees : ReadOnly.EnvironmentsAgree references canonical actual)
    {snapshot : Location} {snapshotType : Ty} (snapshotTyped : world[snapshot]? = some snapshotType)
    (notCell : ∀ payload, snapshotType ≠ OptionalCell.cellType payload)
    {index : Nat} {binding : Resolved.LocalId × Ty} (found : scope[index]? = some binding) :
    ∃ target, target ≠ snapshot ∧
      actual[references index]? = some (.cellRef (OptionalCell.cellType binding.2) target) := by
  obtain ⟨target, typed, selected⟩ := selected_slots related agrees index binding found
  refine ⟨target, fun same => ?_, selected⟩
  subst same
  exact notCell binding.2 (Option.some.inj (snapshotTyped.symm.trans typed))

/-- Inserting the allocation's snapshot reference leaves all selected capture
values unchanged. The general heap correspondence supplies the source slots. -/
theorem captures_inserted {catalog : SourceCoreDataCatalog.Catalog} {mapping : LocationMap}
    {world : StoreTyping} {administrative : Core.Context} {scope : SourceCoreLocalCell.Scope}
    {source : Dynamic.Environment} {canonical actual : Environment} {references : Renaming}
    (related : DataHeap.EnvRepresents catalog mapping world administrative scope source canonical)
    (agrees : ReadOnly.EnvironmentsAgree references canonical actual) (inserted : Value) :
    ∃ captured, Captures actual references scope captured ∧
      Captures (inserted :: actual) (fun index => references index + 1) scope captured := by
  obtain ⟨captured, selected⟩ := captures related agrees
  exact ⟨captured, selected, selected.weaken inserted⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedCaptureEnvironment
