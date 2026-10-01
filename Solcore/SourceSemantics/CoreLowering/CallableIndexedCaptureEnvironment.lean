import Solcore.SourceSemantics.CoreLowering.CallableIndexedAllocationCompletion
import Solcore.SourceSemantics.CoreLowering.DataEnvironment
import Solcore.SourceSemantics.CoreLowering.ReadOnlyRenaming

/-! Capture slots come from the existing mapped lexical environment, including
hidden match cells. Administrative insertion changes their reference indices,
not their values or aliases. These facts concern the compiler's actual capture
selector; an arbitrary closure may retain additional unused native slots. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedCaptureEnvironment
open Core Frontend GeneralHeap CallableIndexedAllocationCompletion

/-- An indexed scope lookup selects a mapped reference, even when that slot is
an internal match binding with no corresponding source lexical name. -/
theorem scope_slot {catalog : SourceCoreDataCatalog.Catalog} {mapping : LocationMap}
    {world : StoreTyping} {administrative : Core.Context} {scope : SourceCoreLocalCell.Scope}
    {source : Dynamic.Environment} {canonical : Environment}
    (related : DataHeap.EnvRepresents catalog mapping world administrative scope source canonical)
    {index : Nat} {binding : Resolved.LocalId × Ty} (found : scope[index]? = some binding) :
    ∃ (location : Nat) (target : Location), mapping[location]? = some target ∧
      canonical[index]? = some (.cellRef (OptionalCell.cellType binding.2) target) := by
  induction related generalizing index with
  | nil => simp at found
  | @cons scope source canonical id location target payload reference tail ih =>
    cases index with
    | zero =>
      have same : (id, payload) = binding := Option.some.inj found
      subst binding
      exact ⟨location.index, target, reference.mapped, rfl⟩
    | succ index => exact ih found
  | @internal scope source canonical id location target payload reference absent tail ih =>
    cases index with
    | zero =>
      have same : (id, payload) = binding := Option.some.inj found
      subst binding
      exact ⟨location.index, target, reference.mapped, rfl⟩
    | succ index => exact ih found

/-- Real renamed lexical references remain source-mapped; no assumption about
the types of unrelated administrative slots is needed. -/
theorem mapped_slots {catalog : SourceCoreDataCatalog.Catalog} {mapping : LocationMap}
    {world : StoreTyping} {administrative : Core.Context} {scope : SourceCoreLocalCell.Scope}
    {source : Dynamic.Environment} {canonical actual : Environment} {references : Renaming}
    (related : DataHeap.EnvRepresents catalog mapping world administrative scope source canonical)
    (agrees : ReadOnly.EnvironmentsAgree references canonical actual) :
    ∀ index binding, scope[index]? = some binding → ∃ target,
      target ∈ mapping ∧ actual[references index]? = some (.cellRef (OptionalCell.cellType binding.2) target) := by
  intro index binding found
  obtain ⟨location, target, mapped, selected⟩ := scope_slot related found
  exact ⟨target, List.mem_of_getElem? mapped, agrees selected⟩

theorem captures {catalog : SourceCoreDataCatalog.Catalog} {mapping : LocationMap}
    {world : StoreTyping} {administrative : Core.Context} {scope : SourceCoreLocalCell.Scope}
    {source : Dynamic.Environment} {canonical actual : Environment} {references : Renaming}
    (related : DataHeap.EnvRepresents catalog mapping world administrative scope source canonical)
    (agrees : ReadOnly.EnvironmentsAgree references canonical actual) :
    ∃ captured, Captures actual references scope captured := by
  apply Captures.of_slots
  intro index binding found
  obtain ⟨target, _, selected⟩ := mapped_slots related agrees index binding found
  exact ⟨target, selected⟩

/-- A protected snapshot is not among the values selected by an authenticated
capture slot, even if an unrelated native environment slot holds its reference. -/
theorem excludes_snapshot {catalog : SourceCoreDataCatalog.Catalog} {mapping : LocationMap}
    {world : StoreTyping} {administrative : Core.Context} {scope : SourceCoreLocalCell.Scope}
    {source : Dynamic.Environment} {canonical actual : Environment} {references : Renaming}
    (related : DataHeap.EnvRepresents catalog mapping world administrative scope source canonical)
    (agrees : ReadOnly.EnvironmentsAgree references canonical actual)
    {snapshot : Location} (unmapped : snapshot ∉ mapping)
    {index : Nat} {binding : Resolved.LocalId × Ty} (found : scope[index]? = some binding) :
    ∃ target, target ≠ snapshot ∧
      actual[references index]? = some (.cellRef (OptionalCell.cellType binding.2) target) := by
  obtain ⟨target, mapped, selected⟩ := mapped_slots related agrees index binding found
  exact ⟨target, fun same => unmapped (same ▸ mapped), selected⟩

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
