import Solcore.Frontend.LocalReferenceElaboration
import Solcore.Frontend.LocalReferenceProperties
import Solcore.Resolved.LoweringProperties

/-! Exact typed elaboration for canonical identifiers and grouping. Both tables
remain arbitrary ordered inputs, including duplicate names and identities. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem elaborateLocalReference?_sound {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateLocalReference? table context source = some (core, type)) :
    ∃ id index, ResolvesLocalReference table source id ∧
      Resolved.LocalScope.IndexOf (Resolved.LocalScope.ids context) id index ∧
      Resolved.LocalScope.Lookup context id type ∧ core = .var index := by
  simp only [elaborateLocalReference?, bind, Option.bind_eq_some_iff, pure] at accepted
  obtain ⟨resolved, resolution, actualCore, lowering, actualType, inferred, result⟩ := accepted
  cases result
  obtain ⟨id, reference, rfl⟩ := resolveLocalReference?_eq_some_iff.mp resolution
  change (Resolved.LocalScope.index? (Resolved.LocalScope.ids context) id).map Core.Expr.var =
    some core at lowering
  simp only [Option.map_eq_some_iff] at lowering
  obtain ⟨index, indexResult, rfl⟩ := lowering
  have indexed := Resolved.LocalScope.index?_iff.mp indexResult
  have typed := Core.infer_sound inferred
  cases typed with
  | var atType =>
      exact ⟨id, index, reference, indexed,
        Resolved.LocalScope.lookup_of_indexed indexed atType, rfl⟩

theorem elaborateLocalReference?_complete {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} {id : Resolved.LocalId} {index : Nat} {type : Core.Ty}
    (reference : ResolvesLocalReference table source id)
    (indexed : Resolved.LocalScope.IndexOf (Resolved.LocalScope.ids context) id index)
    (found : Resolved.LocalScope.Lookup context id type) :
    elaborateLocalReference? table context source = some (.var index, type) := by
  have lowering := (Resolved.Lowers.var indexed).complete
  have inferred := Core.infer_complete
    (Core.HasType.var ((Resolved.LocalScope.lookup_iff_getElem? indexed).mp found)
      (definitions := []))
  simp [elaborateLocalReference?, reference.complete, lowering, inferred]

theorem elaborateLocalReference?_iff {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty} :
    elaborateLocalReference? table context source = some (core, type) ↔
      ∃ id index, ResolvesLocalReference table source id ∧
        Resolved.LocalScope.IndexOf (Resolved.LocalScope.ids context) id index ∧
        Resolved.LocalScope.Lookup context id type ∧ core = .var index := by
  constructor
  · exact elaborateLocalReference?_sound
  · rintro ⟨id, index, reference, indexed, found, rfl⟩
    exact elaborateLocalReference?_complete reference indexed found

/-- Independent reference typing is exactly the existence of a checked elaboration. -/
theorem localReferenceHasType_iff_elaborates {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} {type : Core.Ty} :
    LocalReferenceHasType table context source type ↔
      ∃ core, elaborateLocalReference? table context source = some (core, type) := by
  constructor
  · intro typing
    cases typing with
    | resolved reference found =>
        obtain ⟨index, indexed, _⟩ := found.indexed
        exact ⟨_, elaborateLocalReference?_complete reference indexed found⟩
  · rintro ⟨core, accepted⟩
    obtain ⟨id, index, reference, _, found, _⟩ := elaborateLocalReference?_sound accepted
    exact .resolved reference found

/-- Every returned type has the existing declarative Core typing derivation. -/
theorem elaborateLocalReference?_core_hasType {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateLocalReference? table context source = some (core, type)) :
    Core.HasType (Resolved.LocalScope.values context) core type := by
  obtain ⟨id, index, _, indexed, found, rfl⟩ := elaborateLocalReference?_sound accepted
  exact .var ((Resolved.LocalScope.lookup_iff_getElem? indexed).mp found)

/-- A resolved name does not suffice: its ID must occur in the supplied context. -/
theorem elaborateLocalReference?_eq_none_of_missing_id {table : LocalNameTable}
    {context : Resolved.Context} {source : Syntax.Expr} {id : Resolved.LocalId}
    (reference : ResolvesLocalReference table source id)
    (missing : id ∉ Resolved.LocalScope.ids context) :
    elaborateLocalReference? table context source = none := by
  have indexMissing := Resolved.LocalScope.index?_eq_none_iff.mpr missing
  simp [elaborateLocalReference?, reference.complete, Resolved.Expr.lower?, indexMissing]

/-- Adapter failure is exactly absence of an independent supported-reference type. -/
theorem elaborateLocalReference?_eq_none_iff {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} :
    elaborateLocalReference? table context source = none ↔
      ¬ ∃ type, LocalReferenceHasType table context source type := by
  constructor
  · intro rejected ⟨type, typing⟩
    obtain ⟨core, accepted⟩ := localReferenceHasType_iff_elaborates.mp typing
    rw [rejected] at accepted
    cases accepted
  · intro missing
    cases result : elaborateLocalReference? table context source with
    | none => rfl
    | some pair =>
        exact False.elim (missing ⟨pair.2,
          localReferenceHasType_iff_elaborates.mpr ⟨pair.1, result⟩⟩)

end Solcore.Frontend
