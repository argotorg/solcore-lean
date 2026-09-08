import Solcore.Frontend.LocalInputs
import Solcore.Frontend.LocalReferenceProperties
import Solcore.Resolved.LocalScopeProperties

/-! Unique row identities keep selected names, types, and values aligned.
Membership alone selects an identity, not a spelling: repeated names still
obey the independent first-match name lookup judgment. -/

set_option autoImplicit false

namespace Solcore.Frontend

private theorem lookup_projected_of_mem {α : Type} (project : TypedLocalBinding → α)
    {bindings : List TypedLocalBinding} {binding : TypedLocalBinding}
    (unique : (bindings.map (·.id)).Nodup) (member : binding ∈ bindings) :
    Resolved.LocalScope.Lookup (bindings.map fun row => (row.id, project row))
      binding.id (project binding) := by
  induction bindings with
  | nil => cases member
  | cons head rest ih =>
      have uniqueParts := List.nodup_cons.mp unique
      rcases List.mem_cons.mp member with same | member
      · subst head
        exact .head
      · have different : head.id ≠ binding.id := by
          intro same
          apply uniqueParts.1
          change head.id ∈ rest.map (·.id)
          rw [same]
          exact List.mem_map.mpr ⟨binding, member, rfl⟩
        exact .tail different (ih uniqueParts.2 member)

namespace LocalInputs

theorem context_lookup_of_mem (inputs : LocalInputs) {binding : TypedLocalBinding}
    (member : binding ∈ inputs.bindings) :
    Resolved.LocalScope.Lookup inputs.context binding.id binding.type :=
  lookup_projected_of_mem (·.type) inputs.ids_nodup member

theorem environment_lookup_of_mem (inputs : LocalInputs) {binding : TypedLocalBinding}
    (member : binding ∈ inputs.bindings) :
    Resolved.LocalScope.Lookup inputs.environment binding.id binding.value :=
  lookup_projected_of_mem (·.value) inputs.ids_nodup member

/-- A successful first-match name query identifies one actual row whose type
and value are selected by both identity projections. Later equal spellings
are not selected merely because they occur in the input list. -/
theorem lookup?_binding (inputs : LocalInputs) {spelling : String} {id : Resolved.LocalId}
    (selected : LocalNameTable.lookup? inputs.names spelling = some id) :
    ∃ binding, binding ∈ inputs.bindings ∧ binding.name = spelling ∧ binding.id = id ∧
      Resolved.LocalScope.Lookup inputs.context id binding.type ∧
      Resolved.LocalScope.Lookup inputs.environment id binding.value ∧
      Core.ValueHasType binding.value binding.type := by
  have namedMember := (LocalNameTable.lookup?_iff.mp selected).mem
  obtain ⟨binding, member, same⟩ := List.mem_map.mp namedMember
  have nameEq : binding.name = spelling := congrArg Prod.fst same
  have idEq : binding.id = id := congrArg Prod.snd same
  refine ⟨binding, member, nameEq, idEq, ?_, ?_, binding.valueTyped⟩
  · simpa only [idEq] using inputs.context_lookup_of_mem member
  · simpa only [idEq] using inputs.environment_lookup_of_mem member

/-- The newly prepended name and fresh identity select the same supplied type
and value, including when the spelling already occurs among older rows. -/
theorem bindFresh_lookups (inputs : LocalInputs) (owner : Resolved.DeclarationId)
    (name : String) (type : Core.Ty) (value : Core.Value)
    (valueTyped : Core.ValueHasType value type) :
    LocalNameTable.Lookup (inputs.bindFresh owner name type value valueTyped).names
        name (Resolved.freshLocalId owner inputs.ids) ∧
      Resolved.LocalScope.Lookup (inputs.bindFresh owner name type value valueTyped).context
        (Resolved.freshLocalId owner inputs.ids) type ∧
      Resolved.LocalScope.Lookup (inputs.bindFresh owner name type value valueTyped).environment
        (Resolved.freshLocalId owner inputs.ids) value :=
  ⟨.head, .head, .head⟩

end LocalInputs

end Solcore.Frontend
