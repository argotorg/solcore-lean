import Solcore.Frontend.LocalInputsLookupProperties
import Solcore.Frontend.LocalInputsProperties

/-! Shared lookup facts for preserving source meaning when a fresh typed input
is added. Freshness is relative to the existing input rows, not global. -/

set_option autoImplicit false

namespace Solcore.Frontend.LocalInputExtensionSupport

theorem fresh_ne_of_named (inputs : LocalInputs) (owner : Resolved.DeclarationId)
    {spelling : String} {id : Resolved.LocalId}
    (named : LocalNameTable.Lookup inputs.names spelling id) :
    Resolved.freshLocalId owner inputs.ids ≠ id := by
  obtain ⟨binding, member, _, idEq, _⟩ :=
    inputs.lookup?_binding (LocalNameTable.lookup?_iff.mpr named)
  intro same
  apply inputs.bindFresh_id_fresh owner
  exact List.mem_map.mpr ⟨binding, member, idEq.trans same.symm⟩

theorem identity_lookup_cons_iff {α : Type} {scope : Resolved.LocalScope α}
    {id newId : Resolved.LocalId} {value newValue : α} (different : newId ≠ id) :
    Resolved.LocalScope.Lookup ((newId, newValue) :: scope) id value ↔
      Resolved.LocalScope.Lookup scope id value := by
  constructor
  · intro found
    cases found with
    | head => exact False.elim (different rfl)
    | tail _ found => exact found
  · exact Resolved.LocalScope.Lookup.tail different

end Solcore.Frontend.LocalInputExtensionSupport
