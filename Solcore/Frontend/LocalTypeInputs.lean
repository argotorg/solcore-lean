import Solcore.Frontend.LocalReference
import Solcore.Resolved.Typing
import Solcore.Resolved.FreshIdentity

/-! Ordered type-only local inputs share identities between name resolution
and typing. They contain neither runtime values nor inhabitation evidence. -/

set_option autoImplicit false

namespace Solcore.Frontend

structure LocalTypeBinding where
  name : String
  id : Resolved.LocalId
  type : Core.Ty

structure LocalTypeInputs where
  bindings : List LocalTypeBinding
  ids_nodup : (bindings.map (·.id)).Nodup

namespace LocalTypeInputs

def ids (inputs : LocalTypeInputs) : List Resolved.LocalId :=
  inputs.bindings.map (·.id)

def names (inputs : LocalTypeInputs) : LocalNameTable :=
  inputs.bindings.map fun binding => (binding.name, binding.id)

def context (inputs : LocalTypeInputs) : Resolved.Context :=
  inputs.bindings.map fun binding => (binding.id, binding.type)

def empty : LocalTypeInputs := ⟨[], by simp⟩

/-- This explicit construction introduces no source-level binding policy. -/
def bindFresh (inputs : LocalTypeInputs) (owner : Resolved.DeclarationId)
    (name : String) (type : Core.Ty) : LocalTypeInputs where
  bindings := { name, id := Resolved.freshLocalId owner inputs.ids, type } :: inputs.bindings
  ids_nodup := by
    change (Resolved.freshLocalId owner inputs.ids :: inputs.ids).Nodup
    exact List.nodup_cons.mpr
      ⟨Resolved.freshLocalId_not_mem owner inputs.ids, inputs.ids_nodup⟩

end LocalTypeInputs

end Solcore.Frontend
