import Solcore.Frontend.LocalReference
import Solcore.Resolved.Typing
import Solcore.Resolved.Eval
import Solcore.Resolved.FreshIdentity
import Solcore.Core.Safety

/-! Explicit typed local inputs with unique assigned identities. All three
projections retain the same order; repeated spellings keep the existing
first-match table behavior. This does not introduce source binding syntax. -/

set_option autoImplicit false

namespace Solcore.Frontend

/-- One supplied local value with structural Core typing evidence. This does
not assert allocation or runtime store validity for a contained reference. -/
structure TypedLocalBinding where
  name : String
  id : Resolved.LocalId
  type : Core.Ty
  value : Core.Value
  valueTyped : Core.ValueHasType value type

/-- A shared ordered input for name resolution, checking, and execution.
Unique IDs prevent one spelling from selecting another row's type or value. -/
structure LocalInputs where
  bindings : List TypedLocalBinding
  ids_nodup : (bindings.map (·.id)).Nodup

namespace LocalInputs

def ids (inputs : LocalInputs) : List Resolved.LocalId :=
  inputs.bindings.map (·.id)

def names (inputs : LocalInputs) : LocalNameTable :=
  inputs.bindings.map fun binding => (binding.name, binding.id)

def context (inputs : LocalInputs) : Resolved.Context :=
  inputs.bindings.map fun binding => (binding.id, binding.type)

def environment (inputs : LocalInputs) : Resolved.Environment :=
  inputs.bindings.map fun binding => (binding.id, binding.value)

def empty : LocalInputs := ⟨[], by simp⟩

/-- Prepend one explicitly typed input using an ID fresh only for these
inputs. A repeated spelling shadows its previous table entry; this is not
a source-language allocation policy or an existing-source preservation law. -/
def bindFresh (inputs : LocalInputs) (owner : Resolved.DeclarationId)
    (name : String) (type : Core.Ty) (value : Core.Value)
    (valueTyped : Core.ValueHasType value type) : LocalInputs where
  bindings := {
    name
    id := Resolved.freshLocalId owner inputs.ids
    type
    value
    valueTyped
  } :: inputs.bindings
  ids_nodup := by
    change (Resolved.freshLocalId owner inputs.ids :: inputs.ids).Nodup
    exact List.nodup_cons.mpr
      ⟨Resolved.freshLocalId_not_mem owner inputs.ids, inputs.ids_nodup⟩

end LocalInputs

end Solcore.Frontend
