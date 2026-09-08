import Solcore.Resolved.Identity

/-! Owner-only local identity relabeling shared by value-free declarations and
actual runtime binding. Binder indices are retained without an allocator claim. -/

set_option autoImplicit false

namespace Solcore.Frontend

def ownerLocalIdMap (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (id : Resolved.LocalId) : Resolved.LocalId :=
  ⟨mapping id.owner, id.binderIndex⟩

theorem ownerLocalIdMap_injective
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (injective : Function.Injective mapping) :
    Function.Injective (ownerLocalIdMap mapping) := by
  intro left right same
  have owners := injective (congrArg Resolved.LocalId.owner same)
  have indices := congrArg Resolved.LocalId.binderIndex same
  cases left
  cases right
  cases owners
  cases indices
  rfl

end Solcore.Frontend
