import Solcore.Semantics.WorldState

set_option autoImplicit false

namespace Solcore.Semantics

@[ext] theorem Account.ext
    {left right : Account}
    (same : ∀ slot,
      left.storageValue? slot = right.storageValue? slot) :
    left = right := by
  cases left
  cases right
  simp only [Account.storageValue?] at same
  congr
  funext slot
  exact same slot

@[ext] theorem WorldState.ext
    {left right : WorldState}
    (same : ∀ address,
      left.account? address = right.account? address) :
    left = right := by
  cases left
  cases right
  simp only [WorldState.account?] at same
  congr
  funext address
  exact same address

end Solcore.Semantics
