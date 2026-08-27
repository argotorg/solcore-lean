import Solcore.Semantics.RuntimeScalars

set_option autoImplicit false

namespace Solcore.Semantics

/-- An account whose semantic storage lookup never returns a stored zero. -/
structure Account where private mk ::
  private storage : Core.Word → Option Core.Word
  private storage_nonzero :
    ∀ slot value, storage slot = some value → value ≠ Core.Word.zero

/-- Semantic lookup for an explicitly present or absent account. -/
structure WorldState where private mk ::
  private accounts : Address → Option Account

namespace Account

/-- The present account whose storage contains no entries. -/
def empty : Account :=
  ⟨fun _ => none, by simp⟩

/-- Observe whether a semantic nonzero storage value exists. -/
def storageValue?
    (account : Account)
    (slot : Core.Word) : Option Core.Word :=
  account.storage slot

/-- Read a missing storage slot as zero. -/
def storageRead (account : Account) (slot : Core.Word) : Core.Word :=
  (account.storageValue? slot).getD Core.Word.zero

/-- Store nonzero values and delete the selected value when writing zero. -/
def storageWrite
    (account : Account)
    (slot value : Core.Word) : Account :=
  if zero : value = Core.Word.zero then
    ⟨fun current => if current = slot then none else account.storage current,
      by
        intro current stored present
        split at present
        · contradiction
        · exact account.storage_nonzero current stored present⟩
  else
    ⟨fun current => if current = slot then some value else account.storage current,
      by
        intro current stored present
        split at present
        · intro stored_zero
          exact zero ((Option.some.inj present).trans stored_zero)
        · exact account.storage_nonzero current stored present⟩

end Account

namespace WorldState

/-- The world state in which every account is absent. -/
def empty : WorldState :=
  ⟨fun _ => none⟩

/-- Look up an account without conflating absence with an empty account. -/
def account?
    (state : WorldState)
    (address : Address) : Option Account :=
  state.accounts address

/-- Insert or replace an explicitly present account. -/
def putAccount
    (state : WorldState)
    (address : Address)
    (account : Account) : WorldState :=
  ⟨fun current => if current = address then some account
    else state.accounts current⟩

/-- Update storage only when the addressed account exists. -/
def writeStorage?
    (state : WorldState)
    (address : Address)
    (slot value : Core.Word) : Option WorldState := do
  let account ← state.account? address
  some (state.putAccount address (account.storageWrite slot value))

end WorldState

end Solcore.Semantics
