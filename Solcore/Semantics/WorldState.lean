import Solcore.Semantics.RuntimeScalars
import Std.Data.ExtTreeMap.Basic

set_option autoImplicit false

namespace Solcore.Semantics

private abbrev StoredWord :=
  { value : Core.Word // value ≠ Core.Word.zero }

private abbrev AccountStorage :=
  Std.ExtTreeMap Core.Word StoredWord

/-- An existing account with canonical sparse word storage. -/
structure Account where private mk ::
  private storage : AccountStorage
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq

private abbrev AccountMap := Std.ExtTreeMap Address Account

/-- A finite map in which an address may have no account. -/
structure WorldState where private mk ::
  private accounts : AccountMap
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq

namespace Account

/-- The present account whose storage contains no entries. -/
def empty : Account := ⟨∅⟩

/-- Observe whether a physical nonzero storage entry exists. -/
def storageValue?
    (account : Account)
    (slot : Core.Word) : Option Core.Word :=
  (account.storage.get? slot).map Subtype.val

/-- Read a missing storage slot as zero. -/
def storageRead (account : Account) (slot : Core.Word) : Core.Word :=
  (account.storageValue? slot).getD Core.Word.zero

/-- Store nonzero values and delete the entry when writing zero. -/
def storageWrite
    (account : Account)
    (slot value : Core.Word) : Account :=
  if zero : value = Core.Word.zero then
    ⟨account.storage.erase slot⟩
  else
    ⟨account.storage.insert slot ⟨value, zero⟩⟩

end Account

namespace WorldState

/-- The world state in which every account is absent. -/
def empty : WorldState := ⟨∅⟩

/-- Look up an account without conflating absence with an empty account. -/
def account?
    (state : WorldState)
    (address : Address) : Option Account :=
  state.accounts.get? address

/-- Insert or replace an explicitly present account. -/
def putAccount
    (state : WorldState)
    (address : Address)
    (account : Account) : WorldState :=
  ⟨state.accounts.insert address account⟩

/-- Update storage only when the addressed account exists. -/
def writeStorage?
    (state : WorldState)
    (address : Address)
    (slot value : Core.Word) : Option WorldState := do
  let account ← state.account? address
  some (state.putAccount address (account.storageWrite slot value))

end WorldState

end Solcore.Semantics
