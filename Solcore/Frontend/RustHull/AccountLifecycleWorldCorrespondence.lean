import Solcore.Frontend.RustHull.AccountLifecycleSemantics
import Solcore.Frontend.RustHull.CatalogWorldCorrespondence

/-! Destruction updates retain exact catalog identities. Pending deletion only
changes a lifecycle flag; transaction finalization owns actual removal. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.AccountLifecycleCorrespondence
open Core
open StorageCorrespondence (Accounts)
open CatalogWorldCorrespondence (Anchor Links)

def publishAccounts (accounts : Accounts) (current : Word) (account : AccountState.Account) (identity : Nat) : Accounts :=
  if account.created then StorageCorrespondence.put current {account with destroyed := true} identity accounts else accounts

def destroyAccounts (accounts : Accounts) (balances : StorageSemantics.Words) (current beneficiary : Word) (complete : Bool) :
    Except Word (Accounts × StorageSemantics.Words) := do
  let current := AccountLifecycleSemantics.address current
  let beneficiary := AccountLifecycleSemantics.address beneficiary
  let (account, identity) ← StorageCorrespondence.get accounts current complete
  let next ← AccountLifecycleSemantics.balances account.created current beneficiary balances
  return (publishAccounts accounts current account identity, next)

theorem publish_source (accounts : Accounts) (current : Word) (account : AccountState.Account) (identity : Nat) :
    (publishAccounts accounts current account identity).map Prod.fst =
      AccountLifecycleSemantics.publish (accounts.map Prod.fst) current account := by
  simp only [publishAccounts, AccountLifecycleSemantics.publish]
  split
  · exact StorageCorrespondence.put_source ..
  · rfl

theorem destroy_source (accounts : Accounts) (balances : StorageSemantics.Words) (current beneficiary : Word) (complete : Bool) :
    (destroyAccounts accounts balances current beneficiary complete).map (fun next => (next.1.map Prod.fst, next.2)) =
      AccountLifecycleSemantics.destroy (accounts.map Prod.fst) balances current beneficiary complete := by
  unfold destroyAccounts AccountLifecycleSemantics.destroy
  dsimp only
  rw [← StorageCorrespondence.get_source]
  cases found : StorageCorrespondence.get accounts (AccountLifecycleSemantics.address current) complete with
  | error reason => rfl
  | ok pair =>
    rcases pair with ⟨account, identity⟩
    dsimp only [Bind.bind, Except.bind, Except.map, Pure.pure, Except.pure]
    cases next : AccountLifecycleSemantics.balances account.created (AccountLifecycleSemantics.address current)
        (AccountLifecycleSemantics.address beneficiary) balances with
    | error reason => rfl
    | ok values => simp only [publish_source]

theorem publish_links {anchors : List Anchor} {accounts : Accounts} {current : Word}
    {account : AccountState.Account} {identity : Nat} {complete : Bool}
    (linked : Links anchors accounts) (found : StorageCorrespondence.get accounts current complete = .ok (account, identity)) :
    Links anchors (publishAccounts accounts current account identity) := by
  intro anchor member
  obtain ⟨selected, selectedAt, code⟩ := linked anchor member
  unfold publishAccounts
  split
  · by_cases same : current = anchor.address
    · subst current
      have original : StorageCorrespondence.get accounts anchor.address complete = .ok (selected, anchor.identity) := by
        simp only [StorageCorrespondence.get, selectedAt]
      cases Except.ok.inj (found.symm.trans original)
      exact ⟨_, CatalogWorldCorrespondence.lookup_put_same .., code⟩
    · exact ⟨selected, (CatalogWorldCorrespondence.lookup_put_other same ..).trans selectedAt, code⟩
  · exact ⟨selected, selectedAt, code⟩

def nextAccounts (initial : Accounts) : Except Word (Accounts × StorageSemantics.Words) → Accounts
  | .ok next => next.1
  | .error _ => initial

def nextBalances (initial : StorageSemantics.Words) : Except Word (Accounts × StorageSemantics.Words) → StorageSemantics.Words
  | .ok next => next.2
  | .error _ => initial

theorem destroy_links {anchors : List Anchor} {accounts : Accounts} (linked : Links anchors accounts)
    (balances : StorageSemantics.Words) (current beneficiary : Word) (complete : Bool) :
    Links anchors (nextAccounts accounts (destroyAccounts accounts balances current beneficiary complete)) := by
  unfold destroyAccounts
  dsimp only
  cases found : StorageCorrespondence.get accounts (AccountLifecycleSemantics.address current) complete with
  | error reason => exact linked
  | ok pair =>
    rcases pair with ⟨account, identity⟩
    dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
    cases next : AccountLifecycleSemantics.balances account.created (AccountLifecycleSemantics.address current)
        (AccountLifecycleSemantics.address beneficiary) balances with
    | error reason => exact linked
    | ok values => exact publish_links linked found

end Solcore.Frontend.RustHull.AccountLifecycleCorrespondence
