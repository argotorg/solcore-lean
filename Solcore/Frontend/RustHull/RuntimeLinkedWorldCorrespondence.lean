import Solcore.Frontend.RustHull.CatalogWorldCorrespondence

/-! The actual world cell retains selected catalog identities across storage
operations. Existing source world observations are recovered by forgetting
only the additional code-link evidence. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeLinkedWorldCorrespondence
open Core Correspondence ScalarExecution CatalogWorldCorrespondence

abbrev Accounts := StorageCorrespondence.Accounts

def StateRel (anchors : List Anchor) (source : StorageSemantics.World) (location : Nat) (store : Core.Store) : Prop :=
  ∃ accounts : Accounts, accounts.map Prod.fst = source ∧ Links anchors accounts ∧
    store.read? location = some (StorageCorrespondence.world accounts)

theorem StateRel.forget {anchors : List Anchor} {source : StorageSemantics.World} {location : Nat} {store : Core.Store}
    (related : StateRel anchors source location store) : StorageCorrespondence.StateRel source location store := by
  obtain ⟨accounts, same, _, read⟩ := related
  exact ⟨accounts, same, read⟩

theorem StateRel.retained {anchors : List Anchor} {source : StorageSemantics.World} {location : Nat}
    {initial final : Core.Store} (related : StateRel anchors source location initial)
    (retained : StoreRetains initial final) : StateRel anchors source location final := by
  obtain ⟨accounts, same, links, read⟩ := related
  exact ⟨accounts, same, links, (retained.read location (List.getElem?_eq_some_iff.mp read).1).trans read⟩

theorem StateRel.read_preserved {anchors : List Anchor} {source : StorageSemantics.World} {location : Nat}
    {initial final : Core.Store} (related : StateRel anchors source location initial)
    (preserved : ∀ value, initial.read? location = some value → final.read? location = some value) :
    StateRel anchors source location final := by
  obtain ⟨accounts, same, links, read⟩ := related
  exact ⟨accounts, same, links, preserved _ read⟩

theorem initial {anchors : List Anchor} {accounts : Accounts} {location : Nat} {store : Core.Store}
    (links : Links anchors accounts) (found : store.read? location = some (StorageCorrespondence.world accounts)) :
    StateRel anchors (accounts.map Prod.fst) location store := ⟨accounts, rfl, links, found⟩

/-- The selected source record and the actual runtime identity belong to the
same account lookup; unrelated existential encoding witnesses are not mixed. -/
theorem selected {anchors : List Anchor} {source : StorageSemantics.World} {location : Nat} {store : Core.Store}
    (related : StateRel anchors source location store) {anchor : Anchor} (member : anchor ∈ anchors) :
    ∃ accounts account, accounts.map Prod.fst = source ∧ Links anchors accounts ∧
      store.read? location = some (StorageCorrespondence.world accounts) ∧
      StorageSemantics.lookup anchor.address source = some account ∧
      StorageCorrespondence.lookup anchor.address accounts = some (account, anchor.identity) ∧
      account.code = some anchor.bytes := by
  obtain ⟨accounts, same, links, read⟩ := related
  obtain ⟨account, found, code⟩ := links anchor member
  refine ⟨accounts, account, same, links, read, ?_, found, code⟩
  rw [← same, ← StorageCorrespondence.lookup_source, found]
  rfl

theorem get_preserves {anchors : List Anchor} {source : StorageSemantics.World} {location : Nat}
    {environment : Core.Environment} {store : Core.Store}
    (related : StateRel anchors source location store) {anchor : Anchor} (member : anchor ∈ anchors)
    {worldReference addressExpr completeExpr : Core.Expr} (complete : Bool)
    (worldEvaluated : Core.Evaluates environment store worldReference (.cellRef AccountState.type location) store)
    (addressEvaluated : Core.Evaluates environment store addressExpr (.word anchor.address) store)
    (completeEvaluated : Core.Evaluates environment store completeExpr (.bool complete) store) :
    ∃ account final, StorageSemantics.lookup anchor.address source = some account ∧ account.code = some anchor.bytes ∧
      Core.Evaluates environment store (AccountState.get (.loadCell worldReference) addressExpr completeExpr)
        (.inRight .word (StorageCorrespondence.record account anchor.identity)) final ∧
      StateRel anchors source location final ∧ StoreRetains store final := by
  obtain ⟨accounts, account, same, links, read, sourceFound, found, code⟩ := selected related member
  have evaluated := StorageCorrespondence.get_evaluates accounts anchor.address complete
    (.loadCell worldEvaluated read) addressEvaluated completeEvaluated
  have retained : StoreRetains store (StorageCorrespondence.getStore accounts anchor.address complete environment store) :=
    StoreRetains.append _ _
  exact ⟨account, _, sourceFound, code,
    by simpa only [StorageCorrespondence.get, found, StorageCorrespondence.getValue] using evaluated,
    related.retained retained, retained⟩

theorem writeStore_world {accounts : Accounts} {location : Nat} {store : Core.Store}
    (read : store.read? location = some (StorageCorrespondence.world accounts))
    (address : Word) (complete : Bool) (key value : Word) (transient : Bool) (environment : Core.Environment) :
    (StorageCorrespondence.writeStore accounts location address complete key value transient environment store).read? location =
      some (StorageCorrespondence.world (writeAccounts accounts address complete key value transient)) := by
  cases obtained : StorageCorrespondence.get accounts address complete with
  | error reason =>
    simp only [StorageCorrespondence.writeStore, writeAccounts, obtained]
    exact StorageCorrespondence.appended_read read _
  | ok pair =>
    rcases pair with ⟨account, identity⟩
    simpa only [writeAccounts, obtained] using StorageCorrespondence.writeStore_written obtained read

/-- Exact encoded accounts, including every retained code identity, are exposed
before the ordinary source-world projection. -/
theorem writeStorage_exact {environment : Core.Environment} {initial store : Core.Store}
    {worldReference addressExpr completeExpr keyExpr valueExpr : Core.Expr}
    (accounts : Accounts) {anchors : List Anchor} (links : Links anchors accounts)
    (location : Nat) (address : Word) (complete : Bool) (key value : Word) (transient : Bool)
    (arguments : Core.Evaluates environment initial
      (bundle [worldReference, addressExpr, completeExpr, keyExpr, valueExpr])
      (StorageCorrespondence.writeArguments location address complete key value) store)
    (read : store.read? location = some (StorageCorrespondence.world accounts)) :
    let next := writeAccounts accounts address complete key value transient
    let final := StorageCorrespondence.writeStore accounts location address complete key value transient environment store
    Core.Evaluates environment initial
      (AccountState.writeStorage worldReference addressExpr completeExpr keyExpr valueExpr transient)
      (StorageCorrespondence.unitResult (StorageSemantics.writeStorage (accounts.map Prod.fst) address complete key value transient)) final ∧
      final.read? location = some (StorageCorrespondence.world next) ∧ Links anchors next ∧
      StorageCorrespondence.Frame location store final :=
  ⟨StorageCorrespondence.writeStorage_evaluates accounts location address complete key value transient arguments read,
    writeStore_world read address complete key value transient environment,
    Links.write links address complete key value transient,
    StorageCorrespondence.writeStore_frame accounts location address complete key value transient environment store⟩

theorem writeStorage_preserves {environment : Core.Environment} {initial store : Core.Store}
    {worldReference addressExpr completeExpr keyExpr valueExpr : Core.Expr}
    {anchors : List Anchor} {source : StorageSemantics.World} {location : Nat}
    (address : Word) (complete : Bool) (key value : Word) (transient : Bool)
    (arguments : Core.Evaluates environment initial
      (bundle [worldReference, addressExpr, completeExpr, keyExpr, valueExpr])
      (StorageCorrespondence.writeArguments location address complete key value) store)
    (related : StateRel anchors source location store) :
    ∃ final, Core.Evaluates environment initial
      (AccountState.writeStorage worldReference addressExpr completeExpr keyExpr valueExpr transient)
      (StorageCorrespondence.unitResult (StorageSemantics.writeStorage source address complete key value transient)) final ∧
      StateRel anchors ((StorageSemantics.writeStorage source address complete key value transient).toOption.getD source) location final ∧
      StorageCorrespondence.Frame location store final := by
  obtain ⟨accounts, rfl, links, read⟩ := related
  obtain ⟨evaluated, found, linked, frame⟩ := writeStorage_exact accounts links location address complete key value transient arguments read
  exact ⟨_, evaluated, ⟨_, writeAccounts_source accounts address complete key value transient, linked, found⟩, frame⟩

theorem readStorage_preserves {environment : Core.Environment} {initial store : Core.Store}
    {worldReference addressExpr completeExpr keyExpr : Core.Expr}
    {anchors : List Anchor} {source : StorageSemantics.World} {location : Nat}
    (address : Word) (complete : Bool) (key : Word) (transient : Bool)
    (arguments : Core.Evaluates environment initial
      (bundle [worldReference, addressExpr, completeExpr, keyExpr])
      (StorageCorrespondence.readArguments location address complete key) store)
    (related : StateRel anchors source location store) :
    ∃ final, Core.Evaluates environment initial
      (AccountState.readStorage worldReference addressExpr completeExpr keyExpr transient)
      (StorageCorrespondence.wordResult (StorageSemantics.readStorage source address complete key transient)) final ∧
      StateRel anchors source location final ∧ StoreRetains store final := by
  obtain ⟨accounts, rfl, links, read⟩ := related
  obtain ⟨suffix, _, extended⟩ := StorageCorrespondence.readStore_extension accounts location address complete key transient environment store
  have retained : StoreRetains store (StorageCorrespondence.readStore accounts location address complete key transient environment store) := by
    rw [extended]
    exact .append _ _
  exact ⟨_, StorageCorrespondence.readStorage_evaluates accounts location address complete key transient arguments read,
    (show StateRel anchors (accounts.map Prod.fst) location store from ⟨accounts, rfl, links, read⟩).retained retained, retained⟩

theorem finalize_preserves {environment : Core.Environment} {initial store : Core.Store}
    {worldReference balancesReference : Core.Expr} {anchors : List Anchor}
    (accounts : Accounts) (links : Links anchors accounts) (survives : Survives anchors accounts)
    (balances : StorageSemantics.Words) (worldLocation balancesLocation : Nat)
    (arguments : Core.Evaluates environment initial (.pair worldReference balancesReference)
      (.pair (.cellRef AccountState.type worldLocation) (.cellRef WordMapping.type balancesLocation)) store)
    (worldRead : store.read? worldLocation = some (StorageCorrespondence.world accounts))
    (balancesRead : store.read? balancesLocation = some (WordMapping.encode balances)) :
    ∃ final, Core.Evaluates environment initial (AccountState.finalize worldReference balancesReference)
      (.inRight .word .unit) final ∧
      final.read? worldLocation = some (StorageCorrespondence.world (StorageCorrespondence.finalize accounts balances).1) ∧
      Links anchors (StorageCorrespondence.finalize accounts balances).1 ∧
      final.read? balancesLocation = some (WordMapping.encode (StorageCorrespondence.finalize accounts balances).2) ∧
      StorageCorrespondence.FinalizeFrame worldLocation balancesLocation store final := by
  obtain ⟨final, evaluated, worldFinal, balancesFinal, frame⟩ :=
    StorageCorrespondence.finalize_evaluates accounts balances worldLocation balancesLocation arguments worldRead balancesRead
  exact ⟨final, evaluated, worldFinal, Links.finalize links survives balances, balancesFinal, frame⟩

end Solcore.Frontend.RustHull.RuntimeLinkedWorldCorrespondence
