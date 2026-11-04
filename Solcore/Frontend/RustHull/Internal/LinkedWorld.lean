import Solcore.Frontend.RustHull.Internal.StorageState
import Solcore.Frontend.RustHull.Internal.RuntimeObjects
import Solcore.Frontend.RustHull.Contract
import Solcore.Frontend.RustHull.Semantics.World
import Solcore.Frontend.RustHull.Internal.EffectBuiltins
import Solcore.Frontend.RustHull.Internal.EffectLayers
import Solcore.Frontend.RustHull.Internal.TerminationLayers
import Solcore.Frontend.RustHull.Internal.AccountLayers

/-!
# Linked world

Exact catalog links and executable identities survive every call-free operation.
-/

section
-- leanmerge: from Solcore.Frontend.RustHull.CatalogWorldCorrespondence
/-! Code anchors retain the executable identities assigned by actual contract
initialization. They are representation evidence; source account semantics
continues to use addresses, bytecode, and ordinary storage alone. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.CatalogWorldCorrespondence
open Core StorageCorrespondence

structure Anchor where
  address : Word
  bytes : List UInt8
  identity : Nat

def Anchor.Holds (anchor : Anchor) (accounts : Accounts) : Prop :=
  ∃ account, lookup anchor.address accounts = some (account, anchor.identity) ∧ account.code = some anchor.bytes

def Links (anchors : List Anchor) (accounts : Accounts) : Prop :=
  ∀ anchor ∈ anchors, anchor.Holds accounts

theorem lookup_member {address : Word} {accounts : Accounts} {account : AccountState.Account} {identity : Nat}
    (found : lookup address accounts = some (account, identity)) : (account, identity) ∈ accounts := by
  induction accounts with
  | nil => cases found
  | cons entry rest ih =>
    rcases entry with ⟨head, headIdentity⟩
    simp only [lookup] at found
    split at found
    · cases Option.some.inj found
      exact .head _
    · exact .tail _ (ih found)

theorem lookup_address {address : Word} {accounts : Accounts} {account : AccountState.Account} {identity : Nat}
    (found : lookup address accounts = some (account, identity)) : account.address = address := by
  induction accounts with
  | nil => cases found
  | cons entry rest ih =>
    rcases entry with ⟨head, headIdentity⟩
    simp only [lookup] at found
    split at found
    · rename_i same
      cases Option.some.inj found
      exact (beq_iff_eq.mp same).symm
    · exact ih found

theorem lookup_of_source {address : Word} {accounts : Accounts} {account : AccountState.Account}
    (found : StorageSemantics.lookup address (accounts.map Prod.fst) = some account) :
    ∃ identity, lookup address accounts = some (account, identity) := by
  have source := lookup_source accounts address
  rw [found] at source
  cases actual : lookup address accounts with
  | none => simp only [actual, Option.map_none] at source; contradiction
  | some pair =>
    rcases pair with ⟨selected, identity⟩
    simp only [actual, Option.map_some, Option.some.injEq] at source
    subst selected
    exact ⟨identity, rfl⟩

theorem lookup_put_same (accounts : Accounts) (address : Word) (account : AccountState.Account) (identity : Nat) :
    lookup address (put address account identity accounts) = some ({account with address := address}, identity) := by
  induction accounts with
  | nil => simp [put, lookup]
  | cons entry rest ih =>
    rcases entry with ⟨head, headIdentity⟩
    simp only [put]
    split <;> simp_all [lookup]

theorem lookup_put_other {address target : Word} (different : address ≠ target)
    (accounts : Accounts) (account : AccountState.Account) (identity : Nat) :
    lookup target (put address account identity accounts) = lookup target accounts := by
  induction accounts with
  | nil => simp [put, lookup, Ne.symm different]
  | cons entry rest ih =>
    rcases entry with ⟨head, headIdentity⟩
    by_cases same : address = head.address
    · subst address
      simp [put, lookup, Ne.symm different]
    · simp only [put, show (address == head.address) = false from beq_eq_false_iff_ne.mpr same, Bool.false_eq_true, ↓reduceIte, lookup]
      split <;> simp_all

def writeAccounts (accounts : Accounts) (address : Word) (complete : Bool) (key value : Word) (transient : Bool) : Accounts :=
  match get accounts address complete with
  | .error _ => accounts
  | .ok (account, identity) => put address (StorageSemantics.update account transient key value) identity accounts

theorem Anchor.write {anchor : Anchor} {accounts : Accounts} (linked : anchor.Holds accounts)
    (address : Word) (complete : Bool) (key value : Word) (transient : Bool) :
    anchor.Holds (writeAccounts accounts address complete key value transient) := by
  obtain ⟨selected, selectedAt, code⟩ := linked
  unfold writeAccounts
  cases obtained : get accounts address complete with
  | error reason => exact ⟨selected, selectedAt, code⟩
  | ok entry =>
    rcases entry with ⟨account, identity⟩
    by_cases same : address = anchor.address
    · subst address
      have original : get accounts anchor.address complete = .ok (selected, anchor.identity) := by
        simp only [StorageCorrespondence.get, selectedAt]
      have equal := Except.ok.inj (obtained.symm.trans original)
      cases equal
      refine ⟨_, lookup_put_same accounts anchor.address _ anchor.identity, ?_⟩
      cases transient <;> exact code
    · exact ⟨selected, (lookup_put_other same accounts _ identity).trans selectedAt, code⟩

theorem Links.write {anchors : List Anchor} {accounts : Accounts} (linked : Links anchors accounts)
    (address : Word) (complete : Bool) (key value : Word) (transient : Bool) :
    Links anchors (writeAccounts accounts address complete key value transient) :=
  fun anchor member => Anchor.write (linked anchor member) address complete key value transient

/-- Non-root records retain the byte-oriented identity chosen by the real
initializer, including its first-match catalog policy and address normalization. -/
theorem initialWorld_identity (object : Contract.CompiledObject) (context : Contract.Context)
    {account : AccountState.Account} {identity : Nat}
    (member : (account, identity) ∈ canonical (object.initialWorld context))
    (notRoot : account.address ≠ Contract.normalizeAddress context.address) :
    identity = Contract.codeIdentity object.codeImages account.code := by
  obtain ⟨⟨original, actual⟩, member, equal⟩ := List.mem_map.mp member
  cases equal
  unfold Contract.CompiledObject.initialWorld at member
  obtain ⟨source, _, equal⟩ := List.mem_map.mp member
  cases equal
  have separate : original.address ≠ context.address := by
    intro same
    exact notRoot (congrArg Contract.normalizeAddress same)
  simp only [show (original.address == context.address) = false from beq_eq_false_iff_ne.mpr separate,
    Bool.false_eq_true, ↓reduceIte]

theorem initialWorld_lookup (object : Contract.CompiledObject) (context : Contract.Context)
    {address : Word} {account : AccountState.Account}
    (selected : StorageSemantics.lookup address ((canonical (object.initialWorld context)).map Prod.fst) = some account)
    (notRoot : address ≠ Contract.normalizeAddress context.address) :
    lookup address (canonical (object.initialWorld context)) =
      some (account, Contract.codeIdentity object.codeImages account.code) := by
  obtain ⟨identity, found⟩ := lookup_of_source selected
  have same := initialWorld_identity object context (lookup_member found) (by simpa only [lookup_address found] using notRoot)
  simpa only [same] using found

theorem single_catalog_identity (image : Option (List UInt8)) (bytes : List UInt8)
    (different : image ≠ some bytes) : Contract.codeIdentity [image, some bytes] (some bytes) = 2 := by
  simp [Contract.codeIdentity, List.zipIdx, different]

theorem initialWorld_single_catalog (object : Contract.CompiledObject) (context : Contract.Context)
    (definition : AccountRuntime.CodeDefinition) {image : Option (List UInt8)} {address : Word}
    (images : object.codeImages = [image, some definition.bytes])
    (different : image ≠ some definition.bytes)
    {account : AccountState.Account}
    (selected : StorageSemantics.lookup address ((canonical (object.initialWorld context)).map Prod.fst) = some account)
    (notRoot : address ≠ Contract.normalizeAddress context.address)
    (code : account.code = some definition.bytes) :
    (Anchor.mk address definition.bytes 2).Holds (canonical (object.initialWorld context)) := by
  refine ⟨account, ?_, code⟩
  have found := initialWorld_lookup object context selected notRoot
  simpa only [images, code, single_catalog_identity image definition.bytes different] using found

theorem writeAccounts_source (accounts : Accounts) (address : Word) (complete : Bool)
    (key value : Word) (transient : Bool) :
    (writeAccounts accounts address complete key value transient).map Prod.fst =
      (StorageSemantics.writeStorage (accounts.map Prod.fst) address complete key value transient).toOption.getD
        (accounts.map Prod.fst) := by
  rw [write_source]
  cases obtained : StorageCorrespondence.get accounts address complete with
  | error reason => simp only [writeAccounts, obtained, Except.toOption, Option.getD]
  | ok pair => cases pair; simp only [writeAccounts, obtained, Except.toOption, Option.getD]

theorem lookup_finalize {address : Word} {accounts : Accounts} {account : AccountState.Account} {identity : Nat}
    (found : lookup address accounts = some (account, identity))
    (survives : (account.created && account.destroyed) = false) (balances : StorageSemantics.Words) :
    lookup address (StorageCorrespondence.finalize accounts balances).1 =
      some (StorageSemantics.clearTransaction account, identity) := by
  induction accounts generalizing balances with
  | nil => cases found
  | cons entry rest ih =>
    rcases entry with ⟨head, headIdentity⟩
    by_cases same : address == head.address
    · simp only [lookup, same, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at found
      rcases found with ⟨rfl, rfl⟩
      simp only [StorageCorrespondence.finalize, survives, Bool.false_eq_true, ↓reduceIte,
        lookup, StorageSemantics.clearTransaction, same]
    · have different : (address == head.address) = false := Bool.eq_false_iff.mpr same
      simp only [lookup, different, Bool.false_eq_true, ↓reduceIte] at found
      simp only [StorageCorrespondence.finalize]
      split
      · exact ih found _
      · simpa only [lookup, StorageSemantics.clearTransaction, different, Bool.false_eq_true, ↓reduceIte] using ih found balances

def Survives (anchors : List Anchor) (accounts : Accounts) : Prop :=
  ∀ anchor ∈ anchors, ∀ account, lookup anchor.address accounts = some (account, anchor.identity) →
    (account.created && account.destroyed) = false

theorem Links.finalize {anchors : List Anchor} {accounts : Accounts} (linked : Links anchors accounts)
    (survives : Survives anchors accounts) (balances : StorageSemantics.Words) :
    Links anchors (StorageCorrespondence.finalize accounts balances).1 := by
  intro anchor member
  obtain ⟨account, found, code⟩ := linked anchor member
  exact ⟨StorageSemantics.clearTransaction account, lookup_finalize found (survives anchor member account found) balances, code⟩

theorem compileObject_images {program : Program} {path : List String} {fuel : Nat}
    {image : Option (List UInt8)} {catalog : List AccountRuntime.CodeDefinition} {object : Contract.CompiledObject}
    (accepted : Contract.compileObject program path fuel image catalog = .ok object) :
    object.codeImages = image :: catalog.map (some ∘ AccountRuntime.CodeDefinition.bytes) := by
  unfold Contract.compileObject at accepted
  obtain ⟨expression, _, returned⟩ := lower_bind_eq_ok.mp accepted
  cases Except.ok.inj returned
  rfl

theorem compiled_single_catalog_anchor {program : Program} {path : List String} {fuel : Nat}
    {image : Option (List UInt8)} {definition : AccountRuntime.CodeDefinition} {object : Contract.CompiledObject}
    (accepted : Contract.compileObject program path fuel image [definition] = .ok object)
    (context : Contract.Context) {address : Word} {account : AccountState.Account}
    (different : image ≠ some definition.bytes)
    (selected : StorageSemantics.lookup address ((canonical (object.initialWorld context)).map Prod.fst) = some account)
    (notRoot : address ≠ Contract.normalizeAddress context.address)
    (code : account.code = some definition.bytes) :
    (Anchor.mk address definition.bytes 2).Holds (canonical (object.initialWorld context)) :=
  initialWorld_single_catalog object context definition (compileObject_images accepted) different selected notRoot code

end Solcore.Frontend.RustHull.CatalogWorldCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.AccountLifecycleWorldCorrespondence
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
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeLinkedWorldCorrespondence
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
end

section
-- leanmerge: from Solcore.Frontend.RustHull.LinkedStorageBuiltinCorrespondence
/-! Storage lowering preserves the exact catalog identity attached to each
selected account, including writes and static-write rejection. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.LinkedStorageBuiltinCorrespondence
open Core Correspondence PureCallCorrespondence EffectBuiltinCorrespondence StorageBuiltinCorrespondence

private theorem inner_arity (operation : Operation) {scope : Scope}
    {arguments : List Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope operation.name arguments = .ok lowered) :
    arguments.length = operation.arity := by
  cases operation with
  | load transient | store transient =>
    cases transient <;>
      rcases arguments with _ | ⟨first, _ | ⟨second, _ | ⟨third, rest⟩⟩⟩
    all_goals first
      | rfl
      | change Except.error _ = Except.ok lowered at compiled
        cases compiled

private theorem load_components (transient : Bool) {scope : Scope} {key : Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope (Operation.load transient).name [key] = .ok lowered) :
    ∃ world address complete,
      Effects.reference scope "world" AccountState.type = .ok world ∧
      Effects.reference scope "address" .word = .ok address ∧
      Effects.reference scope "worldComplete" .bool = .ok complete ∧
      lowered = ⟨.word, AccountState.readStorage world (.loadCell address) (.loadCell complete) key transient⟩ := by
  have components : (do
      let raw ← (do
        let world ← Effects.reference scope "world" AccountState.type
        let address ← Effects.reference scope "address" .word
        let complete ← Effects.reference scope "worldComplete" .bool
        pure (Lowered.mk .word (AccountState.readStorage world (.loadCell address) (.loadCell complete) key transient)) : LowerM Lowered)
      pure raw) = .ok lowered := by
    cases transient <;> exact compiled
  obtain ⟨world, worldCompiled, components⟩ := lower_bind_eq_ok.mp components
  obtain ⟨address, addressCompiled, components⟩ := lower_bind_eq_ok.mp components
  obtain ⟨complete, completeCompiled, returned⟩ := lower_bind_eq_ok.mp components
  exact ⟨world, address, complete, worldCompiled, addressCompiled, completeCompiled, (Except.ok.inj returned).symm⟩

private theorem store_components (transient : Bool) {scope : Scope} {key value : Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope (Operation.store transient).name [key, value] = .ok lowered) :
    ∃ static stop world address complete,
      Effects.reference scope "isStatic" .bool = .ok static ∧
      Effects.terminate scope 3 (.word Word.zero) (.word Word.zero) = .ok stop ∧
      Effects.reference scope "world" AccountState.type = .ok world ∧
      Effects.reference scope "address" .word = .ok address ∧
      Effects.reference scope "worldComplete" .bool = .ok complete ∧
      lowered = ⟨.unit, .ifE (.loadCell static) stop
        (AccountState.writeStorage world (.loadCell address) (.loadCell complete) key value transient)⟩ := by
  have components : (do
      let raw ← (do
        let static ← Effects.reference scope "isStatic" .bool
        let stop ← Effects.terminate scope 3 (.word Word.zero) (.word Word.zero)
        let world ← Effects.reference scope "world" AccountState.type
        let address ← Effects.reference scope "address" .word
        let complete ← Effects.reference scope "worldComplete" .bool
        pure (Lowered.mk .unit (.ifE (.loadCell static) stop
          (AccountState.writeStorage world (.loadCell address) (.loadCell complete) key value transient))) : LowerM Lowered)
      pure raw) = .ok lowered := by
    cases transient <;> exact compiled
  obtain ⟨static, staticCompiled, components⟩ := lower_bind_eq_ok.mp components
  obtain ⟨stop, stopCompiled, components⟩ := lower_bind_eq_ok.mp components
  obtain ⟨world, worldCompiled, components⟩ := lower_bind_eq_ok.mp components
  obtain ⟨address, addressCompiled, components⟩ := lower_bind_eq_ok.mp components
  obtain ⟨complete, completeCompiled, returned⟩ := lower_bind_eq_ok.mp components
  exact ⟨static, stop, world, address, complete, staticCompiled, stopCompiled, worldCompiled,
    addressCompiled, completeCompiled, (Except.ok.inj returned).symm⟩

theorem load_preserves (transient : Bool)
    {scope : Scope} {keyExpr : Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope (Operation.load transient).name [keyExpr] = .ok lowered)
    {slots : List EffectSlot} {mapping : Renaming} {environment : Environment} {store : Store}
    {locations : Locations} {state : StorageSemantics.State}
    (runtime : EffectEnvironmentRel slots scope mapping environment)
    (worldMember : ⟨"world", AccountState.type, locations.world⟩ ∈ slots)
    (addressMember : ⟨"address", .word, locations.address⟩ ∈ slots)
    (completeMember : ⟨"worldComplete", .bool, locations.complete⟩ ∈ slots)
    (stateRelated : StorageBuiltinCorrespondence.StateRel locations state store)
    {anchors : List CatalogWorldCorrespondence.Anchor}
    (linked : RuntimeLinkedWorldCorrespondence.StateRel anchors state.world locations.world store)
    (key : Word) (keyEvaluated : Evaluates environment store (keyExpr.rename mapping) (.word key) store) :
    ∃ target final,
      ResultRel lowered.type (StorageSemantics.load state key transient).1 target ∧
      Evaluates environment store (lowered.expression.rename mapping) target final ∧
      RuntimeLinkedWorldCorrespondence.StateRel anchors (StorageSemantics.load state key transient).2.world locations.world final := by
  obtain ⟨world, address, complete, worldCompiled, addressCompiled, completeCompiled, rfl⟩ := load_components transient compiled
  obtain ⟨final, evaluated, worldRelated, frame⟩ := RuntimeLinkedWorldCorrespondence.readStorage_preserves state.address state.complete key transient
    (.pair (reference_evaluates runtime worldMember worldCompiled store)
      (.pair (.loadCell (reference_evaluates runtime addressMember addressCompiled store) stateRelated.address)
        (.pair (.loadCell (reference_evaluates runtime completeMember completeCompiled store) stateRelated.complete) keyEvaluated)))
    linked
  refine ⟨_, final, load_result state key transient, ?_, ?_⟩
  · rw [readStorage_rename]
    exact evaluated
  · rw [load_state]
    exact worldRelated

theorem store_preserves (transient : Bool)
    {scope : Scope} {keyExpr valueExpr : Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope (Operation.store transient).name [keyExpr, valueExpr] = .ok lowered)
    {slots : List EffectSlot} {mapping : Renaming} {environment : Environment} {store : Store}
    {locations : Locations} {state : StorageSemantics.State}
    (runtime : EffectEnvironmentRel slots scope mapping environment)
    (worldMember : ⟨"world", AccountState.type, locations.world⟩ ∈ slots)
    (addressMember : ⟨"address", .word, locations.address⟩ ∈ slots)
    (completeMember : ⟨"worldComplete", .bool, locations.complete⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, locations.isStatic⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, locations.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, locations.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, locations.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, locations.returnSize⟩ ∈ slots)
    (stateRelated : StorageBuiltinCorrespondence.StateRel locations state store)
    {anchors : List CatalogWorldCorrespondence.Anchor}
    (linked : RuntimeLinkedWorldCorrespondence.StateRel anchors state.world locations.world store)
    (key value : Word)
    (keyEvaluated : Evaluates environment store (keyExpr.rename mapping) (.word key) store)
    (valueEvaluated : Evaluates environment store (valueExpr.rename mapping) (.word value) store) :
    ∃ target final,
      ResultRel lowered.type (StorageSemantics.store state key value transient).1 target ∧
      Evaluates environment store (lowered.expression.rename mapping) target final ∧
      RuntimeLinkedWorldCorrespondence.StateRel anchors (StorageSemantics.store state key value transient).2.world locations.world final := by
  obtain ⟨static, stop, world, address, complete, staticCompiled, stopCompiled, worldCompiled,
    addressCompiled, completeCompiled, rfl⟩ := store_components transient compiled
  have staticRead := stateRelated.isStatic
  cases permitted : state.isStatic
  · rw [permitted] at staticRead
    obtain ⟨final, evaluated, worldRelated, frame⟩ := RuntimeLinkedWorldCorrespondence.writeStorage_preserves state.address state.complete key value transient
      (.pair (reference_evaluates runtime worldMember worldCompiled store)
        (.pair (.loadCell (reference_evaluates runtime addressMember addressCompiled store) stateRelated.address)
          (.pair (.loadCell (reference_evaluates runtime completeMember completeCompiled store) stateRelated.complete)
            (.pair keyEvaluated valueEvaluated)))) linked
    refine ⟨_, final, store_result state key value transient permitted, ?_, ?_⟩
    · apply Evaluates.ifFalse (.loadCell (reference_evaluates runtime staticMember staticCompiled store) staticRead)
      rw [writeStorage_rename]
      exact evaluated
    · rw [store_state state key value transient permitted]
      exact worldRelated
  · rw [permitted] at staticRead
    refine ⟨.inLeft .unit (.word Word.maximum), haltStore locations store, ?_, ?_, ?_⟩
    · simpa only [StorageSemantics.store, permitted, ↓reduceIte] using (ResultRel.language (type := .unit) Word.maximum)
    · apply Evaluates.ifTrue (.loadCell (reference_evaluates runtime staticMember staticCompiled store) staticRead)
      exact stop_evaluates stopCompiled runtime memorySizeMember exitMember offsetMember sizeMember stateRelated
    · simp only [StorageSemantics.store, permitted, ↓reduceIte]
      have distinct := stateRelated.distinct
      simp [Locations.all] at distinct
      exact linked.read_preserved (fun _ found => haltStore_other
        (by intro same; simp_all) (by intro same; simp_all) (by intro same; simp_all) found)


/-- Successful compilation and initialized runtime cells determine each
storage observation, including static rejection and all resulting writes. -/
theorem preserves (operation : Operation)
    {scope : Scope} {expected : Core.Ty} {arguments : List Lowered} {lowered : Lowered}
    (compiled : lowerBuiltin scope operation.name expected arguments = .ok lowered)
    {sources : List Semantics.Value} {targets : List Core.Value}
    (related : ArgumentsRel arguments sources targets)
    {slots : List EffectSlot} {mapping : Renaming} {environment : Environment}
    {initial store : Store} {locations : Locations} {state : StorageSemantics.State}
    (runtime : EffectEnvironmentRel slots scope mapping environment)
    (worldMember : ⟨"world", AccountState.type, locations.world⟩ ∈ slots)
    (addressMember : ⟨"address", .word, locations.address⟩ ∈ slots)
    (completeMember : ⟨"worldComplete", .bool, locations.complete⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, locations.isStatic⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, locations.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, locations.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, locations.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, locations.returnSize⟩ ∈ slots)
    (stateRelated : StorageBuiltinCorrespondence.StateRel locations state store)
    {anchors : List CatalogWorldCorrespondence.Anchor}
    (linked : RuntimeLinkedWorldCorrespondence.StateRel anchors state.world locations.world store)
    (packed : Evaluates environment initial ((packArguments arguments).expression.rename mapping)
      (.inRight .word (ScalarExecution.bundleValues targets)) store)
    (sourceType : Ty) :
    ∃ result finalState target finalStore,
      StorageSemantics.builtin operation.name sourceType sources state = some (result, finalState) ∧
      ResultRel lowered.type result target ∧
      Evaluates environment initial (lowered.expression.rename mapping) target finalStore ∧
      RuntimeLinkedWorldCorrespondence.StateRel anchors finalState.world locations.world finalStore := by
  have supported : Effects.supports operation.name = true := by
    cases operation with | load transient | store transient => cases transient <;> rfl
  obtain ⟨words, raw, rawCompiled, typed, loweredEqual⟩ := outer_components supported compiled
  have arity : arguments.length = operation.arity := by
    simpa only [List.length_map, List.length_range] using inner_arity operation rawCompiled
  cases operation with
  | load transient =>
      obtain ⟨keyExpr, key, rfl, rfl, rfl⟩ := one_word related words arity
      obtain ⟨target, final, resultRelated, evaluated, finalRelated⟩ := load_preserves transient rawCompiled
        (runtime.temporary .word (.word key)) worldMember addressMember completeMember stateRelated linked key (.var rfl)
      cases typed
      cases loweredEqual
      refine ⟨(StorageSemantics.load state key transient).1, (StorageSemantics.load state key transient).2,
        target, final, ?_, resultRelated, ?_, finalRelated⟩
      · cases transient <;> rfl
      · exact LanguageResult.bind_success _ packed evaluated
  | store transient =>
      obtain ⟨keyExpr, valueExpr, key, value, rfl, rfl, rfl⟩ := two_words related words arity
      obtain ⟨target, final, resultRelated, evaluated, finalRelated⟩ := store_preserves transient rawCompiled
        (runtime.temporary (.product .word .word) (.pair (.word key) (.word value)))
        worldMember addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
        stateRelated linked key value (.first (.var rfl)) (.second (.var rfl))
      cases typed
      cases loweredEqual
      refine ⟨(StorageSemantics.store state key value transient).1, (StorageSemantics.store state key value transient).2,
        target, final, ?_, resultRelated, ?_, finalRelated⟩
      · cases transient <;> rfl
      · exact LanguageResult.bind_success _ packed evaluated

end Solcore.Frontend.RustHull.LinkedStorageBuiltinCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.LinkedBuiltinWorldSupport
/-! A separate, deterministic execution witness carries exact catalog links
through a builtin. It can be combined with ordinary effect preservation without
changing the existing source or runtime models. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.LinkedBuiltinWorldCorrespondence
open Correspondence ScalarExecution PureCallCorrespondence

abbrev Anchors := List CatalogWorldCorrespondence.Anchor

def ExternalWorldPreservation {σ : Type} (supported : String → Prop)
    (model : StateModel σ) (slots : List EffectSlot) (effects : Semantics.ExternalSemantics σ)
    (anchors : Anchors) (location : Nat) (sourceWorld : σ → StorageSemantics.World) : Prop :=
  ∀ {functions name type sources initial final result}, supported name →
    functions.find? (·.name == name) = none →
    Semantics.EvalCall functions effects name type sources initial result final →
    ∀ {typeFuel expected}, lowerType typeFuel type = .ok expected →
    ∀ {scope arguments lowered}, lowerBuiltin scope name expected arguments = .ok lowered →
    ∀ {world mapping environment initialStore argumentStore targets codes locations captured},
      ArgumentsRel arguments sources targets →
      Core.Evaluates environment initialStore ((packArguments arguments).expression.rename mapping)
        (.inRight .word (bundleValues targets)) argumentStore →
      EffectEnvironmentRel slots scope mapping environment →
      StateRel model world initial argumentStore →
      InstalledGlobals codes locations captured argumentStore →
      RuntimeLinkedWorldCorrespondence.StateRel anchors (sourceWorld initial.external) location argumentStore →
      ∃ target finalStore, Core.Evaluates environment initialStore (lowered.expression.rename mapping) target finalStore ∧
        RuntimeLinkedWorldCorrespondence.StateRel anchors (sourceWorld final.external) location finalStore

theorem memory_frame {layout : RuntimeEffectsCorrespondence.Layout}
    {anchors : Anchors} {source : StorageSemantics.World} {initial final : Core.Store}
    (linked : RuntimeLinkedWorldCorrespondence.StateRel anchors source layout.storage.world initial)
    (frame : MemoryCorrespondence.Frame layout.memory layout.storage.memorySize initial final) :
    RuntimeLinkedWorldCorrespondence.StateRel anchors source layout.storage.world final := by
  have distinct := layout.distinct
  simp [StorageBuiltinCorrespondence.Locations.all] at distinct
  exact linked.read_preserved (fun _ found => frame.read _ _
    (by intro same; simp_all) (by intro same; simp_all) found)

end Solcore.Frontend.RustHull.LinkedBuiltinWorldCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.LinkedRuntimeWorldCorrespondence
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.LinkedRuntimeWorldCorrespondence
open Correspondence DerivationCorrespondence ScalarExecution RuntimeEffectsCorrespondence LinkedBuiltinWorldCorrespondence

private theorem memory_unsupported (operation : StorageBuiltinCorrespondence.Operation)
    (type : Ty) (arguments : List Semantics.Value) (state : MemorySemantics.State) :
    MemorySemantics.builtin operation.name type arguments state = none := by
  cases operation with | load transient | store transient => cases transient <;> rfl

theorem external_preserves (layout : Layout) (baseline : Nat → Option Core.Value)
    (slots : List EffectSlot)
    (memoryMember : ⟨"memory", Core.WordMapping.type, layout.memory⟩ ∈ slots)
    (worldMember : ⟨"world", AccountState.type, layout.storage.world⟩ ∈ slots)
    (addressMember : ⟨"address", .word, layout.storage.address⟩ ∈ slots)
    (completeMember : ⟨"worldComplete", .bool, layout.storage.complete⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, layout.storage.isStatic⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, layout.storage.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, layout.storage.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, layout.storage.returnSize⟩ ∈ slots) :
    ∀ anchors, ExternalWorldPreservation supported (model layout baseline) slots RuntimeEffectsSemantics.effects
      anchors layout.storage.world (fun state => state.storage.world) := by
  intro anchors
  intro functions name type sources initial final result available notFunction called
  rcases available with memory | storage
  · obtain ⟨operation, rfl⟩ := memory
    cases called with
    | function selected called => rw [notFunction] at selected; contradiction
    | primitive absent computed =>
        cases operation <;> simp [MemoryBuiltinCorrespondence.Operation.name, Semantics.primitive?] at computed
    | external absent notPrimitive computed =>
        intro typeFuel expected typeCompiled scope arguments lowered compiled world mapping environment initialStore argumentStore targets codes locations captured related packed runtime state installed linked
        obtain ⟨computedResult, computedState, target, finalStore, meaning, resultRelated, evaluated, memoryFinal, frame⟩ :=
          MemoryBuiltinCorrespondence.preserves operation compiled related runtime memoryMember memorySizeMember
            (memory_related state) packed type
        have combined : RuntimeEffectsSemantics.builtin operation.name type sources initial.external =
            some (computedResult, {initial.external with memory := computedState}) := by
          simp only [RuntimeEffectsSemantics.builtin, meaning]
        have same := Option.some.inj (computed.symm.trans combined)
        cases same
        exact ⟨target, finalStore, evaluated, memory_frame linked frame⟩
  · obtain ⟨operation, rfl⟩ := storage
    cases called with
    | function selected called => rw [notFunction] at selected; contradiction
    | primitive absent computed =>
        cases operation with | load transient | store transient =>
          cases transient <;> simp [StorageBuiltinCorrespondence.Operation.name, Semantics.primitive?] at computed
    | external absent notPrimitive computed =>
        intro typeFuel expected typeCompiled scope arguments lowered compiled world mapping environment initialStore argumentStore targets codes locations captured related packed runtime state installed linked
        obtain ⟨computedResult, computedState, target, finalStore, meaning, resultRelated, evaluated, linkedFinal⟩ :=
          LinkedStorageBuiltinCorrespondence.preserves operation compiled related runtime worldMember addressMember
            completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
            (storage_related state) linked packed type
        have combined : RuntimeEffectsSemantics.builtin operation.name type sources initial.external =
            some (computedResult, {initial.external with storage := computedState}) := by
          simp only [RuntimeEffectsSemantics.builtin, memory_unsupported, meaning, Option.map_some]
        have same := Option.some.inj (computed.symm.trans combined)
        cases same
        exact ⟨target, finalStore, evaluated, linkedFinal⟩

end Solcore.Frontend.RustHull.LinkedRuntimeWorldCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.LinkedEnvironmentWorldCorrespondence
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Solcore.Frontend.RustHull.LinkedEnvironmentWorldCorrespondence
open Correspondence DerivationCorrespondence ScalarExecution RuntimeEnvironmentEffectsCorrespondence LinkedBuiltinWorldCorrespondence

private theorem environment_unsupported {name : String} (available : RuntimeEffectsCorrespondence.supported name)
    (type : Ty) (arguments : List Semantics.Value) (state : EnvironmentSemantics.State) :
    EnvironmentSemantics.builtin name type arguments state = none := by
  rcases available with ⟨operation, rfl⟩ | ⟨operation, rfl⟩
  · cases operation <;> rfl
  · cases operation with | load transient | store transient => cases transient <;> rfl

private theorem runtime_unsupported (operation : EnvironmentSemantics.Operation)
    (type : Ty) (arguments : List Semantics.Value) (state : RuntimeEffectsSemantics.State) :
    RuntimeEffectsSemantics.builtin operation.name type arguments state = none := by
  cases operation <;> (try first | cases ‹EnvironmentSemantics.Direct› | cases ‹EnvironmentSemantics.AmbientWord›)
  all_goals rfl

theorem external_preserves (layout : Layout) (baseline : Nat → Option Core.Value)
    (slots : List EffectSlot) (passive : Passive layout slots)
    (memoryMember : ⟨"memory", Core.WordMapping.type, layout.memory⟩ ∈ slots)
    (worldMember : ⟨"world", AccountState.type, layout.storage.world⟩ ∈ slots)
    (addressMember : ⟨"address", .word, layout.storage.address⟩ ∈ slots)
    (completeMember : ⟨"worldComplete", .bool, layout.storage.complete⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, layout.storage.isStatic⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, layout.storage.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, layout.storage.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, layout.storage.returnSize⟩ ∈ slots) :
    ∀ anchors, ExternalWorldPreservation (supported slots) (model layout baseline slots) slots RuntimeEnvironmentEffectsSemantics.effects
      anchors layout.storage.world (fun state => state.runtime.storage.world) := by
  intro anchors
  intro functions name type sources initial final result enabled notFunction called
  rcases enabled with runtimeEnabled | ⟨operation, rfl, available⟩
  · cases called with
    | function selected called => rw [notFunction] at selected; contradiction
    | primitive absent computed =>
        rcases runtimeEnabled with ⟨operation, rfl⟩ | ⟨operation, rfl⟩
        · cases operation <;> simp [MemoryBuiltinCorrespondence.Operation.name, Semantics.primitive?] at computed
        · cases operation with | load transient | store transient =>
            cases transient <;> simp [StorageBuiltinCorrespondence.Operation.name, Semantics.primitive?] at computed
    | external absent notPrimitive computed =>
        change RuntimeEnvironmentEffectsSemantics.builtin _ _ _ _ = some _ at computed
        cases runtimeComputed : RuntimeEffectsSemantics.builtin name type sources initial.external.runtime with
        | none =>
            simp [RuntimeEnvironmentEffectsSemantics.builtin, runtimeComputed,
              environment_unsupported runtimeEnabled] at computed
        | some output =>
            rcases output with ⟨runtimeResult, runtimeState⟩
            simp only [RuntimeEnvironmentEffectsSemantics.builtin, runtimeComputed, Option.some.injEq,
              Prod.mk.injEq] at computed
            rcases computed with ⟨rfl, rfl⟩
            intro typeFuel expected typeCompiled scope arguments lowered compiled world mapping environment initialStore argumentStore targets codes locations captured related packed runtime state installed linked
            have call : Semantics.EvalCall functions RuntimeEffectsSemantics.effects name type sources
                (sourceRuntime initial) runtimeResult {sourceRuntime initial with external := runtimeState} :=
              .external absent notPrimitive runtimeComputed
            obtain ⟨target, finalStore, evaluated, linkedFinal⟩ :=
              LinkedRuntimeWorldCorrespondence.external_preserves layout baseline slots memoryMember worldMember
                addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember anchors
                runtimeEnabled notFunction call typeCompiled compiled related packed runtime (runtime_related state) installed linked
            exact ⟨target, finalStore, evaluated, linkedFinal⟩
  · cases called with
    | function selected called => rw [notFunction] at selected; contradiction
    | primitive absent computed =>
        cases operation <;> (try first | cases ‹EnvironmentSemantics.Direct› | cases ‹EnvironmentSemantics.AmbientWord›)
        all_goals simp [EnvironmentSemantics.Operation.name, EnvironmentSemantics.Direct.name,
          EnvironmentSemantics.AmbientWord.name, Semantics.primitive?] at computed
    | external absent notPrimitive computed =>
        intro typeFuel expected typeCompiled scope arguments lowered compiled world mapping environment initialStore argumentStore targets codes locations captured related packed runtime state installed linked
        obtain ⟨computedResult, target, finalStore, meaning, resultRelated, evaluated, observations, retained⟩ :=
          EnvironmentBuiltinCorrespondence.preserves operation compiled related runtime available
            (observations_related state) packed type
        have combined : RuntimeEnvironmentEffectsSemantics.builtin operation.name type sources initial.external =
            some (computedResult, initial.external) := by
          simp only [RuntimeEnvironmentEffectsSemantics.builtin, runtime_unsupported, meaning, Option.map_some]
        have same := Option.some.inj (computed.symm.trans combined)
        cases same
        exact ⟨target, finalStore, evaluated, linked.retained retained⟩

end Solcore.Frontend.RustHull.LinkedEnvironmentWorldCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.LinkedLogWorldCorrespondence
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Solcore.Frontend.RustHull.LinkedLogWorldCorrespondence
open Correspondence DerivationCorrespondence ScalarExecution RuntimeLogEffectsCorrespondence LinkedBuiltinWorldCorrespondence

private theorem primitive_none {slots : List EffectSlot} {name : String}
    (enabled : supported slots name) (type : Ty) (arguments : List Semantics.Value) :
    Semantics.primitive? name type arguments = none := by
  rcases enabled with ((memory | storage) | environment) | ⟨operation, rfl⟩
  · obtain ⟨operation, rfl⟩ := memory
    cases operation <;> rfl
  · obtain ⟨operation, rfl⟩ := storage
    cases operation with | load transient | store transient => cases transient <;> rfl
  · obtain ⟨operation, rfl, _⟩ := environment
    cases operation <;> (try first | cases ‹EnvironmentSemantics.Direct› | cases ‹EnvironmentSemantics.AmbientWord›)
    all_goals rfl
  · cases operation <;> rfl

private theorem runtime_unsupported (operation : LogsSemantics.Operation)
    (type : Ty) (arguments : List Semantics.Value) (state : RuntimeEnvironmentEffectsSemantics.State) :
    RuntimeEnvironmentEffectsSemantics.builtin operation.name type arguments state = none := by
  cases operation <;> rfl

theorem external_preserves (layout : Layout) (baseline : Nat → Option Core.Value)
    (slots : List EffectSlot) (passive : Passive layout slots)
    (memoryMember : ⟨"memory", Core.WordMapping.type, layout.memory⟩ ∈ slots)
    (worldMember : ⟨"world", AccountState.type, layout.storage.world⟩ ∈ slots)
    (addressMember : ⟨"address", .word, layout.storage.address⟩ ∈ slots)
    (completeMember : ⟨"worldComplete", .bool, layout.storage.complete⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, layout.storage.isStatic⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, layout.storage.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, layout.storage.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, layout.storage.returnSize⟩ ∈ slots)
    (logsMember : ⟨"logs", Core.WordMapping.type, layout.logs⟩ ∈ slots)
    (logSizeMember : ⟨"logSize", .word, layout.logSize⟩ ∈ slots) :
    ∀ anchors, ExternalWorldPreservation (supported slots) (model layout baseline slots) slots RuntimeLogEffectsSemantics.effects
      anchors layout.storage.world (fun state => state.runtime.runtime.storage.world) := by
  intro anchors
  intro functions name type sources initial final result enabled notFunction called
  cases called with
  | function selected called => rw [notFunction] at selected; contradiction
  | primitive absent computed => rw [primitive_none enabled] at computed; contradiction
  | external absent notPrimitive computed =>
      cases computed with
      | @runtime finalRuntime computed =>
          have runtimeEnabled : RuntimeEnvironmentEffectsCorrespondence.supported slots name := by
            rcases enabled with runtime | ⟨operation, rfl⟩
            · exact runtime
            · rw [runtime_unsupported] at computed
              contradiction
          intro typeFuel expected typeCompiled scope arguments lowered compiled world mapping environment initialStore argumentStore targets codes locations captured related packed runtime state installed linked
          have call : Semantics.EvalCall functions RuntimeEnvironmentEffectsSemantics.effects name type sources
              (sourceRuntime initial) result {sourceRuntime initial with external := finalRuntime} :=
            .external absent notPrimitive computed
          obtain ⟨target, finalStore, evaluated, linkedFinal⟩ :=
            LinkedEnvironmentWorldCorrespondence.external_preserves layout.toLayout (patched layout baseline initial.external)
              slots (passive_runtime passive) memoryMember worldMember addressMember completeMember staticMember
              memorySizeMember exitMember offsetMember sizeMember anchors runtimeEnabled notFunction call
              typeCompiled compiled related packed runtime (runtime_related state) installed linked
          exact ⟨target, finalStore, evaluated, linkedFinal⟩
      | logs computed =>
          cases computed with
          | log operation resultType offset length topics count executed =>
              intro typeFuel expected typeCompiled scope arguments lowered compiled world mapping environment initialStore argumentStore targets codes locations captured related packed runtime state installed linked
              obtain ⟨target, finalStore, resultRelated, evaluated, finalState, frame⟩ :=
                LogBuiltinCorrespondence.preserves operation compiled count executed related runtime
                  memoryMember memorySizeMember logsMember logSizeMember addressMember staticMember exitMember offsetMember sizeMember
                  (logs_related state) packed
              refine ⟨target, finalStore, evaluated, linked.read_preserved ?_⟩
              intro value found
              have joint := layout.jointDistinct
              simp [StorageBuiltinCorrespondence.Locations.all] at joint
              apply frame.preserved _ _ _ found
              simp [logLocations, LogBuiltinCorrespondence.Locations.mutable, LogsCorrespondence.Locations.all]
              simp_all [ne_comm]


end Solcore.Frontend.RustHull.LinkedLogWorldCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ReadOnlyWorldBuiltinCorrespondence
/-! Termination and return-data copying retain the exact encoded world,
including catalog identities hidden by the ordinary resource projection. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ReadOnlyWorldBuiltinCorrespondence
open Core Correspondence PureCallCorrespondence EffectBuiltinCorrespondence ScalarExecution

namespace Termination
open TerminationSemantics TerminationBuiltinCorrespondence

theorem finalStore_world {locations : StorageBuiltinCorrespondence.Locations}
    {state : RuntimeEffectsSemantics.State} {store : Store}
    (storage : StorageBuiltinCorrespondence.StateRel locations state.storage store)
    (kind : Nat) (offset length : Word) :
    ∀ value, store.read? locations.world = some value →
      (finalStore locations state kind offset length store).read? locations.world = some value := by
  intro value read
  have distinct := storage.distinct
  simp [StorageBuiltinCorrespondence.Locations.all] at distinct
  unfold finalStore
  split
  · exact read
  · apply finishStore_other (by intro same; simp_all) (by intro same; simp_all) (by intro same; simp_all)
    exact (MemoryCorrespondence.touchStore_other store (by intro same; simp_all) _ _ _).trans read

private theorem inner_arity (operation : Operation) {scope : Scope}
    {arguments : List Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope operation.name arguments = .ok lowered) :
    arguments.length = operation.arity := by
  cases operation <;>
    rcases arguments with _ | ⟨first, _ | ⟨second, _ | ⟨third, rest⟩⟩⟩
  all_goals first
    | rfl
    | change Except.error _ = Except.ok lowered at compiled
      cases compiled

private theorem zero_components (operation : Operation) (zero : operation.arity = 0)
    {scope : Scope} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope operation.name [] = .ok lowered) :
    ∃ expression, Effects.terminate scope operation.kind (.word Word.zero) (.word Word.zero) = .ok expression ∧
      lowered = ⟨.unit, expression⟩ := by
  have expanded : Effects.lowerBuiltin scope operation.name [] = (do
      let raw ← (do
        let expression ← Effects.terminate scope operation.kind (.word Word.zero) (.word Word.zero)
        pure (Lowered.mk .unit expression) : LowerM Lowered)
      pure raw) := by
    cases operation <;> first | rfl | cases zero
  rw [expanded] at compiled
  obtain ⟨expression, terminated, returned⟩ := lower_bind_eq_ok.mp compiled
  exact ⟨expression, terminated, (Except.ok.inj returned).symm⟩

private theorem two_components (operation : Operation) (two : operation.arity = 2)
    {scope : Scope} {offset length : Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope operation.name [offset, length] = .ok lowered) :
    ∃ expression, Effects.terminate scope operation.kind offset length = .ok expression ∧
      lowered = ⟨.unit, expression⟩ := by
  have expanded : Effects.lowerBuiltin scope operation.name [offset, length] = (do
      let raw ← (do
        let expression ← Effects.terminate scope operation.kind offset length
        pure (Lowered.mk .unit expression) : LowerM Lowered)
      pure raw) := by
    cases operation <;> first | rfl | cases two
  rw [expanded] at compiled
  obtain ⟨expression, terminated, returned⟩ := lower_bind_eq_ok.mp compiled
  exact ⟨expression, terminated, (Except.ok.inj returned).symm⟩

/-- Argument typing and arity are derived from the accepted outer compiler.
The range and exit registers, including overflow and zero-length behavior,
correspond to the independent source operation at the final actual store. -/
theorem preserves (operation : Operation)
    {scope : Scope} {expected : Core.Ty} {arguments : List Lowered} {lowered : Lowered}
    (compiled : lowerBuiltin scope operation.name expected arguments = .ok lowered)
    {sources : List Semantics.Value} {targets : List Core.Value}
    (related : ArgumentsRel arguments sources targets)
    {slots : List EffectSlot} {mapping : Renaming} {environment : Environment}
    {initial store : Store} {state : RuntimeEffectsSemantics.State} {layout : RuntimeEffectsCorrespondence.Layout}
    (runtime : EffectEnvironmentRel slots scope mapping environment)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, layout.storage.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, layout.storage.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, layout.storage.returnSize⟩ ∈ slots)
    (memory : MemoryCorrespondence.StateRel layout.memory layout.storage.memorySize state.memory store)
    (storage : StorageBuiltinCorrespondence.StateRel layout.storage state.storage store)
    (packed : Evaluates environment initial ((packArguments arguments).expression.rename mapping)
      (.inRight .word (bundleValues targets)) store) (sourceType : Ty) :
    ∃ result finalState target final,
      builtin operation.name sourceType sources state = some (result, finalState) ∧
      ResultRel lowered.type result target ∧
      Evaluates environment initial (lowered.expression.rename mapping) target final ∧
      MemoryCorrespondence.StateRel layout.memory layout.storage.memorySize finalState.memory final ∧
      StorageBuiltinCorrespondence.StateRel layout.storage finalState.storage final ∧
      RuntimeEffectsCorrespondence.Frame layout store final ∧ ClosuresPreserved store final ∧
      ∀ value, store.read? layout.storage.world = some value → final.read? layout.storage.world = some value := by
  obtain ⟨words, raw, rawCompiled, typed, loweredEqual⟩ :=
    outer_components (by cases operation <;> rfl) compiled
  have arity : arguments.length = operation.arity := by
    simpa only [List.length_map, List.length_range] using inner_arity operation rawCompiled
  by_cases zero : operation.arity = 0
  · have empty : arguments = [] := List.eq_nil_of_length_eq_zero (arity.trans zero)
    subst arguments
    cases related
    obtain ⟨expression, terminated, rfl⟩ := zero_components operation zero rawCompiled
    cases typed
    cases loweredEqual
    obtain ⟨resultRelated, memoryFinal, storageFinal, frame⟩ := terminate_state memory storage operation.kind Word.zero Word.zero
    refine ⟨_, _, _, _, ?_, resultRelated, ?_, memoryFinal, storageFinal, frame,
      terminate_closures memory storage operation.kind Word.zero Word.zero, finalStore_world storage _ _ _⟩
    · cases operation <;> first | rfl | cases zero
    · apply LanguageResult.bind_success .unit packed
      exact terminate_evaluates terminated (runtime.temporary .unit .unit)
        memorySizeMember exitMember offsetMember sizeMember storage memory.size Word.zero Word.zero
        (fun _ _ => .word) (fun _ _ => .word)
  · have two : operation.arity = 2 := by cases operation <;> simp_all [Operation.arity]
    obtain ⟨offsetExpr, lengthExpr, offset, length, rfl, rfl, rfl⟩ := two_words related words (arity.trans two)
    obtain ⟨expression, terminated, rfl⟩ := two_components operation two rawCompiled
    cases typed
    cases loweredEqual
    obtain ⟨resultRelated, memoryFinal, storageFinal, frame⟩ := terminate_state memory storage operation.kind offset length
    refine ⟨_, _, _, _, ?_, resultRelated, ?_, memoryFinal, storageFinal, frame,
      terminate_closures memory storage operation.kind offset length, finalStore_world storage _ _ _⟩
    · cases operation <;> first | rfl | cases two
    · apply LanguageResult.bind_success .unit packed
      apply terminate_evaluates terminated
        (runtime.temporary (.product .word .word) (.pair (.word offset) (.word length)))
        memorySizeMember exitMember offsetMember sizeMember storage memory.size offset length
      · intro extra store
        exact .first (rightValue := .word length) (.var (by simp [Renaming.lift]))
      · intro extra store
        exact .second (leftValue := .word offset) (.var (by simp [Renaming.lift]))

end Termination

namespace ReturnData
private theorem inner_arity {scope : Scope} {arguments : List Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope "returndatacopy" arguments = .ok lowered) :
    arguments.length = 3 := by
  rcases arguments with _ | ⟨first, _ | ⟨second, _ | ⟨third, _ | ⟨fourth, rest⟩⟩⟩⟩
  all_goals first
    | rfl
    | change Except.error _ = Except.ok lowered at compiled
      cases compiled

private theorem components {scope : Scope} {destination source length : Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope "returndatacopy" [destination, source, length] = .ok lowered) :
    ∃ dataSize invalid memory size data,
      Effects.reference scope "returnDataSize" .word = .ok dataSize ∧
      Effects.terminate scope 3 (.word Word.zero) (.word Word.zero) = .ok invalid ∧
      Effects.reference scope "memory" WordMapping.type = .ok memory ∧
      Effects.reference scope "memorySize" .word = .ok size ∧
      Effects.reference scope "returnData" WordMapping.type = .ok data ∧
      lowered = ⟨.unit, .ifE (.binary .wordGt source (.loadCell dataSize)) invalid
        (.ifE (.binary .wordGt length (.binary .wordSub (.loadCell dataSize) source)) invalid
          (Memory.copyPackedFrom memory size destination (.loadCell data) source length))⟩ := by
  have expanded : (do
      let raw ← (do
        let dataSize ← Effects.reference scope "returnDataSize" .word
        let invalid ← Effects.terminate scope 3 (.word Word.zero) (.word Word.zero)
        let memory ← Effects.reference scope "memory" WordMapping.type
        let size ← Effects.reference scope "memorySize" .word
        let data ← Effects.reference scope "returnData" WordMapping.type
        pure (Lowered.mk .unit (.ifE (.binary .wordGt source (.loadCell dataSize)) invalid
          (.ifE (.binary .wordGt length (.binary .wordSub (.loadCell dataSize) source)) invalid
            (Memory.copyPackedFrom memory size destination (.loadCell data) source length)))) : LowerM Lowered)
      pure raw) = .ok lowered := compiled
  obtain ⟨dataSize, dataSizeCompiled, expanded⟩ := lower_bind_eq_ok.mp expanded
  obtain ⟨invalid, invalidCompiled, expanded⟩ := lower_bind_eq_ok.mp expanded
  obtain ⟨memory, memoryCompiled, expanded⟩ := lower_bind_eq_ok.mp expanded
  obtain ⟨size, sizeCompiled, expanded⟩ := lower_bind_eq_ok.mp expanded
  obtain ⟨data, dataCompiled, returned⟩ := lower_bind_eq_ok.mp expanded
  exact ⟨dataSize, invalid, memory, size, data, dataSizeCompiled, invalidCompiled,
    memoryCompiled, sizeCompiled, dataCompiled, (Except.ok.inj returned).symm⟩

theorem preserves {scope : Scope} {expected : Core.Ty} {arguments : List Lowered} {lowered : Lowered}
    (compiled : lowerBuiltin scope "returndatacopy" expected arguments = .ok lowered)
    {entries : MemorySemantics.Entries} {dataSize : Word} {sourceType : Ty} {sources : List Semantics.Value}
    {state finalState : RuntimeEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (called : ReturnDataSemantics.Builtin entries dataSize "returndatacopy" sourceType sources state result finalState)
    {targets : List Core.Value} (related : ArgumentsRel arguments sources targets)
    {slots : List EffectSlot} {mapping : Renaming} {environment : Environment}
    {initial store : Store} {layout : RuntimeEffectsCorrespondence.Layout} {dataLocation dataSizeLocation : Nat}
    (runtime : EffectEnvironmentRel slots scope mapping environment)
    (memoryMember : ⟨"memory", WordMapping.type, layout.memory⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, layout.storage.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, layout.storage.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, layout.storage.returnSize⟩ ∈ slots)
    (dataMember : ⟨"returnData", WordMapping.type, dataLocation⟩ ∈ slots)
    (dataSizeMember : ⟨"returnDataSize", .word, dataSizeLocation⟩ ∈ slots)
    (dataRead : store.read? dataLocation = some (WordMapping.encode entries))
    (dataSizeRead : store.read? dataSizeLocation = some (.word dataSize))
    (memory : MemoryCorrespondence.StateRel layout.memory layout.storage.memorySize state.memory store)
    (storage : StorageBuiltinCorrespondence.StateRel layout.storage state.storage store)
    (packed : Evaluates environment initial ((packArguments arguments).expression.rename mapping)
      (.inRight .word (ScalarExecution.bundleValues targets)) store) :
    ∃ target final,
      ResultRel lowered.type result target ∧
      Evaluates environment initial (lowered.expression.rename mapping) target final ∧
      MemoryCorrespondence.StateRel layout.memory layout.storage.memorySize finalState.memory final ∧
      StorageBuiltinCorrespondence.StateRel layout.storage finalState.storage final ∧
      RuntimeEffectsCorrespondence.Frame layout store final ∧ ClosuresPreserved store final ∧
      ∀ value, store.read? layout.storage.world = some value → final.read? layout.storage.world = some value := by
  obtain ⟨words, raw, rawCompiled, typed, loweredEqual⟩ := outer_components (by rfl) compiled
  have arity : arguments.length = 3 := by
    simpa only [List.length_map, List.length_range] using inner_arity rawCompiled
  obtain ⟨destinationExpr, sourceExpr, lengthExpr, destination, source, length, rfl, rfl, rfl⟩ :=
    MemoryCopyBuiltinCorrespondence.three_words related words arity
  obtain ⟨dataSizeRef, invalid, memoryRef, sizeRef, dataRef,
    dataSizeCompiled, invalidCompiled, memoryCompiled, sizeCompiled, dataCompiled, rfl⟩ := components rawCompiled
  cases typed
  cases loweredEqual
  let input := Value.pair (.word destination) (.pair (.word source) (.word length))
  let inputType := Core.Ty.product .word (.product .word .word)
  have runtime' := runtime.temporary inputType input
  have terminated := TerminationBuiltinCorrespondence.terminate_evaluates invalidCompiled runtime'
    memorySizeMember exitMember offsetMember sizeMember storage memory.size Word.zero Word.zero
    (fun _ _ => .word) (fun _ _ => .word)
  have terminatedState := TerminationBuiltinCorrespondence.terminate_state memory storage 3 Word.zero Word.zero
  have terminatedClosures : ClosuresPreserved store
      (TerminationBuiltinCorrespondence.finalStore layout.storage state 3 Word.zero Word.zero store) :=
    TerminationBuiltinCorrespondence.terminate_closures memory storage 3 Word.zero Word.zero
  have sourceEvaluated : Evaluates (input :: environment) store
      ((projectArgument 1 3 (.var 0)).rename mapping.lift) (.word source) store :=
    .first (.second (.var rfl))
  have lengthEvaluated : Evaluates (input :: environment) store
      ((projectArgument 2 3 (.var 0)).rename mapping.lift) (.word length) store :=
    .second (.second (.var rfl))
  have dataSizeEvaluated := Evaluates.loadCell (reference_evaluates runtime' dataSizeMember dataSizeCompiled store) dataSizeRead
  cases called with
  | copy executed =>
      cases executed with
      | sourceOverflow invalidSource =>
          obtain ⟨resultRelated, memoryFinal, storageFinal, frame⟩ := terminatedState
          refine ⟨_, _, resultRelated, ?_, memoryFinal, storageFinal, frame, terminatedClosures, Termination.finalStore_world storage _ _ _⟩
          apply LanguageResult.bind_success .unit packed
          exact .ifTrue (.binary sourceEvaluated dataSizeEvaluated (by simp [BinaryOp.apply, invalidSource])) terminated
      | lengthOverflow validSource invalidLength =>
          obtain ⟨resultRelated, memoryFinal, storageFinal, frame⟩ := terminatedState
          refine ⟨_, _, resultRelated, ?_, memoryFinal, storageFinal, frame, terminatedClosures, Termination.finalStore_world storage _ _ _⟩
          apply LanguageResult.bind_success .unit packed
          apply Evaluates.ifFalse (.binary sourceEvaluated dataSizeEvaluated (by simp [BinaryOp.apply, validSource]))
          exact .ifTrue (.binary lengthEvaluated (.binary dataSizeEvaluated sourceEvaluated rfl)
            (by simp [BinaryOp.apply, invalidLength])) terminated
      | copied validSource validLength executed =>
          obtain ⟨target, final, resultRelated, evaluated, finalRelated, frame⟩ :=
            MemoryCopyCorrespondence.copyPackedFrom_preserves executed memory
              (reference_evaluates runtime' memoryMember memoryCompiled store)
              (reference_evaluates runtime' memorySizeMember sizeCompiled store)
              (.first (.var (index := 0) rfl))
              (.loadCell (reference_evaluates runtime' dataMember dataCompiled store) dataRead)
              sourceEvaluated lengthEvaluated
          refine ⟨target, final, resultRelated, ?_, finalRelated,
            RuntimeEffectsCorrespondence.memory_preserves_storage storage frame,
            RuntimeEffectsCorrespondence.Frame.of_memory frame,
            MemoryEffectCorrespondence.closures_preserved memory frame, ?_⟩
          · apply LanguageResult.bind_success .unit packed
            apply Evaluates.ifFalse (.binary sourceEvaluated dataSizeEvaluated (by simp [BinaryOp.apply, validSource]))
            apply Evaluates.ifFalse (.binary lengthEvaluated (.binary dataSizeEvaluated sourceEvaluated rfl)
              (by simp [BinaryOp.apply, validLength]))
            rw [MemoryCopyCorrespondence.copyPackedFrom_rename]
            exact evaluated
          · intro value found
            have distinct := layout.distinct
            simp [StorageBuiltinCorrespondence.Locations.all] at distinct
            exact frame.read _ _ (by intro same; simp_all) (by intro same; simp_all) found

end ReturnData
end Solcore.Frontend.RustHull.ReadOnlyWorldBuiltinCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.LinkedFullWorldCorrespondence
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Solcore.Frontend.RustHull.LinkedFullWorldCorrespondence
open Correspondence DerivationCorrespondence ScalarExecution RuntimeFullEffectsCorrespondence LinkedBuiltinWorldCorrespondence
open RuntimeLogEffectsCorrespondence (Layout model Passive)

private theorem primitive_none {slots : List EffectSlot} {name : String}
    (enabled : supported slots name) (type : Ty) (arguments : List Semantics.Value) :
    Semantics.primitive? name type arguments = none := by
  rcases enabled with (((memory | storage) | environment) | logs) | ⟨operation, rfl⟩
  · obtain ⟨operation, rfl⟩ := memory
    cases operation <;> rfl
  · obtain ⟨operation, rfl⟩ := storage
    cases operation with | load transient | store transient => cases transient <;> rfl
  · obtain ⟨operation, rfl, _⟩ := environment
    cases operation <;> (try first | cases ‹EnvironmentSemantics.Direct› | cases ‹EnvironmentSemantics.AmbientWord›)
    all_goals rfl
  · obtain ⟨operation, rfl⟩ := logs
    cases operation <;> rfl
  · cases operation <;> rfl

private theorem termination_unsupported {slots : List EffectSlot} {name : String}
    (enabled : RuntimeLogEffectsCorrespondence.supported slots name)
    (type : Ty) (arguments : List Semantics.Value) (state : RuntimeEffectsSemantics.State) :
    TerminationSemantics.builtin name type arguments state = none := by
  rcases enabled with ((memory | storage) | environment) | ⟨operation, rfl⟩
  · obtain ⟨operation, rfl⟩ := memory
    cases operation <;> rfl
  · obtain ⟨operation, rfl⟩ := storage
    cases operation with | load transient | store transient => cases transient <;> rfl
  · obtain ⟨operation, rfl, _⟩ := environment
    cases operation <;> (try first | cases ‹EnvironmentSemantics.Direct› | cases ‹EnvironmentSemantics.AmbientWord›)
    all_goals rfl
  · cases operation <;> rfl

private theorem log_named {name : String} {type : Ty} {arguments : List Semantics.Value}
    {initial final : LogsSemantics.State} {result : Semantics.Result Semantics.Value}
    (computed : LogsSemantics.Builtin name type arguments initial result final) :
    ∃ operation : LogsSemantics.Operation, operation.name = name := by
  cases computed with | log operation _ _ _ _ _ _ => exact ⟨operation, rfl⟩

private theorem runtime_unsupported (operation : TerminationSemantics.Operation)
    {type : Ty} {arguments : List Semantics.Value} {initial final : RuntimeLogEffectsSemantics.State}
    {result : Semantics.Result Semantics.Value}
    (computed : RuntimeLogEffectsSemantics.Builtin operation.name type arguments initial result final) : False := by
  cases computed with
  | runtime computed =>
      have missing : RuntimeEnvironmentEffectsSemantics.builtin operation.name type arguments initial.runtime = none := by
        cases operation <;> rfl
      rw [missing] at computed
      contradiction
  | logs computed =>
      obtain ⟨log, named⟩ := log_named computed
      cases log <;> cases operation <;> simp [LogsSemantics.Operation.name, TerminationSemantics.Operation.name] at named

theorem external_preserves (layout : RuntimeLogEffectsCorrespondence.Layout) (baseline : Nat → Option Core.Value)
    (slots : List EffectSlot) (passive : RuntimeLogEffectsCorrespondence.Passive layout slots)
    (memoryMember : ⟨"memory", Core.WordMapping.type, layout.memory⟩ ∈ slots)
    (worldMember : ⟨"world", AccountState.type, layout.storage.world⟩ ∈ slots)
    (addressMember : ⟨"address", .word, layout.storage.address⟩ ∈ slots)
    (completeMember : ⟨"worldComplete", .bool, layout.storage.complete⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, layout.storage.isStatic⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, layout.storage.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, layout.storage.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, layout.storage.returnSize⟩ ∈ slots)
    (logsMember : ⟨"logs", Core.WordMapping.type, layout.logs⟩ ∈ slots)
    (logSizeMember : ⟨"logSize", .word, layout.logSize⟩ ∈ slots) :
    ∀ anchors, ExternalWorldPreservation (supported slots) (model layout baseline slots) slots RuntimeFullEffectsSemantics.effects
      anchors layout.storage.world (fun state => state.runtime.runtime.storage.world) := by
  intro anchors
  intro functions name type sources initial final result enabled notFunction called
  cases called with
  | function selected called => rw [notFunction] at selected; contradiction
  | primitive absent computed => rw [primitive_none enabled] at computed; contradiction
  | external absent notPrimitive computed =>
      cases computed with
      | runtime computed =>
          have runtimeEnabled : RuntimeLogEffectsCorrespondence.supported slots name := by
            rcases enabled with runtime | ⟨operation, rfl⟩
            · exact runtime
            · exact False.elim (runtime_unsupported operation computed)
          have call : Semantics.EvalCall functions RuntimeLogEffectsSemantics.effects name type sources initial result _ :=
            .external absent notPrimitive computed
          intro typeFuel expected typeCompiled
          exact LinkedLogWorldCorrespondence.external_preserves layout baseline slots passive
            memoryMember worldMember addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
            logsMember logSizeMember anchors runtimeEnabled notFunction call typeCompiled
      | @termination finalRuntime computed =>
          have terminationEnabled : TerminationEffectCorrespondence.supported name := by
            rcases enabled with runtime | termination
            · rw [termination_unsupported runtime] at computed
              contradiction
            · exact termination
          obtain ⟨operation, rfl⟩ := terminationEnabled
          intro typeFuel expected typeCompiled scope arguments lowered compiled world mapping environment initialStore argumentStore targets codes locations captured related packed runtime state installed linked
          have beforeRuntime := RuntimeEnvironmentEffectsCorrespondence.runtime_related (RuntimeLogEffectsCorrespondence.runtime_related state)
          obtain ⟨computedResult, computedState, target, finalStore, meaning, resultRelated, evaluated, memoryFinal, storageFinal, frame, retained, preserved⟩ :=
            ReadOnlyWorldBuiltinCorrespondence.Termination.preserves operation compiled related runtime
              memorySizeMember exitMember offsetMember sizeMember
              (RuntimeEffectsCorrespondence.memory_related beforeRuntime)
              (RuntimeEffectsCorrespondence.storage_related beforeRuntime) packed type
          have unchanged : ∀ (state : RuntimeEffectsSemantics.State) kind offset length,
              (TerminationSemantics.terminate state kind offset length).2.storage.world = state.storage.world := by
            intro state kind offset length
            unfold TerminationSemantics.terminate
            split <;> rfl
          have worldSame : computedState.storage.world = initial.external.runtime.runtime.storage.world := by
            cases operation <;> simp [TerminationSemantics.builtin, TerminationSemantics.Operation.name] at meaning
            all_goals split at meaning
            all_goals try contradiction
            all_goals have changed := congrArg (fun output => output.2.storage.world) (Option.some.inj meaning)
            all_goals simpa only [unchanged, RuntimeEnvironmentEffectsCorrespondence.sourceRuntime, RuntimeLogEffectsCorrespondence.sourceRuntime] using changed.symm
          have same := Option.some.inj (computed.symm.trans meaning)
          cases same
          refine ⟨target, finalStore, evaluated, ?_⟩
          change RuntimeLinkedWorldCorrespondence.StateRel anchors finalRuntime.storage.world layout.storage.world finalStore
          rw [worldSame]
          exact linked.read_preserved preserved


end Solcore.Frontend.RustHull.LinkedFullWorldCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.LinkedCopyWorldCorrespondence
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Solcore.Frontend.RustHull.LinkedCopyWorldCorrespondence
open Correspondence DerivationCorrespondence ScalarExecution RuntimeCopyEffectsCorrespondence LinkedBuiltinWorldCorrespondence
open RuntimeLogEffectsCorrespondence (Layout model Passive)

private theorem primitive_none {slots : List EffectSlot} {name : String}
    (enabled : supported slots name) (type : Ty) (arguments : List Semantics.Value) :
    Semantics.primitive? name type arguments = none := by
  rcases enabled with ((((memory | storage) | environment) | logs) | termination) | ⟨operation, rfl, _⟩
  · obtain ⟨operation, rfl⟩ := memory
    cases operation <;> rfl
  · obtain ⟨operation, rfl⟩ := storage
    cases operation with | load transient | store transient => cases transient <;> rfl
  · obtain ⟨operation, rfl, _⟩ := environment
    cases operation <;> (try first | cases ‹EnvironmentSemantics.Direct› | cases ‹EnvironmentSemantics.AmbientWord›)
    all_goals rfl
  · obtain ⟨operation, rfl⟩ := logs
    cases operation <;> rfl
  · obtain ⟨operation, rfl⟩ := termination
    cases operation <;> rfl
  · cases operation <;> rfl

private theorem copy_named {calldata : MemorySemantics.Entries} {name : String} {type : Ty}
    {arguments : List Semantics.Value} {initial final : MemorySemantics.State} {result : Semantics.Result Semantics.Value}
    (computed : MemoryCopySemantics.Builtin calldata name type arguments initial result final) :
    ∃ operation : MemoryCopySemantics.Operation, operation.name = name := by
  cases computed with
  | move _ => exact ⟨.move, rfl⟩
  | calldata _ => exact ⟨.calldata, rfl⟩

private theorem log_named {name : String} {type : Ty} {arguments : List Semantics.Value}
    {initial final : LogsSemantics.State} {result : Semantics.Result Semantics.Value}
    (computed : LogsSemantics.Builtin name type arguments initial result final) :
    ∃ operation : LogsSemantics.Operation, operation.name = name := by
  cases computed with | log operation _ _ _ _ _ _ => exact ⟨operation, rfl⟩

private theorem runtime_unsupported (operation : MemoryCopySemantics.Operation)
    {type : Ty} {arguments : List Semantics.Value} {initial final : RuntimeFullEffectsSemantics.State}
    {result : Semantics.Result Semantics.Value}
    (computed : RuntimeFullEffectsSemantics.Builtin operation.name type arguments initial result final) : False := by
  cases computed with
  | runtime computed =>
      cases computed with
      | runtime computed =>
          have missing : RuntimeEnvironmentEffectsSemantics.builtin operation.name type arguments initial.runtime = none := by
            cases operation <;> rfl
          rw [missing] at computed
          contradiction
      | logs computed =>
          obtain ⟨log, named⟩ := log_named computed
          cases log <;> cases operation <;> simp [LogsSemantics.Operation.name, MemoryCopySemantics.Operation.name] at named
  | termination computed =>
      have missing : TerminationSemantics.builtin operation.name type arguments initial.runtime.runtime = none := by
        cases operation <;> rfl
      rw [missing] at computed
      contradiction

private theorem name_separate {slots : List EffectSlot} {name : String}
    (enabled : RuntimeFullEffectsCorrespondence.supported slots name) (operation : MemoryCopySemantics.Operation) :
    operation.name ≠ name := by
  rcases enabled with (((memory | storage) | environment) | logs) | termination
  · obtain ⟨op, rfl⟩ := memory
    cases op <;> cases operation <;> decide
  · obtain ⟨op, rfl⟩ := storage
    cases op with | load transient | store transient => cases transient <;> cases operation <;> decide
  · obtain ⟨op, rfl, _⟩ := environment
    cases op <;> (try first | cases ‹EnvironmentSemantics.Direct› | cases ‹EnvironmentSemantics.AmbientWord›)
    all_goals cases operation <;> decide
  · obtain ⟨op, rfl⟩ := logs
    cases op <;> cases operation <;> decide
  · obtain ⟨op, rfl⟩ := termination
    cases op <;> cases operation <;> decide

theorem external_preserves (layout : Layout) (baseline : Nat → Option Core.Value)
    (slots : List EffectSlot) (passive : Passive layout slots)
    (memoryMember : ⟨"memory", Core.WordMapping.type, layout.memory⟩ ∈ slots)
    (worldMember : ⟨"world", AccountState.type, layout.storage.world⟩ ∈ slots)
    (addressMember : ⟨"address", .word, layout.storage.address⟩ ∈ slots)
    (completeMember : ⟨"worldComplete", .bool, layout.storage.complete⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, layout.storage.isStatic⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, layout.storage.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, layout.storage.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, layout.storage.returnSize⟩ ∈ slots)
    (logsMember : ⟨"logs", Core.WordMapping.type, layout.logs⟩ ∈ slots)
    (logSizeMember : ⟨"logSize", .word, layout.logSize⟩ ∈ slots) :
    ∀ anchors, ExternalWorldPreservation (supported slots) (model layout baseline slots) slots RuntimeCopyEffectsSemantics.effects
      anchors layout.storage.world (fun state => state.runtime.runtime.storage.world) := by
  intro anchors
  intro functions name type sources initial final result enabled notFunction called
  cases called with
  | function selected called => rw [notFunction] at selected; contradiction
  | primitive absent computed => rw [primitive_none enabled] at computed; contradiction
  | external absent notPrimitive computed =>
      cases computed with
      | runtime computed =>
          have runtimeEnabled : RuntimeFullEffectsCorrespondence.supported slots name := by
            rcases enabled with runtime | ⟨operation, rfl, _⟩
            · exact runtime
            · exact False.elim (runtime_unsupported operation computed)
          have call : Semantics.EvalCall functions RuntimeFullEffectsSemantics.effects name type sources initial result _ :=
            .external absent notPrimitive computed
          intro typeFuel expected typeCompiled
          exact LinkedFullWorldCorrespondence.external_preserves layout baseline slots passive
            memoryMember worldMember addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
            logsMember logSizeMember anchors runtimeEnabled notFunction call typeCompiled
      | @copy finalMemory computed =>
          have copyEnabled : ∃ operation : MemoryCopySemantics.Operation, operation.name = name ∧ Available slots operation := by
            rcases enabled with runtime | copy
            · obtain ⟨operation, named⟩ := copy_named computed
              exact False.elim (name_separate runtime operation named)
            · exact copy
          obtain ⟨operation, rfl, available⟩ := copyEnabled
          intro typeFuel expected typeCompiled scope arguments lowered compiled world mapping environment initialStore argumentStore targets codes locations captured related packed runtime state installed linked
          have beforeEnvironment := RuntimeLogEffectsCorrespondence.runtime_related state
          have beforeRuntime := RuntimeEnvironmentEffectsCorrespondence.runtime_related beforeEnvironment
          have memoryRelated := RuntimeEffectsCorrespondence.memory_related beforeRuntime
          have calldataRead : ∀ location, ⟨"calldata", Core.WordMapping.type, location⟩ ∈ slots →
              argumentStore.read? location = some (Core.WordMapping.encode initial.external.runtime.environment.calldata) := by
            intro location member
            exact RuntimeEnvironmentEffectsCorrespondence.observations_related beforeEnvironment _ member _ rfl
          obtain ⟨target, finalStore, resultRelated, evaluated, memoryFinal, frame⟩ :=
            MemoryCopyBuiltinCorrespondence.preserves operation compiled computed related runtime memoryMember memorySizeMember
              available calldataRead memoryRelated packed
          exact ⟨target, finalStore, evaluated, memory_frame linked frame⟩


end Solcore.Frontend.RustHull.LinkedCopyWorldCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.LinkedHashWorldCorrespondence
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Solcore.Frontend.RustHull.LinkedHashWorldCorrespondence
open Correspondence DerivationCorrespondence ScalarExecution RuntimeHashEffectsCorrespondence LinkedBuiltinWorldCorrespondence
open RuntimeLogEffectsCorrespondence (Layout model Passive)

private theorem primitive_none {slots : List EffectSlot} {name : String}
    (enabled : supported slots name) (type : Ty) (arguments : List Semantics.Value) :
    Semantics.primitive? name type arguments = none := by
  rcases enabled with (((((memory | storage) | environment) | logs) | termination) | copy) | rfl
  · obtain ⟨operation, rfl⟩ := memory
    cases operation <;> rfl
  · obtain ⟨operation, rfl⟩ := storage
    cases operation with | load transient | store transient => cases transient <;> rfl
  · obtain ⟨operation, rfl, _⟩ := environment
    cases operation <;> (try first | cases ‹EnvironmentSemantics.Direct› | cases ‹EnvironmentSemantics.AmbientWord›)
    all_goals rfl
  · obtain ⟨operation, rfl⟩ := logs
    cases operation <;> rfl
  · obtain ⟨operation, rfl⟩ := termination
    cases operation <;> rfl
  · obtain ⟨operation, rfl, _⟩ := copy
    cases operation <;> rfl
  · rfl

private theorem copy_named {calldata : MemorySemantics.Entries} {name : String} {type : Ty}
    {arguments : List Semantics.Value} {initial final : MemorySemantics.State} {result : Semantics.Result Semantics.Value}
    (computed : MemoryCopySemantics.Builtin calldata name type arguments initial result final) :
    ∃ operation : MemoryCopySemantics.Operation, operation.name = name := by
  cases computed with
  | move _ => exact ⟨.move, rfl⟩
  | calldata _ => exact ⟨.calldata, rfl⟩

private theorem log_named {name : String} {type : Ty} {arguments : List Semantics.Value}
    {initial final : LogsSemantics.State} {result : Semantics.Result Semantics.Value}
    (computed : LogsSemantics.Builtin name type arguments initial result final) :
    ∃ operation : LogsSemantics.Operation, operation.name = name := by
  cases computed with | log operation _ _ _ _ _ _ => exact ⟨operation, rfl⟩

private theorem hash_named {name : String} {type : Ty} {arguments : List Semantics.Value}
    {initial final : MemorySemantics.State} {result : Semantics.Result Semantics.Value}
    (computed : KeccakSemantics.Builtin name type arguments initial result final) : name = "keccak256" := by
  cases computed
  rfl

private theorem runtime_unsupported {type : Ty} {arguments : List Semantics.Value}
    {initial final : RuntimeCopyEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (computed : RuntimeCopyEffectsSemantics.Builtin "keccak256" type arguments initial result final) : False := by
  cases computed with
  | runtime computed =>
      cases computed with
      | runtime computed =>
          cases computed with
          | runtime computed => contradiction
          | logs computed =>
              obtain ⟨operation, named⟩ := log_named computed
              cases operation <;> simp [LogsSemantics.Operation.name] at named
      | termination computed => contradiction
  | copy computed =>
      obtain ⟨operation, named⟩ := copy_named computed
      cases operation <;> simp [MemoryCopySemantics.Operation.name] at named

theorem external_preserves (layout : Layout) (baseline : Nat → Option Core.Value)
    (slots : List EffectSlot) (passive : Passive layout slots)
    (memoryMember : ⟨"memory", Core.WordMapping.type, layout.memory⟩ ∈ slots)
    (worldMember : ⟨"world", AccountState.type, layout.storage.world⟩ ∈ slots)
    (addressMember : ⟨"address", .word, layout.storage.address⟩ ∈ slots)
    (completeMember : ⟨"worldComplete", .bool, layout.storage.complete⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, layout.storage.isStatic⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, layout.storage.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, layout.storage.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, layout.storage.returnSize⟩ ∈ slots)
    (logsMember : ⟨"logs", Core.WordMapping.type, layout.logs⟩ ∈ slots)
    (logSizeMember : ⟨"logSize", .word, layout.logSize⟩ ∈ slots) :
    ∀ anchors, ExternalWorldPreservation (supported slots) (model layout baseline slots) slots RuntimeHashEffectsSemantics.effects
      anchors layout.storage.world (fun state => state.runtime.runtime.storage.world) := by
  intro anchors
  intro functions name type sources initial final result enabled notFunction called
  cases called with
  | function selected called => rw [notFunction] at selected; contradiction
  | primitive absent computed => rw [primitive_none enabled] at computed; contradiction
  | external absent notPrimitive computed =>
      cases computed with
      | runtime computed =>
          have runtimeEnabled : RuntimeCopyEffectsCorrespondence.supported slots name := by
            rcases enabled with runtime | rfl
            · exact runtime
            · exact False.elim (runtime_unsupported computed)
          have call : Semantics.EvalCall functions RuntimeCopyEffectsSemantics.effects name type sources initial result _ :=
            .external absent notPrimitive computed
          intro typeFuel expected typeCompiled
          exact LinkedCopyWorldCorrespondence.external_preserves layout baseline slots passive
            memoryMember worldMember addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
            logsMember logSizeMember anchors runtimeEnabled notFunction call typeCompiled
      | hash computed =>
          have named := hash_named computed
          subst name
          intro typeFuel expected typeCompiled scope arguments lowered compiled world mapping environment initialStore argumentStore targets codes locations captured related packed runtime state installed linked
          have beforeEnvironment := RuntimeLogEffectsCorrespondence.runtime_related state
          have beforeRuntime := RuntimeEnvironmentEffectsCorrespondence.runtime_related beforeEnvironment
          have memoryRelated := RuntimeEffectsCorrespondence.memory_related beforeRuntime
          obtain ⟨target, finalStore, resultRelated, evaluated, memoryFinal, frame⟩ :=
            KeccakBuiltinCorrespondence.preserves compiled computed related runtime memoryMember memorySizeMember memoryRelated packed
          exact ⟨target, finalStore, evaluated, memory_frame linked frame⟩


end Solcore.Frontend.RustHull.LinkedHashWorldCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.LinkedAccountWorldCorrespondence
/-! Exact catalog links survive the concrete account/image inspection leaves. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.LinkedAccountWorldCorrespondence
open Correspondence ScalarExecution DerivationCorrespondence
open RuntimeAccountEffectsCorrespondence
open LinkedBuiltinWorldCorrespondence

private theorem primitive_none {slots : List EffectSlot} {name : String}
    (enabled : supported slots name) (type : Ty) (arguments : List Semantics.Value) :
    Semantics.primitive? name type arguments = none := by
  rcases enabled with ((((((memory | storage) | environment) | logs) | termination) | copy) | hash) | ⟨operation, rfl⟩
  · obtain ⟨operation, rfl⟩ := memory
    cases operation <;> rfl
  · obtain ⟨operation, rfl⟩ := storage
    cases operation with | load transient | store transient => cases transient <;> rfl
  · obtain ⟨operation, rfl, _⟩ := environment
    cases operation <;> (try first | cases ‹EnvironmentSemantics.Direct› | cases ‹EnvironmentSemantics.AmbientWord›)
    all_goals rfl
  · obtain ⟨operation, rfl⟩ := logs
    cases operation <;> rfl
  · obtain ⟨operation, rfl⟩ := termination
    cases operation <;> rfl
  · obtain ⟨operation, rfl, _⟩ := copy
    cases operation <;> rfl
  · subst name
    rfl
  · cases operation <;> rfl

private theorem copy_named {calldata : MemorySemantics.Entries} {name : String} {type : Ty}
    {arguments : List Semantics.Value} {initial final : MemorySemantics.State} {result : Semantics.Result Semantics.Value}
    (computed : MemoryCopySemantics.Builtin calldata name type arguments initial result final) :
    ∃ operation : MemoryCopySemantics.Operation, operation.name = name := by
  cases computed with
  | move _ => exact ⟨.move, rfl⟩
  | calldata _ => exact ⟨.calldata, rfl⟩

private theorem log_named {name : String} {type : Ty} {arguments : List Semantics.Value}
    {initial final : LogsSemantics.State} {result : Semantics.Result Semantics.Value}
    (computed : LogsSemantics.Builtin name type arguments initial result final) :
    ∃ operation : LogsSemantics.Operation, operation.name = name := by
  cases computed with | log operation _ _ _ _ _ _ => exact ⟨operation, rfl⟩

private theorem hash_named {name : String} {type : Ty} {arguments : List Semantics.Value}
    {initial final : MemorySemantics.State} {result : Semantics.Result Semantics.Value}
    (computed : KeccakSemantics.Builtin name type arguments initial result final) : name = "keccak256" := by
  cases computed
  rfl

private theorem runtime_unsupported (operation : AccountObservationSemantics.Operation)
    {type : Ty} {arguments : List Semantics.Value} {initial final : RuntimeHashEffectsSemantics.State}
    {result : Semantics.Result Semantics.Value}
    (computed : RuntimeHashEffectsSemantics.Builtin operation.name type arguments initial result final) : False := by
  cases computed with
  | runtime computed =>
      cases computed with
      | runtime computed =>
          cases computed with
          | runtime computed =>
              cases computed with
              | runtime computed =>
                  have missing : RuntimeEnvironmentEffectsSemantics.builtin operation.name type arguments initial.runtime = none := by
                    cases operation <;> rfl
                  rw [missing] at computed
                  contradiction
              | logs computed =>
                  obtain ⟨log, named⟩ := log_named computed
                  cases operation <;> cases log <;> simp [AccountObservationSemantics.Operation.name, LogsSemantics.Operation.name] at named
          | termination computed =>
              have missing : TerminationSemantics.builtin operation.name type arguments initial.runtime.runtime = none := by
                cases operation <;> rfl
              rw [missing] at computed
              contradiction
      | copy computed =>
          obtain ⟨copy, named⟩ := copy_named computed
          cases operation <;> cases copy <;> simp [AccountObservationSemantics.Operation.name, MemoryCopySemantics.Operation.name] at named
  | hash computed =>
      have named := hash_named computed
      cases operation <;> simp [AccountObservationSemantics.Operation.name] at named

theorem external_preserves (layout : Layout) (baseline : Nat → Option Core.Value)
    (slots : List EffectSlot) (passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots)
    (memoryMember : ⟨"memory", Core.WordMapping.type, layout.memory⟩ ∈ slots)
    (worldMember : ⟨"world", AccountState.type, layout.storage.world⟩ ∈ slots)
    (addressMember : ⟨"address", .word, layout.storage.address⟩ ∈ slots)
    (completeMember : ⟨"worldComplete", .bool, layout.storage.complete⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, layout.storage.isStatic⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, layout.storage.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, layout.storage.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, layout.storage.returnSize⟩ ∈ slots)
    (logsMember : ⟨"logs", Core.WordMapping.type, layout.logs⟩ ∈ slots)
    (logSizeMember : ⟨"logSize", .word, layout.logSize⟩ ∈ slots)
    (balancesMember : ⟨"balances", Core.WordMapping.type, layout.balances⟩ ∈ slots) :
    ∀ anchors, ExternalWorldPreservation (supported slots) (model layout baseline slots) slots RuntimeAccountEffectsSemantics.effects
      anchors layout.storage.world (fun state => state.runtime.runtime.runtime.storage.world) := by
  intro anchors
  intro functions name type sources initial final result enabled notFunction called
  cases called with
  | function selected called => rw [notFunction] at selected; contradiction
  | primitive absent computed => rw [primitive_none enabled] at computed; contradiction
  | external absent notPrimitive computed =>
      cases computed with
      | runtime computed =>
          have runtimeEnabled : RuntimeHashEffectsCorrespondence.supported slots name := by
            rcases enabled with runtime | ⟨operation, rfl⟩
            · exact runtime
            · exact False.elim (runtime_unsupported operation computed)
          have call : Semantics.EvalCall functions RuntimeHashEffectsSemantics.effects name type sources
              (sourceRuntime initial) result _ := .external absent notPrimitive computed
          intro typeFuel expected typeCompiled scope arguments lowered compiled world mapping environment initialStore argumentStore targets codes locations captured related packed runtime state installed linked
          obtain ⟨target, finalStore, evaluated, finalLinked⟩ :=
            LinkedHashWorldCorrespondence.external_preserves layout.toLogLayout baseline slots passive
              memoryMember worldMember addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
              logsMember logSizeMember anchors runtimeEnabled notFunction call typeCompiled compiled related packed runtime (runtime_related state) installed linked
          exact ⟨target, finalStore, evaluated, finalLinked⟩
      | observation computed =>
          obtain ⟨operation, named⟩ := computed.named
          subst name
          intro typeFuel expected typeCompiled scope arguments lowered compiled world mapping environment initialStore argumentStore targets codes locations captured related packed runtime state installed linked
          have beforeLog := runtime_related state
          have beforeEnvironment := RuntimeLogEffectsCorrespondence.runtime_related beforeLog
          have beforeRuntime := RuntimeEnvironmentEffectsCorrespondence.runtime_related beforeEnvironment
          have memoryRelated := RuntimeEffectsCorrespondence.memory_related beforeRuntime
          have storageRelated := RuntimeEffectsCorrespondence.storage_related beforeRuntime
          obtain ⟨target, finalStore, resultRelated, evaluated, memoryFinal, frame⟩ :=
            AccountObservationBuiltinCorrespondence.preserves operation compiled computed related runtime
              memoryMember memorySizeMember worldMember addressMember completeMember balancesMember
              memoryRelated storageRelated (balances_related state) packed
          exact ⟨target, finalStore, evaluated, memory_frame linked frame⟩

end Solcore.Frontend.RustHull.LinkedAccountWorldCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.LinkedCodeWorldCorrespondence
/-! Exact catalog links survive the concrete account/image inspection leaves. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.LinkedCodeWorldCorrespondence
open Correspondence ScalarExecution DerivationCorrespondence
open RuntimeCodeEffectsCorrespondence
open LinkedBuiltinWorldCorrespondence

private theorem primitive_none {slots : List EffectSlot} {name : String}
    (enabled : supported slots name) (type : Ty) (arguments : List Semantics.Value) :
    Semantics.primitive? name type arguments = none := by
  rcases enabled with (((((((memory | storage) | environment) | logs) | termination) | copy) | hash) | account) | ⟨operation, rfl⟩
  · obtain ⟨operation, rfl⟩ := memory
    cases operation <;> rfl
  · obtain ⟨operation, rfl⟩ := storage
    cases operation with | load transient | store transient => cases transient <;> rfl
  · obtain ⟨operation, rfl, _⟩ := environment
    cases operation <;> (try first | cases ‹EnvironmentSemantics.Direct› | cases ‹EnvironmentSemantics.AmbientWord›)
    all_goals rfl
  · obtain ⟨operation, rfl⟩ := logs
    cases operation <;> rfl
  · obtain ⟨operation, rfl⟩ := termination
    cases operation <;> rfl
  · obtain ⟨operation, rfl, _⟩ := copy
    cases operation <;> rfl
  · subst name
    rfl
  · obtain ⟨operation, rfl⟩ := account
    cases operation <;> rfl
  · cases operation <;> rfl

private theorem copy_named {calldata : MemorySemantics.Entries} {name : String} {type : Ty}
    {arguments : List Semantics.Value} {initial final : MemorySemantics.State} {result : Semantics.Result Semantics.Value}
    (computed : MemoryCopySemantics.Builtin calldata name type arguments initial result final) :
    ∃ operation : MemoryCopySemantics.Operation, operation.name = name := by
  cases computed with
  | move _ => exact ⟨.move, rfl⟩
  | calldata _ => exact ⟨.calldata, rfl⟩

private theorem log_named {name : String} {type : Ty} {arguments : List Semantics.Value}
    {initial final : LogsSemantics.State} {result : Semantics.Result Semantics.Value}
    (computed : LogsSemantics.Builtin name type arguments initial result final) :
    ∃ operation : LogsSemantics.Operation, operation.name = name := by
  cases computed with | log operation _ _ _ _ _ _ => exact ⟨operation, rfl⟩

private theorem hash_named {name : String} {type : Ty} {arguments : List Semantics.Value}
    {initial final : MemorySemantics.State} {result : Semantics.Result Semantics.Value}
    (computed : KeccakSemantics.Builtin name type arguments initial result final) : name = "keccak256" := by
  cases computed
  rfl

private theorem hash_runtime_unsupported (operation : CodeImageSemantics.Operation)
    {type : Ty} {arguments : List Semantics.Value} {initial final : RuntimeHashEffectsSemantics.State}
    {result : Semantics.Result Semantics.Value}
    (computed : RuntimeHashEffectsSemantics.Builtin operation.name type arguments initial result final) : False := by
  cases computed with
  | runtime computed =>
      cases computed with
      | runtime computed =>
          cases computed with
          | runtime computed =>
              cases computed with
              | runtime computed =>
                  have missing : RuntimeEnvironmentEffectsSemantics.builtin operation.name type arguments initial.runtime = none := by
                    cases operation <;> rfl
                  rw [missing] at computed
                  contradiction
              | logs computed =>
                  obtain ⟨log, named⟩ := log_named computed
                  cases operation <;> cases log <;> simp [CodeImageSemantics.Operation.name, LogsSemantics.Operation.name] at named
          | termination computed =>
              have missing : TerminationSemantics.builtin operation.name type arguments initial.runtime.runtime = none := by
                cases operation <;> rfl
              rw [missing] at computed
              contradiction
      | copy computed =>
          obtain ⟨copy, named⟩ := copy_named computed
          cases operation <;> cases copy <;> simp [CodeImageSemantics.Operation.name, MemoryCopySemantics.Operation.name] at named
  | hash computed =>
      have named := hash_named computed
      cases operation <;> simp [CodeImageSemantics.Operation.name] at named

private theorem runtime_unsupported (operation : CodeImageSemantics.Operation)
    {type : Ty} {arguments : List Semantics.Value} {initial final : RuntimeAccountEffectsSemantics.State}
    {result : Semantics.Result Semantics.Value}
    (computed : RuntimeAccountEffectsSemantics.Builtin operation.name type arguments initial result final) : False := by
  cases computed with
  | runtime computed => exact hash_runtime_unsupported operation computed
  | observation computed =>
      obtain ⟨observation, named⟩ := computed.named
      cases operation <;> cases observation <;>
        simp [CodeImageSemantics.Operation.name, AccountObservationSemantics.Operation.name] at named

theorem external_preserves (layout : Layout) (baseline : Nat → Option Core.Value)
    (slots : List EffectSlot) (image : Option (List UInt8)) (passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots)
    (memoryMember : ⟨"memory", Core.WordMapping.type, layout.memory⟩ ∈ slots)
    (worldMember : ⟨"world", AccountState.type, layout.storage.world⟩ ∈ slots)
    (addressMember : ⟨"address", .word, layout.storage.address⟩ ∈ slots)
    (completeMember : ⟨"worldComplete", .bool, layout.storage.complete⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, layout.storage.isStatic⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, layout.storage.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, layout.storage.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, layout.storage.returnSize⟩ ∈ slots)
    (logsMember : ⟨"logs", Core.WordMapping.type, layout.logs⟩ ∈ slots)
    (logSizeMember : ⟨"logSize", .word, layout.logSize⟩ ∈ slots)
    (balancesMember : ⟨"balances", Core.WordMapping.type, layout.balances⟩ ∈ slots)
    (codeMember : ⟨"code", Core.WordMapping.type, layout.code⟩ ∈ slots)
    (knownMember : ⟨"codeKnown", .bool, layout.known⟩ ∈ slots) :
    ∀ anchors, ExternalWorldPreservation (supported slots) (model layout baseline slots image) slots (RuntimeCodeEffectsSemantics.effects image)
      anchors layout.storage.world (fun state => state.runtime.runtime.runtime.storage.world) := by
  intro anchors
  intro functions name type sources initial final result enabled notFunction called
  cases called with
  | function selected called => rw [notFunction] at selected; contradiction
  | primitive absent computed => rw [primitive_none enabled] at computed; contradiction
  | external absent notPrimitive computed =>
      cases computed with
      | runtime computed =>
          have runtimeEnabled : RuntimeAccountEffectsCorrespondence.supported slots name := by
            rcases enabled with runtime | ⟨operation, rfl⟩
            · exact runtime
            · exact False.elim (runtime_unsupported operation computed)
          have call : Semantics.EvalCall functions RuntimeAccountEffectsSemantics.effects name type sources
              initial result _ := .external absent notPrimitive computed
          intro typeFuel expected typeCompiled scope arguments lowered compiled world mapping environment initialStore argumentStore targets codes locations captured related packed runtime state installed linked
          obtain ⟨target, finalStore, evaluated, finalLinked⟩ :=
            LinkedAccountWorldCorrespondence.external_preserves layout.toAccountLayout baseline slots passive
              memoryMember worldMember addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
              logsMember logSizeMember balancesMember anchors runtimeEnabled notFunction call typeCompiled compiled related packed runtime (account_related state) installed linked
          exact ⟨target, finalStore, evaluated, finalLinked⟩
      | copy computed =>
          obtain ⟨operation, named⟩ := computed.named
          subst name
          intro typeFuel expected typeCompiled scope arguments lowered compiled world mapping environment initialStore argumentStore targets codes locations captured related packed runtime state installed linked
          have beforeAccount := account_related state
          have beforeLog := RuntimeAccountEffectsCorrespondence.runtime_related beforeAccount
          have beforeEnvironment := RuntimeLogEffectsCorrespondence.runtime_related beforeLog
          have beforeRuntime := RuntimeEnvironmentEffectsCorrespondence.runtime_related beforeEnvironment
          have memoryRelated := RuntimeEffectsCorrespondence.memory_related beforeRuntime
          obtain ⟨target, finalStore, resultRelated, evaluated, memoryFinal, frame⟩ :=
            CodeImageBuiltinCorrespondence.preserves operation compiled computed related runtime
              memoryMember memorySizeMember codeMember knownMember
              (code_related state) (known_related state) memoryRelated packed
          exact ⟨target, finalStore, evaluated, memory_frame linked frame⟩

end Solcore.Frontend.RustHull.LinkedCodeWorldCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.LinkedBuiltinWorldCorrespondence
/-! Exact executable catalog IDs survive every call-free runtime operation. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.LinkedBuiltinWorldCorrespondence
open Correspondence ScalarExecution DerivationCorrespondence
open RuntimeReturnDataEffectsCorrespondence

private theorem copy_world {entries : MemorySemantics.Entries} {size : Core.Word} {name : String} {type : Ty}
    {arguments : List Semantics.Value} {initial final : RuntimeEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (called : ReturnDataSemantics.Builtin entries size name type arguments initial result final) :
    final.storage.world = initial.storage.world := by
  cases called with
  | copy executed => cases executed <;> rfl

theorem external_preserves (layout : Layout) (baseline : Nat → Option Core.Value)
    (slots : List EffectSlot) (image : Option (List UInt8)) (withCode : Bool) (passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots)
    (memoryMember : ⟨"memory", Core.WordMapping.type, layout.memory⟩ ∈ slots)
    (worldMember : ⟨"world", AccountState.type, layout.storage.world⟩ ∈ slots)
    (addressMember : ⟨"address", .word, layout.storage.address⟩ ∈ slots)
    (completeMember : ⟨"worldComplete", .bool, layout.storage.complete⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, layout.storage.isStatic⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, layout.storage.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, layout.storage.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, layout.storage.returnSize⟩ ∈ slots)
    (logsMember : ⟨"logs", Core.WordMapping.type, layout.logs⟩ ∈ slots)
    (logSizeMember : ⟨"logSize", .word, layout.logSize⟩ ∈ slots)
    (balancesMember : ⟨"balances", Core.WordMapping.type, layout.balances⟩ ∈ slots)
    (codeMembers : ∀ cells, layout.codeCells = some cells →
      (⟨"code", Core.WordMapping.type, cells.code⟩ ∈ slots ∧ ⟨"codeKnown", .bool, cells.known⟩ ∈ slots))
    (dataMember : ⟨"returnData", Core.WordMapping.type, layout.returnData⟩ ∈ slots)
    (dataSizeMember : ⟨"returnDataSize", .word, layout.returnDataSize⟩ ∈ slots)
    (mode : layout.codeCells.isSome = withCode) :
    ∀ anchors, ExternalWorldPreservation (supported slots withCode) (model layout baseline slots image) slots
      (RuntimeReturnDataEffectsSemantics.effects image) anchors layout.storage.world
      (fun state => state.runtime.runtime.runtime.runtime.storage.world) := by
  intro anchors
  intro functions name type sources initial final result enabled notFunction called
  cases called with
  | function selected called => rw [notFunction] at selected; contradiction
  | primitive absent computed => rw [primitive_none enabled] at computed; contradiction
  | external absent notPrimitive computed =>
      cases computed with
      | runtime computed =>
          have sizeEqual := congrArg (fun environment => environment.direct .returnDataSize)
            (RuntimeReturnDataEffectsSemantics.runtime_environment computed)
          intro typeFuel expected typeCompiled scope arguments lowered compiled world mapping environment initialStore argumentStore targets codes locations captured related packed runtime state installed linked
          cases present : layout.codeCells with
          | some cells =>
              let codeLayout : RuntimeCodeEffectsCorrespondence.Layout :=
                { toAccountLayout := layout.toAccountLayout
                  code := cells.code, known := cells.known
                  codeBelow := cells.codeBelow, knownBelow := cells.knownBelow
                  codeOutside := cells.codeOutside, knownOutside := cells.knownOutside }
              have beforeAccount := account_related state
              have codeState : StateRel (RuntimeCodeEffectsCorrespondence.model codeLayout
                  (patched layout baseline initial.external) slots image) world (sourceRuntime initial) argumentStore :=
                ⟨beforeAccount.toHeapRel, beforeAccount.external.1, beforeAccount.external.2.1,
                  beforeAccount.external.2.2, state.external.2.2.2.2.2 cells present⟩
              have call : Semantics.EvalCall functions (RuntimeCodeEffectsSemantics.effects image) name type sources
                  (sourceRuntime initial) result _ := .external absent notPrimitive computed
              obtain ⟨target, finalStore, evaluated, finalLinked⟩ :=
                LinkedCodeWorldCorrespondence.external_preserves codeLayout
                  (patched layout baseline initial.external) slots image passive
                  memoryMember worldMember addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
                  logsMember logSizeMember balancesMember (codeMembers cells present).1 (codeMembers cells present).2 anchors
                  (runtime_enabled enabled computed) notFunction call typeCompiled compiled related packed runtime codeState installed linked
              exact ⟨target, finalStore, evaluated, finalLinked⟩
          | none =>
              have disabled : withCode = false := by simpa only [present, Option.isSome_none] using mode.symm
              have accountEnabled := account_enabled (disabled ▸ enabled) computed
              cases computed with
              | runtime computed =>
                  have call : Semantics.EvalCall functions RuntimeAccountEffectsSemantics.effects name type sources
                      (sourceRuntime initial) result _ := .external absent notPrimitive computed
                  obtain ⟨target, finalStore, evaluated, finalLinked⟩ :=
                    LinkedAccountWorldCorrespondence.external_preserves layout.toAccountLayout
                      (patched layout baseline initial.external) slots passive
                      memoryMember worldMember addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
                      logsMember logSizeMember balancesMember anchors accountEnabled notFunction call typeCompiled compiled related packed runtime
                      (account_related state) installed linked
                  exact ⟨target, finalStore, evaluated, finalLinked⟩
              | copy computed =>
                  obtain ⟨operation, named⟩ := computed.named
                  subst name
                  exact False.elim (code_unsupported operation accountEnabled)
      | copy computed =>
          have named := computed.named
          subst name
          intro typeFuel expected typeCompiled scope arguments lowered compiled world mapping environment initialStore argumentStore targets codes locations captured related packed runtime state installed linked
          have beforeAccount := account_related state
          have beforeLog := RuntimeAccountEffectsCorrespondence.runtime_related beforeAccount
          have beforeEnvironment := RuntimeLogEffectsCorrespondence.runtime_related beforeLog
          have beforeRuntime := RuntimeEnvironmentEffectsCorrespondence.runtime_related beforeEnvironment
          obtain ⟨target, finalStore, resultRelated, evaluated, memoryFinal, storageFinal, frame, retained, worldRead⟩ :=
            ReadOnlyWorldBuiltinCorrespondence.ReturnData.preserves compiled computed related runtime
              memoryMember memorySizeMember exitMember offsetMember sizeMember dataMember dataSizeMember
              (data_related state) (size_related state)
              (RuntimeEffectsCorrespondence.memory_related beforeRuntime)
              (RuntimeEffectsCorrespondence.storage_related beforeRuntime) packed
          have unchanged := copy_world computed
          exact ⟨target, finalStore, evaluated, by
            change RuntimeLinkedWorldCorrespondence.StateRel anchors _ layout.storage.world finalStore
            simpa only [RuntimeReturnDataEffectsSemantics.withRuntime, RuntimeFullEffectsSemantics.withRuntime, unchanged] using linked.read_preserved worldRead
            ⟩
      | guard computed =>
          have named := computed.named
          subst name
          intro typeFuel expected typeCompiled scope arguments lowered compiled world mapping environment initialStore argumentStore targets codes locations captured related packed runtime state installed linked
          obtain ⟨target, resultRelated, evaluated⟩ := MemoryGuardBuiltinCorrespondence.preserves compiled computed related packed
          exact ⟨target, argumentStore, evaluated, linked⟩

end Solcore.Frontend.RustHull.LinkedBuiltinWorldCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeLinkedStateCorrespondence
/-! Code links strengthen any concrete prefix-based runtime model. The source
world and the exact encoded world share one witness, including executable IDs. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeLinkedStateCorrespondence
open Correspondence

def LinkedRead (anchors : List CatalogWorldCorrespondence.Anchor) (source : StorageSemantics.World)
    (location : Nat) (read : Nat → Option Core.Value) : Prop :=
  ∃ accounts : StorageCorrespondence.Accounts, accounts.map Prod.fst = source ∧
    CatalogWorldCorrespondence.Links anchors accounts ∧ read location = some (StorageCorrespondence.world accounts)

def model {σ : Type} (boundary : Nat) (resources : σ → (Nat → Option Core.Value) → Prop)
    (anchors : List CatalogWorldCorrespondence.Anchor) (worldLocation : Nat)
    (sourceWorld : σ → StorageSemantics.World) : StateModel σ :=
  StateModel.cutoff boundary (fun state read => resources state read ∧ LinkedRead anchors (sourceWorld state) worldLocation read)

theorem base_related {σ : Type} {boundary : Nat} {resources : σ → (Nat → Option Core.Value) → Prop}
    {anchors : List CatalogWorldCorrespondence.Anchor} {worldLocation : Nat} {sourceWorld : σ → StorageSemantics.World}
    {world : World} {state : Semantics.State σ} {store : Core.Store}
    (related : StateRel (model boundary resources anchors worldLocation sourceWorld) world state store) :
    StateRel (StateModel.cutoff boundary resources) world state store :=
  ⟨related.toHeapRel, related.external.1, related.external.2.1, related.external.2.2.1⟩

theorem linked_related {σ : Type} {boundary : Nat} {resources : σ → (Nat → Option Core.Value) → Prop}
    {anchors : List CatalogWorldCorrespondence.Anchor} {worldLocation : Nat} {sourceWorld : σ → StorageSemantics.World}
    {world : World} {state : Semantics.State σ} {store : Core.Store}
    (below : worldLocation < boundary)
    (related : StateRel (model boundary resources anchors worldLocation sourceWorld) world state store) :
    RuntimeLinkedWorldCorrespondence.StateRel anchors (sourceWorld state.external) worldLocation store := by
  obtain ⟨accounts, source, linked, read⟩ := related.external.2.2.2
  exact ⟨accounts, source, linked, by simpa only [prefixRead, below, ↓reduceIte] using read⟩

theorem of_base {σ : Type} {boundary : Nat} {resources : σ → (Nat → Option Core.Value) → Prop}
    {anchors : List CatalogWorldCorrespondence.Anchor} {worldLocation : Nat} {sourceWorld : σ → StorageSemantics.World}
    {world : World} {state : Semantics.State σ} {store : Core.Store}
    (below : worldLocation < boundary)
    (related : StateRel (StateModel.cutoff boundary resources) world state store)
    (linked : RuntimeLinkedWorldCorrespondence.StateRel anchors (sourceWorld state.external) worldLocation store) :
    StateRel (model boundary resources anchors worldLocation sourceWorld) world state store := by
  obtain ⟨accounts, source, links, read⟩ := linked
  exact ⟨related.toHeapRel, related.external.1, related.external.2.1, related.external.2.2,
    accounts, source, links, by simpa only [prefixRead, below, ↓reduceIte] using read⟩

end Solcore.Frontend.RustHull.RuntimeLinkedStateCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeLinkedReturnDataStateCorrespondence
/-! Call-free child frames preserve exact executable identities alongside their
ordinary runtime state. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeLinkedReturnDataEffectsCorrespondence
open Correspondence
open RuntimeReturnDataEffectsCorrespondence (Layout Resources)
abbrev Anchors := List CatalogWorldCorrespondence.Anchor

def sourceWorld (state : RuntimeReturnDataEffectsSemantics.State) : StorageSemantics.World :=
  state.runtime.runtime.runtime.runtime.storage.world

def model (layout : Layout) (baseline : Nat → Option Core.Value) (slots : List EffectSlot)
    (image : Option (List UInt8)) (anchors : Anchors) : StateModel RuntimeReturnDataEffectsSemantics.State :=
  RuntimeLinkedStateCorrespondence.model layout.boundary (Resources layout baseline slots image)
    anchors layout.storage.world sourceWorld

theorem world_below (layout : Layout) : layout.storage.world < layout.boundary :=
  layout.below _ (by simp [StorageBuiltinCorrespondence.Locations.all])

theorem base_related {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    {image : Option (List UInt8)} {anchors : Anchors} {world : World}
    {state : Semantics.State RuntimeReturnDataEffectsSemantics.State} {store : Core.Store}
    (related : StateRel (model layout baseline slots image anchors) world state store) :
    StateRel (RuntimeReturnDataEffectsCorrespondence.model layout baseline slots image) world state store :=
  RuntimeLinkedStateCorrespondence.base_related related

theorem linked_related {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    {image : Option (List UInt8)} {anchors : Anchors} {world : World}
    {state : Semantics.State RuntimeReturnDataEffectsSemantics.State} {store : Core.Store}
    (related : StateRel (model layout baseline slots image anchors) world state store) :
    RuntimeLinkedWorldCorrespondence.StateRel anchors (sourceWorld state.external) layout.storage.world store :=
  RuntimeLinkedStateCorrespondence.linked_related (world_below layout) related

theorem of_base {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    {image : Option (List UInt8)} {anchors : Anchors} {world : World}
    {state : Semantics.State RuntimeReturnDataEffectsSemantics.State} {store : Core.Store}
    (related : StateRel (RuntimeReturnDataEffectsCorrespondence.model layout baseline slots image) world state store)
    (linked : RuntimeLinkedWorldCorrespondence.StateRel anchors (sourceWorld state.external) layout.storage.world store) :
    StateRel (model layout baseline slots image anchors) world state store :=
  RuntimeLinkedStateCorrespondence.of_base (world_below layout) related linked

end Solcore.Frontend.RustHull.RuntimeLinkedReturnDataEffectsCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeLinkedReturnDataEffectsCorrespondence
/-! The same actual builtin evaluation carries both runtime state and exact
catalog links, so recursive source execution retains executable identity. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeLinkedReturnDataEffectsCorrespondence
open Correspondence ScalarExecution DerivationCorrespondence
open RuntimeReturnDataEffectsCorrespondence (Layout supported)

theorem external_preserves (layout : Layout) (baseline : Nat → Option Core.Value)
    (slots : List EffectSlot) (image : Option (List UInt8)) (withCode : Bool) (passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots)
    (memoryMember : ⟨"memory", Core.WordMapping.type, layout.memory⟩ ∈ slots)
    (worldMember : ⟨"world", AccountState.type, layout.storage.world⟩ ∈ slots)
    (addressMember : ⟨"address", .word, layout.storage.address⟩ ∈ slots)
    (completeMember : ⟨"worldComplete", .bool, layout.storage.complete⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, layout.storage.isStatic⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, layout.storage.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, layout.storage.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, layout.storage.returnSize⟩ ∈ slots)
    (logsMember : ⟨"logs", Core.WordMapping.type, layout.logs⟩ ∈ slots)
    (logSizeMember : ⟨"logSize", .word, layout.logSize⟩ ∈ slots)
    (balancesMember : ⟨"balances", Core.WordMapping.type, layout.balances⟩ ∈ slots)
    (codeMembers : ∀ cells, layout.codeCells = some cells →
      (⟨"code", Core.WordMapping.type, cells.code⟩ ∈ slots ∧ ⟨"codeKnown", .bool, cells.known⟩ ∈ slots))
    (dataMember : ⟨"returnData", Core.WordMapping.type, layout.returnData⟩ ∈ slots)
    (dataSizeMember : ⟨"returnDataSize", .word, layout.returnDataSize⟩ ∈ slots)
    (mode : layout.codeCells.isSome = withCode) (anchors : Anchors) :
    ExternalCallPreservation (supported slots withCode) (model layout baseline slots image anchors) slots
      (RuntimeReturnDataEffectsSemantics.effects image) := by
  intro functions name type sources initial final result enabled notFunction called
  intro typeFuel expected typeCompiled scope arguments lowered compiled world mapping environment initialStore argumentStore targets codes locations captured related packed runtime state installed
  have base := base_related state
  obtain ⟨target, finalStore, resultRelated, evaluated, finalState, installedFinal, retained⟩ :=
    RuntimeReturnDataEffectsCorrespondence.external_preserves layout baseline slots image withCode passive memoryMember worldMember addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember logsMember logSizeMember balancesMember codeMembers dataMember dataSizeMember mode
      enabled notFunction called typeCompiled compiled related packed runtime base installed
  obtain ⟨linkedTarget, linkedStore, linkedEvaluated, finalLinked⟩ :=
    LinkedBuiltinWorldCorrespondence.external_preserves layout baseline slots image withCode passive memoryMember worldMember addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember logsMember logSizeMember balancesMember codeMembers dataMember dataSizeMember mode anchors
      enabled notFunction called typeCompiled compiled related packed runtime base installed (linked_related state)
  have same := Core.evaluation_deterministic evaluated linkedEvaluated
  cases same.2
  exact ⟨target, finalStore, resultRelated, evaluated, of_base finalState finalLinked, installedFinal, retained⟩

theorem assemble_program (layout : Layout) (baseline : Nat → Option Core.Value)
    (slots : List EffectSlot) (image : Option (List UInt8)) (withCode : Bool) (passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots)
    (memoryMember : ⟨"memory", Core.WordMapping.type, layout.memory⟩ ∈ slots)
    (worldMember : ⟨"world", AccountState.type, layout.storage.world⟩ ∈ slots)
    (addressMember : ⟨"address", .word, layout.storage.address⟩ ∈ slots)
    (completeMember : ⟨"worldComplete", .bool, layout.storage.complete⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, layout.storage.isStatic⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, layout.storage.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, layout.storage.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, layout.storage.returnSize⟩ ∈ slots)
    (logsMember : ⟨"logs", Core.WordMapping.type, layout.logs⟩ ∈ slots)
    (logSizeMember : ⟨"logSize", .word, layout.logSize⟩ ∈ slots)
    (balancesMember : ⟨"balances", Core.WordMapping.type, layout.balances⟩ ∈ slots)
    (codeMembers : ∀ cells, layout.codeCells = some cells →
      (⟨"code", Core.WordMapping.type, cells.code⟩ ∈ slots ∧ ⟨"codeKnown", .bool, cells.known⟩ ∈ slots))
    (dataMember : ⟨"returnData", Core.WordMapping.type, layout.returnData⟩ ∈ slots)
    (dataSizeMember : ⟨"returnDataSize", .word, layout.returnDataSize⟩ ∈ slots)
    (mode : layout.codeCells.isSome = withCode) (anchors : Anchors)
    {functions : List Function} {function : Function} {entry : String} {runtime : Scope}
    {fuel : Nat} {own : Signature} {allocated : Core.Expr}
    (accepted : assemble functions entry runtime fuel = .ok (own, allocated))
    (selected : functions.find? (·.name == entry) = some function)
    (eligible : ExecutableProgram (supported slots withCode) functions)
    {sources : List Semantics.Value} {targets : List Core.Value}
    (values : ValuesRel own.parameters sources targets)
    {initial final : Semantics.State RuntimeReturnDataEffectsSemantics.State}
    {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction functions (RuntimeReturnDataEffectsSemantics.effects image)
      function sources initial sourceResult final)
    {world : World} {runtimeValues caller : Core.Environment} {store : Core.Store}
    (runtimeLength : runtimeValues.length = runtime.length)
    (covered : ScopeCoverage [] runtime)
    (runtimeRelated : EffectEnvironmentRel slots runtime Core.Renaming.id
      (runtimeValues ++ bundleValues targets :: caller))
    (separated : EffectSlotsSeparate slots)
    (state : StateRel (model layout baseline slots image anchors) world initial store) :
    ∃ extension target finalStore,
      ResultRel own.result sourceResult target ∧
      Core.Evaluates (runtimeValues ++ bundleValues targets :: caller) store allocated target finalStore ∧
      StateRel (model layout baseline slots image anchors) (world ++ extension) final finalStore ∧
      ClosuresPreserved store finalStore :=
  assemble_recursive_program_effects accepted selected
    (external_preserves layout baseline slots image withCode passive memoryMember worldMember addressMember completeMember staticMember
      memorySizeMember exitMember offsetMember sizeMember logsMember logSizeMember balancesMember codeMembers dataMember dataSizeMember mode anchors) eligible values evaluated
    runtimeLength covered runtimeRelated separated state


end Solcore.Frontend.RustHull.RuntimeLinkedReturnDataEffectsCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeLinkedReturnDataEffectsFrameCorrespondence
/-! Source return-data operations reach actual frame calls and final snapshots.
The same proof covers ordinary frames and frames with linked code slots. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeLinkedReturnDataEffectsFrameCorrespondence
open Correspondence ScalarExecution DerivationCorrespondence
open RuntimeReturnDataEffectsCorrespondence (Layout)
open RuntimeLinkedReturnDataEffectsCorrespondence (model base_related assemble_program)
private abbrev account_related := @RuntimeReturnDataEffectsCorrespondence.account_related
open RuntimeAccountEffectsCorrespondence (runtime_related balances_related)
open RuntimeReturnDataEffectsCorrespondence (supported)

abbrev slotTypes := RuntimeLogEffectsFrameCorrespondence.slotTypes
abbrev cell_observed := @RuntimeLogEffectsFrameCorrespondence.cell_observed
def snapshotValues (state : RuntimeReturnDataEffectsSemantics.State) :=
  RuntimeAccountEffectsFrameCorrespondence.snapshotValues state.runtime

/-- A frame installed earlier retains its captured environment. The body and
completion wrapper observe the final source world and balances through the
compiler's actual frame references. -/
theorem compileFrame_call_preserves_observed {program : Program} {code : CodeBlock} {slots : List EffectSlot}
    {fuel : Nat} {compiled : Core.Expr} {withCode : Bool}
    (accepted : AccountRuntime.compileFrame program code (slotTypes slots) fuel = .ok compiled)
    (eligible : ExecutableProgram (supported slots withCode)
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {layout : Layout} {image : Option (List UInt8)} {anchors : List CatalogWorldCorrespondence.Anchor}
    {initial : RuntimeReturnDataEffectsSemantics.State}
    {before initialStore store : Core.Store} {values environment captured : Core.Environment}
    {function argument : Core.Expr} {closure : Core.Value}
    (closureRelated : CapturedClosure compiled captured closure)
    (resolved : Core.Evaluates environment before function closure initialStore)
    (supplied : Core.Evaluates environment initialStore argument (bundleValues values) store)
    (length : values.length = slots.length)
    (runtime : EffectEnvironmentRel slots (AccountRuntime.frameScope (slotTypes slots)) Core.Renaming.id
      (values.reverse ++ .unit :: bundleValues values :: captured))
    (separated : EffectSlotsSeparate slots)
    (memoryMember : ⟨"memory", Core.WordMapping.type, layout.memory⟩ ∈ slots)
    (worldMember : ⟨"world", AccountState.type, layout.storage.world⟩ ∈ slots)
    (addressMember : ⟨"address", .word, layout.storage.address⟩ ∈ slots)
    (completeMember : ⟨"worldComplete", .bool, layout.storage.complete⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, layout.storage.isStatic⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, layout.storage.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, layout.storage.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, layout.storage.returnSize⟩ ∈ slots)
    (logsMember : ⟨"logs", Core.WordMapping.type, layout.logs⟩ ∈ slots)
    (logSizeMember : ⟨"logSize", .word, layout.logSize⟩ ∈ slots)
    (balancesMember : ⟨"balances", Core.WordMapping.type, layout.balances⟩ ∈ slots)
    (codeMembers : ∀ cells, layout.codeCells = some cells →
      ⟨"code", Core.WordMapping.type, cells.code⟩ ∈ slots ∧ ⟨"codeKnown", .bool, cells.known⟩ ∈ slots)
    (dataMember : ⟨"returnData", Core.WordMapping.type, layout.returnData⟩ ∈ slots)
    (dataSizeMember : ⟨"returnDataSize", .word, layout.returnDataSize⟩ ∈ slots)
    (mode : layout.codeCells.isSome = withCode)
    (initialRelated : StateRel (model layout (prefixRead layout.boundary store) slots image anchors) [] ⟨[], initial⟩ store)
    (passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots)
    {final : Semantics.State RuntimeReturnDataEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) (RuntimeReturnDataEffectsSemantics.effects image)
      (AccountRuntime.frameFunction code) [] ⟨[], initial⟩ result final) :
    ∃ extension status accounts finalStore,
      accounts.map Prod.fst = final.external.runtime.runtime.runtime.runtime.storage.world ∧
      ResultRel .unit result status ∧
      Core.Evaluates environment before (.apply function argument)
        (frameCompletionValue status (snapshotValues final.external accounts)
          (StorageCorrespondence.get accounts final.external.runtime.runtime.runtime.runtime.storage.address final.external.runtime.runtime.runtime.runtime.storage.complete)) finalStore ∧
      StateRel (model layout (prefixRead layout.boundary store) slots image anchors)
        extension final finalStore ∧
      finalStore.read? layout.storage.world = some (StorageCorrespondence.world accounts) := by
  obtain ⟨own, body, cells, assembled, references, rfl⟩ := compileFrame_components accepted
  have selected := MemoryFrameCorrespondence.frame_selected accepted
  obtain ⟨signatures, codes, selectedFunction, selectedCode, index, _, sourceSelected,
    signatureCompiled, _, _, _, _, _⟩ := assemble_selection assembled
  have sameFunction := Option.some.inj (sourceSelected.symm.trans selected)
  subst selectedFunction
  obtain ⟨parameters, resultType⟩ := MemoryFrameCorrespondence.frame_signature signatureCompiled
  have argumentValues : ValuesRel own.parameters [] [] := by rw [parameters]; exact .nil
  obtain ⟨extension, status, bodyStore, related, executed, state, _⟩ :=
    assemble_program layout (prefixRead layout.boundary store) slots image withCode passive
      memoryMember worldMember addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
      logsMember logSizeMember balancesMember codeMembers dataMember dataSizeMember mode anchors assembled selected eligible argumentValues evaluated
      (runtimeValues := values.reverse) (caller := bundleValues values :: captured)
      (by simpa [AccountRuntime.frameScope, slotTypes, MemoryFrameCorrespondence.slotTypes] using length)
      (MemoryFrameCorrespondence.frame_coverage _) runtime separated
      initialRelated
  have finalStorage := RuntimeEffectsCorrespondence.storage_related
    (RuntimeEnvironmentEffectsCorrespondence.runtime_related (RuntimeLogEffectsCorrespondence.runtime_related (runtime_related (account_related (base_related state)))))
  have finalLogs := RuntimeLogEffectsCorrespondence.logs_related (runtime_related (account_related (base_related state)))
  obtain ⟨accounts, sourceWorld, worldRead⟩ := finalStorage.world
  have finalWorld := cell_observed references runtime worldMember worldRead
  have finalAddress := cell_observed references runtime addressMember finalStorage.address
  have finalComplete := cell_observed references runtime completeMember finalStorage.complete
  have finalSnapshot : ∀ name ∈ frameSnapshotNames,
      FrameCellObserved cells (values.reverse ++ .unit :: bundleValues values :: captured)
        bodyStore name (snapshotValues final.external accounts name) := by
    intro name member
    simp [frameSnapshotNames] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact cell_observed references runtime exitMember finalStorage.exit
    · exact cell_observed references runtime offsetMember finalStorage.returnOffset
    · exact cell_observed references runtime sizeMember finalStorage.returnSize
    · exact cell_observed references runtime memoryMember finalLogs.logs.memory
    · exact cell_observed references runtime logsMember finalLogs.logs.logs
    · exact cell_observed references runtime logSizeMember finalLogs.logs.logSize
    · exact cell_observed references runtime balancesMember (balances_related (account_related (base_related state)))
    · exact finalWorld
  have completed := frameCompletion_evaluates executed accounts final.external.runtime.runtime.runtime.runtime.storage.address final.external.runtime.runtime.runtime.runtime.storage.complete
    finalWorld finalAddress finalComplete finalSnapshot
  obtain ⟨suffix, _, extended⟩ := StorageCorrespondence.getStore_extension accounts
    final.external.runtime.runtime.runtime.runtime.storage.address final.external.runtime.runtime.runtime.runtime.storage.complete
    (status :: (values.reverse ++ .unit :: bundleValues values :: captured)) bodyStore
  refine ⟨extension, status, accounts, _, sourceWorld, by simpa only [resultType] using related,
    frameUnpack_call_evaluates (by simpa only [slotTypes, MemoryFrameCorrespondence.slotTypes, List.length_map] using length)
      closureRelated resolved supplied completed, ?_, ?_⟩
  · rw [show bundleValues ([] : List Core.Value) = .unit from rfl, extended]
    simpa only [List.nil_append] using state.appendCore suffix
  · rw [show bundleValues ([] : List Core.Value) = .unit from rfl, extended]
    exact ((StoreRetains.append bodyStore suffix).read layout.storage.world
      (List.getElem?_eq_some_iff.mp worldRead).1).trans worldRead

theorem compileFrame_call_preserves {program : Program} {code : CodeBlock} {slots : List EffectSlot}
    {fuel : Nat} {compiled : Core.Expr} {withCode : Bool}
    (accepted : AccountRuntime.compileFrame program code (slotTypes slots) fuel = .ok compiled)
    (eligible : ExecutableProgram (supported slots withCode)
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {layout : Layout} {image : Option (List UInt8)} {anchors : List CatalogWorldCorrespondence.Anchor}
    {initial : RuntimeReturnDataEffectsSemantics.State}
    {before initialStore store : Core.Store} {values environment captured : Core.Environment}
    {function argument : Core.Expr} {closure : Core.Value}
    (closureRelated : CapturedClosure compiled captured closure)
    (resolved : Core.Evaluates environment before function closure initialStore)
    (supplied : Core.Evaluates environment initialStore argument (bundleValues values) store)
    (length : values.length = slots.length)
    (runtime : EffectEnvironmentRel slots (AccountRuntime.frameScope (slotTypes slots)) Core.Renaming.id
      (values.reverse ++ .unit :: bundleValues values :: captured))
    (separated : EffectSlotsSeparate slots)
    (memoryMember : ⟨"memory", Core.WordMapping.type, layout.memory⟩ ∈ slots)
    (worldMember : ⟨"world", AccountState.type, layout.storage.world⟩ ∈ slots)
    (addressMember : ⟨"address", .word, layout.storage.address⟩ ∈ slots)
    (completeMember : ⟨"worldComplete", .bool, layout.storage.complete⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, layout.storage.isStatic⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, layout.storage.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, layout.storage.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, layout.storage.returnSize⟩ ∈ slots)
    (logsMember : ⟨"logs", Core.WordMapping.type, layout.logs⟩ ∈ slots)
    (logSizeMember : ⟨"logSize", .word, layout.logSize⟩ ∈ slots)
    (balancesMember : ⟨"balances", Core.WordMapping.type, layout.balances⟩ ∈ slots)
    (codeMembers : ∀ cells, layout.codeCells = some cells →
      ⟨"code", Core.WordMapping.type, cells.code⟩ ∈ slots ∧ ⟨"codeKnown", .bool, cells.known⟩ ∈ slots)
    (dataMember : ⟨"returnData", Core.WordMapping.type, layout.returnData⟩ ∈ slots)
    (dataSizeMember : ⟨"returnDataSize", .word, layout.returnDataSize⟩ ∈ slots)
    (mode : layout.codeCells.isSome = withCode)
    (initialRelated : StateRel (model layout (prefixRead layout.boundary store) slots image anchors) [] ⟨[], initial⟩ store)
    (passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots)
    {final : Semantics.State RuntimeReturnDataEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) (RuntimeReturnDataEffectsSemantics.effects image)
      (AccountRuntime.frameFunction code) [] ⟨[], initial⟩ result final) :
    ∃ extension status accounts finalStore,
      accounts.map Prod.fst = final.external.runtime.runtime.runtime.runtime.storage.world ∧
      ResultRel .unit result status ∧
      Core.Evaluates environment before (.apply function argument)
        (frameCompletionValue status (snapshotValues final.external accounts)
          (StorageCorrespondence.get accounts final.external.runtime.runtime.runtime.runtime.storage.address final.external.runtime.runtime.runtime.runtime.storage.complete)) finalStore ∧
      StateRel (model layout (prefixRead layout.boundary store) slots image anchors)
        extension final finalStore := by
  obtain ⟨extension, status, accounts, finalStore, represented, related, executed, state, _⟩ :=
    compileFrame_call_preserves_observed accepted eligible closureRelated resolved supplied length runtime separated
      memoryMember worldMember addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
      logsMember logSizeMember balancesMember codeMembers dataMember dataSizeMember mode initialRelated passive evaluated
  exact ⟨extension, status, accounts, finalStore, represented, related, executed, state⟩

/-- Direct evaluation of freshly compiled frame code is a special case of the
same theorem for captured calls. -/
theorem compileFrame_preserves {program : Program} {code : CodeBlock} {slots : List EffectSlot}
    {fuel : Nat} {compiled : Core.Expr} {withCode : Bool}
    (accepted : AccountRuntime.compileFrame program code (slotTypes slots) fuel = .ok compiled)
    (eligible : ExecutableProgram (supported slots withCode)
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {layout : Layout} {image : Option (List UInt8)} {anchors : List CatalogWorldCorrespondence.Anchor}
    {initial : RuntimeReturnDataEffectsSemantics.State}
    {initialStore store : Core.Store} {values environment : Core.Environment} {argument : Core.Expr}
    (supplied : Core.Evaluates environment initialStore argument (bundleValues values) store)
    (length : values.length = slots.length)
    (runtime : EffectEnvironmentRel slots (AccountRuntime.frameScope (slotTypes slots)) Core.Renaming.id
      (values.reverse ++ .unit :: bundleValues values :: environment))
    (separated : EffectSlotsSeparate slots)
    (memoryMember : ⟨"memory", Core.WordMapping.type, layout.memory⟩ ∈ slots)
    (worldMember : ⟨"world", AccountState.type, layout.storage.world⟩ ∈ slots)
    (addressMember : ⟨"address", .word, layout.storage.address⟩ ∈ slots)
    (completeMember : ⟨"worldComplete", .bool, layout.storage.complete⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, layout.storage.isStatic⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, layout.storage.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, layout.storage.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, layout.storage.returnSize⟩ ∈ slots)
    (logsMember : ⟨"logs", Core.WordMapping.type, layout.logs⟩ ∈ slots)
    (logSizeMember : ⟨"logSize", .word, layout.logSize⟩ ∈ slots)
    (balancesMember : ⟨"balances", Core.WordMapping.type, layout.balances⟩ ∈ slots)
    (codeMembers : ∀ cells, layout.codeCells = some cells →
      ⟨"code", Core.WordMapping.type, cells.code⟩ ∈ slots ∧ ⟨"codeKnown", .bool, cells.known⟩ ∈ slots)
    (dataMember : ⟨"returnData", Core.WordMapping.type, layout.returnData⟩ ∈ slots)
    (dataSizeMember : ⟨"returnDataSize", .word, layout.returnDataSize⟩ ∈ slots)
    (mode : layout.codeCells.isSome = withCode)
    (initialRelated : StateRel (model layout (prefixRead layout.boundary store) slots image anchors) [] ⟨[], initial⟩ store)
    (passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots)
    {final : Semantics.State RuntimeReturnDataEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) (RuntimeReturnDataEffectsSemantics.effects image)
      (AccountRuntime.frameFunction code) [] ⟨[], initial⟩ result final) :
    ∃ extension status accounts finalStore,
      accounts.map Prod.fst = final.external.runtime.runtime.runtime.runtime.storage.world ∧
      ResultRel .unit result status ∧
      Core.Evaluates environment initialStore (.apply compiled argument)
        (frameCompletionValue status (snapshotValues final.external accounts)
          (StorageCorrespondence.get accounts final.external.runtime.runtime.runtime.runtime.storage.address final.external.runtime.runtime.runtime.runtime.storage.complete)) finalStore ∧
      StateRel (model layout (prefixRead layout.boundary store) slots image anchors)
        extension final finalStore := by
  obtain ⟨own, body, cells, _, _, rfl⟩ := compileFrame_components accepted
  exact compileFrame_call_preserves accepted eligible (CapturedClosure.lambda _ _ _ environment)
    Core.Evaluates.lambda supplied length runtime separated memoryMember worldMember addressMember completeMember
    staticMember memorySizeMember exitMember offsetMember sizeMember logsMember logSizeMember balancesMember codeMembers dataMember dataSizeMember mode initialRelated passive
    evaluated

end Solcore.Frontend.RustHull.RuntimeLinkedReturnDataEffectsFrameCorrespondence
end
