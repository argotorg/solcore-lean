import Solcore.Frontend.RustHull.StorageCorrespondence
import Solcore.Frontend.RustHull.ContractCatalogCorrespondence
import Solcore.Frontend.RustHull.Contract

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
