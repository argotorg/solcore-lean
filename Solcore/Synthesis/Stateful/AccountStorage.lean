import Solcore.ContractRuntime.WorldState
import Solcore.Core.WordMapping
import Lean.Data.Json

/-! The whole committed storage of the observed contract accounts, shared by the
original-Core observers and the imported-Hull scenario runners. Each account is
reported with its role, its bound address and every nonzero slot in strictly
increasing slot order, so zero and absent are the same observation. Original
Core enumerates its account exactly (`Account.mem_storageEntries_iff`); Hull's
committed entries are canonicalized to the value their lookup selects. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Stateful.AccountStorage
open Lean Solcore.Core Solcore.ContractRuntime

/-- The role of the one observed contract in the storage-family profiles. -/
def contractRole : String := "contract"

/-- Nonzero entries as ordered `{slot, value}` decimal Words. -/
def entriesJson (entries : List (Word × Word)) : Json :=
  toJson (entries.map fun (slot, value) => Json.mkObj [
    ("slot", toJson (toString slot.val)), ("value", toJson (toString value.val))])

/-- One observed account: its role, decimal address and whole storage. -/
def accountJson (role : String) (address : Nat) (entries : List (Word × Word)) : Json :=
  Json.mkObj [("role", toJson role), ("address", toJson (toString address)),
    ("storage", entriesJson entries)]

/-- Original Core: every observed account's exact storage enumeration in one
committed world, in role order. An absent account is reported as null, which
the comparison rejects. -/
def worldJson (world : WorldState) (accounts : List (String × Address)) : Json :=
  toJson (accounts.map fun (role, address) =>
    match world.account? address with
    | some account => accountJson role address.val account.storageEntries
    | none => Json.null)

/-- Original Core: the one observed contract of a storage-family profile. -/
def contractJson (world : WorldState) (address : Address) : Json :=
  worldJson world [(contractRole, address)]

/-- Apply the entries' writes so that the first entry for each key wins, as
`WordMapping.lookupEntries` selects it. -/
private def entriesAccount (entries : WordMapping.Entries) : Account :=
  entries.foldr (fun entry account => account.storageWrite entry.1 entry.2) Account.empty

private theorem entriesAccount_storageRead (entries : WordMapping.Entries) (slot : Word) :
    (entriesAccount entries).storageRead slot = WordMapping.lookupEntries slot entries := by
  induction entries with
  | nil => simp [entriesAccount, Account.storageRead_empty, WordMapping.lookupEntries]
  | cons entry rest ih =>
      obtain ⟨key, value⟩ := entry
      have unfolded : entriesAccount ((key, value) :: rest) = (entriesAccount rest).storageWrite key value := rfl
      rw [unfolded]
      by_cases same : slot = key
      · subst same
        simp [Account.storageRead_storageWrite_same, WordMapping.lookupEntries]
      · rw [Account.storageRead_storageWrite_other _ _ _ _ same, ih]
        simp [WordMapping.lookupEntries, same]

/-- Imported Hull: the value the entries' lookup selects for every distinct
key, zero values dropped, in strictly increasing slot order. -/
def canonicalEntries (entries : WordMapping.Entries) : List (Word × Word) :=
  (entriesAccount entries).storageEntries

/-- Canonicalization is exact: an entry is listed precisely when the lookup
selects that nonzero value. -/
theorem mem_canonicalEntries_iff (entries : WordMapping.Entries) (slot value : Word) :
    (slot, value) ∈ canonicalEntries entries ↔
      WordMapping.lookupEntries slot entries = value ∧ value ≠ Word.zero := by
  rw [canonicalEntries, ← entriesAccount_storageRead]
  constructor
  · intro member
    refine ⟨?_, Account.storageEntries_nonzero _ _ _ member⟩
    simp [Account.storageRead, (Account.mem_storageEntries_iff _ _ _).1 member]
  · rintro ⟨read, nonzero⟩
    apply (Account.mem_storageEntries_iff _ _ _).2
    cases stored : (entriesAccount entries).storageValue? slot with
    | none =>
        simp [Account.storageRead, stored] at read
        exact absurd read.symm nonzero
    | some found =>
        simp only [Account.storageRead, stored, Option.getD_some] at read
        rw [read]

theorem canonicalEntries_sorted (entries : WordMapping.Entries) :
    (canonicalEntries entries).Pairwise (fun left right => left.1.val < right.1.val) := by
  unfold canonicalEntries Account.storageEntries
  rw [List.pairwise_map]
  exact Account.storageSlots_sorted _

/-- Imported Hull: one observed account from its committed entries. -/
def hullAccountJson (role : String) (address : Word) (entries : WordMapping.Entries) : Json :=
  accountJson role address.val (canonicalEntries entries)

/-- A history row whose whole-storage observation omits the bound addresses,
to compare one contract's observations under different bindings. -/
def unbound (row : Json) : Json :=
  match row.getObjValAs? (List Json) "accountStorage" with
  | .ok accounts =>
      row.setObjVal! "accountStorage" (toJson (accounts.map fun account => account.setObjVal! "address" Json.null))
  | .error _ => row

/-- Whether a history row observes exactly the given addresses, in role order. -/
def boundTo (row : Json) (addresses : List Nat) : Bool :=
  match row.getObjValAs? (List Json) "accountStorage" with
  | .ok accounts => accounts.length == addresses.length && (accounts.zip addresses).all fun (account, address) =>
      (account.getObjValAs? String "address").toOption == some (toString address)
  | .error _ => false

end Solcore.Synthesis.Stateful.AccountStorage
