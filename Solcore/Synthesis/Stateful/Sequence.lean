import Lean.Data.Json
import Solcore.Synthesis.Core.Seed
import Solcore.ContractRuntime.WorldState
import Solcore.Core.WordMapping
import Solcore.Synthesis.Core.StdDispatch
import Solcore.ContractRuntime.CheckedCoreContract

/-!
# Stateful sequences

Transaction sequences, the storage observation and std calldata shared by the stateful profiles.
Main declarations: `Sequence.maxTransactions`, `Sequence.blocks`, `AccountStorage.contractJson`,
`StdCalldata`.
-/

section
-- leanmerge: from Solcore.Synthesis.Stateful.Sequence
/-! Generated stateful sequences: the bound on a scenario's ordered
transactions, shared by the case modules and the imported-Hull scenario
runners, and the three-transaction blocks a generated sequence is drawn from.
Three transactions are exactly the original single-block sequence. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Stateful.Sequence
open Lean Solcore.Synthesis.Core

/-- A stateful scenario has one to eight ordered transactions. Generation keeps
three unless a longer random sequence is requested, and the fixed corpora keep
one to three. -/
def maxTransactions : Nat := 8

/-- The number of three-transaction blocks that `count` transactions use. -/
def blockCount (count : Nat) : Nat := (count + 2) / 3

/-- Block zero uses the scenario seed. Block `k + 1` uses the high half of draw
`k + 1` of a separate stream: the low bits of a power-of-two LCG have short
periods. -/
def blockSeeds (seed : Seed) (blocks : Nat) : List Seed := Id.run do
  let mut state := Seed.ofNat (seed.toNat ^^^ 0x74782d626c6f636b)
  let mut seeds : Array Seed := #[]
  for block in List.range blocks do
    if block == 0 then
      seeds := seeds.push seed
    else
      let (value, next) := state.draw
      seeds := seeds.push (Seed.ofNat (value.toNat / 2 ^ 32))
      state := next
  return seeds.toList

/-- The first `count` elements of consecutive blocks; `block` draws one block
from its seed, given the index of the block's first transaction. -/
def blocks {α : Type} (block : Seed → Nat → List α) (seed : Seed) (count : Nat) : List α :=
  ((blockSeeds seed (blockCount count)).zipIdx.flatMap fun (blockSeed, index) =>
    block blockSeed (3 * index)).take count

/-- The sequence choices of every block that `count` transactions use. -/
def blockChoices (choices : Seed → List Nat) (seed : Seed) (count : Nat) : List Nat :=
  (blockSeeds seed (blockCount count)).flatMap choices

def checkCount (count : Nat) : Except String Unit :=
  unless 1 ≤ count && count ≤ maxTransactions do
    throw s!"a generated sequence has 1 to {maxTransactions} transactions"

/-- A generated origin records a transaction count other than three. -/
def recordCount (origin : Json) (count : Nat) : Json :=
  if count == 3 then origin else origin.setObjVal! "transactionCount" (toJson count)

/-- A generated origin's transaction count; a recorded three is noncanonical. -/
def savedCount (origin : Json) : Except String Nat :=
  match origin.getObjVal? "transactionCount" with
  | .error _ => return 3
  | .ok value => do
      let count ← value.getNat?
      checkCount count
      if count == 3 then throw "a saved origin records the default transaction count"
      return count

end Solcore.Synthesis.Stateful.Sequence
end

section
-- leanmerge: from Solcore.Synthesis.Stateful.AccountStorage
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
end

section
-- leanmerge: from Solcore.Synthesis.Stateful.StdCalldata
/-! A second model of the pinned std's dispatcher and lazy calldata decoder,
written over the calldata bytes instead of in Core and shared by the
malformed-calldata profiles. Natural arithmetic cannot wrap, as std's checked
word arithmetic does not. The changes every malformation shares are applied to
a canonical encoding here; each profile names the positions of its own Words. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Stateful.StdCalldata
open Solcore.Core (Word)
open Solcore.ContractRuntime (encodeWordBytesBE encodeBytesText)
open Solcore.Synthesis.Core.StdDispatch (noSelectorError truncatedError maxLength)

/-- Calldata of every transaction stays within one KiB. -/
def maxCalldata : Nat := 1024

/-- The byte at an index, zero past the end; callers read only present bytes. -/
def byteAt (bytes : ByteArray) (index : Nat) : Nat :=
  (bytes.data[index]?.map UInt8.toNat).getD 0

def bigEndian (bytes : ByteArray) (offset count : Nat) : Nat :=
  (List.range count).foldl (fun total index => total * 256 + byteAt bytes (offset + index)) 0

def wordAt (bytes : ByteArray) (offset : Nat) : Nat := bigEndian bytes offset 32

def replaceWord (bytes : ByteArray) (offset : Nat) (value : Word) : ByteArray :=
  bytes.extract 0 offset ++ encodeWordBytesBE value ++ bytes.extract (offset + 32) bytes.size

/-- Trailing bytes are zeros (0), `0xff` (1) or the ramp `1, 2, 3, ...` (2). -/
def patternNames : List String := ["zeros", "ones", "ramp"]

def patternByte (pattern position : Nat) : UInt8 :=
  match pattern with
  | 0 => 0
  | 1 => 0xff
  | _ => (position + 1).toUInt8

/-- The change a malformation makes to a canonical encoding: none, a prefix of
the selector, a selector xor mask, a cut, trailing bytes, or one replaced Word
at a byte position. -/
inductive Change where
  | none
  | short (bytes : Nat)
  | selector (mask : Nat)
  | truncate (kept : Nat)
  | trailing (count pattern : Nat)
  | word (position : Nat) (value : Word)
  deriving BEq, Repr

def Change.apply (canonical : ByteArray) : Change → ByteArray
  | .none => canonical
  | .short bytes => canonical.extract 0 bytes
  | .selector mask =>
      let changed := (bigEndian canonical 0 4 ^^^ mask) % 2 ^ 32
      ByteArray.mk #[(changed / 2 ^ 24 % 256).toUInt8, (changed / 2 ^ 16 % 256).toUInt8,
        (changed / 2 ^ 8 % 256).toUInt8, (changed % 256).toUInt8] ++ canonical.extract 4 canonical.size
  | .truncate kept => canonical.extract 0 kept
  | .trailing count pattern => canonical ++ ByteArray.mk ((List.range count).map (patternByte pattern)).toArray
  | .word position value => replaceWord canonical position value

/-- A change within its bounds: selector prefixes, nonzero 32-bit masks, cuts
inside the calldata past the selector, one to 64 trailing bytes, and a Word
replaced inside the canonical encoding. -/
def Change.valid (canonicalSize : Nat) : Change → Bool
  | .none => true
  | .short bytes => bytes < 4
  | .selector mask => 0 < mask && mask < 2 ^ 32
  | .truncate kept => 4 ≤ kept && kept < canonicalSize
  | .trailing count pattern => 1 ≤ count && count ≤ 64 && pattern < 3
  | .word position _ => 4 ≤ position && position + 32 ≤ canonicalSize

/-- An error selector as its four bytes. -/
def selectorText (selector : Nat) : String :=
  encodeBytesText (ByteArray.mk #[(selector / 2 ^ 24 % 256).toUInt8, (selector / 2 ^ 16 % 256).toUInt8,
    (selector / 2 ^ 8 % 256).toUInt8, (selector % 256).toUInt8])

/-- std's dispatch and the head of `(uint256 flags, T value)` for a dynamic
`T`: the flags and the head offset `o`, once the default fallback is not
reached, the 64-byte head exists, `o <= size - 4` and 32 bytes remain at
`4 + o`. Otherwise the rejecting error selector. -/
def dynamicHead? (input : ByteArray) (selector : Nat) : Except Nat (Nat × Nat) :=
  let size := input.size
  if size < 4 then .error noSelectorError
  else if bigEndian input 0 4 != selector then .error noSelectorError
  else if size < 68 then .error truncatedError
  else
    let offset := wordAt input 36
    if offset > size - 4 then .error truncatedError
    else if size - (4 + offset) < 32 then .error truncatedError
    else .ok (wordAt input 4, offset)

/-- std's `checkArrayHead` for 32-byte elements, for an array whose length
Word is the 32 bytes at `start`: the length, once it is at most `~0 / 32` and
its elements fit after the length Word. -/
def arrayAt? (input : ByteArray) (start : Nat) : Except Nat Nat :=
  let length := wordAt input start
  if length > maxLength then .error truncatedError
  else if 32 * length > input.size - (start + 32) then .error truncatedError
  else .ok length

/-- std's lazy decode of row `index` of a dynamic-element array whose offset
table starts at `table`: the row's start and length, once its table Word `r`
satisfies `r <= size - table`, 32 bytes remain at `table + r` and the row passes
`arrayAt?`. -/
def rowAt? (input : ByteArray) (table index : Nat) : Except Nat (Nat × Nat) := do
  let size := input.size
  let entry := wordAt input (table + 32 * index)
  if entry > size - table then throw truncatedError
  if size - (table + entry) < 32 then throw truncatedError
  let length ← arrayAt? input (table + entry)
  return (table + entry, length)

end Solcore.Synthesis.Stateful.StdCalldata
end
