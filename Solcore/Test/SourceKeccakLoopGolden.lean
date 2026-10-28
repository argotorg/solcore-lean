import Solcore.Synthesis.Source.KeccakLoopCases

/-! Golden cases for the Keccak-loop profile. Every expected value is written
out by hand from the protocol, not computed by either model; only the slots
that hold the entries come from the independent `Solcore.Abi.V1.Keccak256`.
The steps add a known constant `c`, so iteration `i` writes
`entries[key] + acc + input + c` to the entry of its key
`(input & ~7) | (i & keyMask)` and then to `acc`, and logs the counter, the key
and the value; afterwards the result is `acc` plus the iteration count, which
odd flags revert. The sequences cover key masks 0, 1, 3 and 7, loop masks 0, 3
and 7, zero to three and five to seven iterations, reverts after one, two,
five and seven logged iterations, which keep the prior storage and commit no
log, entries reused within a transaction and across transactions, entries
keyed by the input's high part and wrapping sums. Both the guarded Core
contract and the source-loop model must give each row. -/
set_option autoImplicit false

namespace Tests.SourceKeccakLoopGolden

open Lean
open Solcore.Core (Word)
open Solcore.ContractRuntime
open Solcore.Synthesis.Core
open Solcore.Synthesis.Stateful
open Solcore.Synthesis.Stateful.KeccakLoopExecution (Transaction)

private def get {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def w (value : Nat) : Word := Word.ofNatModulo value

/-- The step `x ↦ x + c`: aggregate template 0 around the constant scalar. -/
def step (c : Nat) : IO Aggregates.CheckedDAG := do
  let some dag := Aggregates.CheckedDAG.ofParts? [Solcore.Synthesis.Source.Aggregate.template 0 (.word (w c))]
      (.apply (.var 1) (.var 0)) | throw (IO.userError "constant step failed admission")
  return dag

/-- The expected row: status, output Word, `acc`, every nonzero entry as a
`(key, value)` pair and the committed logs as `(counter, key, value)`. -/
structure Expected where
  status : String
  output : Nat
  acc : Nat
  entries : List (Nat × Nat)
  logs : List (Nat × Nat × Nat)

def highKey : Nat := 2 ^ 255
def topKey : Nat := 2 ^ 256 - 8

private def tx (index flags input : Nat) : Transaction := ⟨"tx-" ++ toString index, w flags, w input⟩

private def sevenEntries : List (Nat × Nat) := [(0, 12), (1, 20), (2, 28), (3, 36), (4, 44), (5, 52), (6, 60)]

/-- Loop and key masks 7 and `c = 1`: every iteration has its own entry. No
iteration; one; seven, the first rereading entry 0; a revert after seven
logged iterations; then three iterations on the high part's entries, whose
sums wrap. -/
def sevenRows : List (Transaction × Expected) := [
  (tx 0 0 0, ⟨"returned", 0, 0, [], []⟩),
  -- 0 + 0 + 1 + 1 = 2 at key 0; result 2 + 1.
  (tx 1 0 1, ⟨"returned", 3, 2, [(0, 2)], [(0, 0, 2)]⟩),
  -- With 7 + 1 added: 2 + 2 + 8 = 12 at key 0, then 0 + 12 + 8 = 20 at key 1,
  -- 28, 36, 44, 52 and 60; result 60 + 7.
  (tx 2 0 7, ⟨"returned", 67, 60, sevenEntries,
    [(0, 0, 12), (1, 1, 20), (2, 2, 28), (3, 3, 36), (4, 4, 44), (5, 5, 52), (6, 6, 60)]⟩),
  -- 12 + 60 + 8 = 80, then 20 + 80 + 8 = 108, 144, 188, 240, 300 and 368;
  -- result 375, reverted: no log and the prior storage.
  (tx 3 1 7, ⟨"reverted", 375, 60, sevenEntries, []⟩),
  -- With 2^255 + 3 + 1 added: 0 + 60 gives 2^255 + 64 at key 2^255, then
  -- 0 + 2^255 + 64 wraps to 68 at key 2^255 + 1, and 0 + 68 gives 2^255 + 72
  -- at key 2^255 + 2; result 2^255 + 75.
  (tx 4 2 (highKey + 3), ⟨"returned", highKey + 75, highKey + 72,
    sevenEntries ++ [(highKey, highKey + 64), (highKey + 1, 68), (highKey + 2, highKey + 72)],
    [(0, highKey, highKey + 64), (1, highKey + 1, 68), (2, highKey + 2, highKey + 72)]⟩)]

/-- Loop mask 7, key mask 0 and `c = 0`: every iteration of a transaction
shares one entry. Three iterations on entry 0; one on entry 8, from the
input's high part; a revert after two iterations on entry 0; one iteration
rereading the entry the revert left; then seven. -/
def zeroRows : List (Transaction × Expected) := [
  -- 0 + 0 + 3 = 3, then 3 + 3 + 3 = 9 and 9 + 9 + 3 = 21; result 24.
  (tx 0 0 3, ⟨"returned", 24, 21, [(0, 21)], [(0, 0, 3), (1, 0, 9), (2, 0, 21)]⟩),
  -- 0 + 21 + 9 = 30 at key 8; result 31.
  (tx 1 0 9, ⟨"returned", 31, 30, [(0, 21), (8, 30)], [(0, 8, 30)]⟩),
  -- 21 + 30 + 2 = 53, then 53 + 53 + 2 = 108; result 110, reverted.
  (tx 2 3 2, ⟨"reverted", 110, 30, [(0, 21), (8, 30)], []⟩),
  -- 21 + 30 + 1 = 52; result 53.
  (tx 3 0 1, ⟨"returned", 53, 52, [(0, 52), (8, 30)], [(0, 0, 52)]⟩),
  -- 52 + 52 + 7 = 111, then twice the last plus 7: 229, 465, 937, 1881, 3769
  -- and 7545; result 7552.
  (tx 4 0 7, ⟨"returned", 7552, 7545, [(0, 7545), (8, 30)],
    [(0, 0, 111), (1, 0, 229), (2, 0, 465), (3, 0, 937), (4, 0, 1881), (5, 0, 3769), (6, 0, 7545)]⟩)]

/-- Loop mask 3, key mask 1 and `c = 2`: iterations alternate two entries.
Three iterations on entries 0, 1 and 0; three on the top input's entries,
where `input + c` wraps to 1; a revert after one iteration; then two
iterations rereading entries 0 and 1. -/
def oneRows : List (Transaction × Expected) := [
  -- 0 + 0 + 5 = 5 at key 0, 0 + 5 + 5 = 10 at key 1, 5 + 10 + 5 = 20 at key 0.
  (tx 0 0 3, ⟨"returned", 23, 20, [(0, 20), (1, 10)], [(0, 0, 5), (1, 1, 10), (2, 0, 20)]⟩),
  -- 0 + 20 + 1 = 21 at key 2^256 - 8, 0 + 21 + 1 = 22 at the next, then
  -- 21 + 22 + 1 = 44 at 2^256 - 8 again; result 47.
  (tx 1 0 (2 ^ 256 - 1), ⟨"returned", 47, 44, [(0, 20), (1, 10), (topKey, 44), (topKey + 1, 22)],
    [(0, topKey, 21), (1, topKey + 1, 22), (2, topKey, 44)]⟩),
  -- 20 + 44 + 3 = 67; result 68, reverted.
  (tx 2 1 1, ⟨"reverted", 68, 44, [(0, 20), (1, 10), (topKey, 44), (topKey + 1, 22)], []⟩),
  -- 20 + 44 + 4 = 68 at key 0, then 10 + 68 + 4 = 82 at key 1; result 84.
  (tx 3 0 2, ⟨"returned", 84, 82, [(0, 68), (1, 82), (topKey, 44), (topKey + 1, 22)],
    [(0, 0, 68), (1, 1, 82)]⟩)]

/-- Loop mask 7, key mask 3 and `c = 0`: iterations cycle four entries. Six
iterations, the last two rereading entries 0 and 1; then a revert after five
iterations, the fifth rewriting the entry of the first. -/
def threeRows : List (Transaction × Expected) := [
  -- 6, 12, 18 and 24 at keys 0 to 3, then 6 + 24 + 6 = 36 at key 0 and
  -- 12 + 36 + 6 = 54 at key 1; result 60.
  (tx 0 0 6, ⟨"returned", 60, 54, [(0, 36), (1, 54), (2, 18), (3, 24)],
    [(0, 0, 6), (1, 1, 12), (2, 2, 18), (3, 3, 24), (4, 0, 36), (5, 1, 54)]⟩),
  -- 36 + 54 + 5 = 95, 154, 177, 206, then 95 + 206 + 5 = 306; result 311.
  (tx 1 1 5, ⟨"reverted", 311, 54, [(0, 36), (1, 54), (2, 18), (3, 24)], []⟩)]

/-- Loop mask 0 and `c = 5`: no iteration whatever the input. -/
def idleRows : List (Transaction × Expected) := [
  (tx 0 0 7, ⟨"returned", 0, 0, [], []⟩),
  (tx 1 1 1, ⟨"reverted", 0, 0, [], []⟩)]

private def emitter : String := toString StorageExecution.fixtureBindings.address.val

private def wordText (value : Nat) : String := encodeBytesText (encodeWordBytesBE (w value))

private def valueAt (expected : Expected) (slot : Word) : Nat :=
  if slot == w 0 then expected.acc
  else ((expected.entries.find? fun (key, _) => KeccakLoopExecution.entrySlot (w key) == slot).map Prod.snd).getD 0

private def storageJson (slots : List Word) (expected : Expected) : Json :=
  toJson (slots.map fun slot => Json.mkObj [
    ("slot", toJson (toString slot.val)), ("value", toJson (toString (valueAt expected slot)))])

private def logsJson (expected : Expected) : Json :=
  toJson (expected.logs.map fun (counter, key, value) => Json.mkObj [
    ("address", toJson emitter), ("topics", toJson [toString counter, toString key]),
    ("data", toJson (wordText value))])

def check (name : String) (slots : List Word) (row : Json) (model : KeccakLoopExecution.ModelRow)
    (expected : Expected) : IO Unit := do
  ensure ((row.getObjValAs? String "status").toOption == some expected.status &&
      (row.getObjValAs? String "output").toOption == some (wordText expected.output) &&
      (row.getObjVal? "committedStorage").toOption == some (storageJson slots expected) &&
      (row.getObjVal? "logs").toOption == some (logsJson expected))
    s!"{name}: original Core differs from the expected row {row.compress}"
  ensure (model.reverted == (expected.status == "reverted") && model.result == w expected.output &&
      KeccakLoopExecution.modelSlots model slots == slots.map (fun slot => w (valueAt expected slot)) &&
      model.logs == expected.logs.map (fun (counter, key, value) =>
        ({ordinal := counter, key := w key, value := w value} : KeccakLoopExecution.ModelLog)))
    s!"{name}: the source-loop model differs from the expected row"

/-- Each golden sequence's name, loop mask, key mask, step constant, rows and
addressed keys. -/
def goldenPlans : List (String × Nat × Nat × Nat × List (Transaction × Expected) × List Nat) := [
  ("key mask 7", 7, 7, 1, sevenRows, (List.range 7) ++ [highKey, highKey + 1, highKey + 2]),
  ("key mask 0", 7, 0, 0, zeroRows, [0, 8]),
  ("key mask 1", 3, 1, 2, oneRows, [0, 1, topKey, topKey + 1]),
  ("key mask 3", 7, 3, 0, threeRows, [0, 1, 2, 3]),
  ("loop mask 0", 0, 3, 5, idleRows, [])]

def testSourceKeccakLoopGolden : IO Unit := do
  let fuel := 1000000
  for (name, mask, keyMask, constant, rows, addressed) in goldenPlans do
    let step ← step constant
    let some plan := KeccakLoop.CheckedPlan.ofParts? step mask keyMask
      | throw (IO.userError s!"{name}: the Keccak-loop wrapper failed admission")
    let transactions := rows.map Prod.fst
    -- The observed slots are slot zero and the entry slot of every addressed
    -- key, in increasing order.
    let slots := KeccakLoopExecution.observedSlots mask keyMask transactions
    ensure (slots.length == addressed.length + 1 && slots.contains (w 0) &&
        addressed.all (fun key => slots.contains (KeccakLoopExecution.entrySlot (w key))) &&
        (slots.zip slots.tail).all (fun (lower, upper) => lower.val < upper.val))
      s!"{name}: the observed slots differ from the addressed keys"
    let history := KeccakLoopExecution.observe plan transactions StorageExecution.fixtureBindings fuel
    ensure ((history.getObjValAs? String "status").toOption == some "complete") s!"{name}: the history is incomplete"
    ensure ((history.getObjVal? "observedSlots").toOption == some (KeyedStorageExecution.slotsJson slots))
      s!"{name}: the history observes other slots"
    let observed ← get (history.getObjValAs? (Array Json) "transactions")
    let some modelled := KeccakLoopExecution.model step fuel mask keyMask transactions
      | throw (IO.userError s!"{name}: the source-loop model failed")
    ensure (observed.size == rows.length && modelled.length == rows.length) s!"{name}: a row is missing"
    for ((row, model), (transaction, expected)) in (observed.toList.zip modelled).zip rows do
      check s!"{name} {transaction.id}" slots row model expected
      -- The recorded iteration count is the input's bits under the mask.
      ensure (KeccakLoopExecution.iterations mask transaction.input ≤ mask) s!"{name}: iterations exceed the mask"
  -- The plan admits exactly the four loop masks and the four key masks.
  let constant ← step 1
  for mask in [2, 4, 5, 6, 8, 15] do
    ensure (KeccakLoop.CheckedPlan.ofParts? constant mask 0).isNone s!"loop mask {mask} was admitted"
    ensure (KeccakLoop.CheckedPlan.ofParts? constant 1 mask).isNone s!"key mask {mask} was admitted"

end Tests.SourceKeccakLoopGolden
