import Solcore.Synthesis.Source.StorageLoopCases

/-! Golden cases for the storage-loop profile. Every expected row is written
out by hand from the protocol, not computed by either model. The steps add a
known constant `c`, so iteration `i` writes
`slot 0 + slot 1 + slot (1 + i) + slot (2 + i) + input + c` to slot `2 + i`
and to slot zero; afterwards slot one grows by the iteration count and the
result is slot zero plus slot one, which odd flags revert. The sequences cover
zero, one, two, three and seven iterations, masks zero, one, three and seven,
a revert after loop writes, a slot written by one iteration and read by the
next, slots written by one transaction and read by a later one, and wrapping
sums. Both the guarded Core contract and the source-loop model must give each
row. -/
set_option autoImplicit false

namespace Tests.SourceStorageLoopGolden

open Lean
open Solcore.Core (Word)
open Solcore.ContractRuntime
open Solcore.Synthesis.Core
open Solcore.Synthesis.Stateful
open Solcore.Synthesis.Stateful.StorageLoopExecution (Transaction)

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

/-- The expected row: status, output Word and slots zero to eight. -/
structure Expected where
  status : String
  output : Nat
  values : List Nat

private def slots (values : List Nat) : Json :=
  toJson ((List.range StorageLoop.slotCount).map fun slot => Json.mkObj [
    ("slot", toJson (toString slot)), ("value", toJson (toString (values.getD slot 0)))])

private def wordText (value : Nat) : String := encodeBytesText (encodeWordBytesBE (w value))

private def tx (index flags input : Nat) : Transaction := ⟨"tx-" ++ toString index, w flags, w input⟩

/-- Mask 7 and `c = 1`. No iteration; one; seven over the carried slots; a
revert after seven iterations, which keeps the prior slots; then three. -/
def sevenRows : List (Transaction × Expected) := [
  (tx 0 0 0, ⟨"returned", 0, []⟩),
  -- 0 + 0 + 0 + 0 + 1 + 1 = 2; slot one 1; result 3.
  (tx 1 0 1, ⟨"returned", 3, [2, 1, 2]⟩),
  -- With 7 + 1 added: 2 + 1 + 1 + 2 = 14, then 14 + 1 + 14 = 37, 83, 175, 359,
  -- 727 and 1463; slot one 8; result 1471.
  (tx 2 0 7, ⟨"returned", 1471, [1463, 8, 14, 37, 83, 175, 359, 727, 1463]⟩),
  -- 1463 + 8 + 8 + 14 + 8 = 1501, then 1501 + 8 + 1501 + 37 + 8 = 3055, 6209,
  -- 12609, 25593, 51929 and 105337; slot one 15; result 105352, reverted.
  (tx 3 1 7, ⟨"reverted", 105352, [1463, 8, 14, 37, 83, 175, 359, 727, 1463]⟩),
  -- With 3 + 1 added: 1463 + 8 + 8 + 14 + 4 = 1497, then
  -- 1497 + 8 + 1497 + 37 + 4 = 3043 and 3043 + 8 + 3043 + 83 + 4 = 6181.
  (tx 4 2 3, ⟨"returned", 6192, [6181, 11, 1497, 3043, 6181, 175, 359, 727, 1463]⟩)]

/-- Mask 0 and `c = 5`: no iteration whatever the input. -/
def zeroRows : List (Transaction × Expected) := [
  (tx 0 0 7, ⟨"returned", 0, []⟩),
  (tx 1 1 1, ⟨"reverted", 0, []⟩)]

/-- Mask 1 and `c = 0`; the second sum wraps: 3 + 1 + 1 + 3 + (2^256 - 1) = 7. -/
def oneRows : List (Transaction × Expected) := [
  (tx 0 0 3, ⟨"returned", 4, [3, 1, 3]⟩),
  (tx 1 0 (2 ^ 256 - 1), ⟨"returned", 9, [7, 2, 7]⟩),
  (tx 2 3 2, ⟨"reverted", 9, [7, 2, 7]⟩)]

/-- Mask 3 and `c = 2`. Two iterations: 8, then 8 + 0 + 8 + 0 + 8 = 24. Three
iterations of an input with the high bit: with 2^255 + 5 added,
24 + 2 + 2 + 8 gives 2^255 + 41, then 2^255 + 113 and 2^255 + 233, since
twice 2^255 wraps to zero. -/
def threeRows : List (Transaction × Expected) := [
  (tx 0 0 6, ⟨"returned", 26, [24, 2, 8, 24]⟩),
  (tx 1 0 (2 ^ 255 + 3), ⟨"returned", 2 ^ 255 + 238,
    [2 ^ 255 + 233, 5, 2 ^ 255 + 41, 2 ^ 255 + 113, 2 ^ 255 + 233]⟩)]

def check (name : String) (row : Json) (model : StorageLoopExecution.ModelRow) (expected : Expected) : IO Unit := do
  ensure ((row.getObjValAs? String "status").toOption == some expected.status &&
      (row.getObjValAs? String "output").toOption == some (wordText expected.output) &&
      (row.getObjVal? "committedStorage").toOption == some (slots expected.values))
    s!"{name}: original Core differs from the expected row {row.compress}"
  ensure (model.reverted == (expected.status == "reverted") && model.result == w expected.output &&
      model.slots == (List.range StorageLoop.slotCount).map (fun slot => w (expected.values.getD slot 0)))
    s!"{name}: the source-loop model differs from the expected row"

/-- Each golden sequence's name, mask, step constant and rows. -/
def goldenPlans : List (String × Nat × Nat × List (Transaction × Expected)) := [
  ("mask 7", 7, 1, sevenRows), ("mask 0", 0, 5, zeroRows), ("mask 1", 1, 0, oneRows), ("mask 3", 3, 2, threeRows)]

def testSourceStorageLoopGolden : IO Unit := do
  let fuel := 1000000
  for (name, mask, constant, rows) in goldenPlans do
    let step ← step constant
    let some plan := StorageLoop.CheckedPlan.ofParts? step mask
      | throw (IO.userError s!"{name}: the storage-loop wrapper failed admission")
    let transactions := rows.map Prod.fst
    let history := StorageLoopExecution.observe plan transactions StorageExecution.fixtureBindings fuel
    ensure ((history.getObjValAs? String "status").toOption == some "complete") s!"{name}: the history is incomplete"
    let observed ← get (history.getObjValAs? (Array Json) "transactions")
    let some modelled := StorageLoopExecution.model step fuel mask transactions
      | throw (IO.userError s!"{name}: the source-loop model failed")
    ensure (observed.size == rows.length && modelled.length == rows.length) s!"{name}: a row is missing"
    for ((row, model), (transaction, expected)) in (observed.toList.zip modelled).zip rows do
      check s!"{name} {transaction.id}" row model expected
      -- The recorded iteration count is the input's bits under the mask.
      ensure (StorageLoopExecution.iterations mask transaction.input ≤ mask) s!"{name}: iterations exceed the mask"
  -- The plan admits exactly the four masks.
  let constant ← step 1
  for mask in [2, 4, 5, 6, 8, 15] do
    ensure (StorageLoop.CheckedPlan.ofParts? constant mask).isNone s!"mask {mask} was admitted"

end Tests.SourceStorageLoopGolden
