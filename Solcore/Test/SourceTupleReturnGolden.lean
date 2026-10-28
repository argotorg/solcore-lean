import Solcore.Synthesis.Source.TupleReturnCases

/-! Golden cases for the tuple-return profile. Every expected row is written
out by hand from the protocol, not computed by either model. The steps add a
known constant `c`, so a transaction computes `r = slot 0 + input + c`, writes
`r` to slot 0, slot 1 plus one to slot 1 and the input to slot 2, and returns
the first `arity` Words of `(r, slot 1, prior slot 0, prior slot 2)`; odd flags
revert with `r` and keep the prior slots. The sequences cover arities two,
three and four, both outcomes, values carried from earlier committed
transactions past a revert, and wrapping sums. Both the Core contract and the
source model must give each row. -/
set_option autoImplicit false

namespace Tests.SourceTupleReturnGolden

open Lean
open Solcore.Core (Word)
open Solcore.ContractRuntime
open Solcore.Synthesis.Core
open Solcore.Synthesis.Stateful
open Solcore.Synthesis.Stateful.TupleReturnExecution (Transaction)

private def get {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def w (value : Nat) : Word := Word.ofNatModulo value

/-- The step `x ↦ x + c`: aggregate template 0 around the constant scalar. -/
private def step (c : Nat) : IO Aggregates.CheckedDAG := do
  let some dag := Aggregates.CheckedDAG.ofParts? [Solcore.Synthesis.Source.Aggregate.template 0 (.word (w c))]
      (.apply (.var 1) (.var 0)) | throw (IO.userError "constant step failed admission")
  return dag

/-- The expected row: status, the output Words and slots zero to two. -/
private structure Expected where
  status : String
  output : List Nat
  values : List Nat

private def slots (values : List Nat) : Json :=
  toJson ((List.range TupleReturn.slotCount).map fun slot => Json.mkObj [
    ("slot", toJson (toString slot)), ("value", toJson (toString (values.getD slot 0)))])

private def wordsText (values : List Nat) : String :=
  encodeBytesText (values.foldl (fun bytes value => bytes ++ encodeWordBytesBE (w value)) ByteArray.empty)

private def tx (index flags input : Nat) : Transaction := ⟨"tx-" ++ toString index, w flags, w input⟩

/-- Arity 4 and `c = 1`. A revert between two committed transactions leaves
slot 2 at the earlier input; the fourth sum wraps: 14 + (2^256 - 1) + 1 = 14. -/
private def fourRows : List (Transaction × Expected) := [
  -- 0 + 5 + 1 = 6; count 1; prior slots zero.
  (tx 0 0 5, ⟨"returned", [6, 1, 0, 0], [6, 1, 5]⟩),
  -- 6 + 9 + 1 = 16, reverted with one Word; the slots stay.
  (tx 1 1 9, ⟨"reverted", [16], [6, 1, 5]⟩),
  -- 6 + 7 + 1 = 14; count 2; prior 6; last 5, not the reverted 9.
  (tx 2 2 7, ⟨"returned", [14, 2, 6, 5], [14, 2, 7]⟩),
  (tx 3 0 (2 ^ 256 - 1), ⟨"returned", [14, 3, 14, 7], [14, 3, 2 ^ 256 - 1]⟩),
  -- 14 + 0 + 1 = 15, reverted.
  (tx 4 3 0, ⟨"reverted", [15], [14, 3, 2 ^ 256 - 1]⟩),
  -- 14 + 1 + 1 = 16; last is the full-width input.
  (tx 5 4 1, ⟨"returned", [16, 4, 14, 2 ^ 256 - 1], [16, 4, 1]⟩)]

/-- Arity 2 and `c = 0`. -/
private def twoRows : List (Transaction × Expected) := [
  (tx 0 0 3, ⟨"returned", [3, 1], [3, 1, 3]⟩),
  -- 3 + 4 = 7, reverted.
  (tx 1 1 4, ⟨"reverted", [7], [3, 1, 3]⟩),
  (tx 2 0 (2 ^ 255), ⟨"returned", [2 ^ 255 + 3, 2], [2 ^ 255 + 3, 2, 2 ^ 255]⟩)]

/-- Arity 3 and `c = 2`. The first transaction reverts from empty storage; the
third sum wraps: 12 + (2^256 - 2) + 2 = 12. -/
private def threeRows : List (Transaction × Expected) := [
  (tx 0 1 1, ⟨"reverted", [3], []⟩),
  (tx 1 0 10, ⟨"returned", [12, 1, 0], [12, 1, 10]⟩),
  (tx 2 0 (2 ^ 256 - 2), ⟨"returned", [12, 2, 12], [12, 2, 2 ^ 256 - 2]⟩)]

private def check (name : String) (row : Json) (model : TupleReturnExecution.ModelRow) (expected : Expected) : IO Unit := do
  ensure ((row.getObjValAs? String "status").toOption == some expected.status &&
      (row.getObjValAs? String "output").toOption == some (wordsText expected.output) &&
      (row.getObjVal? "committedStorage").toOption == some (slots expected.values))
    s!"{name}: original Core differs from the expected row {row.compress}"
  ensure (model.reverted == (expected.status == "reverted") && model.output == expected.output.map w &&
      model.slots == (List.range TupleReturn.slotCount).map (fun slot => w (expected.values.getD slot 0)))
    s!"{name}: the source model differs from the expected row"
  ensure (encodeBytesText (TupleReturnExecution.outputBytes model) == wordsText expected.output)
    s!"{name}: the source model's output bytes differ"

def testSourceTupleReturnGolden : IO Unit := do
  let fuel := 1000000
  for (name, arity, constant, rows) in [("arity 4", 4, 1, fourRows), ("arity 2", 2, 0, twoRows),
      ("arity 3", 3, 2, threeRows)] do
    let step ← step constant
    let some plan := TupleReturn.CheckedPlan.ofParts? step arity
      | throw (IO.userError s!"{name}: the tuple-return wrapper failed admission")
    ensure (plan.contract.entryProfile == .wordTupleOutcomeV1 (arity - 2))
      s!"{name}: the contract does not use the tuple convention of its arity"
    let transactions := rows.map Prod.fst
    let history := TupleReturnExecution.observe plan transactions StorageExecution.fixtureBindings fuel
    ensure ((history.getObjValAs? String "status").toOption == some "complete") s!"{name}: the history is incomplete"
    let observed ← get (history.getObjValAs? (Array Json) "transactions")
    let some modelled := TupleReturnExecution.model step fuel arity transactions
      | throw (IO.userError s!"{name}: the source model failed")
    ensure (observed.size == rows.length && modelled.length == rows.length) s!"{name}: a row is missing"
    for ((row, model), (transaction, expected)) in (observed.toList.zip modelled).zip rows do
      check s!"{name} {transaction.id}" row model expected
  -- The plan admits exactly the three arities.
  let constant ← step 1
  for arity in [0, 1, 5, 8] do
    ensure (TupleReturn.CheckedPlan.ofParts? constant arity).isNone s!"arity {arity} was admitted"
  -- A flipped expectation is detected.
  let some plan := TupleReturn.CheckedPlan.ofParts? constant 4 | throw (IO.userError "arity 4 failed admission")
  let history := TupleReturnExecution.observe plan [tx 0 0 5] StorageExecution.fixtureBindings fuel
  let observed ← get (history.getObjValAs? (Array Json) "transactions")
  ensure ((observed[0]?.bind fun row => (row.getObjValAs? String "output").toOption) !=
      some (wordsText [6, 1, 0, 1])) "a changed last Word was accepted"

end Tests.SourceTupleReturnGolden
