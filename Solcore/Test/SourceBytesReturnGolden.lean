import Solcore.Synthesis.Source.BytesReturnCases

/-! Golden cases for the bytes-return profile. Every expected row is written out
as hexadecimal text computed from the protocol, not by either model. The steps
add a known constant `c`, so a transaction computes `r = slot 0 + input + c`,
writes `r` to slot 0, slot 1 plus one to slot 1 and the input to slot 2, and
returns the first `length` bytes of `r · K` and `(slot 1 · K) xor (prior slot
2)` in std's encoding: the offset 32, the length, the data and zeros to a whole
Word. Odd flags revert with `r` and keep the prior slots. The sequences cover
the lengths 0, 1, 31, 32, 33, 63 and 64, both outcomes, values carried from
earlier committed transactions past a revert, and wrapping sums. Both the Core
contract and the source model must give each row. -/
set_option autoImplicit false

namespace Tests.SourceBytesReturnGolden

open Lean
open Solcore.Core (Word)
open Solcore.ContractRuntime
open Solcore.Synthesis.Core
open Solcore.Synthesis.Stateful
open Solcore.Synthesis.Stateful.BytesReturnExecution (Transaction)

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

/-- The expected row: status, the whole output as hexadecimal text and slots
zero to two. -/
private structure Expected where
  status : String
  output : String
  values : List Nat

private def slots (values : List Nat) : Json :=
  toJson ((List.range BytesReturn.slotCount).map fun slot => Json.mkObj [
    ("slot", toJson (toString slot)), ("value", toJson (toString (values.getD slot 0)))])

private def tx (index flags input length : Nat) : Transaction :=
  ⟨"tx-" ++ toString index, w flags, w input, w length⟩

/-- The offset Word and a length Word, the head of every returned value. -/
private def head (lengthDigits : String) : String :=
  "0000000000000000000000000000000000000000000000000000000000000020" ++
    String.ofList (List.replicate (64 - lengthDigits.length) '0') ++ lengthDigits

private def zeros (digits : Nat) : String := String.ofList (List.replicate digits '0')

/-- `c = 1`. Every bank length but 63 returns; a revert between two committed
transactions leaves slot 2 at the earlier input; the fourth sum wraps:
14 + (2^256 - 1) + 1 = 14. -/
private def firstRows : List (Transaction × Expected) := [
  -- 0 + 5 + 1 = 6: the empty value, the head alone.
  (tx 0 0 5 0, ⟨"returned", head "0", [6, 1, 5]⟩),
  -- 6 + 9 + 1 = 16, reverted with one Word; the slots stay.
  (tx 1 1 9 31, ⟨"reverted", zeros 62 ++ "10", [6, 1, 5]⟩),
  -- 6 + 7 + 1 = 14; 31 bytes of 14 · K; the last byte of the Word is zeroed.
  (tx 2 2 7 31, ⟨"returned", head "1f" ++
    "a708a824f612c933529285451500f2d8e71e27e752e2407b95edccf96a95cc00", [14, 2, 7]⟩),
  -- 14 + (2^256 - 1) + 1 wraps to 14; one byte of 14 · K.
  (tx 3 0 (2 ^ 256 - 1) 1, ⟨"returned", head "1" ++ "a7" ++ zeros 62, [14, 3, 2 ^ 256 - 1]⟩),
  -- 14 + 0 + 1 = 15, reverted.
  (tx 4 3 0 64, ⟨"reverted", zeros 62 ++ "0f", [14, 3, 2 ^ 256 - 1]⟩),
  -- 14 + 1 + 1 = 16; both Words: 16 · K, then (4 · K) xor (2^256 - 1).
  (tx 5 4 1 64, ⟨"returned", head "40" ++
    "e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e950" ++
    "8722191a02d60fa8318cfe7e8c48df2fbdf76250317636b81e4e57b8bcf9c5ab", [16, 4, 1]⟩),
  -- 16 + 3 + 1 = 20; exactly one Word of 20 · K.
  (tx 6 0 3 32, ⟨"returned", head "20" ++
    "5c55827df1d1b1b7083f07874293a4114a2b146f08b0ee67687849644f1f23a4", [20, 5, 3]⟩),
  -- 20 + 2^255 + 1; a Word and one byte of (6 · K) xor 3.
  (tx 7 0 (2 ^ 255) 33, ⟨"returned", head "21" ++
    "7a8cfc37711c2dccfbdbc7e79f816c455aad3bdafc5360b960e4b3761fe0b239" ++ "b5" ++ zeros 62,
    [2 ^ 255 + 21, 6, 2 ^ 255]⟩)]

/-- `c = 0`. The first transaction reverts from empty storage; the third sum
wraps: 10 + (2^256 - 2) = 8. -/
private def secondRows : List (Transaction × Expected) := [
  (tx 0 1 1 63, ⟨"reverted", zeros 63 ++ "1", []⟩),
  -- 63 bytes of 10 · K and K, the second Word's last byte zeroed.
  (tx 1 0 10 63, ⟨"returned", head "3f" ++
    "2e2ac13ef8e8d8db841f83c3a149d208a5158a3784587733b43c24b2278f91d2" ++
    "9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e00", [10, 1, 10]⟩),
  (tx 2 0 (2 ^ 256 - 2) 0, ⟨"returned", head "0", [8, 2, 2 ^ 256 - 2]⟩)]

private def check (name : String) (row : Json) (model : BytesReturnExecution.ModelRow) (expected : Expected) : IO Unit := do
  ensure ((row.getObjValAs? String "status").toOption == some expected.status &&
      (row.getObjValAs? String "output").toOption == some ("0x" ++ expected.output) &&
      (row.getObjVal? "committedStorage").toOption == some (slots expected.values))
    s!"{name}: original Core differs from the expected row {row.compress}"
  ensure (model.reverted == (expected.status == "reverted") &&
      encodeBytesText model.output == "0x" ++ expected.output &&
      model.slots == (List.range BytesReturn.slotCount).map (fun slot => w (expected.values.getD slot 0)))
    s!"{name}: the source model differs from the expected row"

def testSourceBytesReturnGolden : IO Unit := do
  let fuel := 1000000
  ensure (Solcore.Synthesis.Source.BytesReturn.multiplierLiteral ==
      "0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95")
    "the emitted multiplier differs from the defined constant"
  for (name, constant, rows) in [("first", 1, firstRows), ("second", 0, secondRows)] do
    let step ← step constant
    let some plan := BytesReturn.CheckedPlan.ofStep? step
      | throw (IO.userError s!"{name}: the bytes-return wrapper failed admission")
    ensure (plan.contract.entryProfile == .boundedBytesOutcomeV1)
      s!"{name}: the contract does not use the bounded bytes convention"
    let transactions := rows.map Prod.fst
    let history := BytesReturnExecution.observe plan transactions StorageExecution.fixtureBindings fuel
    ensure ((history.getObjValAs? String "status").toOption == some "complete") s!"{name}: the history is incomplete"
    let observed ← get (history.getObjValAs? (Array Json) "transactions")
    let some modelled := BytesReturnExecution.model step fuel transactions
      | throw (IO.userError s!"{name}: the source model failed")
    ensure (observed.size == rows.length && modelled.length == rows.length) s!"{name}: a row is missing"
    for ((row, model), (transaction, expected)) in (observed.toList.zip modelled).zip rows do
      check s!"{name} {transaction.id}" row model expected
  -- The byte after a 31-byte value is nonzero in memory and zero in the output.
  let some plan := BytesReturn.CheckedPlan.ofStep? (← step 1) | throw (IO.userError "the wrapper failed admission")
  let history := BytesReturnExecution.observe plan [tx 0 0 5 31] StorageExecution.fixtureBindings fuel
  let observed ← get (history.getObjValAs? (Array Json) "transactions")
  let output := (observed[0]?.bind fun row => (row.getObjValAs? String "output").toOption).getD ""
  ensure ((w 6 * w BytesReturn.multiplier).val % 256 != 0) "the memory byte after the length is zero"
  ensure (output.length == 2 + 192 && output.endsWith "00") "a 31-byte value does not end in a zero byte"

end Tests.SourceBytesReturnGolden
