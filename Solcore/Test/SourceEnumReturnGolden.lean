import Solcore.Synthesis.Source.EnumReturnCases

/-! Golden cases for the enum-return profile. Every expected row is written out
as hexadecimal text computed from the protocol and std's encoding, not by
either model, with the tags from `cast keccak`. The steps add a known constant
`c`, so a transaction computes `r = slot 0 + input + c`, writes `r` to slot 0,
slot 1 plus one to slot 1 and the input to slot 2, and returns constructor
`choice` with its fields: none, `d0 = r · K`, `(d0, d1)` with
`d1 = (slot 1 · K) xor (prior slot 2)`, or the first `length` bytes of `d0` and
`d1`. A static enum is its tag, fields and zero Words up to the widest
constructor; a dynamic one is the offset 32, then that body and a `bytes`
field's tail. Odd flags revert with `r` and keep the prior slots. The scenarios
cover static and dynamic shapes, every field kind, padding, the lengths 0, 1,
31, 32, 33, 63 and 64, both outcomes, values carried past a revert, and
wrapping sums. Both the Core contract and the source model must give each row. -/
set_option autoImplicit false

namespace Tests.SourceEnumReturnGolden

open Lean
open Solcore.Core (Word)
open Solcore.ContractRuntime
open Solcore.Synthesis.Core
open Solcore.Synthesis.Core.EnumReturn (Constructor Shape)
open Solcore.Synthesis.Stateful
open Solcore.Synthesis.Stateful.EnumReturnExecution (Transaction)

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
  toJson ((List.range EnumReturn.slotCount).map fun slot => Json.mkObj [
    ("slot", toJson (toString slot)), ("value", toJson (toString (values.getD slot 0)))])

private def tx (index flags input choice length : Nat) : Transaction :=
  ⟨"tx-" ++ toString index, w flags, w input, w choice, w length⟩

/-- One Word's 64 hexadecimal digits, written as the digits after a run of zeros. -/
private def hexWord (digits : String) : String :=
  String.ofList (List.replicate (64 - digits.length) '0') ++ digits

private def zeroWord : String := hexWord ""

-- The tags `keccak256("Name(fields)")`, as `cast keccak` writes them.
-- Blob(bytes)
private def tagBlobBytes : String := "d05ce3dc4caf4a4b252e3323bde615dc3b9d54623e1859c892f0b4ecf5e45164"
-- Idle()
private def tagIdleUnit : String := "ae897c555b7596dee56949d599aa959af71416324ac27ef76dd898923ab34d4f"
-- OverflowedAccumulator(bytes)
private def tagOverflowedAccumulatorBytes : String := "1d021c79c75f3d483321c073ba0acaa5b4589d7a6ad132e8b5fe27d9b76d678b"
-- Pair(uint256,uint256)
private def tagPairPair : String := "2d3b57dedfada8371bdae932a6881ace0dec34c90dd19fd49b2164124e699e2d"
-- Q(bytes)
private def tagQBytes : String := "ceddd0f6fa798287ec511a63a42164c8eb23d85a7f6355be56c0e9119d5f93b4"
-- Q(uint256)
private def tagQWord : String := "5dcad53f88dc9d20c351c1bb58593dde38a673b5308c8751aaeb91edd8c97952"
-- Ready()
private def tagReadyUnit : String := "6e12fa0ff1c6b8acb2181ba65fc2867fd8d895d0af9f39674b64abc5ff79275b"
-- Ready(uint256)
private def tagReadyWord : String := "0b217ad5c70346c7cd952bd2463c6684a56f9ed229f5780947586625781b4770"
-- Rejected()
private def tagRejectedUnit : String := "efde6dcf3c2196c5705e848c09f0659d33de3ca0248be3ab40852d1bafc0f1e3"
-- Settled(uint256,uint256)
private def tagSettledPair : String := "f5b268a3ff315cc44ccceeef86259c9e8eef81ceecb14001543809115380dd62"

/-- `Pair(uint256, uint256) | Idle | Q(uint256)`, static with a three-Word head,
`c = 5`. A revert between two returns, then a sum that wraps: 26 + (2^256 -
1) + 5 = 30. -/
private def staticRows : List (Transaction × Expected) := [
  (tx 0 0 7 0 0, ⟨"returned",
      tagPairPair ++
      "6a99b4b1f77dd1076b5904845b256270c619d90f6b9d5bd7a514f8d5c912aefc" ++
      "9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95",
      [12, 1, 7]⟩),
  (tx 1 1 3 1 0, ⟨"reverted",
      hexWord "14",
      [12, 1, 7]⟩),
  (tx 2 2 9 1 0, ⟨"returned",
      tagIdleUnit ++
      zeroWord ++
      zeroWord,
      [26, 2, 9]⟩),
  (tx 3 0 (2 ^ 256 - 1) 2 0, ⟨"returned",
      tagQWord ++
      "8a8043bceaba8a928c5e8b4ae3dd7619ef409ea68d09659b1cb46e1676aeb576" ++
      zeroWord,
      [30, 3, (2 ^ 256 - 1)]⟩)]

/-- `Blob(bytes) | Ready(uint256) | Settled(uint256, uint256) | Rejected`,
dynamic with a three-Word body head, `c = 1`: a `bytes` field's offset is
0x60 and one zero Word precedes its tail. -/
private def dynamicRows : List (Transaction × Expected) := [
  (tx 0 0 4 0 33, ⟨"returned",
      hexWord "20" ++
      tagBlobBytes ++
      hexWord "60" ++
      zeroWord ++
      hexWord "21" ++
      "1715609f7c746c6dc20fc1e1d0a4e904528ac51bc22c3b99da1e125913c7c8e9" ++
      "9e00000000000000000000000000000000000000000000000000000000000000",
      [5, 1, 4]⟩),
  (tx 1 0 6 3 0, ⟨"returned",
      hexWord "20" ++
      tagRejectedUnit ++
      zeroWord ++
      zeroWord,
      [12, 2, 6]⟩),
  (tx 2 3 8 0 64, ⟨"reverted",
      hexWord "15",
      [12, 2, 6]⟩),
  (tx 3 0 (2 ^ 255) 1 0, ⟨"returned",
      hexWord "20" ++
      tagReadyWord ++
      "88d12e6b76c84d1d5ef5c4e4b8132aa4d69c007b5f3fce299d8162e799d43d91" ++
      zeroWord,
      [(2 ^ 255 + 13), 3, (2 ^ 255)]⟩),
  (tx 4 0 0 2 0, ⟨"returned",
      hexWord "20" ++
      tagSettledPair ++
      "2708a824f612c933529285451500f2d8e71e27e752e2407b95edccf96a95cc26" ++
      "f8dde6e5fd29f057ce73018173b720d042089dafce89c947e1b1a84743063a54",
      [(2 ^ 255 + 14), 4, 0]⟩),
  (tx 5 0 1 0 0, ⟨"returned",
      hexWord "20" ++
      tagBlobBytes ++
      hexWord "60" ++
      zeroWord ++
      zeroWord,
      [(2 ^ 255 + 16), 5, 1]⟩)]

/-- `OverflowedAccumulator(bytes) | Q(bytes)`, two `bytes` constructors behind a
two-Word body head, `c = 2`, over the lengths 1, 31, 32, 63 and 64. -/
private def bytesRows : List (Transaction × Expected) := [
  (tx 0 0 1 1 1, ⟨"returned",
      hexWord "20" ++
      tagQBytes ++
      hexWord "40" ++
      hexWord "1" ++
      "da00000000000000000000000000000000000000000000000000000000000000",
      [3, 1, 1]⟩),
  (tx 1 0 2 0 31, ⟨"returned",
      hexWord "20" ++
      tagOverflowedAccumulatorBytes ++
      hexWord "40" ++
      hexWord "1f" ++
      "538454127b096499a94942a28a80796c738f13f3a971203dcaf6e67cb54ae600",
      [7, 2, 2]⟩),
  (tx 2 0 3 1 32, ⟨"returned",
      hexWord "20" ++
      tagQBytes ++
      hexWord "40" ++
      hexWord "20" ++
      "6a99b4b1f77dd1076b5904845b256270c619d90f6b9d5bd7a514f8d5c912aefc",
      [12, 3, 3]⟩),
  (tx 3 0 4 0 63, ⟨"returned",
      hexWord "20" ++
      tagOverflowedAccumulatorBytes ++
      hexWord "40" ++
      hexWord "3f" ++
      "1fe68f0af33cb98b210586c688b813a92926c597216c09c3779f7540ad9c067a" ++
      "78dde6e5fd29f057ce73018173b720d042089dafce89c947e1b1a84743063a00",
      [18, 4, 4]⟩),
  (tx 4 0 5 1 64, ⟨"returned",
      hexWord "20" ++
      tagQBytes ++
      hexWord "40" ++
      hexWord "40" ++
      "736ae31d6e461e24ca4ec96913388d159cb5d98acadd2a0142965bbd62e6ec8d" ++
      "1715609f7c746c6dc20fc1e1d0a4e904528ac51bc22c3b99da1e125913c7c8ed",
      [25, 5, 5]⟩)]

/-- `Idle | Ready`, static and field-less: each value is its one tag Word, `c = 3`. -/
private def tagRows : List (Transaction × Expected) := [
  (tx 0 0 0 1 0, ⟨"returned",
      tagReadyUnit,
      [3, 1, 0]⟩),
  (tx 1 0 1 0 0, ⟨"returned",
      tagIdleUnit,
      [7, 2, 1]⟩),
  (tx 2 1 2 0 0, ⟨"reverted",
      hexWord "c",
      [7, 2, 1]⟩),
  (tx 3 0 5 1 0, ⟨"returned",
      tagReadyUnit,
      [15, 3, 5]⟩)]

private def scenarios : List (String × Nat × List Constructor × List (Transaction × Expected)) := [
    ("static-carried", 5, [⟨"Pair", .twoWords⟩, ⟨"Idle", .noWords⟩, ⟨"Q", .oneWord⟩], staticRows),
    ("dynamic-wide", 1, [⟨"Blob", .boundedBytes⟩, ⟨"Ready", .oneWord⟩, ⟨"Settled", .twoWords⟩, ⟨"Rejected", .noWords⟩], dynamicRows),
    ("two-bytes", 2, [⟨"OverflowedAccumulator", .boundedBytes⟩, ⟨"Q", .boundedBytes⟩], bytesRows),
    ("tags-only", 3, [⟨"Idle", .noWords⟩, ⟨"Ready", .noWords⟩], tagRows)]

private def check (name : String) (row : Json) (model : EnumReturnExecution.ModelRow) (expected : Expected) : IO Unit := do
  ensure ((row.getObjValAs? String "status").toOption == some expected.status &&
      (row.getObjValAs? String "output").toOption == some ("0x" ++ expected.output) &&
      (row.getObjVal? "committedStorage").toOption == some (slots expected.values))
    s!"{name}: original Core differs from the expected row {row.compress}"
  ensure (model.reverted == (expected.status == "reverted") &&
      encodeBytesText model.output == "0x" ++ expected.output &&
      model.slots == (List.range EnumReturn.slotCount).map (fun slot => w (expected.values.getD slot 0)))
    s!"{name}: the source model differs from the expected row"

def testSourceEnumReturnGolden : IO Unit := do
  let fuel := 1000000
  ensure (Solcore.Synthesis.Source.EnumReturn.multiplierLiteral ==
      "0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95")
    "the emitted multiplier differs from the defined constant"
  -- Lean's Keccak-256 tags equal the ones written out.
  ensure (encodeBytesText (encodeWordBytesBE (EnumReturn.tag ⟨"Pair", .twoWords⟩)) == "0x" ++ tagPairPair &&
      encodeBytesText (encodeWordBytesBE (EnumReturn.tag ⟨"Q", .boundedBytes⟩)) == "0x" ++ tagQBytes &&
      encodeBytesText (encodeWordBytesBE (EnumReturn.tag ⟨"Idle", .noWords⟩)) == "0x" ++ tagIdleUnit)
    "a constructor tag differs from keccak256 of its signature"
  for (name, constant, constructors, rows) in scenarios do
    let step ← step constant
    let some shape := Solcore.Synthesis.Source.EnumReturn.Shape.ofList? constructors
      | throw (IO.userError s!"{name}: the shape has fewer than two constructors")
    let some plan := EnumReturn.CheckedPlan.ofParts? step shape
      | throw (IO.userError s!"{name}: the enum-return wrapper failed admission")
    ensure (plan.contract.entryProfile == shape.profile)
      s!"{name}: the contract does not use the shape's enum convention"
    let transactions := rows.map Prod.fst
    let history := EnumReturnExecution.observe plan transactions StorageExecution.fixtureBindings fuel
    ensure ((history.getObjValAs? String "status").toOption == some "complete") s!"{name}: the history is incomplete"
    let observed ← get (history.getObjValAs? (Array Json) "transactions")
    let some modelled := EnumReturnExecution.model step constructors fuel transactions
      | throw (IO.userError s!"{name}: the source model failed")
    ensure (observed.size == rows.length && modelled.length == rows.length) s!"{name}: a row is missing"
    for ((row, model), (transaction, expected)) in (observed.toList.zip modelled).zip rows do
      check s!"{name} {transaction.id}" row model expected
  -- A changed Word fails: the second scenario's first row with another tag.
  let some (transaction, expected) := dynamicRows.head? | throw (IO.userError "no dynamic row")
  let some shape := Solcore.Synthesis.Source.EnumReturn.Shape.ofList?
      [⟨"Blob", .boundedBytes⟩, ⟨"Ready", .oneWord⟩, ⟨"Settled", .twoWords⟩, ⟨"Rejected", .noWords⟩]
    | throw (IO.userError "no shape")
  let some plan := EnumReturn.CheckedPlan.ofParts? (← step 1) shape | throw (IO.userError "no plan")
  let history := EnumReturnExecution.observe plan [transaction] StorageExecution.fixtureBindings fuel
  let observed ← get (history.getObjValAs? (Array Json) "transactions")
  ensure ((observed[0]?.bind fun row => (row.getObjValAs? String "output").toOption) ==
      some ("0x" ++ expected.output) &&
    (observed[0]?.bind fun row => (row.getObjValAs? String "output").toOption) !=
      some ("0x" ++ (expected.output.replace tagBlobBytes tagQBytes)))
    "a changed tag is not detected"

end Tests.SourceEnumReturnGolden
