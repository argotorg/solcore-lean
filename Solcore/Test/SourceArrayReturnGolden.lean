import Solcore.Synthesis.Source.ArrayReturnCases

/-! Golden cases for the array-return profile. Every expected row is written out
as hexadecimal Words computed outside Lean from the protocol and the ABI
encoding of `uint256[]`, `bytes4[]`, `bytes[]` and `uint256[][]`, not by
either model. The steps add a known constant `c`, so a transaction computes
`r = slot 0 + input + c`, writes `r` to slot 0, slot 1 plus one to slot 1 and the
input to slot 2, and returns std's encoding of the plan's array, element `i`
built from `a = r · K + i` and `b = ((slot 1 · K) xor (prior slot 2)) + i`: the
offset 32 and the length, then inline Words, or one offset per element and the
element tails. Odd flags revert with `r` and keep the prior slots. The scenarios
cover every element type, counts 0 to 3, the `bytes` lengths 0, 1, 31, 32, 33,
63 and 64, inner lengths 0 to 2, both outcomes, carries past a revert and
wrapping sums. Both the Core contract and the source model must give each row,
and a changed Word must be detected. -/
set_option autoImplicit false

namespace Tests.SourceArrayReturnGolden

open Lean
open Solcore.Core (Word)
open Solcore.ContractRuntime
open Solcore.Synthesis.Core
open Solcore.Synthesis.Core.ArrayReturn (Element Shape)
open Solcore.Synthesis.Stateful
open Solcore.Synthesis.Stateful.ArrayReturnExecution (Transaction)

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

/-- The expected row: status, the whole output as hexadecimal Words and slots
zero to two. -/
private structure Expected where
  status : String
  output : List String
  values : List Nat

private def slots (values : List Nat) : Json :=
  toJson ((List.range ArrayReturn.slotCount).map fun slot => Json.mkObj [
    ("slot", toJson (toString slot)), ("value", toJson (toString (values.getD slot 0)))])

private def tx (shape : Shape) (index flags input : Nat) : Transaction :=
  Solcore.Synthesis.Source.ArrayReturn.shaped shape ("tx-" ++ toString index) (w flags) (w input)

/-- `uint256`, three elements, `c = 1`: the Words `r · K + i`; a revert keeps the
slots; the last sum wraps: 14 + (2^256 - 1) + 1 = 14. -/
private def wordsShape : Shape := ⟨.words, 3, []⟩

private def wordsRows : List (Transaction × Expected) := [
  (tx wordsShape 0 0 5, ⟨"returned", ["0000000000000000000000000000000000000000000000000000000000000020",
      "0000000000000000000000000000000000000000000000000000000000000003",
      "b54cda58fbbee883b5ac82422d92b138630cec87b5ceadebd28a7c6ae489577e",
      "b54cda58fbbee883b5ac82422d92b138630cec87b5ceadebd28a7c6ae489577f",
      "b54cda58fbbee883b5ac82422d92b138630cec87b5ceadebd28a7c6ae4895780"],
    [6, 1, 5]⟩),
  (tx wordsShape 1 1 9, ⟨"reverted", ["0000000000000000000000000000000000000000000000000000000000000010"],
    [6, 1, 5]⟩),
  (tx wordsShape 2 2 7, ⟨"returned", ["0000000000000000000000000000000000000000000000000000000000000020",
      "0000000000000000000000000000000000000000000000000000000000000003",
      "a708a824f612c933529285451500f2d8e71e27e752e2407b95edccf96a95cc26",
      "a708a824f612c933529285451500f2d8e71e27e752e2407b95edccf96a95cc27",
      "a708a824f612c933529285451500f2d8e71e27e752e2407b95edccf96a95cc28"],
    [14, 2, 7]⟩),
  (tx wordsShape 3 0 (2 ^ 256 - 1), ⟨"returned", ["0000000000000000000000000000000000000000000000000000000000000020",
      "0000000000000000000000000000000000000000000000000000000000000003",
      "a708a824f612c933529285451500f2d8e71e27e752e2407b95edccf96a95cc26",
      "a708a824f612c933529285451500f2d8e71e27e752e2407b95edccf96a95cc27",
      "a708a824f612c933529285451500f2d8e71e27e752e2407b95edccf96a95cc28"],
    [14, 3, (2 ^ 256 - 1)]⟩)]

/-- An empty array, `c = 0`: the offset and the length zero alone. -/
private def emptyShape : Shape := ⟨.words, 0, []⟩

private def emptyRows : List (Transaction × Expected) := [
  (tx emptyShape 0 0 3, ⟨"returned", ["0000000000000000000000000000000000000000000000000000000000000020",
      "0000000000000000000000000000000000000000000000000000000000000000"],
    [3, 1, 3]⟩),
  (tx emptyShape 1 3 4, ⟨"reverted", ["0000000000000000000000000000000000000000000000000000000000000007"],
    [3, 1, 3]⟩)]

/-- `bytes4`, two elements, `c = 0`: the low four bytes of `r · K + i`,
left-aligned; a first revert from empty storage; the last sum wraps. -/
private def fourBytesShape : Shape := ⟨.fourBytes, 2, []⟩

private def fourBytesRows : List (Transaction × Expected) := [
  (tx fourBytesShape 0 1 1, ⟨"reverted", ["0000000000000000000000000000000000000000000000000000000000000001"],
    [0, 0, 0]⟩),
  (tx fourBytesShape 1 0 10, ⟨"returned", ["0000000000000000000000000000000000000000000000000000000000000020",
      "0000000000000000000000000000000000000000000000000000000000000002",
      "278f91d200000000000000000000000000000000000000000000000000000000",
      "278f91d300000000000000000000000000000000000000000000000000000000"],
    [10, 1, 10]⟩),
  (tx fourBytesShape 2 0 (2 ^ 256 - 2), ⟨"returned", ["0000000000000000000000000000000000000000000000000000000000000020",
      "0000000000000000000000000000000000000000000000000000000000000002",
      "860c74a800000000000000000000000000000000000000000000000000000000",
      "860c74a900000000000000000000000000000000000000000000000000000000"],
    [8, 2, (2 ^ 256 - 2)]⟩)]

/-- `bytes` of 31, 32 and 33 bytes, `c = 1`: the offsets 96, 160 and 224, a
data Word cut to 31 bytes, one whole Word, and a Word and one byte of
`((count · K) xor last) + 2`. -/
private def bytesWordsShape : Shape := ⟨.bytes, 3, [31, 32, 33]⟩

private def bytesWordsRows : List (Transaction × Expected) := [
  (tx bytesWordsShape 0 0 5, ⟨"returned", ["0000000000000000000000000000000000000000000000000000000000000020",
      "0000000000000000000000000000000000000000000000000000000000000003",
      "0000000000000000000000000000000000000000000000000000000000000060",
      "00000000000000000000000000000000000000000000000000000000000000a0",
      "00000000000000000000000000000000000000000000000000000000000000e0",
      "000000000000000000000000000000000000000000000000000000000000001f",
      "b54cda58fbbee883b5ac82422d92b138630cec87b5ceadebd28a7c6ae4895700",
      "0000000000000000000000000000000000000000000000000000000000000020",
      "b54cda58fbbee883b5ac82422d92b138630cec87b5ceadebd28a7c6ae489577f",
      "0000000000000000000000000000000000000000000000000000000000000021",
      "b54cda58fbbee883b5ac82422d92b138630cec87b5ceadebd28a7c6ae4895780",
      "9e00000000000000000000000000000000000000000000000000000000000000"],
    [6, 1, 5]⟩),
  (tx bytesWordsShape 1 1 0, ⟨"reverted", ["0000000000000000000000000000000000000000000000000000000000000007"],
    [6, 1, 5]⟩),
  (tx bytesWordsShape 2 2 (2 ^ 255), ⟨"returned", ["0000000000000000000000000000000000000000000000000000000000000020",
      "0000000000000000000000000000000000000000000000000000000000000003",
      "0000000000000000000000000000000000000000000000000000000000000060",
      "00000000000000000000000000000000000000000000000000000000000000a0",
      "00000000000000000000000000000000000000000000000000000000000000e0",
      "000000000000000000000000000000000000000000000000000000000000001f",
      "d38454127b096499a94942a28a80796c738f13f3a971203dcaf6e67cb54ae600",
      "0000000000000000000000000000000000000000000000000000000000000020",
      "d38454127b096499a94942a28a80796c738f13f3a971203dcaf6e67cb54ae614",
      "0000000000000000000000000000000000000000000000000000000000000021",
      "d38454127b096499a94942a28a80796c738f13f3a971203dcaf6e67cb54ae615",
      "3c00000000000000000000000000000000000000000000000000000000000000"],
    [57896044618658097711785492504343953926634992332820282019728792003956564819975, 2, (2 ^ 255)]⟩)]

/-- `bytes` of 0, 63 and 64 bytes, `c = 0`: an empty element's length Word
alone, then both data Words, the second cut to 31 bytes, and both whole. -/
private def bytesEndsShape : Shape := ⟨.bytes, 3, [0, 63, 64]⟩

private def bytesEndsRows : List (Transaction × Expected) := [
  (tx bytesEndsShape 0 0 1, ⟨"returned", ["0000000000000000000000000000000000000000000000000000000000000020",
      "0000000000000000000000000000000000000000000000000000000000000003",
      "0000000000000000000000000000000000000000000000000000000000000060",
      "0000000000000000000000000000000000000000000000000000000000000080",
      "00000000000000000000000000000000000000000000000000000000000000e0",
      "0000000000000000000000000000000000000000000000000000000000000000",
      "000000000000000000000000000000000000000000000000000000000000003f",
      "9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e96",
      "9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e00",
      "0000000000000000000000000000000000000000000000000000000000000040",
      "9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e97",
      "9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e97"],
    [1, 1, 1]⟩),
  (tx bytesEndsShape 1 0 7, ⟨"returned", ["0000000000000000000000000000000000000000000000000000000000000020",
      "0000000000000000000000000000000000000000000000000000000000000003",
      "0000000000000000000000000000000000000000000000000000000000000060",
      "0000000000000000000000000000000000000000000000000000000000000080",
      "00000000000000000000000000000000000000000000000000000000000000e0",
      "0000000000000000000000000000000000000000000000000000000000000000",
      "000000000000000000000000000000000000000000000000000000000000003f",
      "f1bbcdcbfa53e0af9ce60302e76e41a084113b5f9d13928fc363508e860c74a9",
      "3c6ef372fe94f82be73980c0b9db906821044ed7e744e4a3f0d8d423a1831d00",
      "0000000000000000000000000000000000000000000000000000000000000040",
      "f1bbcdcbfa53e0af9ce60302e76e41a084113b5f9d13928fc363508e860c74aa",
      "3c6ef372fe94f82be73980c0b9db906821044ed7e744e4a3f0d8d423a1831d2d"],
    [8, 2, 7]⟩)]

/-- One `bytes` element of one byte, `c = 1`, around a revert; the last sum
wraps. -/
private def bytesOneShape : Shape := ⟨.bytes, 1, [1]⟩

private def bytesOneRows : List (Transaction × Expected) := [
  (tx bytesOneShape 0 0 3, ⟨"returned", ["0000000000000000000000000000000000000000000000000000000000000020",
      "0000000000000000000000000000000000000000000000000000000000000001",
      "0000000000000000000000000000000000000000000000000000000000000020",
      "0000000000000000000000000000000000000000000000000000000000000001",
      "7800000000000000000000000000000000000000000000000000000000000000"],
    [4, 1, 3]⟩),
  (tx bytesOneShape 1 3 0, ⟨"reverted", ["0000000000000000000000000000000000000000000000000000000000000005"],
    [4, 1, 3]⟩),
  (tx bytesOneShape 2 0 (2 ^ 256 - 1), ⟨"returned", ["0000000000000000000000000000000000000000000000000000000000000020",
      "0000000000000000000000000000000000000000000000000000000000000001",
      "0000000000000000000000000000000000000000000000000000000000000020",
      "0000000000000000000000000000000000000000000000000000000000000001",
      "7800000000000000000000000000000000000000000000000000000000000000"],
    [4, 2, (2 ^ 256 - 1)]⟩)]

/-- `uint256[]` of zero, one and two Words, `c = 1`: the inner lengths and
Words behind the offsets 96, 128 and 192. -/
private def nestedShape : Shape := ⟨.nested, 3, [0, 1, 2]⟩

private def nestedRows : List (Transaction × Expected) := [
  (tx nestedShape 0 0 5, ⟨"returned", ["0000000000000000000000000000000000000000000000000000000000000020",
      "0000000000000000000000000000000000000000000000000000000000000003",
      "0000000000000000000000000000000000000000000000000000000000000060",
      "0000000000000000000000000000000000000000000000000000000000000080",
      "00000000000000000000000000000000000000000000000000000000000000c0",
      "0000000000000000000000000000000000000000000000000000000000000000",
      "0000000000000000000000000000000000000000000000000000000000000001",
      "b54cda58fbbee883b5ac82422d92b138630cec87b5ceadebd28a7c6ae489577f",
      "0000000000000000000000000000000000000000000000000000000000000002",
      "b54cda58fbbee883b5ac82422d92b138630cec87b5ceadebd28a7c6ae4895780",
      "9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e97"],
    [6, 1, 5]⟩),
  (tx nestedShape 1 1 1, ⟨"reverted", ["0000000000000000000000000000000000000000000000000000000000000008"],
    [6, 1, 5]⟩),
  (tx nestedShape 2 0 2, ⟨"returned", ["0000000000000000000000000000000000000000000000000000000000000020",
      "0000000000000000000000000000000000000000000000000000000000000003",
      "0000000000000000000000000000000000000000000000000000000000000060",
      "0000000000000000000000000000000000000000000000000000000000000080",
      "00000000000000000000000000000000000000000000000000000000000000c0",
      "0000000000000000000000000000000000000000000000000000000000000000",
      "0000000000000000000000000000000000000000000000000000000000000001",
      "8ff34785799e5cc59082c363445c09d4949362cb90b604e1bbcfbaa056ce033e",
      "0000000000000000000000000000000000000000000000000000000000000002",
      "8ff34785799e5cc59082c363445c09d4949362cb90b604e1bbcfbaa056ce033f",
      "3c6ef372fe94f82be73980c0b9db906821044ed7e744e4a3f0d8d423a1831d31"],
    [9, 2, 2]⟩)]

/-- Two inner arrays of two and zero Words, `c = 0`, after a first revert. -/
private def nestedTwoShape : Shape := ⟨.nested, 2, [2, 0]⟩

private def nestedTwoRows : List (Transaction × Expected) := [
  (tx nestedTwoShape 0 1 0, ⟨"reverted", ["0000000000000000000000000000000000000000000000000000000000000000"],
    [0, 0, 0]⟩),
  (tx nestedTwoShape 1 0 (2 ^ 255), ⟨"returned", ["0000000000000000000000000000000000000000000000000000000000000020",
      "0000000000000000000000000000000000000000000000000000000000000002",
      "0000000000000000000000000000000000000000000000000000000000000040",
      "00000000000000000000000000000000000000000000000000000000000000a0",
      "0000000000000000000000000000000000000000000000000000000000000002",
      "8000000000000000000000000000000000000000000000000000000000000000",
      "9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95",
      "0000000000000000000000000000000000000000000000000000000000000000"],
    [(2 ^ 255), 1, (2 ^ 255)]⟩)]

private def scenarios : List (String × Nat × Shape × List (Transaction × Expected)) := [
  ("words", 1, wordsShape, wordsRows),
  ("empty", 0, emptyShape, emptyRows),
  ("fourBytes", 0, fourBytesShape, fourBytesRows),
  ("bytesWords", 1, bytesWordsShape, bytesWordsRows),
  ("bytesEnds", 0, bytesEndsShape, bytesEndsRows),
  ("bytesOne", 1, bytesOneShape, bytesOneRows),
  ("nested", 1, nestedShape, nestedRows),
  ("nestedTwo", 0, nestedTwoShape, nestedTwoRows)]

/-- Whether original Core's row and the source model's row both equal the
expected row. -/
private def agrees (row : Json) (model : ArrayReturnExecution.ModelRow) (expected : Expected) : Bool :=
  let output := "0x" ++ String.join expected.output
  (row.getObjValAs? String "status").toOption == some expected.status &&
    (row.getObjValAs? String "output").toOption == some output &&
    (row.getObjVal? "committedStorage").toOption == some (slots expected.values) &&
    model.reverted == (expected.status == "reverted") && encodeBytesText model.output == output &&
    model.slots == (List.range ArrayReturn.slotCount).map (fun slot => w (expected.values.getD slot 0))

/-- Original Core's rows and the source model's rows of a scenario. -/
private def observed (constant : Nat) (shape : Shape) (transactions : List Transaction) :
    IO (List (Json × ArrayReturnExecution.ModelRow)) := do
  let fuel := 1000000
  let step ← step constant
  let some plan := ArrayReturn.CheckedPlan.ofParts? step shape
    | throw (IO.userError "the array-return wrapper failed admission")
  ensure (plan.contract.entryProfile == .wordTupleOutcomeV1 shape.bodyWords)
    "the contract does not use the Word-tuple convention of its encoding's Words"
  let history := ArrayReturnExecution.observe plan transactions StorageExecution.fixtureBindings fuel
  ensure ((history.getObjValAs? String "status").toOption == some "complete") "the history is incomplete"
  let rows ← get (history.getObjValAs? (Array Json) "transactions")
  let some modelled := ArrayReturnExecution.model step fuel shape.element transactions
    | throw (IO.userError "the source model failed")
  ensure (rows.size == transactions.length && modelled.length == transactions.length) "a row is missing"
  return rows.toList.zip modelled

def testSourceArrayReturnGolden : IO Unit := do
  ensure (Solcore.Synthesis.Source.ArrayReturn.multiplierLiteral ==
      "0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95")
    "the emitted multiplier differs from the defined constant"
  for (name, constant, shape, rows) in scenarios do
    let pairs ← observed constant shape (rows.map Prod.fst)
    for ((row, model), (transaction, expected)) in pairs.zip rows do
      ensure (agrees row model expected)
        s!"{name} {transaction.id}: original Core or the source model differs from the expected row {row.compress}"
  -- A changed Word, here the second element's Word of the first `uint256`
  -- row, is detected.
  let some (transaction, expected) := wordsRows.head? | throw (IO.userError "no uint256 row")
  let pairs ← observed 1 wordsShape [transaction]
  let some (row, model) := pairs.head? | throw (IO.userError "no observed row")
  let changed := expected.output.set 3 "b54cda58fbbee883b5ac82422d92b138630cec87b5ceadebd28a7c6ae489577e"
  ensure (!agrees row model {expected with output := changed}) "a changed Word was not detected"
  -- The 32nd byte of the 31-byte element's first data Word is nonzero in the
  -- method's memory and zero in the output.
  let some (transaction, expected) := bytesWordsRows.head? | throw (IO.userError "no bytes row")
  let a := w 6 * w ArrayReturn.multiplier
  ensure (a.val % 256 != 0) "the memory byte after the 31-byte element is zero"
  let some data := expected.output[6]? | throw (IO.userError "no data Word")
  ensure (data.endsWith "00" && data.take 62 == (String.ofList (Nat.toDigits 16 a.val)).take 62)
    "the 31-byte element is not its Word cut to 31 bytes"
  let pairs ← observed 1 bytesWordsShape [transaction]
  let some (row, model) := pairs.head? | throw (IO.userError "no observed row")
  ensure (agrees row model expected) "the 31-byte element's padding is not zero"

end Tests.SourceArrayReturnGolden
