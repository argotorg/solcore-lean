import Solcore.Synthesis.Source.EnumArgumentCases

/-! Golden cases for the enum-argument profile: the decoder's exact acceptance
and refusals. Every expected row is written out as hexadecimal text computed
outside Lean from the definitions and the probe's reading of std's decoder, not
by either model, with tags and selectors from `cast keccak`. The steps add a
known constant `c`, so an accepted transaction computes
`r = slot 0 + index + w0 + w1 + w2 + c`, writes `r`, the one-based index and the
decoded Words to slots 0 to 4, and returns `r`; odd decoded flags revert with
`r` and keep the prior slots. A rejection is std's revert data: an error
selector, or nothing for an unknown tag. The scenarios cover static and
dynamic shapes, every field kind with the struct, `bytes` lengths 0, 1, 17, 31,
32, 33, 63 and 64, every malformation kind with accepted and rejected entries,
and the order of the checks. Original Core gives each row under the selector
and empty-revert rules, and the Lean model gives it exactly. -/
set_option autoImplicit false

namespace Tests.SourceEnumArgumentGolden

open Lean
open Solcore.Core (Word)
open Solcore.ContractRuntime
open Solcore.Synthesis.Core
open Solcore.Synthesis.Core.EnumArgument (Constructor Shape)
open Solcore.Synthesis.Stateful
open Solcore.Synthesis.Stateful.EnumArgumentExecution (Transaction Malformation)

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

/-- The expected row: status, std's whole return or revert data as hexadecimal
text, empty for an unknown tag, and slots zero to four. -/
private structure Expected where
  status : String
  output : String
  values : List Nat

private def slots (values : List Nat) : Json :=
  toJson ((List.range EnumArgument.slotCount).map fun slot => Json.mkObj [
    ("slot", toJson (toString slot)), ("value", toJson (toString (values.getD slot 0)))])

private def tx (index flags choice first second length : Nat) (malformation : Malformation) : Transaction :=
  ⟨"tx-" ++ toString index, w flags, choice, w first, w second, length, malformation⟩

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
-- Ready(uint256,uint256)
private def tagReadyStruct : String := "1ee0fddb687f7d726adbdd32a0b3afe38d0593fe9dc00a18a5f4acd116e8b7c9"
-- Rejected()
private def tagRejectedUnit : String := "efde6dcf3c2196c5705e848c09f0659d33de3ca0248be3ab40852d1bafc0f1e3"
-- Settled(uint256,uint256)
private def tagSettledPair : String := "f5b268a3ff315cc44ccceeef86259c9e8eef81ceecb14001543809115380dd62"

-- The selectors of `run(uint256,sum(...))`, as `cast keccak` writes them.
-- run(uint256,sum(uint256,uint256,sum(,uint256)))
private def selectorStaticWords : String := "0x4461c0ed"
-- run(uint256,sum(bytes,sum(uint256,sum(uint256,uint256,))))
private def selectorDynamicWords : String := "0x62de7816"
-- run(uint256,sum(bytes,bytes))
private def selectorTwoBytes : String := "0xf5cc4c83"
-- run(uint256,sum(uint256,uint256,sum(,bytes)))
private def selectorStructFields : String := "0x89fd1ec1"
-- run(uint256,sum(,))
private def selectorTagsOnly : String := "0x9350d233"

private def staticWordsRows : List (Transaction × Expected) := [
  (tx 0 0 0 7 9 0 .none, ⟨"returned",
      "0000000000000000000000000000000000000000000000000000000000000016",
      [22, 1, 7, 9, 0]⟩),
  (tx 1 1 1 0 0 0 .none, ⟨"reverted",
      "000000000000000000000000000000000000000000000000000000000000001d",
      [22, 1, 7, 9, 0]⟩),
  (tx 2 0 2 (2 ^ 256 - 1) 0 0 (.unused (w (2 ^ 256 - 1))), ⟨"returned",
      "000000000000000000000000000000000000000000000000000000000000001d",
      [29, 3, (2 ^ 256 - 1), 0, 0]⟩),
  (tx 3 0 2 3 0 0 (.tag (w 0)), ⟨"reverted",
      "",
      [29, 3, (2 ^ 256 - 1), 0, 0]⟩),
  (tx 4 0 0 1 2 0 (.truncate 131), ⟨"reverted",
      "08638556",
      [29, 3, (2 ^ 256 - 1), 0, 0]⟩),
  (tx 5 0 1 0 0 0 (.short 3), ⟨"reverted",
      "4924aef0",
      [29, 3, (2 ^ 256 - 1), 0, 0]⟩),
  (tx 6 0 2 4 0 0 (.selector 1), ⟨"reverted",
      "4924aef0",
      [29, 3, (2 ^ 256 - 1), 0, 0]⟩),
  (tx 7 2 0 6 8 0 (.retag 1), ⟨"returned",
      "0000000000000000000000000000000000000000000000000000000000000024",
      [36, 2, 0, 0, 0]⟩)]

private def dynamicWordsRows : List (Transaction × Expected) := [
  (tx 0 0 0 1 2 33 .none, ⟨"returned",
      "da3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18eb8",
      [0xda3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18eb8, 1, 33, 0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95, 0x3c00000000000000000000000000000000000000000000000000000000000000]⟩),
  (tx 1 0 1 (2 ^ 255) 0 0 .none, ⟨"returned",
      "5a3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18ebb",
      [0x5a3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18ebb, 2, (2 ^ 255), 0, 0]⟩),
  (tx 2 0 2 3 7 0 (.offset (w 160)), ⟨"reverted",
      "08638556",
      [0x5a3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18ebb, 2, (2 ^ 255), 0, 0]⟩),
  (tx 3 0 3 0 0 0 (.aliased 1), ⟨"returned",
      "5a3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18ebe",
      [0x5a3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18ebe, 2, 0, 0, 0]⟩),
  (tx 4 0 0 1 1 1 (.tail (w 0)), ⟨"reverted",
      "08638556",
      [0x5a3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18ebe, 2, 0, 0, 0]⟩),
  (tx 5 0 0 3 1 1 (.length (w 32)), ⟨"returned",
      "343779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18ee0",
      [0x343779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18ee0, 1, 32, 0xda00000000000000000000000000000000000000000000000000000000000000, 0]⟩),
  (tx 6 0 2 5 5 0 (.truncate 100), ⟨"reverted",
      "08638556",
      [0x343779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18ee0, 1, 32, 0xda00000000000000000000000000000000000000000000000000000000000000, 0]⟩),
  (tx 7 0 1 9 0 0 (.truncate 132), ⟨"returned",
      "343779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18eec",
      [0x343779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18eec, 2, 9, 0, 0]⟩)]

private def twoBytesRows : List (Transaction × Expected) := [
  (tx 0 0 1 1 0 1 .none, ⟨"returned",
      "9e00000000000000000000000000000000000000000000000000000000000005",
      [0x9e00000000000000000000000000000000000000000000000000000000000005, 2, 1, 0x9e00000000000000000000000000000000000000000000000000000000000000, 0]⟩),
  (tx 1 0 0 2 3 31 .none, ⟨"returned",
      "da6ef372fe94f82be73980c0b9db906821044ed7e744e4a3f0d8d423a1831d27",
      [0xda6ef372fe94f82be73980c0b9db906821044ed7e744e4a3f0d8d423a1831d27, 1, 31, 0x3c6ef372fe94f82be73980c0b9db906821044ed7e744e4a3f0d8d423a1831d00, 0]⟩),
  (tx 2 0 1 3 4 32 .none, ⟨"returned",
      "b515609f7c746c6dc20fc1e1d0a4e904528ac51bc22c3b99da1e125913c7c90a",
      [0xb515609f7c746c6dc20fc1e1d0a4e904528ac51bc22c3b99da1e125913c7c90a, 2, 32, 0xdaa66d2c7ddf7441dad6412116c9589c31867643dae756f5e9453e357244abbf, 0]⟩),
  (tx 3 0 0 4 5 63 (.truncate 227), ⟨"returned",
      "4508a824f612c933529285451500f2d8e71e27e752e2407b95edccf96a95cba0",
      [0x4508a824f612c933529285451500f2d8e71e27e752e2407b95edccf96a95cba0, 1, 63, 0x78dde6e5fd29f057ce73018173b720d042089dafce89c947e1b1a84743063a54, 0x1715609f7c746c6dc20fc1e1d0a4e904528ac51bc22c3b99da1e125913c7c800]⟩),
  (tx 4 0 1 5 6 64 .none, ⟨"returned",
      "116ae31d6e461e24ca4ec96913388d159cb5d98acadd2a0142965bbd62e6ec4b",
      [0x116ae31d6e461e24ca4ec96913388d159cb5d98acadd2a0142965bbd62e6ec4b, 2, 64, 0x1715609f7c746c6dc20fc1e1d0a4e904528ac51bc22c3b99da1e125913c7c8e9, 0xb54cda58fbbee883b5ac82422d92b138630cec87b5ceadebd28a7c6ae489577e]⟩),
  (tx 5 0 0 6 7 0 .none, ⟨"returned",
      "116ae31d6e461e24ca4ec96913388d159cb5d98acadd2a0142965bbd62e6ec4e",
      [0x116ae31d6e461e24ca4ec96913388d159cb5d98acadd2a0142965bbd62e6ec4e, 1, 0, 0, 0]⟩),
  (tx 6 0 1 7 8 17 (.padding 1), ⟨"returned",
      "64ef372fe94f82be73980c0b9db906820fb5d98acadd2a0142965bbd62e6ec63",
      [0x64ef372fe94f82be73980c0b9db906820fb5d98acadd2a0142965bbd62e6ec63, 2, 17, 0x538454127b096499a94942a28a80796c73000000000000000000000000000000, 0]⟩),
  (tx 7 0 0 8 9 17 (.length (w 18)), ⟨"returned",
      "56ab04fbe3a3636e107e0f0e8527482293b5d98acadd2a0142965bbd62e6ec78",
      [0x56ab04fbe3a3636e107e0f0e8527482293b5d98acadd2a0142965bbd62e6ec78, 1, 18, 0xf1bbcdcbfa53e0af9ce60302e76e41a084000000000000000000000000000000, 0]⟩)]

private def structFieldsRows : List (Transaction × Expected) := [
  (tx 0 0 0 11 12 0 .none, ⟨"returned",
      "000000000000000000000000000000000000000000000000000000000000001b",
      [27, 1, 11, 12, 0]⟩),
  (tx 1 0 2 0 0 0 .none, ⟨"returned",
      "0000000000000000000000000000000000000000000000000000000000000021",
      [33, 3, 0, 0, 0]⟩),
  (tx 2 0 1 0 0 0 (.trailing 33 1), ⟨"returned",
      "0000000000000000000000000000000000000000000000000000000000000026",
      [38, 2, 0, 0, 0]⟩),
  (tx 3 0 0 13 14 0 (.retag 2), ⟨"reverted",
      "08638556",
      [38, 2, 0, 0, 0]⟩),
  (tx 4 0 1 0 0 0 (.offset (w 32)), ⟨"reverted",
      "",
      [38, 2, 0, 0, 0]⟩),
  (tx 5 0 0 1 1 0 (.tag (w 99)), ⟨"reverted",
      "",
      [38, 2, 0, 0, 0]⟩)]

private def tagsOnlyRows : List (Transaction × Expected) := [
  (tx 0 0 1 0 0 0 .none, ⟨"returned",
      "0000000000000000000000000000000000000000000000000000000000000006",
      [6, 2, 0, 0, 0]⟩),
  (tx 1 0 0 0 0 0 (.trailing 1 0), ⟨"returned",
      "000000000000000000000000000000000000000000000000000000000000000b",
      [11, 1, 0, 0, 0]⟩),
  (tx 2 3 1 0 0 0 .none, ⟨"reverted",
      "0000000000000000000000000000000000000000000000000000000000000011",
      [11, 1, 0, 0, 0]⟩),
  (tx 3 0 0 0 0 0 (.truncate 67), ⟨"reverted",
      "08638556",
      [11, 1, 0, 0, 0]⟩),
  (tx 4 0 1 0 0 0 (.tag (w (2 ^ 255))), ⟨"reverted",
      "",
      [11, 1, 0, 0, 0]⟩)]

private def scenarios : List (String × Nat × List Constructor × String × String × List (Transaction × Expected)) := [
    ("static-words", 5, [⟨"Pair", .twoWords⟩, ⟨"Idle", .noWords⟩, ⟨"Q", .oneWord⟩],
      "run(uint256,sum(uint256,uint256,sum(,uint256)))", selectorStaticWords, staticWordsRows),
    ("dynamic-words", 1, [⟨"Blob", .bytes⟩, ⟨"Ready", .oneWord⟩, ⟨"Settled", .twoWords⟩, ⟨"Rejected", .noWords⟩],
      "run(uint256,sum(bytes,sum(uint256,sum(uint256,uint256,))))", selectorDynamicWords, dynamicWordsRows),
    ("two-bytes", 2, [⟨"OverflowedAccumulator", .bytes⟩, ⟨"Q", .bytes⟩],
      "run(uint256,sum(bytes,bytes))", selectorTwoBytes, twoBytesRows),
    ("struct-fields", 3, [⟨"Ready", .pair⟩, ⟨"Idle", .noWords⟩, ⟨"Blob", .bytes⟩],
      "run(uint256,sum(uint256,uint256,sum(,bytes)))", selectorStructFields, structFieldsRows),
    ("tags-only", 4, [⟨"Idle", .noWords⟩, ⟨"Ready", .noWords⟩],
      "run(uint256,sum(,))", selectorTagsOnly, tagsOnlyRows)]

/-- Original Core reverts with one Word: an error selector stands for std's
four bytes and the Word zero for its empty revert data. -/
private def coreOutput (output : String) : String :=
  "0x" ++ if output.length == 8 then String.ofList (List.replicate 56 '0') ++ output
    else if output.isEmpty then String.ofList (List.replicate 64 '0') else output

private def check (name : String) (row : Json) (model : EnumArgumentExecution.ModelRow) (expected : Expected) :
    IO Unit := do
  ensure ((row.getObjValAs? String "status").toOption == some expected.status &&
      (row.getObjValAs? String "output").toOption == some (coreOutput expected.output) &&
      (row.getObjVal? "committedStorage").toOption == some (slots expected.values))
    s!"{name}: original Core differs from the expected row {row.compress}"
  ensure (model.reverted == (expected.status == "reverted") &&
      encodeBytesText model.output == "0x" ++ expected.output &&
      model.slots == (List.range EnumArgument.slotCount).map (fun slot => w (expected.values.getD slot 0)))
    s!"{name}: the Lean model differs from the expected row"

/-- Original Core's status and output on raw calldata from empty storage. -/
private def runRaw (contract : CheckedCoreContract) (bytes : ByteArray) : IO (String × String) := do
  let bindings := StorageExecution.fixtureBindings
  let registry : CheckedContractRegistry := {
    lookup := fun target => if target = bindings.address then some contract else none }
  let world := StorageExecution.initialWorldForContract contract bindings
  if bounded : bytes.size < Solcore.Core.wordModulus then
    let some ⟨resolved, installed⟩ := registry.resolve? world bindings.address
      | throw (IO.userError "the contract did not resolve")
    let invocation : TopLevelInvocation := {
      target := bindings.address, caller := bindings.caller, callValue := Word.zero,
      inputData := ⟨bytes, bounded⟩ }
    match TopLevelExecution.run resolved invocation installed 1000000 with
    | .completed terminal =>
        match terminal.outcome with
        | .returned out => return ("returned", encodeBytesText out)
        | .reverted out => return ("reverted", encodeBytesText out)
        | .trapped _ => return ("trapped", "")
    | .outOfFuel .. => return ("out-of-fuel", "")
  else throw (IO.userError "calldata exceeds the Word bound")

/-- std's decisions that one malformation cannot reach, on raw calldata of the
second scenario's `Settled(3, 7)`: the selector is checked before the head, the
offset before the tag, and the tag before any field is read. -/
private def orderRows (shape : Shape) : List (String × ByteArray × String) :=
  let canonical := EnumArgumentExecution.inputBytes shape (tx 0 0 2 3 7 0 .none)
  let unknown := StdCalldata.replaceWord canonical 68 (w 7)
  let wrong := StdCalldata.Change.apply canonical (.selector 1)
  [("unknown tag, fields cut", unknown.extract 0 100, ""),
    ("unknown tag, offset past the end", StdCalldata.replaceWord unknown 36 (w (unknown.size - 3)), "08638556"),
    ("wrong selector, head cut", wrong.extract 0 40, "4924aef0"),
    ("known tag, fields cut", canonical.extract 0 131, "08638556"),
    ("known tag, unread padding cut", canonical.extract 0 164, "")]

def testSourceEnumArgumentGolden : IO Unit := do
  let fuel := 1000000
  -- Lean's Keccak-256 tags equal the ones written out; a struct's tag is its fields'.
  ensure (encodeBytesText (encodeWordBytesBE (EnumArgument.tag ⟨"Ready", .pair⟩)) == "0x" ++ tagReadyStruct &&
      EnumArgument.tag ⟨"Ready", .pair⟩ == EnumArgument.tag ⟨"Ready", .twoWords⟩ &&
      encodeBytesText (encodeWordBytesBE (EnumArgument.tag ⟨"Q", .bytes⟩)) == "0x" ++ tagQBytes &&
      encodeBytesText (encodeWordBytesBE (EnumArgument.tag ⟨"Idle", .noWords⟩)) == "0x" ++ tagIdleUnit)
    "a constructor tag differs from keccak256 of its signature"
  for (name, constant, constructors, signature, selector, rows) in scenarios do
    let step ← step constant
    let some shape := Solcore.Synthesis.Source.EnumArgument.Shape.ofList? constructors
      | throw (IO.userError s!"{name}: the shape has fewer than two constructors")
    ensure (shape.signature == signature && Solcore.Synthesis.Source.EnumArgument.selectorText shape == selector)
      s!"{name}: the signature or selector differs from std's structural signature"
    let some plan := EnumArgument.CheckedPlan.ofParts? step shape
      | throw (IO.userError s!"{name}: the enum-argument wrapper failed admission")
    let transactions := rows.map Prod.fst
    for (transaction, expected) in rows do
      let rejected := expected.status == "reverted" && expected.output.length != 64
      ensure (Solcore.Synthesis.Source.EnumArgument.prescribed shape transaction ==
          (if rejected then some ("0x" ++ expected.output) else none))
        s!"{name} {transaction.id}: the prescribed std outcome differs from the expected row"
    let history := EnumArgumentExecution.observe plan transactions StorageExecution.fixtureBindings fuel
    ensure ((history.getObjValAs? String "status").toOption == some "complete") s!"{name}: the history is incomplete"
    let observed ← get (history.getObjValAs? (Array Json) "transactions")
    let some modelled := EnumArgumentExecution.model step shape fuel transactions
      | throw (IO.userError s!"{name}: the Lean model failed")
    ensure (observed.size == rows.length && modelled.length == rows.length) s!"{name}: a row is missing"
    for ((row, model), (transaction, expected)) in (observed.toList.zip modelled).zip rows do
      check s!"{name} {transaction.id}" row model expected
  -- The order of std's checks, on raw calldata, for Core and the Lean model alike.
  let some (_, _, constructors, _, _, _) := scenarios[1]? | throw (IO.userError "no dynamic scenario")
  let some shape := Solcore.Synthesis.Source.EnumArgument.Shape.ofList? constructors | throw (IO.userError "no shape")
  let some plan := EnumArgument.CheckedPlan.ofParts? (← step 1) shape | throw (IO.userError "no plan")
  for (label, bytes, expected) in orderRows shape do
    let (status, output) ← runRaw plan.contract bytes
    let decided := match EnumArgumentExecution.stdDecode shape bytes with
      | .error data => some (encodeBytesText data)
      | .ok _ => none
    if expected.isEmpty && label.endsWith "padding cut" then
      ensure (status == "returned" && decided.isNone) s!"{label}: the cut padding was not accepted"
    else
      ensure (status == "reverted" && output == coreOutput expected && decided == some ("0x" ++ expected))
        s!"{label}: std's order of checks differs ({status} {output})"
  -- A changed expectation fails: the first static row read as a rejection.
  let some (transaction, expected) := staticWordsRows.head? | throw (IO.userError "no static row")
  ensure (Solcore.Synthesis.Source.EnumArgument.prescribed (← (Solcore.Synthesis.Source.EnumArgument.Shape.ofList?
        [⟨"Pair", .twoWords⟩, ⟨"Idle", .noWords⟩, ⟨"Q", .oneWord⟩]).getDM
        (throw (IO.userError "no shape"))) transaction == none &&
      coreOutput expected.output != coreOutput "08638556")
    "a changed expectation is not detected"

end Tests.SourceEnumArgumentGolden
