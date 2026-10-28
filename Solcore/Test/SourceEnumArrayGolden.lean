import Solcore.Synthesis.Source.EnumArrayCases

/-! Golden cases for the enum-array profile: std's exact acceptance and
refusals of calldata arrays of a user enum. Every expected row is written out
as hexadecimal text computed outside Lean from the definitions, by the probe's
independent model of std's decoder, which equalled imported Hull and Sonatina
O0, O2 and Yul on Anvil on every probe transaction, not by either Lean model;
tags and selectors come from `cast keccak`. The steps add a known constant `c`,
so an accepted transaction computes `r = slot 0 + L + both elements' index and
Words + c`, writes `r`, the length and both elements to slots 0 to 9, and
returns `r`; odd decoded flags revert with `r` and keep the prior slots. A
rejection is std's revert data: an error selector, `ArrayOutOfBounds()` among
them, or nothing for an unknown tag. The scenarios cover static and dynamic
element types, every field kind with the struct, empty and three-element
arrays, indices past the length and at `2^256 - 1`, unread malformed elements,
shared bodies, every malformation kind with accepted and rejected entries, and
the order of the checks. Original Core gives each row under the selector and
empty-revert rules, and the Lean model gives it exactly. -/
set_option autoImplicit false

namespace Tests.SourceEnumArrayGolden

open Lean
open Solcore.Core (Word)
open Solcore.ContractRuntime
open Solcore.Synthesis.Core
open Solcore.Synthesis.Core.EnumArgument (Constructor Shape)
open Solcore.Synthesis.Stateful
open Solcore.Synthesis.Stateful.EnumArrayExecution (Element Transaction Malformation)

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
text, empty for an unknown tag, and slots zero to nine. -/
private structure Expected where
  status : String
  output : String
  values : List Nat

private def slots (values : List Nat) : Json :=
  toJson ((List.range EnumArray.slotCount).map fun slot => Json.mkObj [
    ("slot", toJson (toString slot)), ("value", toJson (toString (values.getD slot 0)))])

private def el (choice a b length : Nat) : Element := ⟨choice, w a, w b, length⟩

private def tx (index flags : Nat) (elements : List Element) (first second : Nat) (malformation : Malformation) :
    Transaction :=
  ⟨"tx-" ++ toString index, w flags, elements, w first, w second, malformation⟩

-- The tags `keccak256("Name(fields)")`, as `cast keccak` writes them.
-- Blob(bytes)
private def tagBlobBytes : String := "d05ce3dc4caf4a4b252e3323bde615dc3b9d54623e1859c892f0b4ecf5e45164"
-- Idle()
private def tagIdleUnit : String := "ae897c555b7596dee56949d599aa959af71416324ac27ef76dd898923ab34d4f"
-- Ready()
private def tagReadyUnit : String := "6e12fa0ff1c6b8acb2181ba65fc2867fd8d895d0af9f39674b64abc5ff79275b"
-- Ready(uint256,uint256)
private def tagReadyStruct : String := "1ee0fddb687f7d726adbdd32a0b3afe38d0593fe9dc00a18a5f4acd116e8b7c9"
-- Rejected()
private def tagRejectedUnit : String := "efde6dcf3c2196c5705e848c09f0659d33de3ca0248be3ab40852d1bafc0f1e3"

-- The selectors of `run(uint256,S[],uint256,uint256)`, as `cast keccak` writes them.
-- run(uint256,sum(uint256,uint256,sum(,uint256))[],uint256,uint256)
private def selectorStaticWords : String := "0x7b340d0f"
-- run(uint256,sum(bytes,sum(uint256,sum(uint256,uint256,)))[],uint256,uint256)
private def selectorDynamicWords : String := "0x6c89cba6"
-- run(uint256,sum(bytes,bytes)[],uint256,uint256)
private def selectorTwoBytes : String := "0xbde4b3a9"
-- run(uint256,sum(uint256,uint256,sum(,bytes))[],uint256,uint256)
private def selectorStructFields : String := "0x7608c09b"
-- run(uint256,sum(,)[],uint256,uint256)
private def selectorTagsOnly : String := "0x2dde7185"

private def staticWordsRows : List (Transaction × Expected) := [
  (tx 0 0 [el 0 7 9 0, el 2 3 0 0] 0 1 .none,
    ⟨"returned", "000000000000000000000000000000000000000000000000000000000000001e", [30, 2, 1, 7, 9, 0, 3, 3, 0, 0]⟩),
  (tx 1 1 [el 1 0 0 0] 0 0 .none,
    ⟨"reverted", "0000000000000000000000000000000000000000000000000000000000000028", [30, 2, 1, 7, 9, 0, 3, 3, 0, 0]⟩),
  (tx 2 0 [el 2 (2 ^ 256 - 1) 0 0, el 1 0 0 0] 0 1 (.unused 1 (w (2 ^ 256 - 1))),
    ⟨"returned", "0000000000000000000000000000000000000000000000000000000000000029", [41, 2, 3, (2 ^ 256 - 1), 0, 0, 2, 0, 0, 0]⟩),
  (tx 3 0 [el 0 1 2 0, el 2 4 0 0] 1 0 (.tag 0 (w 0)),
    ⟨"reverted", "", [41, 2, 3, (2 ^ 256 - 1), 0, 0, 2, 0, 0, 0]⟩),
  (tx 4 0 [el 0 1 2 0, el 2 4 0 0] 1 1 (.tag 0 (w 0)),
    ⟨"returned", "000000000000000000000000000000000000000000000000000000000000003e", [62, 2, 3, 4, 0, 0, 3, 4, 0, 0]⟩),
  (tx 5 0 [el 2 5 0 0] 0 0 (.count (w 2)),
    ⟨"reverted", "08638556", [62, 2, 3, 4, 0, 0, 3, 4, 0, 0]⟩),
  (tx 6 0 [] 0 0 .none,
    ⟨"reverted", "7f52b2bf", [62, 2, 3, 4, 0, 0, 3, 4, 0, 0]⟩),
  (tx 7 2 [el 0 6 8 0] 0 0 (.retag 0 2),
    ⟨"returned", "0000000000000000000000000000000000000000000000000000000000000056", [86, 1, 3, 6, 0, 0, 3, 6, 0, 0]⟩),
  (tx 8 0 [el 0 1 2 0] 0 0 (.truncate 131),
    ⟨"reverted", "08638556", [86, 1, 3, 6, 0, 0, 3, 6, 0, 0]⟩),
  (tx 9 0 [el 1 0 0 0] 0 0 (.short 3),
    ⟨"reverted", "4924aef0", [86, 1, 3, 6, 0, 0, 3, 6, 0, 0]⟩),
  (tx 10 0 [el 2 4 0 0, el 0 1 1 0] 1 (2 ^ 256 - 1) .none,
    ⟨"reverted", "7f52b2bf", [86, 1, 3, 6, 0, 0, 3, 6, 0, 0]⟩)]

private def dynamicWordsRows : List (Transaction × Expected) := [
  (tx 0 0 [el 0 1 2 33, el 2 3 7 0, el 3 0 0 0] 0 1 .none,
    ⟨"returned", "da3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18ec8", [(2 ^ 256 - 17089871545297914264645409054526021057658525754966106959376225893052256776504), 3, 1, 33, (2 ^ 256 - 44228642460293897567044858665937249460768678410975614156124097144906896535915), 27138770914995983302399449611411228403110152656009507196747871251854639759360, 3, 3, 7, 0]⟩),
  (tx 1 0 [el 1 5 0 0, el 3 0 0 0] 0 1 (.entry 1 (w 0)),
    ⟨"reverted", "", [(2 ^ 256 - 17089871545297914264645409054526021057658525754966106959376225893052256776504), 3, 1, 33, (2 ^ 256 - 44228642460293897567044858665937249460768678410975614156124097144906896535915), 27138770914995983302399449611411228403110152656009507196747871251854639759360, 3, 3, 7, 0]⟩),
  (tx 2 0 [el 1 5 0 0, el 2 6 7 0] 0 1 (.share 1 0),
    ⟨"returned", "da3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18ed9", [(2 ^ 256 - 17089871545297914264645409054526021057658525754966106959376225893052256776487), 2, 2, 5, 0, 0, 2, 5, 0, 0]⟩),
  (tx 3 0 [el 1 5 0 0] 0 0 (.entry 0 (w 129)),
    ⟨"reverted", "08638556", [(2 ^ 256 - 17089871545297914264645409054526021057658525754966106959376225893052256776487), 2, 2, 5, 0, 0, 2, 5, 0, 0]⟩),
  (tx 4 0 [el 0 4 5 1] 0 0 (.length 0 (w 32)),
    ⟨"returned", "ca3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18f1d", [(2 ^ 256 - 24326877122630176478618595617569015298487899796568642211842324893546827378915), 1, 1, 32, 54277541829991966604798899222822456806220305312019014393495742503709279518720, 0, 1, 32, 54277541829991966604798899222822456806220305312019014393495742503709279518720, 0]⟩),
  (tx 5 0 [el 0 4 5 1] 0 0 (.length 0 (w 33)),
    ⟨"reverted", "08638556", [(2 ^ 256 - 24326877122630176478618595617569015298487899796568642211842324893546827378915), 1, 1, 32, 54277541829991966604798899222822456806220305312019014393495742503709279518720, 0, 1, 32, 54277541829991966604798899222822456806220305312019014393495742503709279518720, 0]⟩),
  (tx 6 0 [el 0 1 2 32] 0 0 (.tail 0 (w 0)),
    ⟨"reverted", "08638556", [(2 ^ 256 - 24326877122630176478618595617569015298487899796568642211842324893546827378915), 1, 1, 32, 54277541829991966604798899222822456806220305312019014393495742503709279518720, 0, 1, 32, 54277541829991966604798899222822456806220305312019014393495742503709279518720, 0]⟩),
  (tx 7 0 [el 0 1 1 1] 0 0 (.padding 0 0),
    ⟨"returned", "063779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18f23", [2811893792365806823780853993842213104622252859440864984905546358307812380451, 1, 1, 1, (2 ^ 256 - 44326659161160106060585767698638339725079916004815528421354856378029244940288), 0, 1, 1, (2 ^ 256 - 44326659161160106060585767698638339725079916004815528421354856378029244940288), 0]⟩),
  (tx 8 0 [el 2 1 2 0] 0 0 (.offset (w 57896044618658097711785492504343953926634992332820282019728792003956564819968)),
    ⟨"reverted", "08638556", [2811893792365806823780853993842213104622252859440864984905546358307812380451, 1, 1, 1, (2 ^ 256 - 44326659161160106060585767698638339725079916004815528421354856378029244940288), 0, 1, 1, (2 ^ 256 - 44326659161160106060585767698638339725079916004815528421354856378029244940288), 0]⟩),
  (tx 9 0 [el 1 9 0 0, el 1 8 0 0] 0 1 (.count (w 3)),
    ⟨"returned", "063779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18f3c", [2811893792365806823780853993842213104622252859440864984905546358307812380476, 3, 2, 9, 0, 0, 2, 8, 0, 0]⟩)]

private def twoBytesRows : List (Transaction × Expected) := [
  (tx 0 0 [el 0 1 2 64, el 1 3 4 31] 1 0 .none,
    ⟨"returned", "b54cda58fbbee883b5ac82422d92b138630cec87b5ceadebd28a7c6ae4895725", [(2 ^ 256 - 33787676287130994555127181978247681058072101134572556857829414853615119935707), 2, 2, 31, (2 ^ 256 - 16893838143565497277563590989123840529036050567286278428914707426807559968000), 0, 1, 64, (2 ^ 256 - 44228642460293897567044858665937249460768678410975614156124097144906896535915), 27334804316728400289481267676813408931732627843689335727209389718099336568106]⟩),
  (tx 1 1 [el 1 (2 ^ 256 - 1) 1 32] 0 0 .none,
    ⟨"reverted", "78dde6e5fd29f057ce73018173b720d042089dafce89c947e1b1a84743063a42", [(2 ^ 256 - 33787676287130994555127181978247681058072101134572556857829414853615119935707), 2, 2, 31, (2 ^ 256 - 16893838143565497277563590989123840529036050567286278428914707426807559968000), 0, 1, 64, (2 ^ 256 - 44228642460293897567044858665937249460768678410975614156124097144906896535915), 27334804316728400289481267676813408931732627843689335727209389718099336568106]⟩),
  (tx 2 0 [el 1 2 3 0] 0 0 (.trailing 64 2),
    ⟨"returned", "b54cda58fbbee883b5ac82422d92b138630cec87b5ceadebd28a7c6ae489572c", [(2 ^ 256 - 33787676287130994555127181978247681058072101134572556857829414853615119935700), 1, 2, 0, 0, 0, 2, 0, 0, 0]⟩),
  (tx 3 0 [el 0 2 3 63] 0 0 (.selector 2147483648),
    ⟨"reverted", "4924aef0", [(2 ^ 256 - 33787676287130994555127181978247681058072101134572556857829414853615119935700), 1, 2, 0, 0, 0, 2, 0, 0, 0]⟩),
  (tx 4 2 [el 0 1 1 33, el 1 1 1 1] 0 1 (.offset (w 0)),
    ⟨"reverted", "", [(2 ^ 256 - 33787676287130994555127181978247681058072101134572556857829414853615119935700), 1, 2, 0, 0, 0, 2, 0, 0, 0]⟩),
  (tx 5 0 [el 0 7 7 17] 0 0 (.retag 0 1),
    ⟨"returned", "5c55827df1d1b1b7083f07874293a411490cec87b5ceadebd28a7c6ae4895755", [41763864692651612047670706750758273610784823299369356856714969782160273790805, 1, 2, 17, 37775770489891303301398944364502977334428462216970956857272192317887696863232, 0, 2, 17, 37775770489891303301398944364502977334428462216970956857272192317887696863232, 0]⟩)]

private def structFieldsRows : List (Transaction × Expected) := [
  (tx 0 0 [el 0 11 12 0, el 2 5 6 17, el 1 0 0 0] 0 1 .none,
    ⟨"returned", "1715609f7c746c6dc20fc1e1d0a4e90452000000000000000000000000000032", [10440966173162903011917676687689568402695856741602633618718639110637867761714, 3, 1, 11, 12, 0, 3, 17, 10440966173162903011917676687689568402695856741602633618718639110637867761664, 0]⟩),
  (tx 1 0 [el 0 1 1 0] 0 0 (.retag 0 1),
    ⟨"returned", "1715609f7c746c6dc20fc1e1d0a4e9045200000000000000000000000000003a", [10440966173162903011917676687689568402695856741602633618718639110637867761722, 1, 2, 0, 0, 0, 2, 0, 0, 0]⟩),
  (tx 2 0 [el 2 1 2 0] 0 0 .none,
    ⟨"returned", "1715609f7c746c6dc20fc1e1d0a4e90452000000000000000000000000000044", [10440966173162903011917676687689568402695856741602633618718639110637867761732, 1, 3, 0, 0, 0, 3, 0, 0, 0]⟩),
  (tx 3 0 [el 0 3 4 0] 0 0 (.truncate 244),
    ⟨"reverted", "08638556", [10440966173162903011917676687689568402695856741602633618718639110637867761732, 1, 3, 0, 0, 0, 3, 0, 0, 0]⟩),
  (tx 4 0 [el 1 0 0 0] 1 0 .none,
    ⟨"reverted", "7f52b2bf", [10440966173162903011917676687689568402695856741602633618718639110637867761732, 1, 3, 0, 0, 0, 3, 0, 0, 0]⟩)]

private def tagsOnlyRows : List (Transaction × Expected) := [
  (tx 0 0 [el 0 0 0 0, el 1 0 0 0, el 0 0 0 0] 2 1 .none,
    ⟨"returned", "000000000000000000000000000000000000000000000000000000000000000a", [10, 3, 1, 0, 0, 0, 2, 0, 0, 0]⟩),
  (tx 1 0 [el 1 0 0 0] 0 0 (.count (w 3618502788666131106986593281521497120414687020801267626233049500247285301248)),
    ⟨"reverted", "08638556", [10, 3, 1, 0, 0, 0, 2, 0, 0, 0]⟩),
  (tx 2 0 [el 1 0 0 0] 0 0 (.count (w 0)),
    ⟨"reverted", "7f52b2bf", [10, 3, 1, 0, 0, 0, 2, 0, 0, 0]⟩),
  (tx 3 0 [el 1 0 0 0, el 0 0 0 0] 1 0 (.tag 0 (w (2 ^ 256 - 8108102160884874896242699696681862164538485728477310456048732216610957744293))),
    ⟨"reverted", "", [10, 3, 1, 0, 0, 0, 2, 0, 0, 0]⟩),
  (tx 4 0 [el 0 0 0 0] 0 0 (.offset (w 32)),
    ⟨"reverted", "08638556", [10, 3, 1, 0, 0, 0, 2, 0, 0, 0]⟩)]

private def scenarios : List (String × Nat × List Constructor × String × String × List (Transaction × Expected)) := [
    ("static-words", 5, [⟨"Pair", .twoWords⟩, ⟨"Idle", .noWords⟩, ⟨"Q", .oneWord⟩],
      "run(uint256,sum(uint256,uint256,sum(,uint256))[],uint256,uint256)", selectorStaticWords, staticWordsRows),
    ("dynamic-words", 1, [⟨"Blob", .bytes⟩, ⟨"Ready", .oneWord⟩, ⟨"Settled", .twoWords⟩, ⟨"Rejected", .noWords⟩],
      "run(uint256,sum(bytes,sum(uint256,sum(uint256,uint256,)))[],uint256,uint256)", selectorDynamicWords, dynamicWordsRows),
    ("two-bytes", 2, [⟨"OverflowedAccumulator", .bytes⟩, ⟨"Q", .bytes⟩],
      "run(uint256,sum(bytes,bytes)[],uint256,uint256)", selectorTwoBytes, twoBytesRows),
    ("struct-fields", 3, [⟨"Ready", .pair⟩, ⟨"Idle", .noWords⟩, ⟨"Blob", .bytes⟩],
      "run(uint256,sum(uint256,uint256,sum(,bytes))[],uint256,uint256)", selectorStructFields, structFieldsRows),
    ("tags-only", 4, [⟨"Idle", .noWords⟩, ⟨"Ready", .noWords⟩],
      "run(uint256,sum(,)[],uint256,uint256)", selectorTagsOnly, tagsOnlyRows)]

/-- Original Core reverts with one Word: an error selector stands for std's
four bytes and the Word zero for its empty revert data. -/
private def coreOutput (output : String) : String :=
  "0x" ++ if output.length == 8 then String.ofList (List.replicate 56 '0') ++ output
    else if output.isEmpty then String.ofList (List.replicate 64 '0') else output

private def check (name : String) (row : Json) (model : EnumArrayExecution.ModelRow) (expected : Expected) :
    IO Unit := do
  ensure ((row.getObjValAs? String "status").toOption == some expected.status &&
      (row.getObjValAs? String "output").toOption == some (coreOutput expected.output) &&
      (row.getObjVal? "committedStorage").toOption == some (slots expected.values))
    s!"{name}: original Core differs from the expected row {row.compress}"
  ensure (model.reverted == (expected.status == "reverted") &&
      encodeBytesText model.output == "0x" ++ expected.output &&
      model.slots == (List.range EnumArray.slotCount).map (fun slot => w (expected.values.getD slot 0)))
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

/-- Decisions that one malformation cannot reach, on raw calldata of the second
scenario's `[Ready(5), Rejected]` read at 0 and 1, whose region starts at 164
and whose bodies at 228 and 324: an aliased table entry, the first index
before the second element, the tag before the fields, the array's head before
the indices, the selector before the head, and an unread element's offset. -/
private def orderRows (shape : Shape) : List (String × ByteArray × String × String) :=
  let canonical := EnumArrayExecution.inputBytes shape (tx 0 0 [el 1 5 0 0, el 3 0 0 0] 0 1 .none)
  let put := StdCalldata.replaceWord
  let rejected := EnumArgument.tag ⟨"Rejected", .noWords⟩
  let wrong := StdCalldata.Change.apply canonical (.selector 1)
  [("aliased table entry", put (put (put (put canonical (164 + 32) rejected) 164 (w 32)) 68 (w 0)) 100 (w 0),
      "returned", "000000000000000000000000000000000000000000000000000000000000000b"),
    ("first out of bounds before the second's unknown tag", put (put canonical 68 (w 2)) 324 (w 7),
      "reverted", "7f52b2bf"),
    ("unknown tag, fields cut", (put canonical 228 (w 7)).extract 0 276, "reverted", ""),
    ("array offset past the end, index out of bounds", put (put canonical 36 (w (canonical.size - 3))) 68 (w 5),
      "reverted", "08638556"),
    ("wrong selector, head cut", wrong.extract 0 40, "reverted", "4924aef0"),
    ("unread element offset past the end", put (put canonical (164 + 32) (w (2 ^ 256 - 1))) 100 (w 0),
      "returned", "0000000000000000000000000000000000000000000000000000000000000011")]

def testSourceEnumArrayGolden : IO Unit := do
  let fuel := 1000000
  -- Lean's Keccak-256 tags equal the ones written out; a struct's tag is its fields'.
  ensure (encodeBytesText (encodeWordBytesBE (EnumArgument.tag ⟨"Ready", .pair⟩)) == "0x" ++ tagReadyStruct &&
      encodeBytesText (encodeWordBytesBE (EnumArgument.tag ⟨"Blob", .bytes⟩)) == "0x" ++ tagBlobBytes &&
      encodeBytesText (encodeWordBytesBE (EnumArgument.tag ⟨"Ready", .noWords⟩)) == "0x" ++ tagReadyUnit &&
      encodeBytesText (encodeWordBytesBE (EnumArgument.tag ⟨"Rejected", .noWords⟩)) == "0x" ++ tagRejectedUnit &&
      encodeBytesText (encodeWordBytesBE (EnumArgument.tag ⟨"Idle", .noWords⟩)) == "0x" ++ tagIdleUnit)
    "a constructor tag differs from keccak256 of its signature"
  for (name, constant, constructors, signature, selector, rows) in scenarios do
    let step ← step constant
    let some shape := Solcore.Synthesis.Source.EnumArgument.Shape.ofList? constructors
      | throw (IO.userError s!"{name}: the shape has fewer than two constructors")
    ensure (EnumArray.signature shape == signature && Solcore.Synthesis.Source.EnumArray.selectorText shape == selector)
      s!"{name}: the signature or selector differs from std's structural signature"
    let some plan := EnumArray.CheckedPlan.ofParts? step shape
      | throw (IO.userError s!"{name}: the enum-array wrapper failed admission")
    let transactions := rows.map Prod.fst
    ensure (transactions.all (Solcore.Synthesis.Source.EnumArray.admits shape)) s!"{name}: a transaction is not admitted"
    for (transaction, expected) in rows do
      let rejected := expected.status == "reverted" && expected.output.length != 64
      ensure (Solcore.Synthesis.Source.EnumArray.prescribed shape transaction ==
          (if rejected then some ("0x" ++ expected.output) else none))
        s!"{name} {transaction.id}: the prescribed std outcome differs from the expected row"
    let history := EnumArrayExecution.observe plan transactions StorageExecution.fixtureBindings fuel
    ensure ((history.getObjValAs? String "status").toOption == some "complete") s!"{name}: the history is incomplete"
    let observed ← get (history.getObjValAs? (Array Json) "transactions")
    let some modelled := EnumArrayExecution.model step shape fuel transactions
      | throw (IO.userError s!"{name}: the Lean model failed")
    ensure (observed.size == rows.length && modelled.length == rows.length) s!"{name}: a row is missing"
    for ((row, model), (transaction, expected)) in (observed.toList.zip modelled).zip rows do
      check s!"{name} {transaction.id}" row model expected
  -- The order of std's checks, on raw calldata, for Core and the Lean model alike.
  let some (_, _, constructors, _, _, _) := scenarios[1]? | throw (IO.userError "no dynamic scenario")
  let some shape := Solcore.Synthesis.Source.EnumArgument.Shape.ofList? constructors | throw (IO.userError "no shape")
  let some plan := EnumArray.CheckedPlan.ofParts? (← step 1) shape | throw (IO.userError "no plan")
  for (label, bytes, status, output) in orderRows shape do
    let (actual, data) ← runRaw plan.contract bytes
    let decided := match EnumArrayExecution.stdDecode shape bytes with
      | .error data => some (encodeBytesText data)
      | .ok _ => none
    ensure (actual == status && data == coreOutput output &&
        decided == (if status == "returned" then none else some ("0x" ++ output)))
      s!"{label}: std's order of checks differs ({actual} {data})"
  -- A changed expectation fails: the first static row read as a rejection.
  let some (transaction, expected) := staticWordsRows.head? | throw (IO.userError "no static row")
  ensure (Solcore.Synthesis.Source.EnumArray.prescribed (← (Solcore.Synthesis.Source.EnumArgument.Shape.ofList?
        [⟨"Pair", .twoWords⟩, ⟨"Idle", .noWords⟩, ⟨"Q", .oneWord⟩]).getDM
        (throw (IO.userError "no shape"))) transaction == none &&
      coreOutput expected.output != coreOutput "08638556")
    "a changed expectation is not detected"

end Tests.SourceEnumArrayGolden
