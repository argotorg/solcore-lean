import Solcore.Synthesis.Source.StorageMappingEmitter
import Solcore.Synthesis.Stateful.StorageMappingExecution

/-! Keccak-mapping protocol regressions through actual installed
ContractRuntime code. The Wire hash closure, built from the proved Core
Keccak builders, is checked against Foundry's `cast keccak` and the separate
`Solcore.Abi.V1.Keccak256`. Golden histories are hand-computed: they cover a
successor key reading the entry its predecessor wrote, the maximum key whose
successor wraps to zero, wrapping arithmetic and a revert that keeps every
declared slot. -/
set_option autoImplicit false

namespace Tests.SourceStorageMappingEmitter

open Lean Solcore.Core Solcore.ContractRuntime Solcore.Synthesis.Core
open Solcore.Synthesis.Core.StorageMapping (CheckedPlan)
open Solcore.Synthesis.Source (EmittedProgram)
open Solcore.Synthesis.Stateful

private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)
private def entry : Wire.Expr := .apply (.var 1) (.var 0)
private def increment : Wire.Expr := .binary .wordAdd (.var 0) (word 1)
private def maximum : Nat := 2 ^ 256 - 1

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

/-- `cast keccak` of the base slot one followed by each key, as decimal Words. -/
private def castSlots : List (Nat × Nat) := [
  (0, 78541660797044910968829902406342334108369226379826116161446442989268089806461),
  (1, 92458281274488595289803937127152923398167637295201432141969818930235769911599),
  (5, 9247535584797915451057180664748820695544591120644449140157971996739901653371),
  (6, 28212876883947467128917703474378516019173305230661588919942657668795042982449),
  (7, 81222191986226809103279119994707868322855741819905904417953092666699096963112),
  (maximum, 71124947674796991739310909576881207026731009306364129481614628957978744178186)]

private def castSlot (key : Nat) : Nat := ((castSlots.find? (·.1 == key)).map (·.2)).getD 0

private def checked (helpers : List Wire.Expr) : IO CheckedPlan := do
  let some step := Aggregates.CheckedDAG.ofParts? helpers entry |
    throw (IO.userError "mapping step did not pass the checked aggregate profile")
  let some plan := CheckedPlan.ofStep? step |
    throw (IO.userError "mapping wrapper did not pass the full Wire host checker")
  return plan

private def emitted (plan : CheckedPlan) : IO EmittedProgram :=
  match Solcore.Synthesis.Source.StorageMapping.emit plan with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"mapping source emission failed: {reprStr error}")

/-- Evaluate the Wire hash closure on two Words through the checked Core machine. -/
private def wireHash (first second : Nat) : IO Nat := do
  let program : Wire.Program := {
    resultType := .word
    dataDefinitions := []
    body := .apply StorageMapping.hashClosure (.pair (word first) (word second))
  }
  ensure program.check "the applied Wire hash closure failed checking"
  match program.toCore.runStateful 1000000 with
  | .done (.word value) _ => pure value.val
  | _ => throw (IO.userError "the Wire hash closure did not return a Word")

private def abiHash (first second : Nat) : Nat :=
  ((decodeWordBytesBE? (Solcore.Abi.V1.Keccak256.hash
    (encodeWordBytesBE (Word.ofNatModulo first) ++ encodeWordBytesBE (Word.ofNatModulo second)))).map (·.val)).getD 0

private def hashChecks : IO Unit := do
  ensure (Wire.Expr.ofCore? StorageMapping.coreHash).isSome "the proved Keccak builders did not convert to Wire"
  ensure (StorageMapping.hashNodes == 2654 && StorageMapping.programOverhead == 93)
    "the Keccak closure or the protocol wrapper changed size"
  for (key, expected) in castSlots do
    ensure ((← wireHash 1 key) == expected && abiHash 1 key == expected &&
      (StorageMappingExecution.entrySlot (Word.ofNatModulo key)).val == expected)
      s!"entry slot of key {key} differs from cast keccak"
  -- keccak256 of 64 zero bytes, and of 2^255 followed by seven, from `cast keccak`.
  ensure ((← wireHash 0 0) == 0xad3228b676f7d3cd4284a5443f17f1962b36e491b30a40b2405849e597ba5fb5 &&
    (← wireHash (2 ^ 255) 7) == 0x5f0acbee363d0168b89f839cbed5de97ddcefff3f3ffbd6a1aef60457f15f108 &&
    abiHash (2 ^ 255) 7 == 0x5f0acbee363d0168b89f839cbed5de97ddcefff3f3ffbd6a1aef60457f15f108)
    "the Wire hash closure differs from cast keccak"

private def transactions (rows : List (Nat × Nat × Nat)) : List StorageMappingExecution.Transaction :=
  rows.zipIdx.map fun ((flags, key, input), index) =>
    ⟨"tx-" ++ toString index, Word.ofNatModulo flags, Word.ofNatModulo key, Word.ofNatModulo input⟩

/-- Sixty-four lowercase hexadecimal digits, written without the observer's
byte encoder. -/
private def hexWord (value : Nat) : String :=
  let digits := Nat.toDigits 16 value
  "0x" ++ String.ofList (List.replicate (64 - digits.length) '0' ++ digits)

/-- The declared slots in increasing order with the values the golden assigns. -/
private def slotRows (slots : List Nat) (values : List (Nat × Nat)) : Json :=
  toJson ((slots.mergeSort (· ≤ ·)).map fun slot => Json.mkObj [("slot", toJson (toString slot)),
    ("value", toJson (toString (((values.find? (·.1 == slot)).map (·.2)).getD 0)))])

private def historyCheck (plan : CheckedPlan) (rows : List (Nat × Nat × Nat)) (slots : List Nat)
    (expected : List (String × Nat × List (Nat × Nat))) : IO Unit := do
  let history := StorageMappingExecution.observe plan (transactions rows) StorageExecution.fixtureBindings 1000000
  let observed := (history.getObjValAs? (List Json) "transactions").toOption.getD []
  ensure ((history.getObjValAs? String "status").toOption == some "complete" && observed.length == expected.length &&
    (history.getObjVal? "observedSlots").toOption == some (toJson ((slots.mergeSort (· ≤ ·)).map toString)) &&
    (history.getObjVal? "initialStorage").toOption == some (slotRows slots []))
    "mapping golden history did not complete from empty declared slots"
  for (row, (status, payload, values)) in observed.zip expected do
    ensure ((row.getObjValAs? String "status").toOption == some status &&
      (row.getObjValAs? String "output").toOption == some (hexWord payload) &&
      (row.getObjVal? "committedStorage").toOption == some (slotRows slots values))
      s!"mapping golden row changed: {row.compress}"

private def goldenChecks : IO Unit := do
  -- step(x) = x: key six reads the entry key five wrote as its successor, and a
  -- reverted maximum key keeps every slot, including its wrapped successor zero.
  let slots := [0, castSlot 5, castSlot 6, castSlot 7, castSlot maximum, castSlot 0]
  historyCheck (← checked [.var 0]) [(0, 5, 7), (0, 6, 3), (1, maximum, 1)] slots [
    ("returned", 9, [(0, 1), (castSlot 5, 7), (castSlot 6, 1)]),
    ("returned", 8, [(0, 2), (castSlot 5, 7), (castSlot 6, 4), (castSlot 7, 2)]),
    ("reverted", 5, [(0, 2), (castSlot 5, 7), (castSlot 6, 4), (castSlot 7, 2)])]
  -- step(x) = x + 1 wraps the maximum input; the maximum key's successor is key zero.
  historyCheck (← checked [increment]) [(0, maximum, maximum), (2, 0, 1)]
    [0, castSlot maximum, castSlot 0, castSlot 1] [
    ("returned", 2, [(0, 1), (castSlot maximum, 0), (castSlot 0, 1)]),
    ("returned", 7, [(0, 2), (castSlot maximum, 0), (castSlot 0, 3), (castSlot 1, 2)])]

private def admissionChecks : IO Unit := do
  for plan in [← checked [increment], ← checked [.var 0]] do
    ensure (plan.program.check && plan.program.toCore.checkHost &&
      plan.program.resultType == .sum .word (.sum .word .word) && plan.contract.entryProfile == .wordOutcomeV1)
      "mapping plan lost full host checking or the typed outcome convention"
    ensure (plan.contract.code.program == plan.program.toCore) "admission replaced the original contract"
    ensure (StorageMapping.canonicalNodes plan.step == Wire.programNodes plan.program &&
      Wire.programNodes plan.program ==
        Wire.programNodes plan.step.program + StorageMapping.programOverhead + StorageMapping.hashNodes)
      "mapping wrapper overhead differs from the complete original Core"
    match plan.program.body with
    | .letE hash (.letE saved _) =>
        ensure (Wire.encodeExpr hash == Wire.encodeExpr StorageMapping.hashClosure &&
          Wire.encodeExpr saved == Wire.encodeExpr plan.step.program.body)
          "mapping wrapper lost its hash closure or ignored its arbitrary entry closure"
    | _ => throw (IO.userError "mapping wrapper lost its initial closure bindings")
    ensure ((← emitted plan) == (← emitted plan)) "mapping emission is nondeterministic"

private def expectedBasic : String := String.intercalate "\n" [
  "import * from std;", "import * from std.dispatch;",
  "import {mstore, revert_} from std.opcodes;", "",
  "function sc_fn0(sc_arg: word) returns (word) {",
  "    let sc_v0: word = 1;", "    let sc_v1: word = (sc_arg + sc_v0);",
  "    return sc_v1;", "}", "",
  "function sc_step(sc_arg: word) returns (word) {",
  "    let sc_v0: word = sc_fn0(sc_arg);", "    return sc_v0;", "}", "",
  "contract SynthesizedMapping {",
  "    counter: word;",
  "    entries: mapping(word => word);",
  "",
  "    function run(flags: uint256, key: uint256, input: uint256) public returns (uint256) {",
  "        let sc_flags: word = Typedef.rep(flags);",
  "        let sc_key: word = Typedef.rep(key);",
  "        let sc_input: word = Typedef.rep(input);",
  "        let sc_old: word = entries[sc_key];",
  "        entries[sc_key] = sc_step(sc_input + sc_old);",
  "        entries[sc_key + 1] = sc_old + 1;",
  "        counter = counter + 1;",
  "        let sc_result: word = entries[sc_key] + entries[sc_key + 1] + counter;",
  "        if ((sc_flags & 1) == 1) {", "            mstore(0, sc_result);",
  "            revert_(0, 32);", "        }",
  "        return uint256(sc_result);", "    }", "}", ""]

private def formattingChecks : IO Unit := do
  let source ← emitted (← checked [increment])
  ensure (source.source == expectedBasic) "mapping protocol source changed"
  ensure (source.contractName == "SynthesizedMapping" && source.methodSignature == "run(uint256,uint256,uint256)" &&
    source.deployPath == ["SynthesizedMappingDeploy"] &&
    source.runtimePath == ["SynthesizedMappingDeploy", "SynthesizedMapping"])
    "mapping wrapper metadata changed"
  -- Raw primitives join the same opcode import only when a step uses them.
  let divided ← emitted (← checked [.binary .wordDiv (.var 0) (word 1)])
  ensure ((divided.source.splitOn "import {mstore, revert_, div as sc_div, ").length == 2)
    "mapping emission lost the merged raw division alias"
  ensure (Solcore.Synthesis.Source.StorageMapping.emitterVersion == "solcore-source-keccak-mapping-v1" &&
    Solcore.Synthesis.Source.StorageMapping.wrapperVersion == "solcore-word-keccak-mapping-contract-v1" &&
    Solcore.Synthesis.Source.StorageMapping.selector == "0x24b912e5" &&
    StorageMapping.version == "core-keccak-mapping-contract-v1") "mapping provenance changed"

private def observerChecks : IO Unit := do
  -- `cast calldata "run(uint256,uint256,uint256)" 1 5 7`
  ensure (StorageMappingExecution.calldata (Word.ofNatModulo 1) (Word.ofNatModulo 5) (Word.ofNatModulo 7) ==
    "0x24b912e5" ++ String.ofList (List.replicate 63 '0') ++ "1" ++ String.ofList (List.replicate 63 '0') ++ "5" ++
      String.ofList (List.replicate 63 '0') ++ "7")
    "mapping calldata is not the selector and three Words"
  let calls := transactions [(0, 5, 7), (0, 6, 3), (1, 7, 0)]
  let declared := (StorageMappingExecution.observedSlots calls).map (·.val)
  ensure (declared.length == 5 && [0, castSlot 5, castSlot 6, castSlot 7].all declared.contains &&
    declared == declared.mergeSort (· ≤ ·))
    "declared slots are not the counter and every key's and successor's entry slot in order"
  let plan ← checked [.var 0]
  let exhausted := StorageMappingExecution.observe plan calls StorageExecution.fixtureBindings 1000
  let rows := (exhausted.getObjValAs? (List Json) "transactions").toOption.getD []
  ensure ((exhausted.getObjValAs? String "status").toOption == some "incomplete" &&
    (exhausted.getObjValAs? (List String) "unexecuted").toOption == some ["tx-1", "tx-2"] && rows.length == 1 &&
    (rows[0]!.getObjValAs? String "status").toOption == some "out-of-fuel" &&
    (exhausted.getObjVal? "finalStorage").toOption == (exhausted.getObjVal? "initialStorage").toOption)
    "mapping observer conflated fuel exhaustion with completion"
  let complete := StorageMappingExecution.observe plan calls StorageExecution.fixtureBindings 1000000
  ensure ((complete.getObjValAs? String "schema").toOption == some "solcore-lean.mapping-history.v1" &&
    (complete.getObjValAs? String "status").toOption == some "complete")
    "history did not declare its schema or complete"

def testSourceStorageMappingEmitter : IO Unit := do
  hashChecks
  admissionChecks
  goldenChecks
  formattingChecks
  observerChecks

end Tests.SourceStorageMappingEmitter
