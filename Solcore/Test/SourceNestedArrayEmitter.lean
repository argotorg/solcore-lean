import Solcore.Synthesis.Source.NestedArrayEmitter
import Solcore.Synthesis.Stateful.NestedArrayExecution

/-! Nested-array protocol regressions through actual installed ContractRuntime
code. Golden histories are hand-computed: they cover ragged rows, an empty row,
an empty outer array, three empty rows, wrapping arithmetic, absent elements
whose slots stay untouched and a revert that keeps the prior slots. Calldata
vectors come from Foundry's `cast calldata` encoder. -/
set_option autoImplicit false

namespace Tests.SourceNestedArrayEmitter

open Lean Solcore.Core Solcore.ContractRuntime Solcore.Synthesis.Core
open Solcore.Synthesis.Core.NestedArray (CheckedPlan)
open Solcore.Synthesis.Source (EmittedProgram)
open Solcore.Synthesis.Stateful

private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)
private def entry : Wire.Expr := .apply (.var 1) (.var 0)
private def increment : Wire.Expr := .binary .wordAdd (.var 0) (word 1)
private def modulus : Nat := 2 ^ 256
private def maximum : Nat := modulus - 1
private def high : Nat := 2 ^ 255

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def checked (helpers : List Wire.Expr) : IO CheckedPlan := do
  let some step := Aggregates.CheckedDAG.ofParts? helpers entry |
    throw (IO.userError "nested-array step did not pass the checked aggregate profile")
  let some plan := CheckedPlan.ofStep? step |
    throw (IO.userError "nested-array wrapper did not pass the full Wire host checker")
  return plan

private def emitted (plan : CheckedPlan) : IO EmittedProgram :=
  match Solcore.Synthesis.Source.NestedArray.emit plan with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"nested-array source emission failed: {reprStr error}")

private def value (rows : List (List Nat)) : List (List Word) := rows.map (·.map Word.ofNatModulo)

private def transactions (rows : List (Nat × List (List Nat))) : List NestedArrayExecution.Transaction :=
  rows.zipIdx.map fun ((flags, values), index) => ⟨"tx-" ++ toString index, Word.ofNatModulo flags, value values⟩

private def slotRows (values : List Nat) : Json := toJson (values.zipIdx.map fun (value, slot) =>
  Json.mkObj [("slot", toJson (toString slot)), ("value", toJson (toString value))])

/-- Sixty-four lowercase hexadecimal digits, written without the observer's
byte encoder. -/
private def hexDigits (value : Nat) : String :=
  let digits := Nat.toDigits 16 value
  String.ofList (List.replicate (64 - digits.length) '0' ++ digits)

private def hexWord (value : Nat) : String := "0x" ++ hexDigits value

/-- One hand-computed row: status, payload and slots zero to eight. -/
private def historyCheck (plan : CheckedPlan) (rows : List (Nat × List (List Nat)))
    (expected : List (String × Nat × List Nat)) : IO Unit := do
  let history := NestedArrayExecution.observe plan (transactions rows) StorageExecution.fixtureBindings 100000
  let observed := (history.getObjValAs? (List Json) "transactions").toOption.getD []
  ensure ((history.getObjValAs? String "status").toOption == some "complete" && observed.length == expected.length &&
    (history.getObjVal? "initialStorage").toOption == some (slotRows (List.replicate 9 0)))
    "nested-array golden history did not complete from empty storage"
  for (row, (status, payload, slots)) in observed.zip expected do
    ensure ((row.getObjValAs? String "status").toOption == some status &&
      (row.getObjValAs? String "output").toOption == some (hexWord (payload % modulus)) &&
      (row.getObjVal? "committedStorage").toOption == some (slotRows (slots.map (· % modulus))))
      s!"nested-array golden row changed: {row.compress}"

private def goldenChecks : IO Unit := do
  -- step(x) = x + 1. Elements (0, 0), (0, 1) and (2, 0) write slots 1, 2 and
  -- 5; the empty row writes nothing. The second call keeps slots 2 and 5. The
  -- odd-flags revert writes 42 and 52 to slots 1 and 2 and returns
  -- 52 + 6 + 8, but keeps every slot.
  let afterSecond := [32, 15, 5, 23, 32, 9, 0, 5, 6]
  historyCheck (← checked [increment]) [(0, [[1, 2], [], [3]]), (0, [[5], [7, 8]]), (1, [[9, 9]])] [
    ("returned", 9 + 3 + 3, [9, 2, 5, 0, 0, 9, 0, 3, 3]),
    ("returned", 32 + 5 + 6, afterSecond),
    ("reverted", 52 + 6 + 8, afterSecond)]
  -- step(x) = x. The maximum plus one wraps the accumulator to zero; an empty
  -- outer array changes nothing; even flags 2 return; an empty first row and
  -- 2^255 + 2^255 wrap again, then 7 remains.
  let afterFirst := [0, maximum, 0, 0, 0, 0, 0, 1, 2]
  historyCheck (← checked [.var 0]) [(0, [[maximum, 1]]), (0, []), (2, [[], [high], [high, 7]])] [
    ("returned", 0 + 1 + 2, afterFirst),
    ("returned", 0 + 1 + 2, afterFirst),
    ("returned", 7 + 4 + 5, [7, maximum, 0, high, 0, 0, 7, 4, 5])]
  -- Three empty rows count as rows only.
  historyCheck (← checked [.var 0]) [(0, [[], [], []])] [("returned", 3, [0, 0, 0, 0, 0, 0, 0, 3, 0])]

/-- The reverted call's working world holds every write; the public runtime
commits the prior, here empty, world. -/
private def rollbackChecks : IO Unit := do
  let plan ← checked [.var 0]
  let bindings := StorageExecution.fixtureBindings
  let world := StorageExecution.initialWorldForContract plan.contract bindings
  let registry : CheckedContractRegistry :=
    ⟨fun address => if address == bindings.address then some plan.contract else none⟩
  let some ⟨contract, installed⟩ := registry.resolve? world bindings.address |
    throw (IO.userError "nested-array contract did not resolve")
  let some input := NestedArrayExecution.inputData? (Word.ofNatModulo 1) (value [[1, 2], [], [3]]) |
    throw (IO.userError "nested-array calldata exceeded the Word-sized input bound")
  let invocation : TopLevelInvocation := {
    target := bindings.address, caller := bindings.caller, callValue := Word.zero, inputData := input }
  match TopLevelExecution.run contract invocation installed 100000 with
  | .outOfFuel _ _ _ _ _ _ => throw (IO.userError "nested-array golden call exhausted fuel")
  | .completed terminal =>
      ensure (terminal.outcome == .reverted (encodeWordBytesBE (Word.ofNatModulo (6 + 3 + 3))))
        "odd flags did not revert with the tentative sum"
      let some working := terminal.terminalContext.context.values.working.1.account? bindings.address |
        throw (IO.userError "working account missing")
      ensure ((List.range 9).map (fun slot => (working.storageRead (Word.ofNatModulo slot)).val) ==
          [6, 1, 3, 0, 0, 6, 0, 3, 3])
        "the working world lost an element, row count or element count write"
      let some committed := terminal.finalWorld.account? bindings.address |
        throw (IO.userError "committed account missing")
      ensure ((List.range 9).all fun slot => (committed.storageValue? (Word.ofNatModulo slot)).isNone)
        "the reverted writes were committed"

private def admissionChecks : IO Unit := do
  for plan in [← checked [increment], ← checked [.var 0]] do
    ensure (plan.program.check && plan.program.toCore.checkHost &&
      plan.program.resultType == .sum .word (.sum .word .word) && plan.contract.entryProfile == .wordOutcomeV1)
      "nested-array plan lost full host checking or the typed outcome convention"
    ensure (plan.contract.code.program == plan.program.toCore) "admission replaced the original contract"
    ensure (NestedArray.canonicalNodes plan.step == Wire.programNodes plan.program &&
      Wire.programNodes plan.program ==
        Wire.programNodes plan.step.program + NestedArray.programOverhead + NestedArray.guardNodes)
      "nested-array wrapper overhead differs from the complete original Core"
    match plan.program.body with
    | .letE saved _ =>
        ensure (Wire.encodeExpr saved == Wire.encodeExpr plan.step.program.body)
          "nested-array wrapper ignored its arbitrary entry closure"
    | _ => throw (IO.userError "nested-array wrapper lost its initial closure binding")
    ensure ((← emitted plan) == (← emitted plan)) "nested-array emission is nondeterministic"
  ensure (NestedArray.programOverhead == 86 && NestedArray.guardNodes == 270 && NestedArray.maxRows == 3 &&
    NestedArray.maxColumns == 2 && NestedArray.rowSlot == 7 && NestedArray.cellSlot == 8)
    "nested-array wrapper size or layout changed"

/-- Element `(i, j)`'s four source lines, written out independently of the emitter. -/
private def expectedCell (row column : Nat) : List String :=
  ["            if (sc_width" ++ toString row ++ " > " ++ toString column ++ ") {",
    "                sc_acc = sc_step(sc_acc + Typedef.rep(sc_row" ++ toString row ++ "[uint256(" ++
      toString column ++ ")]));",
    "                sstore(" ++ toString (1 + 2 * row + column) ++ ", sc_acc);", "            }"]

private def expectedRow (row : Nat) : List String :=
  let i := toString row
  ["        if (sc_rows > " ++ i ++ ") {",
    "            let sc_row" ++ i ++ ": calldata<array<uint256>> = values[uint256(" ++ i ++ ")];",
    "            let sc_width" ++ i ++ ": word = Typedef.rep(sc_row" ++ i ++ ".length());",
    "            sc_cells = sc_cells + sc_width" ++ i ++ ";"] ++
    expectedCell row 0 ++ expectedCell row 1 ++ ["        }"]

private def expectedBasic : String := String.intercalate "\n" ([
  "import * from std;", "import * from std.dispatch;",
  "import {sload, sstore, mstore, revert_} from std.opcodes;", "",
  "function sc_fn0(sc_arg: word) returns (word) {",
  "    let sc_v0: word = 1;", "    let sc_v1: word = (sc_arg + sc_v0);",
  "    return sc_v1;", "}", "",
  "function sc_step(sc_arg: word) returns (word) {",
  "    let sc_v0: word = sc_fn0(sc_arg);", "    return sc_v0;", "}", "",
  "contract SynthesizedNestedArray {",
  "    function run(flags: uint256, values: calldata<array<calldata<array<uint256>>>>) public returns (uint256) {",
  "        let sc_flags: word = Typedef.rep(flags);",
  "        let sc_rows: word = Typedef.rep(values.length());",
  "        let sc_cells: word = 0;",
  "        let sc_acc: word = sload(0);"] ++
  expectedRow 0 ++ expectedRow 1 ++ expectedRow 2 ++ [
  "        sstore(0, sc_acc);",
  "        sstore(7, sload(7) + sc_rows);",
  "        sstore(8, sload(8) + sc_cells);",
  "        let sc_result: word = sload(0) + sload(7) + sload(8);",
  "        if ((sc_flags & 1) == 1) {", "            mstore(0, sc_result);",
  "            revert_(0, 32);", "        }",
  "        return uint256(sc_result);", "    }", "}", ""])

private def formattingChecks : IO Unit := do
  let source ← emitted (← checked [increment])
  ensure (source.source == expectedBasic) "nested-array protocol source changed"
  ensure (source.contractName == "SynthesizedNestedArray" && source.methodSignature == "run(uint256,uint256[][])" &&
    source.deployPath == ["SynthesizedNestedArrayDeploy"] &&
    source.runtimePath == ["SynthesizedNestedArrayDeploy", "SynthesizedNestedArray"])
    "nested-array wrapper metadata changed"
  -- Raw primitives join the same opcode import only when a step uses them.
  let divided ← emitted (← checked [.binary .wordDiv (.var 0) (word 1)])
  ensure ((divided.source.splitOn "import {sload, sstore, mstore, revert_, div as sc_div, ").length == 2)
    "nested-array emission lost the merged raw division alias"
  ensure (Solcore.Synthesis.Source.NestedArray.emitterVersion == "solcore-source-nested-array-v1" &&
    Solcore.Synthesis.Source.NestedArray.wrapperVersion == "solcore-word-nested-array-contract-v1" &&
    Solcore.Synthesis.Source.NestedArray.selector == "0x7095aff8" && NestedArray.version == "core-nested-array-contract-v1")
    "nested-array provenance changed"

/-- Calldata from the selector and the Words that `cast calldata` printed. -/
private def castCalldata (words : List Nat) : String := "0x7095aff8" ++ String.join (words.map hexDigits)

private def observerChecks : IO Unit := do
  -- `cast calldata "run(uint256,uint256[][])" 1 VALUE` from the pinned Foundry release.
  for (rows, words) in [
      ([[5], [7, 8]], [1, 0x40, 2, 0x40, 0x80, 1, 5, 2, 7, 8]),
      ([], [1, 0x40, 0]),
      ([[], [4]], [1, 0x40, 2, 0x40, 0x60, 0, 1, 4]),
      ([[1, 2], [3, 4], [5, 6]], [1, 0x40, 3, 0x60, 0xc0, 0x120, 2, 1, 2, 2, 3, 4, 2, 5, 6])] do
    ensure (NestedArrayExecution.calldata (Word.ofNatModulo 1) (value rows) == castCalldata words)
      s!"nested calldata differs from the canonical head/tail encoding: {rows}"
  ensure ([[], [[]], [[1]], [[1, 2], [3, 4], [5, 6]]].map (fun rows =>
      (NestedArrayExecution.inputBytes Word.zero (value rows)).size) == [100, 164, 196, 484])
    "nested calldata sizes are not the head, the offset table, the row lengths and the elements"
  ensure (NestedArrayExecution.rowOffsets (value [[1, 2], [], [3]]) == [96, 192, 224])
    "row offsets are not measured from the start of the offset table"
  let plan ← checked [.var 0]
  let calls := transactions [(0, [[1]]), (1, [[2, 3]]), (0, [])]
  let exhausted := NestedArrayExecution.observe plan calls StorageExecution.fixtureBindings 0
  let rows := (exhausted.getObjValAs? (List Json) "transactions").toOption.getD []
  ensure ((exhausted.getObjValAs? String "status").toOption == some "incomplete" &&
    (exhausted.getObjValAs? (List String) "unexecuted").toOption == some ["tx-1", "tx-2"] && rows.length == 1 &&
    (rows[0]!.getObjValAs? String "status").toOption == some "out-of-fuel" &&
    (exhausted.getObjVal? "finalStorage").toOption == (exhausted.getObjVal? "initialStorage").toOption)
    "nested-array observer conflated fuel exhaustion with completion"
  let complete := NestedArrayExecution.observe plan calls StorageExecution.fixtureBindings 100000
  ensure ((complete.getObjVal? "observedSlots").toOption ==
      some (toJson ((List.range 9).map toString)) &&
    (complete.getObjValAs? String "schema").toOption == some "solcore-lean.nested-array-history.v2" &&
    (complete.getObjValAs? String "status").toOption == some "complete")
    "history did not declare its slots or schema"

def testSourceNestedArrayEmitter : IO Unit := do
  admissionChecks
  goldenChecks
  rollbackChecks
  formattingChecks
  observerChecks

end Tests.SourceNestedArrayEmitter
