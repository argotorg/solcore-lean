import Solcore.Synthesis.Source.DynamicArrayEmitter
import Solcore.Synthesis.Stateful.DynamicArrayExecution

/-! Dynamic-array protocol regressions through actual installed ContractRuntime
code. Golden histories are hand-computed: the fold over zero to three elements,
per-element slots that keep earlier values when a later array is shorter, the
running element count, zero writes as deletions and rollback of tentative
writes. The canonical calldata vectors were produced by Foundry `cast`. -/
set_option autoImplicit false

namespace Tests.SourceDynamicArrayEmitter

open Lean Solcore.Core Solcore.ContractRuntime Solcore.Synthesis.Core
open Solcore.Synthesis.Core.DynamicArray (CheckedPlan)
open Solcore.Synthesis.Source (EmittedProgram)
open Solcore.Synthesis.Stateful

private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)
private def entry : Wire.Expr := .apply (.var 1) (.var 0)
private def increment : Wire.Expr := .binary .wordAdd (.var 0) (word 1)
private def maximum : Nat := 2 ^ 256 - 1

private def privateStep : Wire.Expr :=
  .letE (.newCell .word (word 0))
    (.letE (.storeCell (.var 0) (.binary .wordAdd (.loadCell (.var 0)) (word 2)))
      (.binary .wordAdd (.var 2) (.loadCell (.var 1))))

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def checked (helpers : List Wire.Expr) (body : Wire.Expr := entry) : IO CheckedPlan := do
  let some step := Aggregates.CheckedDAG.ofParts? helpers body |
    throw (IO.userError "array step did not pass the checked aggregate profile")
  let some plan := CheckedPlan.ofStep? step |
    throw (IO.userError "array wrapper did not pass the full Wire host checker")
  return plan

private def emitted (plan : CheckedPlan) : IO EmittedProgram :=
  match Solcore.Synthesis.Source.DynamicArray.emit plan with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"array source emission failed: {reprStr error}")

private def transactions (rows : List (Nat × List Nat)) : List DynamicArrayExecution.Transaction :=
  rows.zipIdx.map fun ((flags, values), index) =>
    ⟨"tx-" ++ toString index, Word.ofNatModulo flags, values.map Word.ofNatModulo⟩

private def slotRows (values : List Nat) : Json := toJson (values.zipIdx.map fun (value, slot) =>
  Json.mkObj [("slot", toJson (toString slot)), ("value", toJson (toString value))])

/-- Status, payload and slots zero to four after each transaction. -/
private def historyCheck (plan : CheckedPlan) (rows : List (Nat × List Nat))
    (expected : List (String × Nat × List Nat)) : IO Unit := do
  let history := DynamicArrayExecution.observeContract plan.contract (transactions rows)
    StorageExecution.fixtureBindings 10000
  let observed := (history.getObjValAs? (List Json) "transactions").toOption.getD []
  ensure ((history.getObjValAs? String "status").toOption == some "complete" && observed.length == expected.length)
    "array golden history did not complete"
  for (row, (status, payload, committed)) in observed.zip expected do
    ensure ((row.getObjValAs? String "status").toOption == some status &&
      (row.getObjValAs? String "output").toOption == some (encodeBytesText (encodeWordBytesBE (Word.ofNatModulo payload))) &&
      (row.getObjVal? "committedStorage").toOption == some (slotRows committed))
      s!"array golden row changed: {row.compress}"

private def goldenChecks : IO Unit := do
  let identity ← checked [.var 0]
  -- Three elements fold to 1, 4, 11; an odd-flags call folds 11 + max to 10
  -- before reverting; an empty array only rewrites the accumulator and count.
  historyCheck identity [(0, [1, 3, 7]), (1, [maximum]), (2, [])] [
    ("returned", 14, [11, 1, 4, 11, 3]),
    ("reverted", 14, [11, 1, 4, 11, 3]),
    ("returned", 14, [11, 1, 4, 11, 3])]
  -- A shorter array writes only its own element slots.
  historyCheck identity [(0, [5, 6, 7]), (2, [1])] [
    ("returned", 21, [18, 5, 11, 18, 3]),
    ("returned", 23, [19, 19, 11, 18, 4])]
  -- Zero results delete; reverted empty arrays keep the committed count.
  historyCheck (← checked [.var 0] (word 0)) [(0, [5, 6, 7]), (0, [1]), (7, [])] [
    ("returned", 3, [0, 0, 0, 0, 3]),
    ("returned", 4, [0, 0, 0, 0, 4]),
    ("reverted", 4, [0, 0, 0, 0, 4])]
  -- A fresh private cell per invocation; the arbitrary entry adds one overall.
  historyCheck (← checked [privateStep] (.binary .wordSub entry (word 1))) [(maximum - 1, [3]), (7, [1, 2, 3])] [
    ("returned", 5, [4, 4, 0, 0, 1]),
    ("reverted", 17, [4, 4, 0, 0, 1])]

/-- The reverted call's tentative world shows every element write and count. -/
private def tentativeChecks : IO Unit := do
  let plan ← checked [.var 0]
  let bindings := StorageExecution.fixtureBindings
  let world := StorageExecution.initialWorldForContract plan.contract bindings
  let registry : CheckedContractRegistry :=
    ⟨fun address => if address == bindings.address then some plan.contract else none⟩
  let some ⟨contract, installed⟩ := registry.resolve? world bindings.address |
    throw (IO.userError "array contract did not resolve")
  let some input := DynamicArrayExecution.inputData? (Word.ofNatModulo 1)
      [Word.ofNatModulo 2, Word.ofNatModulo 3, Word.ofNatModulo 4] |
    throw (IO.userError "bounded array calldata was rejected")
  let invocation : TopLevelInvocation := {
    target := bindings.address, caller := bindings.caller, callValue := Word.zero, inputData := input }
  match TopLevelExecution.run contract invocation installed 0 with
  | .outOfFuel _ _ _ _ _ _ => pure ()
  | .completed _ => throw (IO.userError "zero fuel completed an array call")
  match TopLevelExecution.run contract invocation installed 10000 with
  | .outOfFuel _ _ _ _ _ _ => throw (IO.userError "array golden call exhausted fuel")
  | .completed result =>
      ensure (result.outcome == .reverted (encodeWordBytesBE (Word.ofNatModulo 12)))
        "odd flags did not revert with the tentative sum"
      let some working := result.terminalContext.context.values.working.1.account? bindings.address |
        throw (IO.userError "working account missing")
      ensure ([0, 1, 2, 3, 4].map (fun slot => (working.storageRead (Word.ofNatModulo slot)).val) == [9, 2, 5, 9, 3])
        "array writes were not applied in element order before the revert"
      let some committed := result.finalWorld.account? bindings.address |
        throw (IO.userError "committed account missing")
      ensure ([0, 1, 2, 3, 4].all (fun slot => (committed.storageValue? (Word.ofNatModulo slot)).isNone) &&
        committed.balance == Word.zero && result.committedJournal.logList.isEmpty)
        "reverted array writes or unrelated effects were committed"

private def admissionChecks : IO Unit := do
  for plan in [← checked [increment], ← checked [privateStep] (.binary .wordSub entry (word 1))] do
    ensure (plan.program.check && plan.program.toCore.checkHost &&
      plan.program.resultType == .sum .word (.sum .word .word) && plan.contract.entryProfile == .wordOutcomeV1)
      "array plan lost full host checking or the typed outcome convention"
    ensure (plan.contract.code.program == plan.program.toCore) "admission replaced the original contract"
    ensure (DynamicArray.canonicalNodes plan.step == Wire.programNodes plan.program &&
      Wire.programNodes plan.program == Wire.programNodes plan.step.program + DynamicArray.programOverhead)
      "array wrapper overhead differs from the complete original Core"
    match plan.program.body with
    | .letE saved _ =>
        ensure (Wire.encodeExpr saved == Wire.encodeExpr plan.step.program.body)
          "array wrapper ignored its arbitrary entry closure"
    | _ => throw (IO.userError "array wrapper lost its initial closure binding")
    ensure ((← emitted plan) == (← emitted plan)) "array emission is nondeterministic"
  -- Raw primitives join the existing opcode import only when a step uses them.
  let divided ← checked [.binary .wordDiv (.var 0) (word 1)]
  match Solcore.Synthesis.Source.DynamicArray.emit divided with
  | .ok emitted => unless (emitted.source.splitOn "import {sload, sstore, mstore, revert_, div as sc_div, ").length == 2 && (emitted.source.splitOn "    let sc_v3: word = sc_div(sc_v0, sc_v2);").length == 2 do
      throw (IO.userError "DynamicArray emission lost the merged raw division alias or its snapshots")
  | .error error => throw (IO.userError s!"DynamicArray raw division was rejected: {reprStr error}")

private def elementLines (index : Nat) : List String :=
  ["        if (sc_length > " ++ toString index ++ ") {",
    "            let sc_value" ++ toString index ++ ": word = Typedef.rep(values[uint256(" ++ toString index ++ ")]);",
    "            sc_acc = sc_step(sc_acc + sc_value" ++ toString index ++ ");",
    "            sstore(" ++ toString (index + 1) ++ ", sc_acc);", "        }"]

private def expectedBasic : String := String.intercalate "\n" ([
  "import * from std;", "import * from std.dispatch;",
  "import {sload, sstore, mstore, revert_} from std.opcodes;", "",
  "function sc_fn0(sc_arg: word) returns (word) {",
  "    let sc_v0: word = 1;", "    let sc_v1: word = (sc_arg + sc_v0);",
  "    return sc_v1;", "}", "",
  "function sc_step(sc_arg: word) returns (word) {",
  "    let sc_v0: word = sc_fn0(sc_arg);", "    return sc_v0;", "}", "",
  "contract SynthesizedDynamicArray {",
  "    function run(flags: uint256, values: calldata<array<uint256>>) public returns (uint256) {",
  "        let sc_flags: word = Typedef.rep(flags);",
  "        let sc_length: word = Typedef.rep(values.length());",
  "        let sc_acc: word = sload(0);"] ++ elementLines 0 ++ elementLines 1 ++ elementLines 2 ++ [
  "        sstore(0, sc_acc);",
  "        let sc_total: word = sload(4) + sc_length;", "        sstore(4, sc_total);",
  "        let sc_result: word = sload(0) + sload(4);",
  "        if ((sc_flags & 1) == 1) {", "            mstore(0, sc_result);",
  "            revert_(0, 32);", "        }",
  "        return uint256(sc_result);", "    }", "}", ""])

private def formattingChecks : IO Unit := do
  let source ← emitted (← checked [increment])
  ensure (source.source == expectedBasic) "dynamic-array protocol source changed"
  ensure (source.contractName == "SynthesizedDynamicArray" && source.methodSignature == "run(uint256,uint256[])" &&
    source.deployPath == ["SynthesizedDynamicArrayDeploy"] &&
    source.runtimePath == ["SynthesizedDynamicArrayDeploy", "SynthesizedDynamicArray"])
    "array wrapper metadata changed"
  ensure (Solcore.Synthesis.Source.DynamicArray.emitterVersion == "solcore-source-dynamic-array-v2" &&
    Solcore.Synthesis.Source.DynamicArray.wrapperVersion == "solcore-word-dynamic-array-contract-v1" &&
    Solcore.Synthesis.Source.DynamicArray.selector == "0x9a94c44b" &&
    DynamicArray.version == "core-dynamic-array-contract-v1" && DynamicArray.maxElements == 3)
    "array provenance changed"

private def zeros (count : Nat) : String := String.ofList (List.replicate count '0')

private def observerChecks : IO Unit := do
  -- `cast calldata "run(uint256,uint256[])" 1 "[5,6]"` and `0 "[]"`.
  ensure (DynamicArrayExecution.calldata (Word.ofNatModulo 1) [Word.ofNatModulo 5, Word.ofNatModulo 6] ==
    "0x9a94c44b" ++ zeros 63 ++ "1" ++ zeros 62 ++ "40" ++ zeros 63 ++ "2" ++ zeros 63 ++ "5" ++ zeros 63 ++ "6")
    "array calldata is not the canonical head/tail encoding"
  ensure (DynamicArrayExecution.calldata Word.zero [] == "0x9a94c44b" ++ zeros 64 ++ zeros 62 ++ "40" ++ zeros 64)
    "empty array calldata is not canonical"
  ensure (DynamicArrayExecution.observedSlots.map (·.val) == [0, 1, 2, 3, 4]) "array observed slots changed"
  let plan ← checked [.var 0]
  let calls := transactions [(2, [1]), (1, [2]), (0, [])]
  let exhausted := DynamicArrayExecution.observeContract plan.contract calls StorageExecution.fixtureBindings 0
  ensure ((exhausted.getObjValAs? String "status").toOption == some "incomplete" &&
    (exhausted.getObjValAs? (List String) "unexecuted").toOption == some ["tx-1", "tx-2"] &&
    (exhausted.getObjVal? "finalStorage").toOption == (exhausted.getObjVal? "initialStorage").toOption)
    "array observer conflated fuel exhaustion with completion"
  let complete := DynamicArrayExecution.observeContract plan.contract calls StorageExecution.fixtureBindings 10000
  ensure ((complete.getObjVal? "observedSlots").toOption == some (toJson (["0", "1", "2", "3", "4"] : List String)))
    "history did not declare its observed slots"

def testSourceDynamicArrayEmitter : IO Unit := do
  admissionChecks
  goldenChecks
  tentativeChecks
  formattingChecks
  observerChecks

end Tests.SourceDynamicArrayEmitter
