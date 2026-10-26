import Solcore.Synthesis.Source.KeyedStorageEmitter
import Solcore.Synthesis.Stateful.KeyedStorageExecution

/-! Keyed-storage protocol regressions through actual installed ContractRuntime
code. Golden histories are hand-computed: they cover the write order key, key + 1,
counter, aliasing of keys zero and maximum with the counter, wrapping successor
slots, zero writes as deletions and rollback of tentative keyed writes. -/
set_option autoImplicit false

namespace Tests.SourceKeyedStorageEmitter

open Lean Solcore.Core Solcore.ContractRuntime Solcore.Synthesis.Core
open Solcore.Synthesis.Core.KeyedStorage (CheckedPlan)
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
    throw (IO.userError "keyed step did not pass the checked aggregate profile")
  let some plan := CheckedPlan.ofStep? step |
    throw (IO.userError "keyed wrapper did not pass the full Wire host checker")
  return plan

private def emitted (plan : CheckedPlan) : IO EmittedProgram :=
  match Solcore.Synthesis.Source.KeyedStorage.emit plan with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"keyed source emission failed: {reprStr error}")

private def transactions (rows : List (Nat × Nat)) : List KeyedStorageExecution.Transaction :=
  rows.zipIdx.map fun ((key, input), index) =>
    ⟨"tx-" ++ toString index, Word.ofNatModulo key, Word.ofNatModulo input⟩

private def slotRows (values : List (Nat × Nat)) : Json := toJson (values.map fun (slot, value) =>
  Json.mkObj [("slot", toJson (toString slot)), ("value", toJson (toString value))])

/-- One hand-computed history row: status, payload and the complete committed
values of the declared slots after the transaction. -/
private def historyCheck (plan : CheckedPlan) (rows : List (Nat × Nat))
    (expected : List (String × Nat × List (Nat × Nat))) : IO Unit := do
  let history := KeyedStorageExecution.observeContract plan.contract (transactions rows)
    StorageExecution.fixtureBindings 10000
  let observed := (history.getObjValAs? (List Json) "transactions").toOption.getD []
  ensure ((history.getObjValAs? String "status").toOption == some "complete" && observed.length == expected.length)
    "keyed golden history did not complete"
  for (row, (status, payload, committed)) in observed.zip expected do
    ensure ((row.getObjValAs? String "status").toOption == some status &&
      (row.getObjValAs? String "output").toOption == some (encodeBytesText (encodeWordBytesBE (Word.ofNatModulo payload))) &&
      (row.getObjVal? "committedStorage").toOption == some (slotRows committed))
      s!"keyed golden row changed: {row.compress}"

private def goldenChecks : IO Unit := do
  let identity ← checked [.var 0]
  -- Key zero reads the counter as old and is overwritten by the counter write;
  -- key maximum's successor wraps to the counter and is also overwritten.
  historyCheck identity [(5, 2), (0, 4), (maximum, 3)] [
    ("returned", 3, [(0, 1), (1, 0), (5, 2), (6, 0), (maximum, 0)]),
    ("returned", 5, [(0, 2), (1, 1), (5, 2), (6, 0), (maximum, 0)]),
    ("reverted", 9, [(0, 2), (1, 1), (5, 2), (6, 0), (maximum, 0)])]
  -- The successor of maximum minus one is maximum, read by the next key.
  historyCheck identity [(maximum - 1, 0), (maximum, 2), (maximum - 1, 6)] [
    ("returned", 1, [(0, 1), (maximum - 1, 0), (maximum, 0)]),
    ("returned", 6, [(0, 2), (maximum - 1, 0), (maximum, 2)]),
    ("returned", 9, [(0, 3), (maximum - 1, 6), (maximum, 0)])]
  -- Zero results delete; the reverted deletion of slot one is not committed.
  historyCheck (← checked [.var 0] (word 0)) [(1, 0), (0, 0), (1, 1)] [
    ("returned", 1, [(0, 1), (1, 0), (2, 0)]),
    ("returned", 5, [(0, 2), (1, 1), (2, 0)]),
    ("reverted", 4, [(0, 2), (1, 1), (2, 0)])]
  -- A fresh private cell per invocation; arbitrary entries remain the step.
  historyCheck (← checked [privateStep] (.binary .wordSub entry (word 1))) [(2 ^ 255, 7), (2 ^ 255, 2)] [
    ("reverted", 9, [(0, 0), (2 ^ 255, 0), (2 ^ 255 + 1, 0)]),
    ("returned", 4, [(0, 1), (2 ^ 255, 3), (2 ^ 255 + 1, 0)])]

/-- The reverted aliasing call's tentative world shows the exact write order. -/
private def tentativeChecks : IO Unit := do
  let plan ← checked [.var 0]
  let bindings := StorageExecution.fixtureBindings
  let world := StorageExecution.initialWorldForContract plan.contract bindings
  let registry : CheckedContractRegistry :=
    ⟨fun address => if address == bindings.address then some plan.contract else none⟩
  let some ⟨contract, installed⟩ := registry.resolve? world bindings.address |
    throw (IO.userError "keyed contract did not resolve")
  let invocation : TopLevelInvocation := {
    target := bindings.address, caller := bindings.caller, callValue := Word.zero,
    inputData := KeyedStorageExecution.inputData Word.maximum (Word.ofNatModulo 3) }
  match TopLevelExecution.run contract invocation installed 0 with
  | .outOfFuel _ _ _ _ _ _ => pure ()
  | .completed _ => throw (IO.userError "zero fuel completed a keyed call")
  match TopLevelExecution.run contract invocation installed 10000 with
  | .outOfFuel _ _ _ _ _ _ => throw (IO.userError "keyed golden call exhausted fuel")
  | .completed result =>
      ensure (result.outcome == .reverted (encodeWordBytesBE (Word.ofNatModulo 5)))
        "odd keyed input did not revert with the tentative sum"
      let some working := result.terminalContext.context.values.working.1.account? bindings.address |
        throw (IO.userError "working account missing")
      ensure (working.storageRead Word.maximum == Word.ofNatModulo 3 &&
        working.storageRead Word.zero == Word.ofNatModulo 1)
        "keyed writes did not apply key, wrapped successor, then counter"
      let some committed := result.finalWorld.account? bindings.address |
        throw (IO.userError "committed account missing")
      ensure (committed.storageRead Word.maximum == Word.zero && (committed.storageValue? Word.zero).isNone &&
        committed.balance == Word.zero && result.committedJournal.logList.isEmpty)
        "reverted keyed writes or unrelated effects were committed"

private def admissionChecks : IO Unit := do
  for plan in [← checked [increment], ← checked [privateStep] (.binary .wordSub entry (word 1))] do
    ensure (plan.program.check && plan.program.toCore.checkHost &&
      plan.program.resultType == .sum .word (.sum .word .word) && plan.contract.entryProfile == .wordOutcomeV1)
      "keyed plan lost full host checking or the typed outcome convention"
    ensure (plan.contract.code.program == plan.program.toCore) "admission replaced the original contract"
    ensure (KeyedStorage.canonicalNodes plan.step == Wire.programNodes plan.program &&
      Wire.programNodes plan.program == Wire.programNodes plan.step.program + KeyedStorage.programOverhead)
      "keyed wrapper overhead differs from the complete original Core"
    match plan.program.body with
    | .letE saved _ =>
        ensure (Wire.encodeExpr saved == Wire.encodeExpr plan.step.program.body)
          "keyed wrapper ignored its arbitrary entry closure"
    | _ => throw (IO.userError "keyed wrapper lost its initial closure binding")
    ensure ((← emitted plan) == (← emitted plan)) "keyed emission is nondeterministic"
  -- Raw primitives join the existing opcode import only when a step uses them.
  let divided ← checked [.binary .wordDiv (.var 0) (word 1)]
  match Solcore.Synthesis.Source.KeyedStorage.emit divided with
  | .ok emitted => unless (emitted.source.splitOn "import {sload, sstore, mstore, revert_, div as sc_div, ").length == 2 && (emitted.source.splitOn "    let sc_v3: word = sc_div(sc_v0, sc_v2);").length == 2 do
      throw (IO.userError "KeyedStorage emission lost the merged raw division alias or its snapshots")
  | .error error => throw (IO.userError s!"KeyedStorage raw division was rejected: {reprStr error}")

private def expectedBasic : String := String.intercalate "\n" [
  "import * from std;", "import * from std.dispatch;",
  "import {sload, sstore, mstore, revert_} from std.opcodes;", "",
  "function sc_fn0(sc_arg: word) returns (word) {",
  "    let sc_v0: word = 1;", "    let sc_v1: word = (sc_arg + sc_v0);",
  "    return sc_v1;", "}", "",
  "function sc_step(sc_arg: word) returns (word) {",
  "    let sc_v0: word = sc_fn0(sc_arg);", "    return sc_v0;", "}", "",
  "contract SynthesizedKeyedStorage {",
  "    function run(key: uint256, input: uint256) public returns (uint256) {",
  "        let sc_key: word = Typedef.rep(key);",
  "        let sc_input: word = Typedef.rep(input);",
  "        let sc_old: word = sload(sc_key);", "        let sc_count: word = sload(0);",
  "        let sc_computed: word = sc_step(sc_input + sc_old);",
  "        sstore(sc_key, sc_computed);", "        sstore(sc_key + 1, sc_old);",
  "        sstore(0, sc_count + 1);",
  "        let sc_final_key: word = sload(sc_key);",
  "        let sc_final_next: word = sload(sc_key + 1);",
  "        let sc_final_count: word = sload(0);",
  "        let sc_result: word = sc_final_key + sc_final_next + sc_final_count;",
  "        if ((sc_input & 1) == 1) {", "            mstore(0, sc_result);",
  "            revert_(0, 32);", "        }",
  "        return uint256(sc_result);", "    }", "}", ""]

private def formattingChecks : IO Unit := do
  let source ← emitted (← checked [increment])
  ensure (source.source == expectedBasic) "keyed protocol source changed"
  ensure (source.contractName == "SynthesizedKeyedStorage" && source.methodSignature == "run(uint256,uint256)" &&
    source.deployPath == ["SynthesizedKeyedStorageDeploy"] &&
    source.runtimePath == ["SynthesizedKeyedStorageDeploy", "SynthesizedKeyedStorage"])
    "keyed wrapper metadata changed"
  ensure (Solcore.Synthesis.Source.KeyedStorage.emitterVersion == "solcore-source-keyed-storage-v2" &&
    Solcore.Synthesis.Source.KeyedStorage.wrapperVersion == "solcore-word-keyed-storage-contract-v1" &&
    Solcore.Synthesis.Source.KeyedStorage.selector == "0x7357f5d2" &&
    KeyedStorage.version == "core-keyed-storage-contract-v1" && KeyedStorage.counterSlot == 0)
    "keyed provenance changed"

private def observerChecks : IO Unit := do
  let slots := KeyedStorageExecution.observedSlots (transactions [(maximum, 1), (0, 2), (maximum, 3)])
  ensure (slots.map (·.val) == [0, 1, maximum]) "observed slots are not the sorted unique counter/key/successor set"
  ensure ((KeyedStorageExecution.observedSlots (transactions [(7, 0)])).map (·.val) == [0, 7, 8])
    "observed slots omitted the counter or successor"
  ensure (KeyedStorageExecution.calldata (Word.ofNatModulo 2) Word.maximum ==
    "0x7357f5d2" ++ String.ofList (List.replicate 63 '0') ++ "2" ++ String.ofList (List.replicate 64 'f'))
    "keyed calldata is not selector, key and input Words"
  let plan ← checked [.var 0]
  let calls := transactions [(3, 2), (4, 1), (5, 0)]
  let exhausted := KeyedStorageExecution.observeContract plan.contract calls StorageExecution.fixtureBindings 0
  ensure ((exhausted.getObjValAs? String "status").toOption == some "incomplete" &&
    (exhausted.getObjValAs? (List String) "unexecuted").toOption == some ["tx-1", "tx-2"] &&
    (exhausted.getObjVal? "finalStorage").toOption == (exhausted.getObjVal? "initialStorage").toOption)
    "keyed observer conflated fuel exhaustion with completion"
  let complete := KeyedStorageExecution.observeContract plan.contract calls StorageExecution.fixtureBindings 10000
  ensure ((complete.getObjVal? "observedSlots").toOption ==
    some (toJson (["0", "3", "4", "5", "6"] : List String))) "history did not declare its observed slots"

def testSourceKeyedStorageEmitter : IO Unit := do
  admissionChecks
  goldenChecks
  tentativeChecks
  formattingChecks
  observerChecks

end Tests.SourceKeyedStorageEmitter
