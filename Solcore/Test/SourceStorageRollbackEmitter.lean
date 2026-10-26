import Solcore.Synthesis.Source.StorageRollbackEmitter
import Solcore.Synthesis.Stateful.StorageExecution

/-! Typed rollback outcomes through actual installed ContractRuntime code.
Golden histories distinguish tentative writes/payloads from committed storage,
and cover original-input parity, Word wrap, private cells and arbitrary entries. -/
set_option autoImplicit false

namespace Tests.SourceStorageRollbackEmitter

open Lean Solcore.Core Solcore.ContractRuntime Solcore.Synthesis.Core
open Solcore.Synthesis.Core.StorageRollback (CheckedPlan)
open Solcore.Synthesis.Source (EmittedProgram)
open Solcore.Synthesis.Stateful

private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)
private def entry : Wire.Expr := .apply (.var 1) (.var 0)
private def increment : Wire.Expr := .binary .wordAdd (.var 0) (word 1)

private def privateStep : Wire.Expr :=
  .letE (.newCell .word (word 0))
    (.letE (.storeCell (.var 0) (.binary .wordAdd (.loadCell (.var 0)) (word 2)))
      (.binary .wordAdd (.var 2) (.loadCell (.var 1))))

private def pairStep : Wire.Expr :=
  .letE (.newCell .word (.var 0))
    (.letE (.pair (.loadCell (.var 0))
      (.letE (.storeCell (.var 0) (word 2)) (.loadCell (.var 1))))
      (.binary .wordAdd (.first (.var 0)) (.second (.var 0))))

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def checked (helpers : List Wire.Expr) (body : Wire.Expr := entry) : IO CheckedPlan := do
  let some step := Aggregates.CheckedDAG.ofParts? helpers body |
    throw (IO.userError "rollback step did not pass the checked aggregate profile")
  let some plan := CheckedPlan.ofStep? step |
    throw (IO.userError "rollback wrapper did not pass the full Wire host checker")
  return plan

private def emitted (plan : CheckedPlan) : IO EmittedProgram :=
  match Solcore.Synthesis.Source.StorageRollback.emit plan with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"rollback source emission failed: {reprStr error}")

private structure Expected where
  input : Word
  reverts : Bool
  payload : Word
  written0 : Word
  committed0 : Word
  committed1 : Word

private def returned (input payload slot0 slot1 : Nat) : Expected :=
  ⟨Word.ofNatModulo input, false, Word.ofNatModulo payload, Word.ofNatModulo slot0,
    Word.ofNatModulo slot0, Word.ofNatModulo slot1⟩

private def reverted (input payload written0 prior0 prior1 : Nat) : Expected :=
  ⟨Word.ofNatModulo input, true, Word.ofNatModulo payload, Word.ofNatModulo written0,
    Word.ofNatModulo prior0, Word.ofNatModulo prior1⟩

private def sequenceCheck (plan : CheckedPlan) (expected : List Expected) (privateCells : Nat := 0) : IO Unit := do
  let bindings := StorageExecution.fixtureBindings
  let registry : CheckedContractRegistry :=
    ⟨fun address => if address == bindings.address then some plan.contract else none⟩
  let mut world := StorageExecution.initialWorldForContract plan.contract bindings
  for row in expected do
    let some prior := world.account? bindings.address | throw (IO.userError "prior account missing")
    let some ⟨contract, installed⟩ := registry.resolve? world bindings.address |
      throw (IO.userError "committed world no longer resolves the original rollback contract")
    let invocation : TopLevelInvocation := {
      target := bindings.address, caller := bindings.caller, callValue := Word.zero,
      inputData := StorageExecution.inputData row.input }
    match TopLevelExecution.run contract invocation installed 0 with
    | .outOfFuel _ _ _ _ _ _ => pure ()
    | .completed _ => throw (IO.userError "zero fuel was treated as a completed return/revert")
    match TopLevelExecution.run contract invocation installed 10000 with
    | .outOfFuel _ _ _ _ _ _ => throw (IO.userError "rollback golden call exhausted its execution budget")
    | .completed result =>
        let expectedValue : Value := if row.reverts then
          .inRight .word (.inLeft .word (.word row.payload))
          else .inLeft (.sum .word .word) (.word row.payload)
        let expectedOutcome : FrameOutcome Word := if row.reverts then
          .reverted (encodeWordBytesBE row.payload) else .returned (encodeWordBytesBE row.payload)
        ensure (result.coreValue == expectedValue && result.outcome == expectedOutcome)
          "typed completion, original-input parity or 32-byte payload changed"
        let some working := result.terminalContext.context.values.working.1.account? bindings.address |
          throw (IO.userError "working account missing")
        ensure (working.storageRead Word.zero == row.written0 &&
          working.storageRead (Word.ofNatModulo 1) == (prior.storageRead (Word.ofNatModulo 1)).add (Word.ofNatModulo 1))
          "return/revert was selected before both tentative writes completed"
        let some committed := result.finalWorld.account? bindings.address |
          throw (IO.userError "committed account missing")
        ensure (committed.storageRead Word.zero == row.committed0 &&
          committed.storageRead (Word.ofNatModulo 1) == row.committed1 &&
          committed.storageRead (Word.ofNatModulo 2) == Word.zero)
          "rollback did not select the expected committed storage"
        if row.committed0 == Word.zero then
          ensure ((committed.storageValue? Word.zero).isNone) "committed zero storage was not sparse"
        if row.written0 == Word.zero then
          ensure ((working.storageValue? Word.zero).isNone) "tentative zero write was not a deletion"
        ensure (committed.balance == Word.zero && committed.nonce == Word.zero &&
          result.committedJournal.logList.isEmpty && result.committedJournal.createdContractList.isEmpty)
          "storage-only execution changed unrelated observations"
        ensure (result.coreStore.length == privateCells && result.coreStore.all (· == .word (Word.ofNatModulo 2)))
          "private step cells were retained or lost across transaction boundaries"
        ensure ((registry.resolve? result.finalWorld bindings.address).isSome)
          "return/revert replaced the installed original Core program"
        world := result.finalWorld

private def executionChecks : IO Unit := do
  let identity ← checked [.var 0]
  sequenceCheck identity [returned 2 3 2 1, reverted 3 7 5 2 1, returned 4 8 6 2]
  sequenceCheck identity [reverted 1 2 1 0 0, reverted 3 4 3 0 0, returned 2 3 2 1]
  sequenceCheck identity [reverted (wordModulus - 1) 0 (wordModulus - 1) 0 0, returned 2 3 2 1]
  sequenceCheck identity [returned (2 ^ 255) (2 ^ 255 + 1) (2 ^ 255) 1,
    reverted 1 (2 ^ 255 + 3) (2 ^ 255 + 1) (2 ^ 255) 1,
    returned (2 ^ 255) 2 0 2]
  let clears ← checked [.ifE (.binary .wordEq (.var 0) (word 1)) (word 0) (.var 0)]
  sequenceCheck clears [returned 2 3 2 1, reverted (wordModulus - 1) 2 0 2 1, returned 0 4 2 2]
  let arbitrary ← checked [privateStep] (.binary .wordSub entry (word 1))
  sequenceCheck arbitrary [returned 0 2 1 1, reverted 1 5 3 1 1, returned 2 6 4 2] 1
  let aggregate ← checked [increment, pairStep] (.apply (.var 1) (.apply (.var 2) (.var 0)))
  sequenceCheck aggregate [returned 2 6 5 1, reverted 3 13 11 5 1, returned 4 14 12 2] 1
  sequenceCheck (← checked [.var 0] (word 0))
    [returned 2 1 0 1, reverted 1 2 0 0 1, returned 4 2 0 2]

private def admissionChecks : IO Unit := do
  for plan in [← checked [increment], ← checked [privateStep] (.binary .wordSub entry (word 1))] do
    ensure (plan.program.check && plan.program.toCore.checkHost &&
      plan.program.resultType == .sum .word (.sum .word .word) && plan.contract.entryProfile == .wordOutcomeV1)
      "rollback plan lost full host checking or the typed outcome convention"
    ensure (plan.contract.code.program == plan.program.toCore) "admission replaced the original contract"
    ensure (StorageRollback.canonicalNodes plan.step == Wire.programNodes plan.program &&
      Wire.programNodes plan.program == Wire.programNodes plan.step.program + StorageRollback.programOverhead)
      "rollback wrapper overhead differs from the complete original Core"
    match plan.program.body with
    | .letE saved _ =>
        ensure (Wire.encodeExpr saved == Wire.encodeExpr plan.step.program.body)
          "rollback wrapper ignored its arbitrary entry closure"
    | _ => throw (IO.userError "rollback wrapper lost its initial closure binding")
    ensure ((← emitted plan) == (← emitted plan)) "rollback emission is nondeterministic"
  -- Raw primitives join the existing opcode import only when a step uses them.
  let divided ← checked [.binary .wordDiv (.var 0) (word 1)]
  match Solcore.Synthesis.Source.StorageRollback.emit divided with
  | .ok emitted => unless (emitted.source.splitOn "import {sload, sstore, mstore, revert_, div as sc_div, ").length == 2 && (emitted.source.splitOn "    let sc_v3: word = sc_div(sc_v0, sc_v2);").length == 2 do
      throw (IO.userError "StorageRollback emission lost the merged raw division alias or its snapshots")
  | .error error => throw (IO.userError s!"StorageRollback raw division was rejected: {reprStr error}")

private def expectedBasic : String := String.intercalate "\n" [
  "import * from std;", "import * from std.dispatch;",
  "import {sload, sstore, mstore, revert_} from std.opcodes;", "",
  "function sc_fn0(sc_arg: word) returns (word) {",
  "    let sc_v0: word = 1;", "    let sc_v1: word = (sc_arg + sc_v0);",
  "    return sc_v1;", "}", "",
  "function sc_step(sc_arg: word) returns (word) {",
  "    let sc_v0: word = sc_fn0(sc_arg);", "    return sc_v0;", "}", "",
  "contract SynthesizedRollback {",
  "    function run(input: uint256) public returns (uint256) {",
  "        let sc_input: word = Typedef.rep(input);",
  "        let sc_old0: word = sload(0);", "        let sc_old1: word = sload(1);",
  "        let sc_computed: word = sc_step(sc_input + sc_old0);",
  "        sstore(0, sc_computed);", "        sstore(1, sc_old1 + 1);",
  "        let sc_final0: word = sload(0);", "        let sc_final1: word = sload(1);",
  "        let sc_result: word = sc_final0 + sc_final1;",
  "        if ((sc_input & 1) == 1) {", "            mstore(0, sc_result);",
  "            revert_(0, 32);", "        }",
  "        return uint256(sc_result);", "    }", "}", ""]

private def formattingChecks : IO Unit := do
  let source ← emitted (← checked [increment])
  ensure (source.source == expectedBasic) "rollback protocol source changed"
  ensure (source.contractName == "SynthesizedRollback" && source.methodSignature == "run(uint256)" &&
    source.deployPath == ["SynthesizedRollbackDeploy"] &&
    source.runtimePath == ["SynthesizedRollbackDeploy", "SynthesizedRollback"])
    "rollback wrapper metadata changed"
  ensure (Solcore.Synthesis.Source.StorageRollback.emitterVersion == "solcore-source-storage-rollback-v2" &&
    Solcore.Synthesis.Source.StorageRollback.wrapperVersion == "solcore-word-storage-rollback-contract-v1" &&
    Solcore.Synthesis.Source.StorageRollback.selector == "0xa444f5e9" &&
    StorageRollback.version == "core-storage-rollback-contract-v1") "rollback provenance changed"

private def observerChecks : IO Unit := do
  let plan ← checked [.var 0]
  let transactions : List StorageExecution.Transaction :=
    [⟨"first", Word.ofNatModulo 2⟩, ⟨"rollback", Word.ofNatModulo 3⟩, ⟨"after", Word.ofNatModulo 4⟩]
  let history := StorageExecution.observeContract plan.contract transactions StorageExecution.fixtureBindings 10000
  let rows := (history.getObjValAs? (List Json) "transactions").toOption.getD []
  ensure ((history.getObjValAs? String "status").toOption == some "complete" && rows.length == 3 &&
    rows.map (fun row => (row.getObjValAs? String "status").toOption) ==
      [some "returned", some "reverted", some "returned"])
    "public observer did not continue after a completed revert"
  ensure ((rows[0]?.bind fun row => (row.getObjVal? "committedStorage").toOption) ==
    (rows[1]?.bind fun row => (row.getObjVal? "committedStorage").toOption))
    "public observer exported tentative reverted storage"
  let exhausted := StorageExecution.observeContract plan.contract transactions StorageExecution.fixtureBindings 0
  ensure ((exhausted.getObjValAs? String "status").toOption == some "incomplete" &&
    (exhausted.getObjValAs? (List String) "unexecuted").toOption == some ["rollback", "after"])
    "public observer conflated fuel exhaustion with a completed rollback"

def testSourceStorageRollbackEmitter : IO Unit := do
  admissionChecks
  executionChecks
  formattingChecks
  observerChecks

end Tests.SourceStorageRollbackEmitter
