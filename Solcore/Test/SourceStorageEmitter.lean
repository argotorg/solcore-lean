import Solcore.Synthesis.Source.StorageEmitter
import Solcore.ContractRuntime.CheckedContractRegistry
import Solcore.ContractRuntime.TopLevelExecution

/-! Fixed-storage source emission and real checked ContractRuntime invocations.
The tests resolve the installed contract again after every committed call and
compare the returned Word plus both slots with a separate recurrence. Input
bytes always use the exact run(uint256) selector and one complete ABI Word. -/
set_option autoImplicit false

namespace Tests.SourceStorageEmitter

open Solcore.Core
open Solcore.ContractRuntime
open Solcore.Synthesis.Core
open Solcore.Synthesis.Source
open Solcore.Synthesis.Core.StorageContract (CheckedPlan)

private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)
def entry : Wire.Expr := .apply (.var 1) (.var 0)
def increment : Wire.Expr := .binary .wordAdd (.var 0) (word 1)

/-- Private memory begins at zero on every invocation; the arbitrary entry
subtracts one, so invoking this helper directly would also be observably wrong. -/
def privateStep : Wire.Expr :=
  .letE (.newCell .word (word 0))
    (.letE (.storeCell (.var 0) (.binary .wordAdd (.loadCell (.var 0)) (word 2)))
      (.binary .wordAdd (.var 2) (.loadCell (.var 1))))

def pairStep : Wire.Expr :=
  .letE (.newCell .word (.var 0))
    (.letE (.pair (.loadCell (.var 0))
      (.letE (.storeCell (.var 0) (word 2)) (.loadCell (.var 1))))
      (.binary .wordAdd (.first (.var 0)) (.second (.var 0))))

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def checked (helpers : List Wire.Expr) (body : Wire.Expr := entry) : IO CheckedPlan := do
  let some step := Aggregates.CheckedDAG.ofParts? helpers body |
    throw (IO.userError "storage step did not pass the checked aggregate profile")
  let some plan := CheckedPlan.ofParts? step |
    throw (IO.userError "storage wrapper did not pass the full Wire host checker")
  return plan

private def emitted (plan : CheckedPlan) : IO EmittedProgram :=
  match Storage.emit plan with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"storage source emission failed: {reprStr error}")

private def selectorBytes : Bytes := [0xa4, 0x44, 0xf5, 0xe9].toByteArray

private def inputData (input : Word) : HostStorageDriver.InputData := {
  bytes := selectorBytes ++ encodeWordBytesBE input
  size_lt_wordModulus := by
    simp only [ByteArray.size_append, encodeWordBytesBE_size]
    change 36 < wordModulus
    decide
}

private def target : Address := ⟨100, by decide⟩
private def caller : Address := ⟨200, by decide⟩

private def invocation (input : Word) : TopLevelInvocation := {
  target, caller, callValue := Word.zero, inputData := inputData input
}

private def sequenceCheck (plan : CheckedPlan) (inputs : List Word)
    (stepResult : Word → Word) (privateCells : Nat) : IO Unit := do
  let registry : CheckedContractRegistry :=
    ⟨fun address => if address == target then some plan.contract else none⟩
  let mut world := WorldState.empty.putAccount target (Account.empty.withCode plan.code)
  let mut expected0 := Word.zero
  let mut expected1 := Word.zero
  for input in inputs do
    ensure ((inputData input).bytes.size == 36 &&
      (inputData input).wordBE? (Word.ofNatModulo 4) == some input)
      "canonical ABI input did not decode to the original Word"
    let some ⟨contract, installed⟩ := registry.resolve? world target |
      throw (IO.userError "committed world no longer resolves the original checked contract")
    let call := invocation input
    match TopLevelExecution.run contract call installed 0 with
    | .outOfFuel _ _ _ _ _ _ => pure ()
    | .completed _ => throw (IO.userError "zero fuel was treated as a completed storage call")
    let next0 := stepResult (input.add expected0)
    let next1 := expected1.add (Word.ofNatModulo 1)
    match TopLevelExecution.run contract call installed 4000 with
    | .outOfFuel _ _ _ _ _ _ => throw (IO.userError "checked storage call exhausted the completion budget")
    | .completed result =>
        let expected := next0.add next1
        ensure (result.coreValue == .word expected && result.outcome == .returned (encodeWordBytesBE expected))
          "checked storage call returned the wrong recurrence or ABI bytes"
        ensure (result.coreStore.length == privateCells)
          "private helper cells survived across contract invocations"
        for cell in result.coreStore do
          ensure (cell == .word (Word.ofNatModulo 2)) "private helper cell contents changed"
        let some account := result.finalWorld.account? target |
          throw (IO.userError "committed storage account disappeared")
        ensure (account.storageRead Word.zero == next0 &&
          account.storageRead (Word.ofNatModulo 1) == next1 &&
          account.storageRead (Word.ofNatModulo 2) == Word.zero)
          "committed slots differ from the independent two-slot recurrence"
        ensure (account.balance == Word.zero && account.nonce == Word.zero)
          "storage-only invocation changed balance or nonce"
        if next0 == Word.zero then
          ensure ((account.storageValue? Word.zero).isNone) "zero storage write was not represented as deletion"
        ensure ((registry.resolve? result.finalWorld target).isSome)
          "storage commit changed the installed checked program"
        world := result.finalWorld
        expected0 := next0
        expected1 := next1

private def admissionChecks : IO Unit := do
  let basic ← checked [increment]
  let arbitrary ← checked [privateStep] (.binary .wordSub entry (word 1))
  let mixed ← checked [increment, pairStep] (.apply (.var 1) (.apply (.var 2) (.var 0)))
  for plan in [basic, arbitrary, mixed] do
    ensure (plan.program.check && plan.program.toCore.checkHost &&
      plan.program.resultType == .word && plan.contract.entryProfile == .returnWord)
      "storage plan escaped Wire/current host checking or changed its completion profile"
    ensure (plan.contract.code.program == plan.program.toCore) "contract admission replaced the original Core"
    ensure (StorageContract.canonicalNodes plan.step == Wire.programNodes plan.program &&
      Wire.programNodes plan.program == Wire.programNodes plan.step.program + StorageContract.programOverhead)
      "storage wrapper node overhead differs from the complete original Core"
    match plan.program.body with
    | .letE saved _ =>
        ensure (Wire.encodeExpr saved == Wire.encodeExpr plan.step.program.body)
          "storage wrapper did not capture the complete arbitrary entry once"
    | _ => throw (IO.userError "storage wrapper lost its initial entry-closure binding")
    let source ← emitted plan
    ensure (source == (← emitted plan)) "storage emission is nondeterministic"
    ensure (source.contractName == "SynthesizedStorage" && source.methodSignature == "run(uint256)" &&
      source.deployPath == ["SynthesizedStorageDeploy"] &&
      source.runtimePath == ["SynthesizedStorageDeploy", "SynthesizedStorage"])
      "storage wrapper metadata changed"
  -- Raw primitives join the existing opcode import only when a step uses them.
  let divided ← checked [.binary .wordDiv (.var 0) (word 1)]
  match Storage.emit divided with
  | .ok emitted => unless (emitted.source.splitOn "import {sload, sstore, div as sc_div, mod as sc_mod, ").length == 2 && (emitted.source.splitOn "    let sc_v3: word = sc_div(sc_v0, sc_v2);").length == 2 do
      throw (IO.userError "Storage emission lost the merged raw division alias or its snapshots")
  | .error error => throw (IO.userError s!"Storage raw division was rejected: {reprStr error}")

private def executionChecks : IO Unit := do
  let inputs := [Word.zero, Word.ofNatModulo 1, Word.ofNatModulo 3, Word.maximum,
    Word.zero, Word.ofNatModulo (2 ^ 255), Word.ofNatModulo 7]
  sequenceCheck (← checked [increment]) inputs (fun input => input.add (Word.ofNatModulo 1)) 0
  sequenceCheck (← checked [privateStep] (.binary .wordSub entry (word 1)))
    inputs (fun input => input.add (Word.ofNatModulo 1)) 1
  sequenceCheck (← checked [increment, pairStep] (.apply (.var 1) (.apply (.var 2) (.var 0))))
    inputs (fun input => input.add (Word.ofNatModulo 3)) 1
  sequenceCheck (← checked [increment] (.var 0))
    [Word.ofNatModulo 5, Word.ofNatModulo (wordModulus - 5), Word.zero] id 0
  sequenceCheck (← checked [increment] (word 0)) inputs (fun _ => Word.zero) 0

private def expectedBasic : String := String.intercalate "\n" [
  "import * from std;", "import * from std.dispatch;",
  "import {sload, sstore} from std.opcodes;", "",
  "function sc_fn0(sc_arg: word) returns (word) {",
  "    let sc_v0: word = 1;",
  "    let sc_v1: word = (sc_arg + sc_v0);",
  "    return sc_v1;", "}", "",
  "function sc_step(sc_arg: word) returns (word) {",
  "    let sc_v0: word = sc_fn0(sc_arg);",
  "    return sc_v0;", "}", "",
  "contract SynthesizedStorage {",
  "    function run(input: uint256) public returns (uint256) {",
  "        let sc_input: word = Typedef.rep(input);",
  "        let sc_old0: word = sload(0);",
  "        let sc_old1: word = sload(1);",
  "        let sc_computed: word = sc_step(sc_input + sc_old0);",
  "        sstore(0, sc_computed);",
  "        sstore(1, sc_old1 + 1);",
  "        let sc_final0: word = sload(0);",
  "        let sc_final1: word = sload(1);",
  "        return uint256(sc_final0 + sc_final1);", "    }", "}", ""]

private def contains (source fragment : String) : Bool := (source.splitOn fragment).length > 1

private def formattingChecks : IO Unit := do
  ensure ((← emitted (← checked [increment])).source == expectedBasic)
    "fixed storage protocol or source wrapper changed"
  let arbitrary ← emitted (← checked [increment] (.binary .wordAdd entry (word 10)))
  ensure (contains arbitrary.source (String.intercalate "\n" [
    "function sc_step(sc_arg: word) returns (word) {",
    "    let sc_v0: word = sc_fn0(sc_arg);", "    let sc_v1: word = 10;",
    "    let sc_v2: word = (sc_v0 + sc_v1);", "    return sc_v2;", "}"]))
    "storage wrapper ignored the arbitrary checked entry"
  ensure (Storage.emitterVersion == "solcore-source-storage-v2" &&
    Storage.wrapperVersion == "solcore-word-storage-contract-v1" &&
    Storage.selector == "0xa444f5e9" && StorageContract.version == "core-storage-contract-v1")
    "storage provenance changed"

def testSourceStorageEmitter : IO Unit := do
  admissionChecks
  executionChecks
  formattingChecks

end Tests.SourceStorageEmitter
