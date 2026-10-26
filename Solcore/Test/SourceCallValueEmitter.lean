import Solcore.Synthesis.Source.CallValueEmitter
import Solcore.Synthesis.Stateful.CallValueExecution

/-! Call-value protocol regressions through actual installed ContractRuntime
code. Golden histories are hand-computed: they cover a funded deployment, value
folded into the step input, the accepted-value slot, wrapping arithmetic,
values on both sides of the 64-bit boundary, refunds on revert and a transfer
the caller cannot fund. -/
set_option autoImplicit false

namespace Tests.SourceCallValueEmitter

open Lean Solcore.Core Solcore.ContractRuntime Solcore.Synthesis.Core
open Solcore.Synthesis.Core.CallValue (CheckedPlan)
open Solcore.Synthesis.Source (EmittedProgram)
open Solcore.Synthesis.Stateful

private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)
private def entry : Wire.Expr := .apply (.var 1) (.var 0)
private def increment : Wire.Expr := .binary .wordAdd (.var 0) (word 1)
private def maximum : Nat := 2 ^ 256 - 1

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def checked (helpers : List Wire.Expr) (deployment : Nat) : IO CheckedPlan := do
  let some step := Aggregates.CheckedDAG.ofParts? helpers entry |
    throw (IO.userError "call-value step did not pass the checked aggregate profile")
  let some plan := CheckedPlan.ofParts? step (Word.ofNatModulo deployment) |
    throw (IO.userError "call-value wrapper did not pass the full Wire host checker")
  return plan

private def emitted (plan : CheckedPlan) : IO EmittedProgram :=
  match Solcore.Synthesis.Source.CallValue.emit plan with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"call-value source emission failed: {reprStr error}")

private def transactions (rows : List (Nat × Nat × Nat)) : List CallValueExecution.Transaction :=
  rows.zipIdx.map fun ((flags, input, value), index) =>
    ⟨"tx-" ++ toString index, Word.ofNatModulo flags, Word.ofNatModulo input, Word.ofNatModulo value⟩

private def slotRows (slot0 slot1 : Nat) : Json := toJson [
  Json.mkObj [("slot", toJson "0"), ("value", toJson (toString slot0))],
  Json.mkObj [("slot", toJson "1"), ("value", toJson (toString slot1))]]

/-- Sixty-four lowercase hexadecimal digits, written without the observer's
byte encoder. -/
private def hexWord (value : Nat) : String :=
  let digits := Nat.toDigits 16 value
  "0x" ++ String.ofList (List.replicate (64 - digits.length) '0' ++ digits)

/-- One hand-computed row: status, payload, slots zero and one, and balance. -/
private def historyCheck (plan : CheckedPlan) (rows : List (Nat × Nat × Nat))
    (expected : List (String × Nat × (Nat × Nat) × Nat)) : IO Unit := do
  let history := CallValueExecution.observe plan (transactions rows) StorageExecution.fixtureBindings 10000
  let observed := (history.getObjValAs? (List Json) "transactions").toOption.getD []
  ensure ((history.getObjValAs? String "status").toOption == some "complete" && observed.length == expected.length &&
    (history.getObjValAs? String "initialBalance").toOption == some (toString plan.deploymentValue.val))
    "call-value golden history did not complete from its deployment value"
  for (row, (status, payload, (slot0, slot1), balance)) in observed.zip expected do
    ensure ((row.getObjValAs? String "status").toOption == some status &&
      (row.getObjValAs? String "output").toOption == some (hexWord payload) &&
      (row.getObjVal? "committedStorage").toOption == some (slotRows slot0 slot1) &&
      (row.getObjValAs? String "committedBalance").toOption == some (toString balance))
      s!"call-value golden row changed: {row.compress}"

private def goldenChecks : IO Unit := do
  -- step(x) = x: the result is input + value + slot 0; a revert refunds.
  historyCheck (← checked [.var 0] 5) [(0, 2, 7), (1, 1, 3), (0, 0, 0)] [
    ("returned", 9, (9, 7), 12),
    ("reverted", 13, (9, 7), 12),
    ("returned", 9, (9, 7), 12)]
  -- step(x) = x + 1 wraps at the maximum; values cross the 64-bit boundary.
  historyCheck (← checked [increment] 0) [(0, maximum, 1), (2, 0, 2 ^ 64), (3, 5, 2 ^ 70)] [
    ("returned", 1, (1, 1), 1),
    ("returned", 2 ^ 64 + 2, (2 ^ 64 + 2, 2 ^ 64 + 1), 2 ^ 64 + 1),
    ("reverted", 2 ^ 70 + 2 ^ 64 + 8, (2 ^ 64 + 2, 2 ^ 64 + 1), 2 ^ 64 + 1)]

/-- The reverted call's working world holds the transferred value and both
writes; the public runtime commits the pre-transfer world. -/
private def refundChecks : IO Unit := do
  let plan ← checked [.var 0] 5
  let bindings := StorageExecution.fixtureBindings
  let world := CallValueExecution.initialWorldForContract plan.contract plan.deploymentValue bindings
  let registry : CheckedContractRegistry :=
    ⟨fun address => if address == bindings.address then some plan.contract else none⟩
  let some ⟨contract, installed⟩ := registry.resolve? world bindings.address |
    throw (IO.userError "call-value contract did not resolve")
  let invocation : TopLevelInvocation := {
    target := bindings.address, caller := bindings.caller, callValue := Word.ofNatModulo 7,
    inputData := CallValueExecution.inputData (Word.ofNatModulo 1) (Word.ofNatModulo 3) }
  match (BalancedTopLevelExecution.run contract invocation installed registry 10000).view with
  | .rejected _ => throw (IO.userError "a funded call value was rejected")
  | .execution execution =>
      match execution.view with
      | .outOfFuel _ _ _ => throw (IO.userError "call-value golden call exhausted fuel")
      | .completed terminal =>
          ensure (terminal.outcome == .reverted (encodeWordBytesBE (Word.ofNatModulo 10)))
            "odd flags did not revert with input + value + slot 0"
          let some working := terminal.terminalContext.context.values.working.1.account? bindings.address |
            throw (IO.userError "working account missing")
          ensure (working.balance == Word.ofNatModulo 12 && working.storageRead Word.zero == Word.ofNatModulo 10 &&
            working.storageRead (Word.ofNatModulo 1) == Word.ofNatModulo 7)
            "the working world lost the transferred value or a write"
          let some committed := terminal.finalWorld.account? bindings.address |
            throw (IO.userError "committed account missing")
          let some caller := terminal.finalWorld.account? bindings.caller |
            throw (IO.userError "committed caller missing")
          ensure (committed.balance == Word.ofNatModulo 5 && (committed.storageValue? Word.zero).isNone &&
            caller.balance == Word.ofNatModulo CallValueExecution.callerFunds)
            "the reverted value or writes were committed"
  -- A caller that cannot fund the value is rejected before any execution.
  let poor := (WorldState.empty.putAccount bindings.caller (Account.empty.withBalance (Word.ofNatModulo 6))).putAccount
    bindings.address ((Account.empty.withCode plan.contract.code).withBalance (Word.ofNatModulo 5))
  let some ⟨poorContract, poorInstalled⟩ := registry.resolve? poor bindings.address |
    throw (IO.userError "call-value contract did not resolve in the unfunded world")
  match (BalancedTopLevelExecution.run poorContract invocation poorInstalled registry 10000).view with
  | .rejected rejected => ensure (rejected.failure == .insufficientBalance) "unfunded value was not an insufficient balance"
  | .execution _ => throw (IO.userError "an unfunded call value executed")

private def admissionChecks : IO Unit := do
  for plan in [← checked [increment] 0, ← checked [.var 0] 5] do
    ensure (plan.program.check && plan.program.toCore.checkHost &&
      plan.program.resultType == .sum .word (.sum .word .word) && plan.contract.entryProfile == .wordOutcomeV1)
      "call-value plan lost full host checking or the typed outcome convention"
    ensure (plan.contract.code.program == plan.program.toCore) "admission replaced the original contract"
    ensure (CallValue.canonicalNodes plan.step == Wire.programNodes plan.program &&
      Wire.programNodes plan.program == Wire.programNodes plan.step.program + CallValue.programOverhead)
      "call-value wrapper overhead differs from the complete original Core"
    match plan.program.body with
    | .letE saved _ =>
        ensure (Wire.encodeExpr saved == Wire.encodeExpr plan.step.program.body)
          "call-value wrapper ignored its arbitrary entry closure"
    | _ => throw (IO.userError "call-value wrapper lost its initial closure binding")
    ensure ((← emitted plan) == (← emitted plan)) "call-value emission is nondeterministic"
  ensure (Wire.encodeProgram (← checked [increment] 0).program == Wire.encodeProgram (← checked [increment] 5).program)
    "the deployment value changed the original Core program"

private def expectedBasic : String := String.intercalate "\n" [
  "import * from std;", "import * from std.dispatch;",
  "import {sload, sstore, mstore, revert_, callvalue as sc_callvalue} from std.opcodes;", "",
  "function sc_fn0(sc_arg: word) returns (word) {",
  "    let sc_v0: word = 1;", "    let sc_v1: word = (sc_arg + sc_v0);",
  "    return sc_v1;", "}", "",
  "function sc_step(sc_arg: word) returns (word) {",
  "    let sc_v0: word = sc_fn0(sc_arg);", "    return sc_v0;", "}", "",
  "contract SynthesizedCallValue {",
  "    constructor() payable {}",
  "    function run(flags: uint256, input: uint256) public payable returns (uint256) {",
  "        let sc_flags: word = Typedef.rep(flags);",
  "        let sc_input: word = Typedef.rep(input);",
  "        let sc_value: word = sc_callvalue();",
  "        let sc_old: word = sload(0);", "        let sc_total: word = sload(1);",
  "        let sc_result: word = sc_step(sc_input + sc_value + sc_old);",
  "        sstore(0, sc_result);", "        sstore(1, sc_total + sc_value);",
  "        if ((sc_flags & 1) == 1) {", "            mstore(0, sc_result);",
  "            revert_(0, 32);", "        }",
  "        return uint256(sc_result);", "    }", "}", ""]

private def formattingChecks : IO Unit := do
  let source ← emitted (← checked [increment] 5)
  ensure (source.source == expectedBasic) "call-value protocol source changed"
  ensure (source.contractName == "SynthesizedCallValue" && source.methodSignature == "run(uint256,uint256)" &&
    source.deployPath == ["SynthesizedCallValueDeploy"] &&
    source.runtimePath == ["SynthesizedCallValueDeploy", "SynthesizedCallValue"])
    "call-value wrapper metadata changed"
  -- Raw primitives join the same opcode import only when a step uses them.
  let divided ← emitted (← checked [.binary .wordDiv (.var 0) (word 1)] 0)
  ensure ((divided.source.splitOn "import {sload, sstore, mstore, revert_, callvalue as sc_callvalue, div as sc_div, ").length == 2)
    "call-value emission lost the merged raw division alias"
  ensure (Solcore.Synthesis.Source.CallValue.emitterVersion == "solcore-source-call-value-v1" &&
    Solcore.Synthesis.Source.CallValue.wrapperVersion == "solcore-word-call-value-contract-v1" &&
    Solcore.Synthesis.Source.CallValue.selector == "0x7357f5d2" && CallValue.version == "core-call-value-contract-v1")
    "call-value provenance changed"

private def observerChecks : IO Unit := do
  ensure (CallValueExecution.calldata (Word.ofNatModulo 2) Word.maximum ==
    "0x7357f5d2" ++ String.ofList (List.replicate 63 '0') ++ "2" ++ String.ofList (List.replicate 64 'f'))
    "call-value calldata is not selector, flags and input Words"
  let plan ← checked [.var 0] 5
  let calls := transactions [(0, 2, 7), (1, 1, 1), (0, 0, 0)]
  let exhausted := CallValueExecution.observe plan calls StorageExecution.fixtureBindings 0
  let rows := (exhausted.getObjValAs? (List Json) "transactions").toOption.getD []
  ensure ((exhausted.getObjValAs? String "status").toOption == some "incomplete" &&
    (exhausted.getObjValAs? (List String) "unexecuted").toOption == some ["tx-1", "tx-2"] && rows.length == 1 &&
    (rows[0]!.getObjValAs? String "committedBalance").toOption == some "5" &&
    (exhausted.getObjVal? "finalBalance").toOption == (exhausted.getObjVal? "initialBalance").toOption)
    "call-value observer conflated fuel exhaustion with completion or committed its value"
  let complete := CallValueExecution.observe plan calls StorageExecution.fixtureBindings 10000
  ensure ((complete.getObjVal? "observedSlots").toOption == some (toJson (["0", "1"] : List String)) &&
    (complete.getObjValAs? String "deploymentValue").toOption == some "5" &&
    (complete.getObjVal? "initialLogs").toOption == some (toJson ([] : List Json)) &&
    (complete.getObjValAs? String "finalBalance").toOption == some "12")
    "history did not declare its slots, deployment value, deployment logs or final balance"

def testSourceCallValueEmitter : IO Unit := do
  admissionChecks
  goldenChecks
  refundChecks
  formattingChecks
  observerChecks

end Tests.SourceCallValueEmitter
