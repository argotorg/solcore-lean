import Solcore.Synthesis.Source.ForwardedCallEmitter
import Solcore.Synthesis.Stateful.ForwardedCallExecution

/-! Forwarded-value protocol regressions through actual installed
ContractRuntime code. Golden histories are hand-computed: they cover committed
forwards on both sides of the 64-bit boundary, the call value folded into the
parent's slot, the forwarded value folded into the child's step, wrapping
arithmetic, a child revert that keeps its amount with the parent, root reverts
alone and after a child revert, and a call value the caller cannot fund.
Calldata comes from Foundry's `cast calldata` encoder. -/
set_option autoImplicit false

namespace Tests.SourceForwardedCallEmitter

open Lean Solcore.Core Solcore.ContractRuntime Solcore.Synthesis.Core
open Solcore.Synthesis.Core.ForwardedCall (CheckedPlan)
open Solcore.Synthesis.Source.NestedCall (EmittedContracts)
open Solcore.Synthesis.Stateful

private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)
private def entry : Wire.Expr := .apply (.var 1) (.var 0)
private def increment : Wire.Expr := .binary .wordAdd (.var 0) (word 1)
private def maximum : Nat := 2 ^ 256 - 1
private def endowment : Nat := 2 ^ 72

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def checked (helpers : List Wire.Expr) : IO CheckedPlan := do
  let some step := Aggregates.CheckedDAG.ofParts? helpers entry |
    throw (IO.userError "forwarded-value step did not pass the checked aggregate profile")
  let some plan := CheckedPlan.ofStep? step |
    throw (IO.userError "forwarded-value wrappers did not pass the full Wire host checker")
  return plan

private def emitted (plan : CheckedPlan) : IO EmittedContracts :=
  match Solcore.Synthesis.Source.ForwardedCall.emit plan with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"forwarded-value source emission failed: {reprStr error}")

private def transactions (rows : List (Nat × Nat × Nat)) : List ForwardedCallExecution.Transaction :=
  rows.zipIdx.map fun ((input, value, amount), index) =>
    ⟨"tx-" ++ toString index, Word.ofNatModulo input, Word.ofNatModulo value, Word.ofNatModulo amount⟩

/-- Both committed accounts at the fixture addresses: balance and slots zero and one. -/
private def accounts (parent child : Nat × Nat × Nat) : Json := toJson ([("parent", "101", parent), ("child", "102", child)].map
  fun (role, address, balance, slot0, slot1) => Json.mkObj [
    ("role", toJson role), ("address", toJson address), ("balance", toJson (toString balance)),
    ("storage", toJson [Json.mkObj [("slot", toJson "0"), ("value", toJson (toString slot0))],
      Json.mkObj [("slot", toJson "1"), ("value", toJson (toString slot1))]])])

/-- Sixty-four lowercase hexadecimal digits, written without the observer's
byte encoder. -/
private def hexWord (value : Nat) : String :=
  let digits := Nat.toDigits 16 value
  "0x" ++ String.ofList (List.replicate (64 - digits.length) '0' ++ digits)

/-- One hand-computed row: root status and payload, both accounts and no logs. -/
private def historyCheck (plan : CheckedPlan) (rows : List (Nat × Nat × Nat))
    (expected : List (String × Nat × (Nat × Nat × Nat) × (Nat × Nat × Nat))) : IO Unit := do
  let history := ForwardedCallExecution.observe plan (transactions rows) NestedCallExecution.fixtureBindings 100000
  let observed := (history.getObjValAs? (List Json) "transactions").toOption.getD []
  ensure ((history.getObjValAs? String "status").toOption == some "complete" && observed.length == expected.length &&
    (history.getObjVal? "initialAccounts").toOption == some (accounts (endowment, 0, 0) (0, 0, 0)))
    "forwarded-value golden history did not complete from the endowed deployment"
  for (row, (status, payload, parent, child)) in observed.zip expected do
    ensure ((row.getObjValAs? String "status").toOption == some status &&
      (row.getObjValAs? String "output").toOption == some (hexWord payload) &&
      (row.getObjVal? "committedAccounts").toOption == some (accounts parent child) &&
      (row.getObjVal? "logs").toOption == some (toJson ([] : List Json)))
      s!"forwarded-value golden row changed: {row.compress}"

private def goldenChecks : IO Unit := do
  -- step(x) = x: a committed forward of five, a child revert that keeps 2^70
  -- with the parent, then a root revert that keeps both accounts.
  historyCheck (← checked [.var 0]) [(0, 7, 5), (1, 0, 2 ^ 70), (2, 1, 1)] [
    ("returned", 12, (endowment + 2, 7, 5), (5, 5, 5)),
    ("returned", 2 ^ 70 + 15, (endowment + 2, 8, 2 ^ 70 + 7), (5, 5, 5)),
    ("reverted", 19, (endowment + 2, 8, 2 ^ 70 + 7), (5, 5, 5))]
  -- step(x) = x + 1 with values across the 64-bit boundary; the maximum input
  -- wraps and makes both frames revert.
  historyCheck (← checked [increment]) [(4, 2 ^ 64, 2 ^ 64 - 1), (5, 2 ^ 70, 2 ^ 64), (maximum, 7, 7)] [
    ("returned", 2 ^ 65 + 8, (endowment + 1, 2 ^ 64 + 4, 2 ^ 64 + 4), (2 ^ 64 - 1, 2 ^ 64 + 4, 2 ^ 64 - 1)),
    ("returned", 2 ^ 70 + 2 ^ 65 + 2 ^ 64 + 20,
      (endowment + 1 + 2 ^ 70, 2 ^ 70 + 2 ^ 64 + 9, 2 ^ 65 + 11), (2 ^ 64 - 1, 2 ^ 64 + 4, 2 ^ 64 - 1)),
    ("reverted", 2 ^ 70 + 2 ^ 65 + 27,
      (endowment + 1 + 2 ^ 70, 2 ^ 70 + 2 ^ 64 + 9, 2 ^ 65 + 11), (2 ^ 64 - 1, 2 ^ 64 + 4, 2 ^ 64 - 1))]

/-- The reverted root's working world holds the call value, the forward and
both frames' writes; the public runtime commits the pre-transfer world. -/
private def refundChecks : IO Unit := do
  let plan ← checked [.var 0]
  let bindings := NestedCallExecution.fixtureBindings
  let world := ForwardedCallExecution.initialWorld plan bindings
  let registry : CheckedContractRegistry := ⟨fun address =>
    if address == bindings.parent then some plan.parentContract
    else if address == bindings.child then some plan.childContract else none⟩
  let some ⟨contract, installed⟩ := registry.resolve? world bindings.parent |
    throw (IO.userError "forwarding parent did not resolve")
  let invocation : TopLevelInvocation := {
    target := bindings.parent, caller := bindings.caller, callValue := Word.ofNatModulo 7,
    inputData := ForwardedCallExecution.inputData bindings (Word.ofNatModulo 2) (Word.ofNatModulo 5) }
  match (BalancedTopLevelExecution.run contract invocation installed registry 100000).view with
  | .rejected _ => throw (IO.userError "a funded call value was rejected")
  | .execution execution =>
      match execution.view with
      | .outOfFuel _ _ _ => throw (IO.userError "forwarded-value golden call exhausted fuel")
      | .completed terminal =>
          ensure (terminal.outcome == .reverted (encodeWordBytesBE (Word.ofNatModulo 16)))
            "bit two did not revert the root with slot zero plus the child payload"
          let working := terminal.terminalContext.context.values.working.1
          let some parent := working.account? bindings.parent | throw (IO.userError "working parent missing")
          let some child := working.account? bindings.child | throw (IO.userError "working child missing")
          ensure (parent.balance == Word.ofNatModulo (endowment + 2) && parent.storageRead Word.zero == Word.ofNatModulo 9 &&
            child.balance == Word.ofNatModulo 5 && child.storageRead (Word.ofNatModulo 1) == Word.ofNatModulo 5)
            "the working world lost the call value, the forward or a write"
          let some committedParent := terminal.finalWorld.account? bindings.parent | throw (IO.userError "committed parent missing")
          let some committedChild := terminal.finalWorld.account? bindings.child | throw (IO.userError "committed child missing")
          let some caller := terminal.finalWorld.account? bindings.caller | throw (IO.userError "committed caller missing")
          ensure (committedParent.balance == Word.ofNatModulo endowment && committedChild.balance == Word.zero &&
            (committedParent.storageValue? Word.zero).isNone && (committedChild.storageValue? Word.zero).isNone &&
            caller.balance == Word.ofNatModulo ForwardedCallExecution.callerFunds)
            "the reverted root committed its value, forward or writes"
  -- A caller that cannot fund the call value is rejected before any execution.
  let poor := ((WorldState.empty.putAccount bindings.caller (Account.empty.withBalance (Word.ofNatModulo 6))).putAccount
    bindings.parent ((Account.empty.withCode plan.parentContract.code).withBalance (Word.ofNatModulo endowment))).putAccount
    bindings.child (Account.empty.withCode plan.childContract.code)
  let some ⟨poorContract, poorInstalled⟩ := registry.resolve? poor bindings.parent |
    throw (IO.userError "forwarding parent did not resolve in the unfunded world")
  match (BalancedTopLevelExecution.run poorContract invocation poorInstalled registry 100000).view with
  | .rejected rejected => ensure (rejected.failure == .insufficientBalance) "unfunded value was not an insufficient balance"
  | .execution _ => throw (IO.userError "an unfunded call value executed")

private def admissionChecks : IO Unit := do
  for plan in [← checked [increment], ← checked [.var 0]] do
    ensure (plan.parentProgram.check && plan.childProgram.check && plan.parentProgram.toCore.checkHost &&
      plan.childProgram.toCore.checkHost && plan.parentProgram.resultType == .sum .word (.sum .word .word) &&
      plan.parentContract.entryProfile == .wordOutcomeV1 && plan.childContract.entryProfile == .wordOutcomeV1)
      "forwarded-value plan lost full host checking or the typed outcome convention"
    ensure (plan.parentContract.code.program == plan.parentProgram.toCore &&
      plan.childContract.code.program == plan.childProgram.toCore) "admission replaced an original contract"
    ensure (ForwardedCall.combinedNodes plan.step ==
        Wire.programNodes plan.parentProgram + Wire.programNodes plan.childProgram &&
      ForwardedCall.combinedNodes plan.step == Wire.programNodes plan.step.program + ForwardedCall.programOverhead)
      "forwarded-value wrapper overhead differs from the complete original Core"
    match plan.childProgram.body with
    | .letE saved _ =>
        ensure (Wire.encodeExpr saved == Wire.encodeExpr plan.step.program.body)
          "forwarded-value child ignored its arbitrary entry closure"
    | _ => throw (IO.userError "forwarded-value child lost its initial closure binding")
    ensure ((← emitted plan) == (← emitted plan)) "forwarded-value emission is nondeterministic"
  ensure (Wire.encodeProgram (← checked [increment]).parentProgram == Wire.encodeProgram (← checked [.var 0]).parentProgram &&
      ForwardedCall.programOverhead == 169) "the parent program depends on the step or the overhead changed"

private def expectedBasic : String := String.intercalate "\n" [
  "import * from std;", "import * from std.dispatch;",
  "import {sload, sstore, mload, mstore, calldataload, gas, call, returndatasize, return_, revert_, invalid, callvalue as sc_callvalue} from std.opcodes;", "",
  "function sc_fn0(sc_arg: word) returns (word) {",
  "    let sc_v0: word = 1;", "    let sc_v1: word = (sc_arg + sc_v0);",
  "    return sc_v1;", "}", "",
  "function sc_step(sc_arg: word) returns (word) {",
  "    let sc_v0: word = sc_fn0(sc_arg);", "    return sc_v0;", "}", "",
  "contract SynthesizedRecipient {",
  "    fallback() payable {",
  "        let sc_input: word = calldataload(0);",
  "        let sc_value: word = sc_callvalue();",
  "        let sc_old0: word = sload(0);", "        let sc_old1: word = sload(1);",
  "        let sc_computed: word = sc_step(sc_input + sc_value + sc_old0);",
  "        sstore(0, sc_computed);", "        sstore(1, sc_old1 + sc_value);",
  "        let sc_ptr: word = mload(64);", "        mstore(64, sc_ptr + 32);",
  "        mstore(sc_ptr, sc_computed);",
  "        if ((sc_input & 1) == 1) {", "            revert_(sc_ptr, 32);", "        }",
  "        return_(sc_ptr, 32);", "    }", "}", "",
  "contract SynthesizedForwarder {",
  "    constructor() payable {}",
  "    function run(target: uint256, input: uint256, amount: uint256) public payable returns (uint256) {",
  "        let sc_target: word = Typedef.rep(target);",
  "        let sc_input: word = Typedef.rep(input);",
  "        let sc_amount: word = Typedef.rep(amount);",
  "        let sc_before: word = sload(0) + sc_input + sc_callvalue();",
  "        sstore(0, sc_before);",
  "        let sc_ptr: word = mload(64);", "        mstore(64, sc_ptr + 64);",
  "        mstore(sc_ptr, sc_input);",
  "        let sc_ok: word = call(gas(), sc_target, sc_amount, sc_ptr, 32, sc_ptr + 32, 32);",
  "        if (!(returndatasize() == 32)) {", "            invalid();", "        }",
  "        let sc_after: word = mload(sc_ptr + 32);",
  "        if (sc_ok == 0) {", "            sc_after = sc_after + 1;", "        }",
  "        sstore(1, sc_after);",
  "        let sc_result: word = sload(0) + sload(1);",
  "        if ((sc_input & 2) == 2) {",
  "            mstore(sc_ptr, sc_result);", "            revert_(sc_ptr, 32);", "        }",
  "        return uint256(sc_result);", "    }", "}", ""]

private def formattingChecks : IO Unit := do
  let source ← emitted (← checked [increment])
  ensure (source.source == expectedBasic) "forwarded-value protocol source changed"
  ensure (source.parentContractName == "SynthesizedForwarder" && source.childContractName == "SynthesizedRecipient" &&
    source.parentMethodSignature == "run(uint256,uint256,uint256)" && source.selector == "0x24b912e5" &&
    source.parentConstructorValue == toString endowment && source.childConstructorValue == "0" &&
    source.parentDeployPath == ["SynthesizedForwarderDeploy"] &&
    source.childRuntimePath == ["SynthesizedRecipientDeploy", "SynthesizedRecipient"])
    "forwarded-value wrapper metadata changed"
  -- Raw primitives join the same opcode import only when a step uses them.
  let divided ← emitted (← checked [.binary .wordDiv (.var 0) (word 1)])
  ensure ((divided.source.splitOn "invalid, callvalue as sc_callvalue, div as sc_div, ").length == 2)
    "forwarded-value emission lost the merged raw division alias"
  ensure (Solcore.Synthesis.Source.ForwardedCall.emitterVersion == "solcore-source-forwarded-value-v1" &&
    Solcore.Synthesis.Source.ForwardedCall.wrapperVersion == "solcore-word-forwarded-value-v1" &&
    ForwardedCall.version == "core-forwarded-value-call-v1" &&
    ForwardedCallExecution.parentEndowment == endowment) "forwarded-value provenance changed"

private def observerChecks : IO Unit := do
  -- `cast calldata "run(uint256,uint256,uint256)" 102 5 1180591620717411303424`
  ensure (ForwardedCallExecution.calldata NestedCallExecution.fixtureBindings (Word.ofNatModulo 5) (Word.ofNatModulo (2 ^ 70)) ==
    "0x24b912e5" ++ String.ofList (List.replicate 62 '0') ++ "66" ++ String.ofList (List.replicate 63 '0') ++ "5" ++
      String.ofList (List.replicate 46 '0') ++ "40" ++ String.ofList (List.replicate 16 '0'))
    "forwarded-value calldata is not the selector, child, input and amount Words"
  let plan ← checked [.var 0]
  let calls := transactions [(0, 7, 5), (1, 0, 1), (0, 0, 0)]
  let exhausted := ForwardedCallExecution.observe plan calls NestedCallExecution.fixtureBindings 0
  let rows := (exhausted.getObjValAs? (List Json) "transactions").toOption.getD []
  ensure ((exhausted.getObjValAs? String "status").toOption == some "incomplete" &&
    (exhausted.getObjValAs? (List String) "unexecuted").toOption == some ["tx-1", "tx-2"] && rows.length == 1 &&
    (rows[0]!.getObjValAs? String "status").toOption == some "out-of-fuel" &&
    (rows[0]!.getObjVal? "logs").toOption == some Json.null &&
    (exhausted.getObjVal? "finalAccounts").toOption == (exhausted.getObjVal? "initialAccounts").toOption)
    "forwarded-value observer conflated fuel exhaustion with completion or committed its value"
  let complete := ForwardedCallExecution.observe plan calls NestedCallExecution.fixtureBindings 100000
  ensure ((complete.getObjValAs? String "schema").toOption == some "solcore-lean.forward-history.v2" &&
    (complete.getObjValAs? String "status").toOption == some "complete")
    "history did not declare its schema or complete"

def testSourceForwardedCallEmitter : IO Unit := do
  admissionChecks
  goldenChecks
  refundChecks
  formattingChecks
  observerChecks

end Tests.SourceForwardedCallEmitter
