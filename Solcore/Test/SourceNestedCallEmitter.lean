import Solcore.Synthesis.Source.NestedCallEmitter
import Solcore.Synthesis.Stateful.NestedCallExecution

/-! Checked parent/child wrappers through the actual nested scheduler. These
goldens distinguish child rollback from root rollback, retain value transfers
only after committed child success, and exercise an arbitrary stateful step. -/
set_option autoImplicit false

namespace Tests.SourceNestedCallEmitter

open Solcore.Core Solcore.ContractRuntime Solcore.Synthesis.Core
open Solcore.Synthesis.Core.NestedCall (CheckedPlan)
open Solcore.Synthesis.Stateful

private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)
private def entry : Wire.Expr := .apply (.var 1) (.var 0)

private def privateStep : Wire.Expr :=
  .letE (.newCell .word (word 0))
    (.letE (.storeCell (.var 0) (.binary .wordAdd (.loadCell (.var 0)) (word 2)))
      (.binary .wordAdd (.var 2) (.loadCell (.var 1))))

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def checked (helpers : List Wire.Expr) (body : Wire.Expr := entry) : IO CheckedPlan := do
  let some step := Aggregates.CheckedDAG.ofParts? helpers body |
    throw (IO.userError "nested-call step did not pass the aggregate checker")
  let some plan := CheckedPlan.ofStep? step |
    throw (IO.userError "nested-call wrappers did not pass the full Wire host checker")
  return plan

private def emitted (plan : CheckedPlan) : IO Solcore.Synthesis.Source.NestedCall.EmittedContracts :=
  match Solcore.Synthesis.Source.NestedCall.emit plan with
  | .ok result => pure result
  | .error error => throw (IO.userError s!"nested-call source emission failed: {reprStr error}")

private structure Snapshot where
  parent0 : Nat
  parent1 : Nat
  child0 : Nat
  child1 : Nat
  parentBalance : Nat
  childBalance : Nat

private structure Expected where
  input : Nat
  reverts : Bool
  payload : Nat
  committed : Snapshot
  /-- False denotes the parent emitter, true the child emitter. -/
  workingLogs : List (Bool × Nat × Nat)

private def logs (bindings : NestedCallExecution.Bindings)
    (entries : List (Bool × Nat × Nat)) : List CheckedCoreWordLog :=
  entries.map fun (child, topic, payload) =>
    ⟨if child then bindings.child else bindings.parent, Word.ofNatModulo topic, Word.ofNatModulo payload⟩

private def sequenceCheck (plan : CheckedPlan) (expected : List Expected) : IO Unit := do
  let bindings := NestedCallExecution.fixtureBindings
  let registry : CheckedContractRegistry := {
    lookup := fun address => if address = bindings.parent then some plan.parentContract
      else if address = bindings.child then some plan.childContract else none }
  let mut world := NestedCallExecution.initialWorld plan bindings
  for row in expected do
    let some ⟨contract, installed⟩ := registry.resolve? world bindings.parent |
      throw (IO.userError "committed parent no longer resolves to its original Core program")
    let invocation : TopLevelInvocation := {
      target := bindings.parent, caller := bindings.caller, callValue := Word.zero,
      inputData := NestedCallExecution.inputData bindings (Word.ofNatModulo row.input) }
    match (OneLevelNestedExecution.run contract invocation installed registry 0).view with
    | .outOfFuel _ _ _ => pure ()
    | .completed _ => throw (IO.userError "zero fuel was treated as a completed nested transaction")
    match (OneLevelNestedExecution.run contract invocation installed registry 10000).view with
    | .outOfFuel _ _ _ => throw (IO.userError "nested golden exhausted its execution budget")
    | .completed result =>
        let payload := Word.ofNatModulo row.payload
        let typed : Value := if row.reverts then
          .inRight .word (.inLeft .word (.word payload))
          else .inLeft (.sum .word .word) (.word payload)
        let outcome : FrameOutcome Word := if row.reverts then
          .reverted (encodeWordBytesBE payload) else .returned (encodeWordBytesBE payload)
        ensure (result.coreValue == typed && result.outcome == outcome)
          "nested wrapper changed the typed completion or exact 32-byte payload"
        let some parent := result.finalWorld.account? bindings.parent |
          throw (IO.userError "committed parent account missing")
        let some child := result.finalWorld.account? bindings.child |
          throw (IO.userError "committed child account missing")
        let snapshot := row.committed
        ensure (parent.storageRead Word.zero == Word.ofNatModulo snapshot.parent0 &&
          parent.storageRead (Word.ofNatModulo 1) == Word.ofNatModulo snapshot.parent1 &&
          child.storageRead Word.zero == Word.ofNatModulo snapshot.child0 &&
          child.storageRead (Word.ofNatModulo 1) == Word.ofNatModulo snapshot.child1 &&
          parent.balance == Word.ofNatModulo snapshot.parentBalance &&
          child.balance == Word.ofNatModulo snapshot.childBalance)
          "nested rollback or value transfer selected the wrong committed accounts"
        ensure (result.workingJournal.logList == logs bindings row.workingLogs &&
          result.committedJournal.logList == (if row.reverts then [] else logs bindings row.workingLogs))
          "child rollback or root rollback changed committed log order"
        ensure (parent.storageRead (Word.ofNatModulo 2) == Word.zero &&
          child.storageRead (Word.ofNatModulo 2) == Word.zero &&
          parent.nonce == Word.zero && child.nonce == Word.zero && result.coreStore.isEmpty &&
          result.committedJournal.createdContractList.isEmpty)
          "nested execution changed an unrelated account field or exposed the child's private heap"
        ensure ((registry.resolve? result.finalWorld bindings.parent).isSome &&
          (registry.resolve? result.finalWorld bindings.child).isSome)
          "nested completion replaced either installed original Core program"
        world := result.finalWorld

private def executionChecks : IO Unit := do
  let identity ← checked [.var 0]
  sequenceCheck identity [
    ⟨4, false, 8, ⟨4, 4, 4, 1, 7, 1⟩, [(false, 1, 4), (true, 2, 4), (false, 3, 4)]⟩,
    ⟨5, false, 19, ⟨9, 10, 4, 1, 7, 1⟩, [(false, 1, 9), (false, 3, 10)]⟩,
    ⟨6, true, 25, ⟨9, 10, 4, 1, 7, 1⟩, [(false, 1, 15), (true, 2, 10), (false, 3, 10)]⟩]
  -- The helper returns input + 2, but the arbitrary entry subtracts one.
  -- Its fresh private cell must not survive either child success or rollback.
  let arbitrary ← checked [privateStep] (.binary .wordSub entry (word 1))
  sequenceCheck arbitrary [
    ⟨4, false, 9, ⟨4, 5, 5, 1, 7, 1⟩, [(false, 1, 4), (true, 2, 5), (false, 3, 5)]⟩,
    ⟨1, false, 13, ⟨5, 8, 5, 1, 7, 1⟩, [(false, 1, 5), (false, 3, 8)]⟩,
    ⟨0, false, 11, ⟨5, 6, 6, 2, 7, 1⟩, [(false, 1, 5), (true, 2, 6), (false, 3, 6)]⟩]

private def admissionChecks : IO Unit := do
  for plan in [← checked [.var 0], ← checked [privateStep] (.binary .wordSub entry (word 1))] do
    ensure (plan.parentProgram.check && plan.childProgram.check &&
      plan.parentProgram.toCore.checkHost && plan.childProgram.toCore.checkHost &&
      plan.parentProgram.resultType == NestedCall.resultType &&
      plan.childProgram.resultType == NestedCall.resultType &&
      plan.parentContract.entryProfile == .wordOutcomeV1 && plan.childContract.entryProfile == .wordOutcomeV1)
      "nested contracts lost full host checking or their typed outcome convention"
    ensure (plan.parentContract.code.program == plan.parentProgram.toCore &&
      plan.childContract.code.program == plan.childProgram.toCore)
      "nested admission replaced an original Core contract"
    ensure (NestedCall.combinedNodes plan.step ==
      Wire.programNodes plan.parentProgram + Wire.programNodes plan.childProgram &&
      NestedCall.combinedNodes plan.step == Wire.programNodes plan.step.program + NestedCall.programOverhead &&
      NestedCall.programOverhead == 179)
      "nested wrapper budget differs from the two complete original Core programs"
    match plan.childProgram.body with
    | .letE saved _ =>
        ensure (Wire.encodeExpr saved == Wire.encodeExpr plan.step.program.body)
          "child wrapper ignored its arbitrary aggregate entry"
    | _ => throw (IO.userError "child wrapper lost its closed entry binding")
    ensure ((← emitted plan) == (← emitted plan)) "nested source emission is nondeterministic"
  let unsupported ← checked [.binary .wordDiv (.var 0) (word 1)]
  match Solcore.Synthesis.Source.NestedCall.emit unsupported with
  | .error (.unsupportedBinary .wordDiv) => pure ()
  | _ => throw (IO.userError "unsupported child step was silently emitted")

private def formattingChecks : IO Unit := do
  let emitted ← emitted (← checked [.var 0])
  ensure (emitted.parentContractName == "SynthesizedCaller" &&
    emitted.childContractName == "SynthesizedCallee" &&
    emitted.parentMethodSignature == "run(uint256,uint256)" && emitted.selector == "0x7357f5d2" &&
    emitted.parentConstructorValue == "8" && emitted.childConstructorValue == "0" &&
    emitted.parentDeployPath == ["SynthesizedCallerDeploy"] &&
    emitted.parentRuntimePath == ["SynthesizedCallerDeploy", "SynthesizedCaller"] &&
    emitted.childDeployPath == ["SynthesizedCalleeDeploy"] &&
    emitted.childRuntimePath == ["SynthesizedCalleeDeploy", "SynthesizedCallee"])
    "nested source metadata changed"
  for fragment in ["log1 as log1_", "fallback() payable", "constructor() payable {}",
    "mstore(64, sc_ptr + 32);", "mstore(64, sc_ptr + 64);",
    "call(gas(), sc_target, sc_value, sc_ptr, 32, sc_ptr + 32, 32)",
    "if (!(returndatasize() == 32))", "invalid();",
    "if ((sc_input & 1) == 1)", "if ((sc_input & 2) == 2)", "if ((sc_input & 4) == 4)"] do
    ensure ((emitted.source.splitOn fragment).length == 2)
      s!"nested source lost or duplicated its protocol fragment: {fragment}"
  ensure (Solcore.Synthesis.Source.NestedCall.emitterVersion == "solcore-source-nested-call-v1" &&
    Solcore.Synthesis.Source.NestedCall.wrapperVersion == "solcore-word-nested-call-v1" &&
    NestedCall.version == "core-nested-word-call-v1") "nested provenance changed"

def testSourceNestedCallEmitter : IO Unit := do
  admissionChecks
  executionChecks
  formattingChecks

end Tests.SourceNestedCallEmitter
