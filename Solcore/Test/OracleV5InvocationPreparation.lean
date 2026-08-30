import Solcore.Oracle.V5.InvocationPreparation

/-! Executable regressions for the safe Oracle v5 invocation boundary. -/

set_option autoImplicit false

namespace Tests.OracleV5InvocationPreparation

open Solcore.Core
open Solcore.Oracle.V5
open Solcore.Semantics

private def target : Address := ⟨1, by decide⟩
private def caller : Address := ⟨2, by decide⟩
private def value : Word := ⟨3, by decide⟩

private def exactLimits : Limits :=
  { Limits.default with calldataBytes := 3 }

private theorem exactLimits_valid : exactLimits.Valid := by
  show 3 < Solcore.Core.wordModulus
  decide

private def input : InvocationInput := {
  target
  caller
  callValue := value
  calldata := [0x10, 0x20, 0x30].toByteArray
  probes := [.accountPresence target, .balance target]
}

private theorem input_within : input.calldata.size ≤ exactLimits.calldataBytes := by
  native_decide

private def exactBoundaryAccepted : Bool :=
  match InvocationPreparation.prepare exactLimits exactLimits_valid input
      input_within with
  | .error _ => false
  | .ok prepared =>
      prepared.invocation.target == target &&
        prepared.invocation.caller == caller &&
        prepared.invocation.callValue == value &&
        prepared.invocation.inputData.bytes == input.calldata &&
        prepared.invocation.inputData.sizeWord == ⟨3, by decide⟩ &&
        prepared.probes.values == input.probes

private def duplicateInput : InvocationInput :=
  { input with probes := [.balance target, .balance target] }

private theorem duplicateInput_within :
    duplicateInput.calldata.size ≤ exactLimits.calldataBytes := by
  native_decide

private def duplicateRejected : Bool :=
  match InvocationPreparation.prepare exactLimits exactLimits_valid
      duplicateInput duplicateInput_within with
  | .ok _ => false
  | .error duplicate =>
      duplicate.firstIndex == 0 && duplicate.secondIndex == 1 &&
        duplicate.probe == .balance target

private def allChecks : Bool := exactBoundaryAccepted && duplicateRejected

private theorem allChecks_exact : allChecks = true := by
  native_decide

def testOracleV5InvocationPreparation : IO Unit := do
  unless allChecks do
    throw (IO.userError "Oracle v5 invocation preparation changed")

end Tests.OracleV5InvocationPreparation
