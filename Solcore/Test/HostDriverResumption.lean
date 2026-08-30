import Solcore.Semantics.HostDriverResumptionProperties

/-! Executable regressions for exact generic-driver fuel resumption. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.Semantics

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private instance : DecidableEq (HostDriverResult Nat) := by
  intro left right
  cases left with
  | mk leftContext leftOutcome =>
      cases right with
      | mk rightContext rightOutcome =>
          simp only [HostDriverResult.mk.injEq]
          exact inferInstance

private def sameResult
    (left right : HostDriverResult Nat) : Bool :=
  decide (left = right)

private def slot : Word := ⟨3, by decide⟩
private def returned : Word := ⟨7, by decide⟩
private def retained : Word := ⟨11, by decide⟩
private def retainedStore : Store := [.word retained]

/-- Every handled request increments the context, making calls observable. -/
private def countingHandler : HostHandler Nat where
  handle count request :=
    match request with
    | .storageRead _ => (count + 1, returned)
    | .storageWrite _ _ => (count + 1, ())
    | .storageAddress => (count + 1, returned)
    | .codeAddress => (count + 1, returned)
    | .callValue => (count + 1, returned)
    | .callerAddress => (count + 1, returned)
    | .inputDataByte? _ => (count + 1, some returned)
    | .inputDataSize => (count + 1, returned)
    | .inputDataWordBE? _ => (count + 1, some returned)
    | .currentAddress => (count + 1, returned)
    | .callContractWord _ _ => (count + 1, .failed returned)

/-- A request followed by exactly two ordinary Core transitions. -/
private def requestReady : State :=
  ⟨.ret (.word slot),
    [.hostApply .storageRead, .letBody .unit []], retainedStore⟩

private def postHandler : State :=
  ⟨.ret (.word returned), [.letBody .unit []], retainedStore⟩

private def afterLet : State :=
  ⟨.eval .unit [.word returned], [], retainedStore⟩

private def doneResult : HostDriverResult Nat :=
  ⟨1, .done .unit retainedStore⟩

private def zeroRun : HostDriverResult Nat :=
  HostDriver.run countingHandler 0 0 requestReady

private def afterRequest : HostDriverResult Nat :=
  zeroRun.resumeWithFuel countingHandler 1

private theorem measured_zero_run :
    zeroRun = ⟨0, .outOfFuel requestReady⟩ := by
  native_decide

private theorem measured_request_cost :
    afterRequest = ⟨1, .outOfFuel postHandler⟩ := by
  native_decide

private theorem measured_post_handler_step :
    afterRequest.resumeWithFuel countingHandler 1 =
      ⟨1, .outOfFuel afterLet⟩ := by
  native_decide

private theorem measured_split_completion :
    afterRequest.resumeWithFuel countingHandler 2 = doneResult := by
  native_decide

private theorem measured_one_shot_completion :
    HostDriver.run countingHandler 0 3 requestReady = doneResult := by
  native_decide

private theorem measured_split_one_shot_exact :
    zeroRun.resumeWithFuel countingHandler 3 =
      HostDriver.run countingHandler 0 3 requestReady := by
  native_decide

private theorem measured_actual_run_zero_identity :
    zeroRun.resumeWithFuel countingHandler 0 = zeroRun := by
  native_decide

private theorem measured_sequential_additions :
    (zeroRun.resumeWithFuel countingHandler 1).resumeWithFuel
        countingHandler 2 =
      zeroRun.resumeWithFuel countingHandler (1 + 2) := by
  native_decide

/-- One ordinary step exposes an intentionally ill-typed host argument. -/
private def uncheckedStart : State :=
  ⟨.eval .unit [], [.hostApply .storageRead], retainedStore⟩

private def uncheckedFaultState : State :=
  ⟨.ret .unit, [.hostApply .storageRead], retainedStore⟩

private def uncheckedFault : MachineFault :=
  .invalidHostArgument .storageRead .unit

private def uncheckedZeroRun : HostDriverResult Nat :=
  HostDriver.run countingHandler 13 0 uncheckedStart

private def uncheckedFaultResult : HostDriverResult Nat :=
  ⟨13, .fault uncheckedFault uncheckedFaultState⟩

private theorem measured_unchecked_exhaustion :
    uncheckedZeroRun = ⟨13, .outOfFuel uncheckedStart⟩ := by
  native_decide

private theorem measured_unchecked_split_fault :
    uncheckedZeroRun.resumeWithFuel countingHandler 1 =
      uncheckedFaultResult := by
  native_decide

private theorem measured_unchecked_one_shot_fault :
    HostDriver.run countingHandler 13 1 uncheckedStart =
      uncheckedFaultResult := by
  native_decide

private theorem measured_unchecked_split_one_shot_exact :
    uncheckedZeroRun.resumeWithFuel countingHandler 1 =
      HostDriver.run countingHandler 13 1 uncheckedStart := by
  native_decide

private def completedInput : HostDriverResult Nat :=
  ⟨29, .done (.word returned) retainedStore⟩

private def faultedInput : HostDriverResult Nat :=
  ⟨31, .fault uncheckedFault uncheckedFaultState⟩

private theorem measured_completed_identity :
    completedInput.resumeWithFuel countingHandler 100 = completedInput := by
  native_decide

private theorem measured_faulted_identity :
    faultedInput.resumeWithFuel countingHandler 100 = faultedInput := by
  native_decide

/-- Exercise every result class and compare split runs with measured one-shots. -/
def testHostDriverResumption : IO Unit := do
  assertTrue (sameResult zeroRun ⟨0, .outOfFuel requestReady⟩)
    "zero fuel did not retain the request-ready state"
  assertTrue (sameResult afterRequest ⟨1, .outOfFuel postHandler⟩)
    "one fuel unit did not handle exactly one request before exhaustion"
  assertTrue
    (sameResult (afterRequest.resumeWithFuel countingHandler 1)
      ⟨1, .outOfFuel afterLet⟩)
    "post-handler resumption repeated the request or skipped a Core step"
  assertTrue
    (sameResult
      (afterRequest.resumeWithFuel countingHandler 2) doneResult)
    "post-handler exhaustion did not resume to the exact done result"
  assertTrue
    (sameResult (zeroRun.resumeWithFuel countingHandler 3)
      (HostDriver.run countingHandler 0 3 requestReady))
    "split done execution changed its context, value, or Store"
  assertTrue
    (sameResult (zeroRun.resumeWithFuel countingHandler 0) zeroRun)
    "zero additional fuel changed an actual run result"
  assertTrue
    (sameResult
      ((zeroRun.resumeWithFuel countingHandler 1).resumeWithFuel
        countingHandler 2)
      (zeroRun.resumeWithFuel countingHandler (1 + 2)))
    "two sequential additions differed from their summed addition"
  assertTrue
    (sameResult uncheckedZeroRun ⟨13, .outOfFuel uncheckedStart⟩)
    "zero fuel did not retain the unchecked pre-fault state"
  assertTrue
    (sameResult
      (uncheckedZeroRun.resumeWithFuel countingHandler 1)
      uncheckedFaultResult)
    "resumed unchecked execution did not reach the exact raw fault"
  assertTrue
    (sameResult
      (uncheckedZeroRun.resumeWithFuel countingHandler 1)
      (HostDriver.run countingHandler 13 1 uncheckedStart))
    "split fault execution changed its context, error, or fault state"
  assertTrue
    (sameResult
      (completedInput.resumeWithFuel countingHandler 100) completedInput)
    "resuming a completed input changed its exact bytes"
  assertTrue
    (sameResult
      (faultedInput.resumeWithFuel countingHandler 100) faultedInput)
    "resuming a faulted input changed its exact bytes"

end Tests
