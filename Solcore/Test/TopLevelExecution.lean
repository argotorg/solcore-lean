import Solcore.Semantics.TopLevelExecutionResumption
import Solcore.Test.TopLevelExecutionFixture

/-! Executable end-to-end regressions for ADR-0145 top-level finalization. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.Semantics
open TopLevelExecutionFixture

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def codeMatches
    (state : WorldState) (address : Address) : Bool :=
  match state.code? address with
  | some selected => selected.program == program
  | none => false

private def testWriteBoundaries : IO Unit := do
  match runWith returnSelector writeRequestFuel with
  | .outOfFuel context _ _ _ delta =>
      assertTrue
        (storageValueAt? context.context.values.working.1
          targetAddress targetSlot == some oldValue)
        "fuel 9 must stop before applying the target storage write"
      assertTrue (delta.slotChange? targetSlot == none)
        "the pre-write speculative delta must be empty"
  | .completed _ =>
      throw (IO.userError "fuel 9 must not complete top-level execution")

  match runWith returnSelector postWriteFuel with
  | .outOfFuel context _ _ _ delta =>
      assertTrue
        (storageValueAt? context.context.values.working.1
          targetAddress targetSlot == some writtenValue)
        "fuel 10 must retain the applied speculative storage write"
      assertTrue
        (delta.slotChange? targetSlot == some (oldValue, writtenValue))
        "the post-write speculative delta must expose the exact old/new pair"
  | .completed _ =>
      throw (IO.userError "fuel 10 must remain resumable")

private def testReturnedCommit : IO Unit := do
  match runWith returnSelector (returnCompletionFuel - 1) with
  | .outOfFuel _ _ _ _ _ => pure ()
  | .completed _ =>
      throw (IO.userError "return must not complete one fuel unit early")

  match runWith returnSelector returnCompletionFuel with
  | .outOfFuel _ _ _ _ _ =>
      throw (IO.userError "return must complete at its measured boundary")
  | .completed result =>
      assertTrue
        (result.outcome == .returned (encodeWordBytesBE returnPayload))
        "the executed left injection must decode as canonical return data"
      assertTrue
        (result.coreValue ==
          .inLeft (.sum .word .word) (.word returnPayload))
        "return must retain the exact dynamic Core value"
      assertTrue (result.coreStore == [])
        "the fixture must retain its exact empty Core-local Store"
      assertTrue (speculativeTargetValue result == some writtenValue)
        "return must retain the speculative storage write"
      assertTrue (finalTargetValue result == some writtenValue)
        "return must commit the terminal working WorldState"
      assertTrue
        (result.committedDelta.slotChange? targetSlot ==
          some (oldValue, writtenValue))
        "return must report the committed target-slot change"
      assertTrue
        (storageValueAt? result.finalWorld targetAddress retainedSlot ==
          some retainedValue)
        "return must preserve an untouched target slot"
      assertTrue
        (storageValueAt? result.finalWorld otherAddress otherSlot ==
          some otherValue)
        "return must preserve a distinct Account"
      assertTrue (codeMatches result.finalWorld targetAddress)
        "return must preserve the installed target code"

private def testCallValueBoundaries : IO Unit := do
  match runWith returnSelector callValueRequestFuel with
  | .outOfFuel context state _ _ delta =>
      assertTrue
        (storageValueAt? context.context.values.working.1
          targetAddress targetSlot == some writtenValue)
        "fuel 16 must retain the earlier storage write"
      assertTrue
        (match hostAdvance state with
          | .suspended suspension => suspension.request == .callValue
          | _ => false)
        "fuel 16 must stop at the call-value request"
      assertTrue
        (delta.slotChange? targetSlot == some (oldValue, writtenValue))
        "call-value suspension must retain the speculative delta"
  | .completed _ =>
      throw (IO.userError "fuel 16 must remain resumable")

  match runWith returnSelector postCallValueFuel with
  | .outOfFuel _ state _ _ _ =>
      assertTrue (state.control == .ret (.word returnSelector))
        "fuel 17 must have injected the exact call value"
  | .completed _ =>
      throw (IO.userError "fuel 17 must remain resumable")

private def testRevertedRollback : IO Unit := do
  match runWith revertSelector (revertTrapCompletionFuel - 1) with
  | .outOfFuel _ _ _ _ _ => pure ()
  | .completed _ =>
      throw (IO.userError "revert must not complete one fuel unit early")

  match runWith revertSelector revertTrapCompletionFuel with
  | .outOfFuel _ _ _ _ _ =>
      throw (IO.userError "revert must complete at its measured boundary")
  | .completed result =>
      assertTrue
        (result.outcome == .reverted (encodeWordBytesBE revertPayload))
        "the executed nested-left injection must decode as revert data"
      assertTrue (speculativeTargetValue result == some writtenValue)
        "revert must retain evidence that the speculative write occurred"
      assertTrue (finalTargetValue result == some oldValue)
        "revert must select the explicit initial WorldState"
      assertTrue (result.committedDelta.slotChange? targetSlot == none)
        "revert must expose no committed target-slot change"
      assertTrue
        (result.workingDelta.slotChange? targetSlot ==
          some (oldValue, writtenValue))
        "revert must keep its pre-rollback working delta observable"
      assertTrue (codeMatches result.finalWorld targetAddress)
        "revert rollback must retain the installed target code"

private def testTrappedRollback : IO Unit := do
  match runWith trapSelector (revertTrapCompletionFuel - 1) with
  | .outOfFuel _ _ _ _ _ => pure ()
  | .completed _ =>
      throw (IO.userError "trap must not complete one fuel unit early")

  match runWith trapSelector revertTrapCompletionFuel with
  | .outOfFuel _ _ _ _ _ =>
      throw (IO.userError "trap must complete at its measured boundary")
  | .completed result =>
      assertTrue (result.outcome == .trapped trapCode)
        "the executed nested-right injection must retain its exact trap code"
      assertTrue (speculativeTargetValue result == some writtenValue)
        "trap must retain evidence that the speculative write occurred"
      assertTrue (finalTargetValue result == some oldValue)
        "trap must select the explicit initial WorldState"
      assertTrue (result.committedDelta.slotChange? targetSlot == none)
        "trap must expose no committed target-slot change"
      assertTrue
        (result.workingDelta.slotChange? targetSlot ==
          some (oldValue, writtenValue))
        "trap must keep its pre-rollback working delta observable"
      assertTrue
        (storageValueAt? result.finalWorld otherAddress otherSlot ==
          some otherValue)
        "trap rollback must preserve a distinct Account"

private def testDirectInputs : IO Unit := do
  let invocation := invocationWith revertSelector
  let inputs := invocation.executionInputs
  assertTrue (inputs.codeAddress == targetAddress)
    "direct-call code address must equal the target"
  assertTrue (inputs.currentAddress == targetAddress)
    "direct-call current address must equal the target"
  assertTrue (inputs.callerAddress == callerAddress)
    "direct-call caller must remain explicit"
  assertTrue (inputs.callValue == revertSelector)
    "direct-call value must remain explicit"
  assertTrue (inputs.inputData.bytes == inputData.bytes)
    "direct-call input bytes must remain explicit"

private def expectReturned
    (execution :
      TopLevelRunResult initialWorld contract returnedInvocation)
    (message : String) : IO Unit := do
  match execution with
  | .outOfFuel _ _ _ _ _ => throw (IO.userError message)
  | .completed result =>
      assertTrue
        (result.outcome == .returned (encodeWordBytesBE returnPayload) &&
          finalTargetValue result == some writtenValue)
        message

private def testResumption : IO Unit := do
  expectReturned
    (TopLevelExecution.resumeWithFuel
      (runWith returnSelector writeRequestFuel)
      (returnCompletionFuel - writeRequestFuel))
    "fuel split 9+19 must reach the exact returned commit"
  expectReturned
    (TopLevelExecution.resumeWithFuel
      (runWith returnSelector postWriteFuel)
      (returnCompletionFuel - postWriteFuel))
    "fuel split 10+18 must reach the exact returned commit"

  match TopLevelExecution.resumeWithFuel
      (runWith revertSelector writeRequestFuel)
      (revertTrapCompletionFuel - writeRequestFuel) with
  | .outOfFuel _ _ _ _ _ =>
      throw (IO.userError "fuel split 9+28 must complete revert")
  | .completed result =>
      assertTrue
        (result.outcome == .reverted (encodeWordBytesBE revertPayload) &&
          finalTargetValue result == some oldValue &&
          result.committedDelta.slotChange? targetSlot == none)
        "resumed revert must roll back the speculative write"

  match TopLevelExecution.resumeWithFuel
      (runWith trapSelector postWriteFuel)
      (revertTrapCompletionFuel - postWriteFuel) with
  | .outOfFuel _ _ _ _ _ =>
      throw (IO.userError "fuel split 10+27 must complete trap")
  | .completed result =>
      assertTrue
        (result.outcome == .trapped trapCode &&
          finalTargetValue result == some oldValue &&
          result.committedDelta.slotChange? targetSlot == none)
        "resumed trap must roll back the speculative write"

  expectReturned
    (TopLevelExecution.resumeWithFuel
      (runWith returnSelector returnCompletionFuel) 64)
    "a completed top-level return must remain terminal"

def testTopLevelExecution : IO Unit := do
  testWriteBoundaries
  testCallValueBoundaries
  testReturnedCommit
  testRevertedRollback
  testTrappedRollback
  testDirectInputs
  testResumption

end Tests
