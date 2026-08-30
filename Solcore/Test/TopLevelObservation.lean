import Solcore.Test.TopLevelObservationFixture

/-! Runtime regressions for read-only direct top-level input observations. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.Semantics
open TopLevelObservationFixture

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def codeMatches
    (state : WorldState) (target : Address) : Bool :=
  match state.code? target with
  | some selected => selected.program == program
  | none => false

private def assertObservation
    (runTarget runCaller : Address)
    (runInput : HostStorageDriver.InputData)
    (label : String) : IO Unit := do
  let invocation := invocationAt runTarget runCaller runInput
  let inputs := invocation.executionInputs
  let installed := installedAt runTarget
  let initialWorld := worldAt runTarget
  let expected := expectedResult runTarget runCaller runInput

  assertTrue (inputs.codeAddress == runTarget)
    s!"{label}: code address was not derived from the direct target"
  assertTrue (inputs.currentAddress == runTarget)
    s!"{label}: current address was not derived from the direct target"
  assertTrue
    ((TopLevelExecution.initialContext installed).context.storageAddress ==
      runTarget)
    s!"{label}: storage address was not derived from the direct target"
  assertTrue (inputs.callerAddress == runCaller)
    s!"{label}: caller address was not retained"
  assertTrue (inputs.inputData.sizeWord == runInput.sizeWord)
    s!"{label}: input size was not retained"
  assertTrue
    (inputs.inputData.byte? observedOffset == runInput.byte? observedOffset)
    s!"{label}: optional input byte was not retained"

  match TopLevelExecution.run contract invocation installed completionFuel with
  | .outOfFuel _ _ _ _ _ =>
      throw (IO.userError s!"{label}: read-only observation did not complete")
  | .completed result =>
      assertTrue (result.coreValue == .word expected)
        s!"{label}: Core did not return the exact observation checksum"
      assertTrue (result.coreStore == [])
        s!"{label}: the read-only fixture changed the Core-local Store"
      assertTrue
        (result.outcome == .returned (encodeWordBytesBE expected))
        s!"{label}: the checksum did not become canonical return bytes"
      assertTrue
        (result.workingDelta.slotChange? retainedSlot == none)
        s!"{label}: read-only execution reported a speculative storage change"
      assertTrue
        (result.committedDelta.slotChange? retainedSlot == none)
        s!"{label}: read-only return reported a committed storage change"
      assertTrue
        (storageValueAt? result.terminalContext.context.values.working.1
            runTarget retainedSlot == some retainedValue)
        s!"{label}: speculative execution changed retained target storage"
      assertTrue
        (storageValueAt? result.finalWorld runTarget retainedSlot ==
          some retainedValue)
        s!"{label}: return changed retained target storage"
      assertTrue
        (storageValueAt? result.finalWorld otherAddress otherSlot ==
          some otherValue)
        s!"{label}: return changed a distinct Account"
      assertTrue (codeMatches result.finalWorld runTarget)
        s!"{label}: return changed the installed checked code"
      assertTrue
        (storageValueAt? initialWorld runTarget retainedSlot ==
          storageValueAt? result.finalWorld runTarget retainedSlot)
        s!"{label}: final target observation differs from the initial world"

def testTopLevelObservation : IO Unit := do
  assertTrue program.checkHost
    "the host checker rejected the read-only observation program"

  let baseline := expectedResult targetAddress callerAddress inputData
  let callerVariant :=
    expectedResult targetAddress alternateCallerAddress inputData
  let byteVariant :=
    expectedResult targetAddress callerAddress differentByteInputData
  let sizeVariant :=
    expectedResult targetAddress callerAddress differentSizeInputData
  let targetVariant :=
    expectedResult alternateTargetAddress callerAddress inputData

  assertTrue
    (baseline != callerVariant && baseline != byteVariant &&
      baseline != sizeVariant && baseline != targetVariant &&
      callerVariant != byteVariant && callerVariant != sizeVariant &&
      callerVariant != targetVariant && byteVariant != sizeVariant &&
      byteVariant != targetVariant && sizeVariant != targetVariant)
    "fixture sentinels do not distinguish caller, byte, size, and target"
  assertTrue
    (expectedResult targetAddress callerAddress missingByteInputData ==
      missingByteResult)
    "missing optional input byte did not select its explicit result"

  assertObservation targetAddress callerAddress inputData "baseline"
  assertObservation targetAddress alternateCallerAddress inputData
    "alternate caller"
  assertObservation targetAddress callerAddress differentByteInputData
    "alternate input byte"
  assertObservation targetAddress callerAddress differentSizeInputData
    "alternate input size"
  assertObservation alternateTargetAddress callerAddress inputData
    "alternate direct target"
  assertObservation targetAddress callerAddress missingByteInputData
    "missing input byte"

end Tests
