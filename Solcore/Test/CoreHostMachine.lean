import Solcore.Core.HostMachineProperties
import Solcore.Core.HostRunner
import Solcore.Core.Wire
import Solcore.Core.Wire.V2
import Solcore.Semantics.CheckedHostCoreProgramProperties

/-! Focused admission and runtime regressions for the Core host boundary. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.Semantics

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def slot : Word := ⟨0x11, by decide⟩
private def response : Word := ⟨0xaa, by decide⟩
private def secondSlot : Word := ⟨0x22, by decide⟩

private def responseFor : (request : HostRequest) → request.Response
  | .storageRead _ => response
  | .storageWrite _ _ => ()
  | .storageAddress => response

private def storageReadProgram : Program := {
  resultType := .word
  body := .apply (.var HostFunction.storageRead.index) (.word slot)
}

private theorem storageReadProgram_host_checked :
    storageReadProgram.checkHost = true := by
  decide

private theorem storageReadProgram_closed_rejected :
    storageReadProgram.check = false := by
  decide

private def illTypedStorageReadProgram : Program := {
  resultType := .word
  body :=
    .apply (.var HostFunction.storageRead.index) (.bool true)
}

private theorem illTypedStorageReadProgram_host_rejected :
    illTypedStorageReadProgram.checkHost = false := by
  decide

private def checkedStorageReadProgram : CheckedHostCoreProgram :=
  ⟨storageReadProgram, storageReadProgram_host_checked⟩

private def storageWriteProgram : Program := {
  resultType := .unit
  body :=
    .apply (.var HostFunction.storageWrite.index)
      (.pair (.word slot) (.word response))
}

private theorem storageWriteProgram_host_checked :
    storageWriteProgram.checkHost = true := by
  decide

private theorem storageWriteProgram_closed_rejected :
    storageWriteProgram.check = false := by
  decide

private def illTypedStorageWriteProgram : Program := {
  resultType := .unit
  body :=
    .apply (.var HostFunction.storageWrite.index)
      (.pair (.word slot) (.bool true))
}

private theorem illTypedStorageWriteProgram_host_rejected :
    illTypedStorageWriteProgram.checkHost = false := by
  decide

private def checkedStorageWriteProgram : CheckedHostCoreProgram :=
  ⟨storageWriteProgram, storageWriteProgram_host_checked⟩

private theorem compileTimeAdmissionRegression :
    CheckedHostCoreProgram.ofProgram? storageReadProgram =
      some checkedStorageReadProgram := by
  exact CheckedHostCoreProgram.ofProgram?_of_checked
    storageReadProgram storageReadProgram_host_checked

private theorem compileTimeRejectedAdmissionRegression :
    CheckedHostCoreProgram.ofProgram? illTypedStorageReadProgram = none :=
  CheckedHostCoreProgram.ofProgram?_of_rejected
    illTypedStorageReadProgram illTypedStorageReadProgram_host_rejected

private theorem compileTimeHostContextIndexRegression :
    hostContext[HostFunction.storageRead.index]? =
      some (HostFunction.functionType .storageRead) :=
  hostContext_storageRead

private theorem compileTimeHostEnvironmentIndexRegression :
    hostEnvironment[HostFunction.storageRead.index]? =
      some (.hostFunction .storageRead) :=
  hostEnvironment_storageRead

private theorem compileTimeWriteContextIndexRegression :
    hostContext[HostFunction.storageWrite.index]? =
      some (HostFunction.functionType .storageWrite) :=
  hostContext_storageWrite

private theorem compileTimeWriteEnvironmentIndexRegression :
    hostEnvironment[HostFunction.storageWrite.index]? =
      some (.hostFunction .storageWrite) :=
  hostEnvironment_storageWrite

private def beginState : State :=
  ⟨.ret (.hostFunction .storageRead),
    [.applyArgument (.word slot) hostEnvironment], []⟩

private def argumentState : State :=
  ⟨.eval (.word slot) hostEnvironment, [.hostApply .storageRead], []⟩

private def requestState : State :=
  ⟨.ret (.word slot), [.hostApply .storageRead], []⟩

private def requestSuspension : HostSuspension :=
  ⟨.storageRead slot, [], []⟩

private def writeRequestState : State :=
  ⟨.ret (.pair (.word slot) (.word response)),
    [.hostApply .storageWrite], []⟩

private def writeSuspension : HostSuspension :=
  ⟨.storageWrite slot response, [], []⟩

private theorem compileTimeBeginCorrespondenceRegression :
    HostTransition beginState argumentState := by
  apply hostAdvance_next_iff.mp
  exact hostAdvance_begin_storageRead (.word slot) hostEnvironment [] []

private theorem compileTimeRequestCorrespondenceRegression :
    HostRequestEmission requestState requestSuspension := by
  apply hostAdvance_suspended_iff.mp
  exact hostAdvance_suspend_storageRead slot [] []

private theorem compileTimeWriteCorrespondenceRegression :
    HostRequestEmission writeRequestState writeSuspension := by
  apply hostAdvance_suspended_iff.mp
  exact hostAdvance_suspend_storageWrite slot response [] []

private theorem compileTimeTransitionDeterminismRegression
    {next : State}
    (step : HostTransition beginState next) :
    next = argumentState :=
  hostTransition_deterministic step compileTimeBeginCorrespondenceRegression

private theorem compileTimeEmissionDeterminismRegression
    {suspension : HostSuspension}
    (emission : HostRequestEmission requestState suspension) :
    suspension = requestSuspension :=
  hostRequestEmission_deterministic
    emission compileTimeRequestCorrespondenceRegression

private def retainedContinuation : List Frame :=
  [.letBody .unit []]

private def retainedStore : Store :=
  [.bool true]

private def retainedSuspension : HostSuspension :=
  ⟨.storageRead slot, retainedContinuation, retainedStore⟩

private theorem compileTimeResumeRegression :
    retainedSuspension.resume response =
      ⟨.ret (.word response), retainedContinuation, retainedStore⟩ :=
  HostSuspension.resume_storageRead
    slot response retainedContinuation retainedStore

private theorem compileTimeWriteResumeRegression :
    writeSuspension.resume () = State.final .unit [] :=
  HostSuspension.resume_storageWrite slot response () [] []

private theorem compileTimeSuspensionTypingRegression :
    HostSuspensionHasType requestSuspension .word [] := by
  apply CheckedHostCoreProgram.runStateful_suspended_hasType
    (fuel := 5) (remainingFuel := 0) checkedStorageReadProgram
  decide

private theorem compileTimeTypedResumeRegression :
    HostStateHasType (requestSuspension.resume response) .word [] :=
  compileTimeSuspensionTypingRegression.resume response

private theorem compileTimeCheckedRunNeverFaults
    (fuel : Nat) (error : MachineFault) (faultState : State) :
    checkedStorageReadProgram.runStateful fuel ≠ .fault error faultState :=
  CheckedHostCoreProgram.runStateful_ne_fault
    checkedStorageReadProgram fuel error faultState

private theorem compileTimeCheckedWriteNeverFaults
    (fuel : Nat) (error : MachineFault) (faultState : State) :
    checkedStorageWriteProgram.runStateful fuel ≠ .fault error faultState :=
  CheckedHostCoreProgram.runStateful_ne_fault
    checkedStorageWriteProgram fuel error faultState

private theorem compileTimeWireV1RejectionRegression :
    Solcore.Core.Wire.V1.Value.ofCore? (.hostFunction .storageRead) = none :=
  rfl

private theorem compileTimeWireV2RejectionRegression :
    Solcore.Core.Wire.V2.Value.ofCore? (.hostFunction .storageRead) = none :=
  rfl

private theorem compileTimeWriteWireV1RejectionRegression :
    Solcore.Core.Wire.V1.Value.ofCore? (.hostFunction .storageWrite) = none :=
  rfl

private theorem compileTimeWriteWireV2RejectionRegression :
    Solcore.Core.Wire.V2.Value.ofCore? (.hostFunction .storageWrite) = none :=
  rfl

private def cellStorageReadProgram : Program := {
  resultType := .word
  body :=
    .letE
      (.newCell .bool (.bool true))
      (.apply (.var (HostFunction.storageRead.index + 1)) (.word slot))
}

private theorem cellStorageReadProgram_host_checked :
    cellStorageReadProgram.checkHost = true := by
  decide

private def twoStorageReadProgram : Program := {
  resultType := .word
  body :=
    .letE
      (.apply (.var HostFunction.storageRead.index) (.word slot))
      (.apply (.var (HostFunction.storageRead.index + 1)) (.word secondSlot))
}

private theorem twoStorageReadProgram_host_checked :
    twoStorageReadProgram.checkHost = true := by
  decide

def testCoreHostMachine : IO Unit := do
  assertTrue storageReadProgram.checkHost
    "the host checker rejected a storage-read program"
  assertTrue (!storageReadProgram.check)
    "the closed checker accepted a program with an unbound host capability"
  assertTrue (!illTypedStorageReadProgram.checkHost)
    "the host checker accepted a storage read with a Boolean argument"
  assertTrue storageWriteProgram.checkHost
    "the host checker rejected a storage-write program"
  assertTrue (!storageWriteProgram.check)
    "the closed checker accepted a storage-write capability"
  assertTrue (!illTypedStorageWriteProgram.checkHost)
    "the host checker accepted an invalid storage-write pair"
  assertTrue
    (CheckedHostCoreProgram.ofProgram? illTypedStorageReadProgram).isNone
    "checked host admission retained a program rejected by the host checker"
  match CheckedHostCoreProgram.ofProgram? storageReadProgram with
  | none =>
      throw (IO.userError "checked host admission rejected accepted code")
  | some code =>
      assertTrue (code.program == storageReadProgram)
        "checked host admission changed the admitted program"

  assertTrue
    (hostContext[HostFunction.storageRead.index]? ==
      some (HostFunction.functionType .storageRead))
    "the storage-read type moved in the host context"
  assertTrue
    (hostEnvironment[HostFunction.storageRead.index]? ==
      some (.hostFunction .storageRead))
    "the storage-read value moved in the host environment"
  assertTrue
    (hostContext[HostFunction.storageWrite.index]? ==
      some (HostFunction.functionType .storageWrite))
    "the storage-write type is absent from the host context"
  assertTrue
    (hostEnvironment[HostFunction.storageWrite.index]? ==
      some (.hostFunction .storageWrite))
    "the storage-write value is absent from the host environment"

  assertTrue (hostAdvance beginState == .next argumentState)
    "host application did not begin by evaluating its argument"
  assertTrue (hostAdvance requestState == .suspended requestSuspension)
    "a Word storage slot did not emit the expected request"
  let invalidState : State :=
    ⟨.ret (.bool true), [.hostApply .storageRead], []⟩
  assertTrue
    (hostAdvance invalidState ==
      .fault (.invalidHostArgument .storageRead (.bool true)))
    "a non-Word storage slot did not retain the raw machine fault"
  assertTrue (hostAdvance writeRequestState == .suspended writeSuspension)
    "a Word pair did not emit the expected storage write"
  let invalidWriteState : State :=
    ⟨.ret (.pair (.word slot) (.bool true)), [.hostApply .storageWrite], []⟩
  assertTrue
    (hostAdvance invalidWriteState ==
      .fault (.invalidHostArgument .storageWrite
        (.pair (.word slot) (.bool true))))
    "a malformed storage-write pair did not fault"

  assertTrue
    (retainedSuspension.resume response ==
      ⟨.ret (.word response), retainedContinuation, retainedStore⟩)
    "resume changed the continuation or Core-local store"
  assertTrue (writeSuspension.resume () == State.final .unit [])
    "storage-write resume did not inject Unit"

  assertTrue
    (checkedStorageReadProgram.runStateful 4 == .outOfFuel requestState)
    "four units of fuel must stop immediately before request emission"
  assertTrue
    (checkedStorageReadProgram.runStateful 5 ==
      .suspended requestSuspension 0)
    "five units of fuel must emit the request with no remaining budget"
  assertTrue
    (hostRun 0 (requestSuspension.resume response) ==
      .done (.word response) [])
    "a response did not resume the suspended program to completion"

  match cellStorageReadProgram.runHostStateful 32 with
  | .suspended suspension remainingFuel =>
      assertTrue (suspension.request == .storageRead slot)
        "the cell program emitted the wrong storage request"
      assertTrue (suspension.continuation == [])
        "the cell program retained an unexpected continuation"
      assertTrue (suspension.store == [.bool true])
        "request suspension lost the Core-local cell store"
      assertTrue (remainingFuel == 22)
        "the cell program changed its exact request boundary"
  | result =>
      throw (IO.userError
        s!"the cell program did not suspend: {reprStr result}")

  match twoStorageReadProgram.runHostStateful 64 with
  | .suspended first remainingFuel =>
      assertTrue (first.request == .storageRead slot)
        "the repeated-read program emitted the wrong first request"
      match hostRun remainingFuel (first.resume (responseFor first.request)) with
      | .suspended second secondRemainingFuel =>
          assertTrue (second.request == .storageRead secondSlot)
            "the repeated-read program emitted the wrong second request"
          assertTrue (decide (secondRemainingFuel < remainingFuel))
            "resuming a request failed to preserve decreasing fuel"
          assertTrue
            (hostRun secondRemainingFuel
                (second.resume (responseFor second.request)) ==
              .done (.word response) [])
            "the second response did not complete the repeated-read program"
      | result =>
          throw (IO.userError
            s!"the repeated-read program did not suspend twice: {reprStr result}")
  | result =>
      throw (IO.userError
        s!"the repeated-read program did not emit its first request: {reprStr result}")

  assertTrue
    (Solcore.Core.Wire.V1.Value.ofCore? (.hostFunction .storageRead)).isNone
    "Core wire v1 encoded an internal host value"
  assertTrue
    (Solcore.Core.Wire.V2.Value.ofCore? (.hostFunction .storageRead)).isNone
    "Core wire v2 encoded an internal host value"
  assertTrue
    (Solcore.Core.Wire.V1.Value.ofCore? (.hostFunction .storageWrite)).isNone
    "Core wire v1 encoded the storage-write host value"
  assertTrue
    (Solcore.Core.Wire.V2.Value.ofCore? (.hostFunction .storageWrite)).isNone
    "Core wire v2 encoded the storage-write host value"

end Tests
