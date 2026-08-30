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
  | .codeAddress => response
  | .callValue => response
  | .callerAddress => response
  | .inputDataByte? _ => some response
  | .inputDataSize => response
  | .inputDataWordBE? _ => some response
  | .currentAddress => response
  | .callContractWord _ _ => .returned response
  | .callContractWordWithValue _ _ _ => .returned response

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

private def storageAddressProgram : Program := {
  resultType := .word
  body := .apply (.var HostFunction.storageAddress.index) .unit
}

private theorem storageAddressProgram_host_checked :
    storageAddressProgram.checkHost = true := by
  decide

private theorem storageAddressProgram_closed_rejected :
    storageAddressProgram.check = false := by
  decide

private def illTypedStorageAddressProgram : Program := {
  resultType := .word
  body := .apply (.var HostFunction.storageAddress.index) (.bool true)
}

private theorem illTypedStorageAddressProgram_host_rejected :
    illTypedStorageAddressProgram.checkHost = false := by
  decide

private def codeAddressProgram : Program := {
  resultType := .word
  body := .apply (.var HostFunction.codeAddress.index) .unit
}

private theorem codeAddressProgram_host_checked :
    codeAddressProgram.checkHost = true := by
  decide

private theorem codeAddressProgram_closed_rejected :
    codeAddressProgram.check = false := by
  decide

private def illTypedCodeAddressProgram : Program := {
  resultType := .word
  body := .apply (.var HostFunction.codeAddress.index) (.bool true)
}

private theorem illTypedCodeAddressProgram_host_rejected :
    illTypedCodeAddressProgram.checkHost = false := by
  decide

private def callValueProgram : Program := {
  resultType := .word
  body := .apply (.var HostFunction.callValue.index) .unit
}

private theorem callValueProgram_host_checked :
    callValueProgram.checkHost = true := by
  decide

private theorem callValueProgram_closed_rejected :
    callValueProgram.check = false := by
  decide

private def illTypedCallValueProgram : Program := {
  resultType := .word
  body := .apply (.var HostFunction.callValue.index) (.bool true)
}

private theorem illTypedCallValueProgram_host_rejected :
    illTypedCallValueProgram.checkHost = false := by
  decide

private def callerAddressProgram : Program := {
  resultType := .word
  body := .apply (.var HostFunction.callerAddress.index) .unit
}

private theorem callerAddressProgram_host_checked :
    callerAddressProgram.checkHost = true := by
  decide

private theorem callerAddressProgram_closed_rejected :
    callerAddressProgram.check = false := by
  decide

private def illTypedCallerAddressProgram : Program := {
  resultType := .word
  body := .apply (.var HostFunction.callerAddress.index) (.bool true)
}

private theorem illTypedCallerAddressProgram_host_rejected :
    illTypedCallerAddressProgram.checkHost = false := by
  decide

private def currentAddressProgram : Program := {
  resultType := .word
  body := .apply (.var HostFunction.currentAddress.index) .unit
}

private theorem currentAddressProgram_host_checked :
    currentAddressProgram.checkHost = true := by
  decide

private theorem currentAddressProgram_closed_rejected :
    currentAddressProgram.check = false := by
  decide

private def illTypedCurrentAddressProgram : Program := {
  resultType := .word
  body := .apply (.var HostFunction.currentAddress.index) (.bool true)
}

private theorem illTypedCurrentAddressProgram_host_rejected :
    illTypedCurrentAddressProgram.checkHost = false := by
  decide

private def inputOffset : Word := ⟨1, by decide⟩

private def inputDataByteProgram : Program := {
  resultType := .sum .unit .word
  body :=
    .apply (.var HostFunction.inputDataByte?.index) (.word inputOffset)
}

private theorem inputDataByteProgram_host_checked :
    inputDataByteProgram.checkHost = true := by
  decide

private theorem inputDataByteProgram_closed_rejected :
    inputDataByteProgram.check = false := by
  decide

private def illTypedInputDataByteProgram : Program := {
  resultType := .sum .unit .word
  body :=
    .apply (.var HostFunction.inputDataByte?.index) (.bool true)
}

private theorem illTypedInputDataByteProgram_host_rejected :
    illTypedInputDataByteProgram.checkHost = false := by
  decide

private def inputDataSizeProgram : Program := {
  resultType := .word
  body := .apply (.var HostFunction.inputDataSize.index) .unit
}

private theorem inputDataSizeProgram_host_checked :
    inputDataSizeProgram.checkHost = true := by
  decide

private theorem inputDataSizeProgram_closed_rejected :
    inputDataSizeProgram.check = false := by
  decide

private def illTypedInputDataSizeProgram : Program := {
  resultType := .word
  body := .apply (.var HostFunction.inputDataSize.index) (.bool true)
}

private theorem illTypedInputDataSizeProgram_host_rejected :
    illTypedInputDataSizeProgram.checkHost = false := by
  decide

private def inputDataWordBEProgram : Program := {
  resultType := .sum .unit .word
  body :=
    .apply (.var HostFunction.inputDataWordBE?.index) (.word inputOffset)
}

private theorem inputDataWordBEProgram_host_checked :
    inputDataWordBEProgram.checkHost = true := by
  decide

private theorem inputDataWordBEProgram_closed_rejected :
    inputDataWordBEProgram.check = false := by
  decide

private def illTypedInputDataWordBEProgram : Program := {
  resultType := .sum .unit .word
  body :=
    .apply (.var HostFunction.inputDataWordBE?.index) (.bool true)
}

private theorem illTypedInputDataWordBEProgram_host_rejected :
    illTypedInputDataWordBEProgram.checkHost = false := by
  decide

private def unboundHostIndexProgram : Program := {
  resultType := .sum .unit .word
  body :=
    .apply (.var HostFunction.all.length) (.word inputOffset)
}

private theorem unboundHostIndexProgram_host_rejected :
    unboundHostIndexProgram.checkHost = false := by
  decide

private def checkedStorageAddressProgram : CheckedHostCoreProgram :=
  ⟨storageAddressProgram, storageAddressProgram_host_checked⟩

private def checkedCodeAddressProgram : CheckedHostCoreProgram :=
  ⟨codeAddressProgram, codeAddressProgram_host_checked⟩

private def checkedCallValueProgram : CheckedHostCoreProgram :=
  ⟨callValueProgram, callValueProgram_host_checked⟩

private def checkedCallerAddressProgram : CheckedHostCoreProgram :=
  ⟨callerAddressProgram, callerAddressProgram_host_checked⟩

private def checkedCurrentAddressProgram : CheckedHostCoreProgram :=
  ⟨currentAddressProgram, currentAddressProgram_host_checked⟩

private def checkedInputDataByteProgram : CheckedHostCoreProgram :=
  ⟨inputDataByteProgram, inputDataByteProgram_host_checked⟩

private def checkedInputDataSizeProgram : CheckedHostCoreProgram :=
  ⟨inputDataSizeProgram, inputDataSizeProgram_host_checked⟩

private def checkedInputDataWordBEProgram : CheckedHostCoreProgram :=
  ⟨inputDataWordBEProgram, inputDataWordBEProgram_host_checked⟩

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

private theorem compileTimeHostCapabilityIndexes :
    HostFunction.storageRead.index = 0 ∧
      HostFunction.storageWrite.index = 1 ∧
      HostFunction.storageAddress.index = 2 ∧
      HostFunction.codeAddress.index = 3 ∧
      HostFunction.callValue.index = 4 ∧
      HostFunction.callerAddress.index = 5 ∧
      HostFunction.inputDataByte?.index = 6 ∧
      HostFunction.inputDataSize.index = 7 ∧
      HostFunction.inputDataWordBE?.index = 8 ∧
      HostFunction.currentAddress.index = 9 := by
  decide

private theorem compileTimeHostCapabilityRegistry :
    HostFunction.all.Nodup ∧
      (∀ function : HostFunction,
        HostFunction.all[function.index]? = some function) ∧
      HostFunction.all.map HostFunction.index =
        List.range HostFunction.all.length :=
  ⟨HostFunction.all_nodup, HostFunction.getElem?_all_index,
    HostFunction.all_indices⟩

private theorem compileTimeHostCapabilityIndexRange (position : Nat) :
    (∃ function : HostFunction, function.index = position) ↔
      position < HostFunction.all.length :=
  HostFunction.exists_index_iff position

private theorem compileTimeHostCapabilityExactLookup
    {position : Nat} {function : HostFunction} :
    HostFunction.all[position]? = some function ↔
      function.index = position :=
  HostFunction.getElem?_all_iff

private theorem compileTimeGenericHostTableLookups :
    ∀ function : HostFunction,
      hostContext[function.index]? = some function.functionType ∧
        hostEnvironment[function.index]? = some (.hostFunction function) :=
  fun function =>
    ⟨hostContext_lookup function, hostEnvironment_lookup function⟩

private theorem compileTimeHostTableLookupRange (position : Nat) :
    (hostContext[position]?.isSome = true ↔
        position < HostFunction.all.length) ∧
      (hostEnvironment[position]?.isSome = true ↔
        position < HostFunction.all.length) :=
  ⟨hostContext_lookup_isSome_iff position,
    hostEnvironment_lookup_isSome_iff position⟩

private theorem compileTimeAddressContextIndexRegression :
    hostContext[HostFunction.storageAddress.index]? =
      some (HostFunction.functionType .storageAddress) :=
  hostContext_storageAddress

private theorem compileTimeAddressEnvironmentIndexRegression :
    hostEnvironment[HostFunction.storageAddress.index]? =
      some (.hostFunction .storageAddress) :=
  hostEnvironment_storageAddress

private theorem compileTimeCodeAddressContextIndexRegression :
    hostContext[HostFunction.codeAddress.index]? =
      some (HostFunction.functionType .codeAddress) :=
  hostContext_codeAddress

private theorem compileTimeCodeAddressEnvironmentIndexRegression :
    hostEnvironment[HostFunction.codeAddress.index]? =
      some (.hostFunction .codeAddress) :=
  hostEnvironment_codeAddress

private theorem compileTimeCallValueContextIndexRegression :
    hostContext[HostFunction.callValue.index]? =
      some (HostFunction.functionType .callValue) :=
  hostContext_callValue

private theorem compileTimeCallValueEnvironmentIndexRegression :
    hostEnvironment[HostFunction.callValue.index]? =
      some (.hostFunction .callValue) :=
  hostEnvironment_callValue

private theorem compileTimeCallerAddressContextIndexRegression :
    hostContext[HostFunction.callerAddress.index]? =
      some (HostFunction.functionType .callerAddress) :=
  hostContext_callerAddress

private theorem compileTimeCallerAddressEnvironmentIndexRegression :
    hostEnvironment[HostFunction.callerAddress.index]? =
      some (.hostFunction .callerAddress) :=
  hostEnvironment_callerAddress

private theorem compileTimeInputDataByteContextIndexRegression :
    hostContext[HostFunction.inputDataByte?.index]? =
      some (HostFunction.functionType .inputDataByte?) :=
  hostContext_inputDataByte?

private theorem compileTimeInputDataByteEnvironmentIndexRegression :
    hostEnvironment[HostFunction.inputDataByte?.index]? =
      some (.hostFunction .inputDataByte?) :=
  hostEnvironment_inputDataByte?

private theorem compileTimeInputDataSizeContextIndexRegression :
    hostContext[HostFunction.inputDataSize.index]? =
      some (HostFunction.functionType .inputDataSize) :=
  hostContext_inputDataSize

private theorem compileTimeInputDataSizeEnvironmentIndexRegression :
    hostEnvironment[HostFunction.inputDataSize.index]? =
      some (.hostFunction .inputDataSize) :=
  hostEnvironment_inputDataSize

private theorem compileTimeInputDataWordBEContextIndexRegression :
    hostContext[HostFunction.inputDataWordBE?.index]? =
      some (HostFunction.functionType .inputDataWordBE?) :=
  hostContext_inputDataWordBE?

private theorem compileTimeInputDataWordBEEnvironmentIndexRegression :
    hostEnvironment[HostFunction.inputDataWordBE?.index]? =
      some (.hostFunction .inputDataWordBE?) :=
  hostEnvironment_inputDataWordBE?

private theorem compileTimeCurrentAddressContextIndexRegression :
    hostContext[HostFunction.currentAddress.index]? =
      some (HostFunction.functionType .currentAddress) :=
  hostContext_currentAddress

private theorem compileTimeCurrentAddressEnvironmentIndexRegression :
    hostEnvironment[HostFunction.currentAddress.index]? =
      some (.hostFunction .currentAddress) :=
  hostEnvironment_currentAddress

private theorem compileTimeCallContractWordContextIndexRegression :
    hostContext[HostFunction.callContractWord.index]? =
      some (HostFunction.functionType .callContractWord) :=
  hostContext_callContractWord

private theorem compileTimeCallContractWordEnvironmentIndexRegression :
    hostEnvironment[HostFunction.callContractWord.index]? =
      some (.hostFunction .callContractWord) :=
  hostEnvironment_callContractWord

private theorem compileTimeCallContractWordWithValueContextIndexRegression :
    hostContext[HostFunction.callContractWordWithValue.index]? =
      some (HostFunction.functionType .callContractWordWithValue) :=
  hostContext_callContractWordWithValue

private theorem compileTimeCallContractWordWithValueEnvironmentIndexRegression :
    hostEnvironment[HostFunction.callContractWordWithValue.index]? =
      some (.hostFunction .callContractWordWithValue) :=
  hostEnvironment_callContractWordWithValue

private theorem compileTimeHostCapabilityLengths :
    HostFunction.all.length = 12 ∧
      hostContext.length = 12 ∧ hostEnvironment.length = 12 :=
  ⟨HostFunction.all_length, hostContext_length, hostEnvironment_length⟩

private theorem compileTimeFirstUnboundHostIndex :
    hostContext[HostFunction.all.length]? = none ∧
      hostEnvironment[HostFunction.all.length]? = none :=
  ⟨hostContext_firstUnbound, hostEnvironment_firstUnbound⟩

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

private def addressBeginState : State :=
  ⟨.ret (.hostFunction .storageAddress),
    [.applyArgument .unit hostEnvironment], []⟩

private def addressArgumentState : State :=
  ⟨.eval .unit hostEnvironment, [.hostApply .storageAddress], []⟩

private def addressRequestState : State :=
  ⟨.ret .unit, [.hostApply .storageAddress], []⟩

private def addressSuspension : HostSuspension :=
  ⟨.storageAddress, [], []⟩

private def codeAddressBeginState : State :=
  ⟨.ret (.hostFunction .codeAddress),
    [.applyArgument .unit hostEnvironment], []⟩

private def codeAddressArgumentState : State :=
  ⟨.eval .unit hostEnvironment, [.hostApply .codeAddress], []⟩

private def codeAddressRequestState : State :=
  ⟨.ret .unit, [.hostApply .codeAddress], []⟩

private def codeAddressSuspension : HostSuspension :=
  ⟨.codeAddress, [], []⟩

private def callValueRequestState : State :=
  ⟨.ret .unit, [.hostApply .callValue], []⟩

private def callValueSuspension : HostSuspension :=
  ⟨.callValue, [], []⟩

private def callerAddressRequestState : State :=
  ⟨.ret .unit, [.hostApply .callerAddress], []⟩

private def callerAddressSuspension : HostSuspension :=
  ⟨.callerAddress, [], []⟩

private def inputDataByteRequestState : State :=
  ⟨.ret (.word inputOffset), [.hostApply .inputDataByte?], []⟩

private def inputDataByteSuspension : HostSuspension :=
  ⟨.inputDataByte? inputOffset, [], []⟩

private def inputDataSizeRequestState : State :=
  ⟨.ret .unit, [.hostApply .inputDataSize], []⟩

private def inputDataSizeSuspension : HostSuspension :=
  ⟨.inputDataSize, [], []⟩

private def inputDataWordBERequestState : State :=
  ⟨.ret (.word inputOffset), [.hostApply .inputDataWordBE?], []⟩

private def inputDataWordBESuspension : HostSuspension :=
  ⟨.inputDataWordBE? inputOffset, [], []⟩

private def currentAddressBeginState : State :=
  ⟨.ret (.hostFunction .currentAddress),
    [.applyArgument .unit hostEnvironment], []⟩

private def currentAddressArgumentState : State :=
  ⟨.eval .unit hostEnvironment, [.hostApply .currentAddress], []⟩

private def currentAddressRequestState : State :=
  ⟨.ret .unit, [.hostApply .currentAddress], []⟩

private def currentAddressSuspension : HostSuspension :=
  ⟨.currentAddress, [], []⟩

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

private theorem compileTimeAddressBeginRegression :
    HostTransition addressBeginState addressArgumentState := by
  apply hostAdvance_next_iff.mp
  exact hostAdvance_begin_storageAddress .unit hostEnvironment [] []

private theorem compileTimeAddressEmissionRegression :
    HostRequestEmission addressRequestState addressSuspension := by
  apply hostAdvance_suspended_iff.mp
  exact hostAdvance_suspend_storageAddress [] []

private theorem compileTimeCodeAddressBeginRegression :
    HostTransition codeAddressBeginState codeAddressArgumentState := by
  apply hostAdvance_next_iff.mp
  exact hostAdvance_begin_codeAddress .unit hostEnvironment [] []

private theorem compileTimeCodeAddressEmissionRegression :
    HostRequestEmission codeAddressRequestState codeAddressSuspension := by
  apply hostAdvance_suspended_iff.mp
  exact hostAdvance_suspend_codeAddress [] []

private theorem compileTimeCallValueEmissionRegression :
    HostRequestEmission callValueRequestState callValueSuspension := by
  apply hostAdvance_suspended_iff.mp
  exact hostAdvance_suspend_callValue [] []

private theorem compileTimeCallerAddressEmissionRegression :
    HostRequestEmission callerAddressRequestState callerAddressSuspension := by
  apply hostAdvance_suspended_iff.mp
  exact hostAdvance_suspend_callerAddress [] []

private theorem compileTimeInputDataByteEmissionRegression :
    HostRequestEmission inputDataByteRequestState inputDataByteSuspension := by
  apply hostAdvance_suspended_iff.mp
  exact hostAdvance_suspend_inputDataByte? inputOffset [] []

private theorem compileTimeInputDataSizeEmissionRegression :
    HostRequestEmission inputDataSizeRequestState inputDataSizeSuspension := by
  apply hostAdvance_suspended_iff.mp
  exact hostAdvance_suspend_inputDataSize [] []

private theorem compileTimeInputDataWordBEEmissionRegression :
    HostRequestEmission inputDataWordBERequestState inputDataWordBESuspension := by
  apply hostAdvance_suspended_iff.mp
  exact hostAdvance_suspend_inputDataWordBE? inputOffset [] []

private theorem compileTimeCurrentAddressBeginRegression :
    HostTransition currentAddressBeginState currentAddressArgumentState := by
  apply hostAdvance_next_iff.mp
  exact hostAdvance_begin_currentAddress .unit hostEnvironment [] []

private theorem compileTimeCurrentAddressEmissionRegression :
    HostRequestEmission currentAddressRequestState currentAddressSuspension := by
  apply hostAdvance_suspended_iff.mp
  exact hostAdvance_suspend_currentAddress [] []

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

private def retainedCodeAddressSuspension : HostSuspension :=
  ⟨.codeAddress, retainedContinuation, retainedStore⟩

private def retainedCallValueSuspension : HostSuspension :=
  ⟨.callValue, retainedContinuation, retainedStore⟩

private def retainedCallerAddressSuspension : HostSuspension :=
  ⟨.callerAddress, retainedContinuation, retainedStore⟩

private def retainedInputDataByteSuspension : HostSuspension :=
  ⟨.inputDataByte? inputOffset, retainedContinuation, retainedStore⟩

private def retainedInputDataSizeSuspension : HostSuspension :=
  ⟨.inputDataSize, retainedContinuation, retainedStore⟩

private def retainedInputDataWordBESuspension : HostSuspension :=
  ⟨.inputDataWordBE? inputOffset, retainedContinuation, retainedStore⟩

private def retainedCurrentAddressSuspension : HostSuspension :=
  ⟨.currentAddress, retainedContinuation, retainedStore⟩

private def retainedCurrentAddressRequestState : State :=
  ⟨.ret .unit,
    .hostApply .currentAddress :: retainedContinuation, retainedStore⟩

private theorem compileTimeRetainedCurrentAddressEmissionRegression :
    HostRequestEmission
      retainedCurrentAddressRequestState retainedCurrentAddressSuspension := by
  apply hostAdvance_suspended_iff.mp
  exact hostAdvance_suspend_currentAddress retainedContinuation retainedStore

private theorem compileTimeInputDataWordBEResponseNoneRegression :
    HostRequest.responseValue (.inputDataWordBE? inputOffset) none =
      .inLeft .word .unit :=
  HostRequest.responseValue_inputDataWordBE?_none inputOffset

private theorem compileTimeInputDataWordBEResponseSomeRegression :
    HostRequest.responseValue (.inputDataWordBE? inputOffset) (some response) =
      .inRight .unit (.word response) :=
  HostRequest.responseValue_inputDataWordBE?_some inputOffset response

private theorem compileTimeResumeRegression :
    retainedSuspension.resume response =
      ⟨.ret (.word response), retainedContinuation, retainedStore⟩ :=
  HostSuspension.resume_storageRead
    slot response retainedContinuation retainedStore

private theorem compileTimeWriteResumeRegression :
    writeSuspension.resume () = State.final .unit [] :=
  HostSuspension.resume_storageWrite slot response () [] []

private theorem compileTimeAddressResumeRegression :
    addressSuspension.resume response = State.final (.word response) [] :=
  HostSuspension.resume_storageAddress response [] []

private theorem compileTimeCodeAddressResumeRegression :
    retainedCodeAddressSuspension.resume response =
      ⟨.ret (.word response), retainedContinuation, retainedStore⟩ :=
  HostSuspension.resume_codeAddress
    response retainedContinuation retainedStore

private theorem compileTimeCallValueResumeRegression :
    retainedCallValueSuspension.resume response =
      ⟨.ret (.word response), retainedContinuation, retainedStore⟩ :=
  HostSuspension.resume_callValue
    response retainedContinuation retainedStore

private theorem compileTimeCallerAddressResumeRegression :
    retainedCallerAddressSuspension.resume response =
      ⟨.ret (.word response), retainedContinuation, retainedStore⟩ :=
  HostSuspension.resume_callerAddress
    response retainedContinuation retainedStore

private theorem compileTimeInputDataByteResumeNoneRegression :
    retainedInputDataByteSuspension.resume none =
      ⟨.ret (.inLeft .word .unit), retainedContinuation, retainedStore⟩ :=
  HostSuspension.resume_inputDataByte?_none
    inputOffset retainedContinuation retainedStore

private theorem compileTimeInputDataByteResumeSomeRegression :
    retainedInputDataByteSuspension.resume (some response) =
      ⟨.ret (.inRight .unit (.word response)),
        retainedContinuation, retainedStore⟩ :=
  HostSuspension.resume_inputDataByte?_some
    inputOffset response retainedContinuation retainedStore

private theorem compileTimeInputDataSizeResumeRegression :
    retainedInputDataSizeSuspension.resume response =
      ⟨.ret (.word response), retainedContinuation, retainedStore⟩ :=
  HostSuspension.resume_inputDataSize
    response retainedContinuation retainedStore

private theorem compileTimeInputDataWordBEResumeNoneRegression :
    retainedInputDataWordBESuspension.resume none =
      ⟨.ret (.inLeft .word .unit), retainedContinuation, retainedStore⟩ :=
  HostSuspension.resume_inputDataWordBE?_none
    inputOffset retainedContinuation retainedStore

private theorem compileTimeInputDataWordBEResumeSomeRegression :
    retainedInputDataWordBESuspension.resume (some response) =
      ⟨.ret (.inRight .unit (.word response)),
        retainedContinuation, retainedStore⟩ :=
  HostSuspension.resume_inputDataWordBE?_some
    inputOffset response retainedContinuation retainedStore

private theorem compileTimeCurrentAddressResumeRegression :
    retainedCurrentAddressSuspension.resume response =
      ⟨.ret (.word response), retainedContinuation, retainedStore⟩ :=
  HostSuspension.resume_currentAddress
    response retainedContinuation retainedStore

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

private theorem compileTimeAddressSuspensionTypingRegression :
    HostSuspensionHasType addressSuspension .word [] := by
  apply CheckedHostCoreProgram.runStateful_suspended_hasType
    (fuel := 5) (remainingFuel := 0) checkedStorageAddressProgram
  decide

private theorem compileTimeAddressTypedResumeRegression :
    HostStateHasType (addressSuspension.resume response) .word [] :=
  compileTimeAddressSuspensionTypingRegression.resume response

private theorem compileTimeCheckedAddressNeverFaults
    (fuel : Nat) (error : MachineFault) (faultState : State) :
    checkedStorageAddressProgram.runStateful fuel ≠ .fault error faultState :=
  CheckedHostCoreProgram.runStateful_ne_fault
    checkedStorageAddressProgram fuel error faultState

private theorem compileTimeCodeAddressSuspensionTypingRegression :
    HostSuspensionHasType codeAddressSuspension .word [] := by
  apply CheckedHostCoreProgram.runStateful_suspended_hasType
    (fuel := 5) (remainingFuel := 0) checkedCodeAddressProgram
  decide

private theorem compileTimeCodeAddressTypedResumeRegression :
    HostStateHasType (codeAddressSuspension.resume response) .word [] :=
  compileTimeCodeAddressSuspensionTypingRegression.resume response

private theorem compileTimeCheckedCodeAddressNeverFaults
    (fuel : Nat) (error : MachineFault) (faultState : State) :
    checkedCodeAddressProgram.runStateful fuel ≠ .fault error faultState :=
  CheckedHostCoreProgram.runStateful_ne_fault
    checkedCodeAddressProgram fuel error faultState

private theorem compileTimeCheckedCallValueNeverFaults
    (fuel : Nat) (error : MachineFault) (faultState : State) :
    checkedCallValueProgram.runStateful fuel ≠ .fault error faultState :=
  CheckedHostCoreProgram.runStateful_ne_fault
    checkedCallValueProgram fuel error faultState

private theorem compileTimeCheckedCallerAddressNeverFaults
    (fuel : Nat) (error : MachineFault) (faultState : State) :
    checkedCallerAddressProgram.runStateful fuel ≠ .fault error faultState :=
  CheckedHostCoreProgram.runStateful_ne_fault
    checkedCallerAddressProgram fuel error faultState

private theorem compileTimeCheckedCurrentAddressNeverFaults
    (fuel : Nat) (error : MachineFault) (faultState : State) :
    checkedCurrentAddressProgram.runStateful fuel ≠ .fault error faultState :=
  CheckedHostCoreProgram.runStateful_ne_fault
    checkedCurrentAddressProgram fuel error faultState

private theorem compileTimeCheckedInputDataByteNeverFaults
    (fuel : Nat) (error : MachineFault) (faultState : State) :
    checkedInputDataByteProgram.runStateful fuel ≠ .fault error faultState :=
  CheckedHostCoreProgram.runStateful_ne_fault
    checkedInputDataByteProgram fuel error faultState

private theorem compileTimeCheckedInputDataSizeNeverFaults
    (fuel : Nat) (error : MachineFault) (faultState : State) :
    checkedInputDataSizeProgram.runStateful fuel ≠ .fault error faultState :=
  CheckedHostCoreProgram.runStateful_ne_fault
    checkedInputDataSizeProgram fuel error faultState

private theorem compileTimeCheckedInputDataWordBENeverFaults
    (fuel : Nat) (error : MachineFault) (faultState : State) :
    checkedInputDataWordBEProgram.runStateful fuel ≠ .fault error faultState :=
  CheckedHostCoreProgram.runStateful_ne_fault
    checkedInputDataWordBEProgram fuel error faultState

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

private theorem compileTimeAddressWireV1RejectionRegression :
    Solcore.Core.Wire.V1.Value.ofCore?
      (.hostFunction .storageAddress) = none :=
  rfl

private theorem compileTimeAddressWireV2RejectionRegression :
    Solcore.Core.Wire.V2.Value.ofCore?
      (.hostFunction .storageAddress) = none :=
  rfl

private theorem compileTimeCodeAddressWireV1RejectionRegression :
    Solcore.Core.Wire.V1.Value.ofCore?
      (.hostFunction .codeAddress) = none :=
  rfl

private theorem compileTimeCodeAddressWireV2RejectionRegression :
    Solcore.Core.Wire.V2.Value.ofCore?
      (.hostFunction .codeAddress) = none :=
  rfl

private theorem compileTimeCallValueWireV1RejectionRegression :
    Solcore.Core.Wire.V1.Value.ofCore?
      (.hostFunction .callValue) = none :=
  rfl

private theorem compileTimeCallValueWireV2RejectionRegression :
    Solcore.Core.Wire.V2.Value.ofCore?
      (.hostFunction .callValue) = none :=
  rfl

private theorem compileTimeCallerAddressWireV1RejectionRegression :
    Solcore.Core.Wire.V1.Value.ofCore?
      (.hostFunction .callerAddress) = none :=
  rfl

private theorem compileTimeCallerAddressWireV2RejectionRegression :
    Solcore.Core.Wire.V2.Value.ofCore?
      (.hostFunction .callerAddress) = none :=
  rfl

private theorem compileTimeInputDataByteWireV1RejectionRegression :
    Solcore.Core.Wire.V1.Value.ofCore?
      (.hostFunction .inputDataByte?) = none :=
  rfl

private theorem compileTimeInputDataByteWireV2RejectionRegression :
    Solcore.Core.Wire.V2.Value.ofCore?
      (.hostFunction .inputDataByte?) = none :=
  rfl

private theorem compileTimeInputDataSizeWireV1RejectionRegression :
    Solcore.Core.Wire.V1.Value.ofCore?
      (.hostFunction .inputDataSize) = none :=
  rfl

private theorem compileTimeInputDataSizeWireV2RejectionRegression :
    Solcore.Core.Wire.V2.Value.ofCore?
      (.hostFunction .inputDataSize) = none :=
  rfl

private theorem compileTimeInputDataWordBEWireV1RejectionRegression :
    Solcore.Core.Wire.V1.Value.ofCore?
      (.hostFunction .inputDataWordBE?) = none :=
  rfl

private theorem compileTimeInputDataWordBEWireV2RejectionRegression :
    Solcore.Core.Wire.V2.Value.ofCore?
      (.hostFunction .inputDataWordBE?) = none :=
  rfl

private theorem compileTimeCurrentAddressWireV1RejectionRegression :
    Solcore.Core.Wire.V1.Value.ofCore?
      (.hostFunction .currentAddress) = none :=
  rfl

private theorem compileTimeCurrentAddressWireV2RejectionRegression :
    Solcore.Core.Wire.V2.Value.ofCore?
      (.hostFunction .currentAddress) = none :=
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
  assertTrue storageAddressProgram.checkHost
    "the host checker rejected storage-address observation"
  assertTrue (!storageAddressProgram.check)
    "the closed checker accepted the storage-address capability"
  assertTrue (!illTypedStorageAddressProgram.checkHost)
    "the host checker accepted a non-Unit storage-address argument"
  assertTrue codeAddressProgram.checkHost
    "the host checker rejected code-address observation"
  assertTrue (!codeAddressProgram.check)
    "the closed checker accepted the code-address capability"
  assertTrue (!illTypedCodeAddressProgram.checkHost)
    "the host checker accepted a non-Unit code-address argument"
  assertTrue callValueProgram.checkHost
    "the host checker rejected call-value observation"
  assertTrue (!callValueProgram.check)
    "the closed checker accepted the call-value capability"
  assertTrue (!illTypedCallValueProgram.checkHost)
    "the host checker accepted a non-Unit call-value argument"
  assertTrue callerAddressProgram.checkHost
    "the host checker rejected caller-address observation"
  assertTrue (!callerAddressProgram.check)
    "the closed checker accepted the caller-address capability"
  assertTrue (!illTypedCallerAddressProgram.checkHost)
    "the host checker accepted a non-Unit caller-address argument"
  assertTrue currentAddressProgram.checkHost
    "the host checker rejected current-address observation"
  assertTrue (!currentAddressProgram.check)
    "the closed checker accepted the current-address capability"
  assertTrue (!illTypedCurrentAddressProgram.checkHost)
    "the host checker accepted a non-Unit current-address argument"
  assertTrue inputDataByteProgram.checkHost
    "the host checker rejected optional input-byte observation"
  assertTrue (!inputDataByteProgram.check)
    "the closed checker accepted the optional input-byte capability"
  assertTrue (!illTypedInputDataByteProgram.checkHost)
    "the host checker accepted a non-Word input-byte offset"
  assertTrue inputDataSizeProgram.checkHost
    "the host checker rejected input-size observation"
  assertTrue (!inputDataSizeProgram.check)
    "the closed checker accepted the input-size capability"
  assertTrue (!illTypedInputDataSizeProgram.checkHost)
    "the host checker accepted a non-Unit input-size argument"
  assertTrue inputDataWordBEProgram.checkHost
    "the host checker rejected strict optional input-word observation"
  assertTrue (!inputDataWordBEProgram.check)
    "the closed checker accepted the optional input-word capability"
  assertTrue (!illTypedInputDataWordBEProgram.checkHost)
    "the host checker accepted a non-Word input-word offset"
  assertTrue (!unboundHostIndexProgram.checkHost)
    "the host checker accepted the first unbound capability index"
  assertTrue
    (hostContext[HostFunction.all.length]?.isNone &&
      hostEnvironment[HostFunction.all.length]?.isNone)
    "host index eleven is no longer the first unbound position"
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
  assertTrue
    (HostFunction.all ==
        [.storageRead, .storageWrite, .storageAddress, .codeAddress,
          .callValue, .callerAddress, .inputDataByte?, .inputDataSize,
          .inputDataWordBE?, .currentAddress, .callContractWord,
          .callContractWordWithValue] &&
      HostFunction.all.all (fun function =>
        HostFunction.all[function.index]? == some function) &&
      HostFunction.all.all (fun function =>
        hostContext[function.index]? == some function.functionType &&
          hostEnvironment[function.index]? == some (.hostFunction function)) &&
      decide HostFunction.all.Nodup &&
      HostFunction.storageRead.index == 0 &&
      HostFunction.storageWrite.index == 1 &&
      HostFunction.storageAddress.index == 2 &&
      HostFunction.codeAddress.index == 3 &&
      HostFunction.callValue.index == 4 &&
      HostFunction.callerAddress.index == 5 &&
      HostFunction.inputDataByte?.index == 6 &&
      HostFunction.inputDataSize.index == 7 &&
      HostFunction.inputDataWordBE?.index == 8 &&
      HostFunction.currentAddress.index == 9 &&
      HostFunction.callContractWord.index == 10 &&
      HostFunction.callContractWordWithValue.index == 11 &&
      HostFunction.all.length == 12 &&
      hostContext.length == 12 && hostEnvironment.length == 12)
    "the append-only host capability layout changed"
  assertTrue
    (hostContext[HostFunction.storageAddress.index]? ==
        some (HostFunction.functionType .storageAddress) &&
      hostEnvironment[HostFunction.storageAddress.index]? ==
        some (.hostFunction .storageAddress))
    "the storage-address capability is absent from its fixed position"
  assertTrue
    (hostContext[HostFunction.codeAddress.index]? ==
        some (HostFunction.functionType .codeAddress) &&
      hostEnvironment[HostFunction.codeAddress.index]? ==
        some (.hostFunction .codeAddress))
    "the code-address capability is absent from its fixed position"
  assertTrue
    (hostContext[HostFunction.callValue.index]? ==
        some (HostFunction.functionType .callValue) &&
      hostEnvironment[HostFunction.callValue.index]? ==
        some (.hostFunction .callValue))
    "the call-value capability is absent from its appended position"
  assertTrue
    (hostContext[HostFunction.callerAddress.index]? ==
        some (HostFunction.functionType .callerAddress) &&
      hostEnvironment[HostFunction.callerAddress.index]? ==
        some (.hostFunction .callerAddress))
    "the caller-address capability is absent from its appended position"
  assertTrue
    (hostContext[HostFunction.inputDataByte?.index]? ==
        some (HostFunction.functionType .inputDataByte?) &&
      hostEnvironment[HostFunction.inputDataByte?.index]? ==
        some (.hostFunction .inputDataByte?))
    "the optional input-byte capability is absent from index six"
  assertTrue
    (hostContext[HostFunction.inputDataSize.index]? ==
        some (HostFunction.functionType .inputDataSize) &&
      hostEnvironment[HostFunction.inputDataSize.index]? ==
        some (.hostFunction .inputDataSize))
    "the input-size capability is absent from index seven"
  assertTrue
    (hostContext[HostFunction.inputDataWordBE?.index]? ==
        some (HostFunction.functionType .inputDataWordBE?) &&
      hostEnvironment[HostFunction.inputDataWordBE?.index]? ==
        some (.hostFunction .inputDataWordBE?))
    "the optional input-word capability is absent from index eight"
  assertTrue
    (hostContext[HostFunction.currentAddress.index]? ==
        some (HostFunction.functionType .currentAddress) &&
      hostEnvironment[HostFunction.currentAddress.index]? ==
        some (.hostFunction .currentAddress))
    "the current-address capability is absent from index nine"

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
  assertTrue (hostAdvance addressBeginState == .next addressArgumentState)
    "storage-address application did not evaluate Unit"
  assertTrue
    (hostAdvance addressRequestState == .suspended addressSuspension)
    "Unit did not emit the storage-address request"
  assertTrue
    (hostAdvance
        ⟨.ret (.bool true), [.hostApply .storageAddress], []⟩ ==
      .fault (.invalidHostArgument .storageAddress (.bool true)))
    "a non-Unit storage-address argument did not fault"
  assertTrue (hostAdvance codeAddressBeginState == .next codeAddressArgumentState)
    "code-address application did not evaluate Unit"
  assertTrue
    (hostAdvance codeAddressRequestState == .suspended codeAddressSuspension)
    "Unit did not emit the code-address request"
  assertTrue
    (hostAdvance
        ⟨.ret (.bool true), [.hostApply .codeAddress], []⟩ ==
      .fault (.invalidHostArgument .codeAddress (.bool true)))
    "a non-Unit code-address argument did not fault"
  assertTrue
    (hostAdvance callValueRequestState == .suspended callValueSuspension)
    "Unit did not emit the call-value request"
  assertTrue
    (hostAdvance
        ⟨.ret (.bool true), [.hostApply .callValue], []⟩ ==
      .fault (.invalidHostArgument .callValue (.bool true)))
    "a non-Unit call-value argument did not fault"
  assertTrue
    (hostAdvance callerAddressRequestState == .suspended callerAddressSuspension)
    "Unit did not emit the caller-address request"
  assertTrue
    (hostAdvance
        ⟨.ret (.bool true), [.hostApply .callerAddress], []⟩ ==
      .fault (.invalidHostArgument .callerAddress (.bool true)))
    "a non-Unit caller-address argument did not retain the raw machine fault"
  assertTrue
    (hostAdvance inputDataByteRequestState ==
      .suspended inputDataByteSuspension)
    "a Word offset did not emit the exact optional input-byte request"
  assertTrue
    (hostAdvance
        ⟨.ret (.bool true), [.hostApply .inputDataByte?], []⟩ ==
      .fault (.invalidHostArgument .inputDataByte? (.bool true)))
    "a non-Word input-byte offset did not retain the raw machine fault"
  assertTrue
    (hostAdvance inputDataSizeRequestState ==
      .suspended inputDataSizeSuspension)
    "Unit did not emit the exact input-size request"
  assertTrue
    (hostAdvance
        ⟨.ret (.bool true), [.hostApply .inputDataSize], []⟩ ==
      .fault (.invalidHostArgument .inputDataSize (.bool true)))
    "a non-Unit input-size argument did not retain the raw machine fault"
  assertTrue
    (hostAdvance inputDataWordBERequestState ==
      .suspended inputDataWordBESuspension)
    "a Word offset did not emit the strict optional input-word request"
  assertTrue
    (hostAdvance
        ⟨.ret (.bool true), [.hostApply .inputDataWordBE?], []⟩ ==
      .fault (.invalidHostArgument .inputDataWordBE? (.bool true)))
    "a non-Word input-word offset did not retain the raw machine fault"
  assertTrue
    (hostAdvance currentAddressBeginState == .next currentAddressArgumentState)
    "current-address application did not evaluate Unit"
  assertTrue
    (hostAdvance currentAddressRequestState ==
      .suspended currentAddressSuspension)
    "Unit did not emit the exact current-address request"
  assertTrue
    (hostAdvance
        ⟨.ret (.bool true), [.hostApply .currentAddress], []⟩ ==
      .fault (.invalidHostArgument .currentAddress (.bool true)))
    "a non-Unit current-address argument did not retain the raw machine fault"

  assertTrue
    (retainedSuspension.resume response ==
      ⟨.ret (.word response), retainedContinuation, retainedStore⟩)
    "resume changed the continuation or Core-local store"
  assertTrue (writeSuspension.resume () == State.final .unit [])
    "storage-write resume did not inject Unit"
  assertTrue
    (addressSuspension.resume response == State.final (.word response) [])
    "storage-address resume did not inject the returned Word"
  assertTrue
    (retainedCodeAddressSuspension.resume response ==
      ⟨.ret (.word response), retainedContinuation, retainedStore⟩)
    "code-address resume changed the returned Word, continuation, or store"
  assertTrue
    (retainedCallValueSuspension.resume response ==
      ⟨.ret (.word response), retainedContinuation, retainedStore⟩)
    "call-value resume changed the returned Word, continuation, or store"
  assertTrue
    (retainedCallerAddressSuspension.resume response ==
      ⟨.ret (.word response), retainedContinuation, retainedStore⟩)
    "caller-address resume changed the returned Word, continuation, or store"
  assertTrue
    (retainedInputDataByteSuspension.resume none ==
      ⟨.ret (.inLeft .word .unit), retainedContinuation, retainedStore⟩)
    "an absent input byte lost its branch, continuation, or Core-local store"
  assertTrue
    (retainedInputDataByteSuspension.resume (some response) ==
      ⟨.ret (.inRight .unit (.word response)),
        retainedContinuation, retainedStore⟩)
    "a present input byte lost its value, continuation, or Core-local store"
  assertTrue
    (retainedInputDataSizeSuspension.resume response ==
      ⟨.ret (.word response), retainedContinuation, retainedStore⟩)
    "input-size resume changed the Word, continuation, or Core-local store"
  assertTrue
    (retainedInputDataWordBESuspension.resume none ==
      ⟨.ret (.inLeft .word .unit), retainedContinuation, retainedStore⟩)
    "an absent input word lost its branch, continuation, or Core-local store"
  assertTrue
    (retainedInputDataWordBESuspension.resume (some response) ==
      ⟨.ret (.inRight .unit (.word response)),
        retainedContinuation, retainedStore⟩)
    "a present input word lost its value, continuation, or Core-local store"
  assertTrue
    (retainedCurrentAddressSuspension.resume response ==
      ⟨.ret (.word response), retainedContinuation, retainedStore⟩)
    "current-address resume changed the Word, continuation, or Core-local store"
  assertTrue
    (hostAdvance retainedCurrentAddressRequestState ==
      .suspended retainedCurrentAddressSuspension)
    "current-address emission changed the continuation or Core-local store"

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
  assertTrue
    (storageAddressProgram.runHostStateful 4 ==
      .outOfFuel addressRequestState)
    "storage-address execution moved its pre-request fuel boundary"
  assertTrue
    (storageAddressProgram.runHostStateful 5 ==
      .suspended addressSuspension 0)
    "storage-address execution changed its exact request budget"
  assertTrue
    (codeAddressProgram.runHostStateful 4 ==
      .outOfFuel codeAddressRequestState)
    "code-address execution moved its pre-request fuel boundary"
  assertTrue
    (codeAddressProgram.runHostStateful 5 ==
      .suspended codeAddressSuspension 0)
    "code-address execution changed its exact request budget"
  assertTrue
    (callValueProgram.runHostStateful 4 ==
      .outOfFuel callValueRequestState)
    "call-value execution moved its pre-request fuel boundary"
  assertTrue
    (callValueProgram.runHostStateful 5 ==
      .suspended callValueSuspension 0)
    "call-value execution changed its exact request budget"
  assertTrue
    (callerAddressProgram.runHostStateful 4 ==
      .outOfFuel callerAddressRequestState)
    "caller-address execution moved its pre-request fuel boundary"
  assertTrue
    (callerAddressProgram.runHostStateful 5 ==
      .suspended callerAddressSuspension 0)
    "caller-address execution changed its exact request budget"
  assertTrue
    (inputDataByteProgram.runHostStateful 4 ==
      .outOfFuel inputDataByteRequestState)
    "input-byte execution moved its pre-request fuel boundary"
  assertTrue
    (inputDataByteProgram.runHostStateful 5 ==
      .suspended inputDataByteSuspension 0)
    "input-byte execution changed its exact request budget"
  assertTrue
    (inputDataSizeProgram.runHostStateful 4 ==
      .outOfFuel inputDataSizeRequestState)
    "input-size execution moved its pre-request fuel boundary"
  assertTrue
    (inputDataSizeProgram.runHostStateful 5 ==
      .suspended inputDataSizeSuspension 0)
    "input-size execution changed its exact request budget"
  assertTrue
    (inputDataWordBEProgram.runHostStateful 4 ==
      .outOfFuel inputDataWordBERequestState)
    "input-word execution moved its pre-request fuel boundary"
  assertTrue
    (inputDataWordBEProgram.runHostStateful 5 ==
      .suspended inputDataWordBESuspension 0)
    "input-word execution changed its exact request budget"
  assertTrue
    (currentAddressProgram.runHostStateful 4 ==
      .outOfFuel currentAddressRequestState)
    "current-address execution moved its pre-request fuel boundary"
  assertTrue
    (currentAddressProgram.runHostStateful 5 ==
      .suspended currentAddressSuspension 0)
    "current-address execution changed its exact request budget"

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
  assertTrue
    (Solcore.Core.Wire.V1.Value.ofCore? (.hostFunction .codeAddress)).isNone
    "Core wire v1 encoded the code-address host value"
  assertTrue
    (Solcore.Core.Wire.V2.Value.ofCore? (.hostFunction .codeAddress)).isNone
    "Core wire v2 encoded the code-address host value"
  assertTrue
    (Solcore.Core.Wire.V1.Value.ofCore? (.hostFunction .callValue)).isNone
    "Core wire v1 encoded the call-value host value"
  assertTrue
    (Solcore.Core.Wire.V2.Value.ofCore? (.hostFunction .callValue)).isNone
    "Core wire v2 encoded the call-value host value"
  assertTrue
    (Solcore.Core.Wire.V1.Value.ofCore? (.hostFunction .callerAddress)).isNone
    "Core wire v1 encoded the caller-address host value"
  assertTrue
    (Solcore.Core.Wire.V2.Value.ofCore? (.hostFunction .callerAddress)).isNone
    "Core wire v2 encoded the caller-address host value"
  assertTrue
    (Solcore.Core.Wire.V1.Value.ofCore?
      (.hostFunction .inputDataByte?)).isNone
    "Core wire v1 encoded the optional input-byte host value"
  assertTrue
    (Solcore.Core.Wire.V2.Value.ofCore?
      (.hostFunction .inputDataByte?)).isNone
    "Core wire v2 encoded the optional input-byte host value"
  assertTrue
    (Solcore.Core.Wire.V1.Value.ofCore?
      (.hostFunction .inputDataSize)).isNone
    "Core wire v1 encoded the input-size host value"
  assertTrue
    (Solcore.Core.Wire.V2.Value.ofCore?
      (.hostFunction .inputDataSize)).isNone
    "Core wire v2 encoded the input-size host value"
  assertTrue
    (Solcore.Core.Wire.V1.Value.ofCore?
      (.hostFunction .inputDataWordBE?)).isNone
    "Core wire v1 encoded the optional input-word host value"
  assertTrue
    (Solcore.Core.Wire.V2.Value.ofCore?
      (.hostFunction .inputDataWordBE?)).isNone
    "Core wire v2 encoded the optional input-word host value"
  assertTrue
    (Solcore.Core.Wire.V1.Value.ofCore?
      (.hostFunction .currentAddress)).isNone
    "Core wire v1 encoded the current-address host value"
  assertTrue
    (Solcore.Core.Wire.V2.Value.ofCore?
      (.hostFunction .currentAddress)).isNone
    "Core wire v2 encoded the current-address host value"

end Tests
