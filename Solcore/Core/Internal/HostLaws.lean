import Solcore.Core.Host
import Solcore.Core.Internal.Renaming
import Solcore.Core.HostMachine
import Solcore.Core.Internal.MachineLaws

/-!
# Laws of the host boundary

Lookups in `hostContext` and `hostEnvironment`, `Program.checkHost` against its relation, the
response of each `HostRequest`, `HostSuspension.resume`, and `hostAdvance` against
`HostTransition` and `HostRequestEmission`.
-/

section
-- leanmerge: from Solcore.Core.Internal.HostContextLaws
/-! Fixed runtime capabilities and checking for Core programs that use them. -/

set_option autoImplicit false

namespace Solcore.Core

@[simp] theorem hostContext_lookup (function : HostFunction) :
    hostContext[function.index]? = some function.functionType := by
  simp [hostContext]

@[simp] theorem hostEnvironment_lookup (function : HostFunction) :
    hostEnvironment[function.index]? = some (.hostFunction function) := by
  simp [hostEnvironment]

theorem hostContext_length_all :
    hostContext.length = HostFunction.all.length := by
  simp [hostContext]

theorem hostEnvironment_length_all :
    hostEnvironment.length = HostFunction.all.length := by
  simp [hostEnvironment]

theorem hostContext_lookup_isSome_iff (position : Nat) :
    hostContext[position]?.isSome = true ↔
      position < HostFunction.all.length := by
  simp [hostContext, Option.isSome_iff_ne_none]

theorem hostEnvironment_lookup_isSome_iff (position : Nat) :
    hostEnvironment[position]?.isSome = true ↔
      position < HostFunction.all.length := by
  simp [hostEnvironment, Option.isSome_iff_ne_none]

@[simp] theorem hostContext_firstUnbound :
    hostContext[HostFunction.all.length]? = none := by
  apply List.getElem?_eq_none_iff.mpr
  simp [hostContext]

@[simp] theorem hostEnvironment_firstUnbound :
    hostEnvironment[HostFunction.all.length]? = none := by
  apply List.getElem?_eq_none_iff.mpr
  simp [hostEnvironment]

@[simp] theorem hostContext_storageRead :
    hostContext[HostFunction.storageRead.index]? =
      some (HostFunction.functionType .storageRead) :=
  hostContext_lookup .storageRead

@[simp] theorem hostEnvironment_storageRead :
    hostEnvironment[HostFunction.storageRead.index]? =
      some (.hostFunction .storageRead) :=
  hostEnvironment_lookup .storageRead

@[simp] theorem hostContext_storageWrite :
    hostContext[HostFunction.storageWrite.index]? =
      some (HostFunction.functionType .storageWrite) :=
  hostContext_lookup .storageWrite

@[simp] theorem hostEnvironment_storageWrite :
    hostEnvironment[HostFunction.storageWrite.index]? =
      some (.hostFunction .storageWrite) :=
  hostEnvironment_lookup .storageWrite

@[simp] theorem hostContext_storageAddress :
    hostContext[HostFunction.storageAddress.index]? =
      some (HostFunction.functionType .storageAddress) :=
  hostContext_lookup .storageAddress

@[simp] theorem hostEnvironment_storageAddress :
    hostEnvironment[HostFunction.storageAddress.index]? =
      some (.hostFunction .storageAddress) :=
  hostEnvironment_lookup .storageAddress

@[simp] theorem hostContext_codeAddress :
    hostContext[HostFunction.codeAddress.index]? =
      some (HostFunction.functionType .codeAddress) :=
  hostContext_lookup .codeAddress

@[simp] theorem hostEnvironment_codeAddress :
    hostEnvironment[HostFunction.codeAddress.index]? =
      some (.hostFunction .codeAddress) :=
  hostEnvironment_lookup .codeAddress

@[simp] theorem hostContext_callValue :
    hostContext[HostFunction.callValue.index]? =
      some (HostFunction.functionType .callValue) :=
  hostContext_lookup .callValue

@[simp] theorem hostEnvironment_callValue :
    hostEnvironment[HostFunction.callValue.index]? =
      some (.hostFunction .callValue) :=
  hostEnvironment_lookup .callValue

@[simp] theorem hostContext_callerAddress :
    hostContext[HostFunction.callerAddress.index]? =
      some (HostFunction.functionType .callerAddress) :=
  hostContext_lookup .callerAddress

@[simp] theorem hostEnvironment_callerAddress :
    hostEnvironment[HostFunction.callerAddress.index]? =
      some (.hostFunction .callerAddress) :=
  hostEnvironment_lookup .callerAddress

@[simp] theorem hostContext_inputDataByte? :
    hostContext[HostFunction.inputDataByte?.index]? =
      some (HostFunction.functionType .inputDataByte?) :=
  hostContext_lookup .inputDataByte?

@[simp] theorem hostEnvironment_inputDataByte? :
    hostEnvironment[HostFunction.inputDataByte?.index]? =
      some (.hostFunction .inputDataByte?) :=
  hostEnvironment_lookup .inputDataByte?

@[simp] theorem hostContext_inputDataSize :
    hostContext[HostFunction.inputDataSize.index]? =
      some (HostFunction.functionType .inputDataSize) :=
  hostContext_lookup .inputDataSize

@[simp] theorem hostEnvironment_inputDataSize :
    hostEnvironment[HostFunction.inputDataSize.index]? =
      some (.hostFunction .inputDataSize) :=
  hostEnvironment_lookup .inputDataSize

@[simp] theorem hostContext_inputDataWordBE? :
    hostContext[HostFunction.inputDataWordBE?.index]? =
      some (HostFunction.functionType .inputDataWordBE?) :=
  hostContext_lookup .inputDataWordBE?

@[simp] theorem hostEnvironment_inputDataWordBE? :
    hostEnvironment[HostFunction.inputDataWordBE?.index]? =
      some (.hostFunction .inputDataWordBE?) :=
  hostEnvironment_lookup .inputDataWordBE?

@[simp] theorem hostContext_currentAddress :
    hostContext[HostFunction.currentAddress.index]? =
      some (HostFunction.functionType .currentAddress) :=
  hostContext_lookup .currentAddress

@[simp] theorem hostEnvironment_currentAddress :
    hostEnvironment[HostFunction.currentAddress.index]? =
      some (.hostFunction .currentAddress) :=
  hostEnvironment_lookup .currentAddress

@[simp] theorem hostContext_callContractWord :
    hostContext[HostFunction.callContractWord.index]? =
      some (HostFunction.functionType .callContractWord) :=
  hostContext_lookup .callContractWord

@[simp] theorem hostEnvironment_callContractWord :
    hostEnvironment[HostFunction.callContractWord.index]? =
      some (.hostFunction .callContractWord) :=
  hostEnvironment_lookup .callContractWord

@[simp] theorem hostContext_callContractWordWithValue :
    hostContext[HostFunction.callContractWordWithValue.index]? =
      some (HostFunction.functionType .callContractWordWithValue) :=
  hostContext_lookup .callContractWordWithValue

@[simp] theorem hostEnvironment_callContractWordWithValue :
    hostEnvironment[HostFunction.callContractWordWithValue.index]? =
      some (.hostFunction .callContractWordWithValue) :=
  hostEnvironment_lookup .callContractWordWithValue

@[simp] theorem hostContext_createContractWord :
    hostContext[HostFunction.createContractWord.index]? =
      some (HostFunction.functionType .createContractWord) :=
  hostContext_lookup .createContractWord

@[simp] theorem hostEnvironment_createContractWord :
    hostEnvironment[HostFunction.createContractWord.index]? =
      some (.hostFunction .createContractWord) :=
  hostEnvironment_lookup .createContractWord

@[simp] theorem hostContext_emitLogWord :
    hostContext[HostFunction.emitLogWord.index]? =
      some (HostFunction.functionType .emitLogWord) :=
  hostContext_lookup .emitLogWord

@[simp] theorem hostEnvironment_emitLogWord :
    hostEnvironment[HostFunction.emitLogWord.index]? =
      some (.hostFunction .emitLogWord) :=
  hostEnvironment_lookup .emitLogWord

@[simp] theorem hostContext_length : hostContext.length = 14 :=
  hostContext_length_all.trans HostFunction.all_length

@[simp] theorem hostEnvironment_length : hostEnvironment.length = 14 :=
  hostEnvironment_length_all.trans HostFunction.all_length

namespace Program

theorem checkHost_full_sound
    {program : Program}
    (checked : program.checkHost = true) :
    program.HostWellTyped := by
  by_cases definitionsAccepted : program.dataDefinitions.isWellFormed = true
  · by_cases resultAccepted :
        program.resultType.isWellFormed program.dataDefinitions = true
    · cases inferred : infer? hostContext program.body program.dataDefinitions with
      | none =>
          simp [checkHost, definitionsAccepted, resultAccepted, inferred] at checked
      | some inferredType =>
          have typeEquality : inferredType = program.resultType := by
            simpa [checkHost, definitionsAccepted, resultAccepted, inferred]
              using checked
          subst inferredType
          exact {
            dataDefinitionsWellFormed :=
              DataEnvironment.isWellFormed_sound definitionsAccepted
            resultTypeWellFormed := Ty.isWellFormed_sound resultAccepted
            bodyHasType := infer_sound inferred
          }
    · simp [checkHost, definitionsAccepted, resultAccepted] at checked
  · simp [checkHost, definitionsAccepted] at checked

theorem checkHost_sound
    {program : Program}
    (checked : program.checkHost = true) :
    HasType hostContext program.body program.resultType program.dataDefinitions :=
  (checkHost_full_sound checked).bodyHasType

theorem checkHost_complete
    {program : Program}
    (wellTyped : program.HostWellTyped) :
    program.checkHost = true := by
  simp [
    checkHost,
    DataEnvironment.isWellFormed_complete wellTyped.dataDefinitionsWellFormed,
    Ty.isWellFormed_complete wellTyped.resultTypeWellFormed,
    infer_complete wellTyped.bodyHasType
  ]

/-- Every closed well-typed program is also well typed with host capabilities
available but unused. -/
theorem WellTyped.toHostWellTyped
    {program : Program}
    (wellTyped : program.WellTyped) :
    program.HostWellTyped := by
  refine ⟨wellTyped.dataDefinitionsWellFormed,
    wellTyped.resultTypeWellFormed, ?_⟩
  simpa using wellTyped.bodyHasType.rename
    (target := hostContext) (mapping := Renaming.id) (by
      intro index type found
      simp at found)

/-- Closed-checker acceptance is sufficient for host-checker admission. -/
theorem checkHost_of_check
    {program : Program}
    (checked : program.check = true) :
    program.checkHost = true :=
  checkHost_complete (check_full_sound checked).toHostWellTyped

theorem checkHost_iff_hostWellTyped
    {program : Program} :
    program.checkHost = true ↔ program.HostWellTyped :=
  ⟨checkHost_full_sound, checkHost_complete⟩

end Program

end Solcore.Core
end

section
-- leanmerge: from Solcore.Core.Internal.HostLaws
/-! First-order host requests and resumable Core-machine suspensions. -/

set_option autoImplicit false

namespace Solcore.Core

namespace ContractCallWordResult

@[simp] theorem value_type (result : ContractCallWordResult) :
    result.value.type = resultType := by
  cases result <;> rfl

end ContractCallWordResult

namespace HostRequest

@[simp] theorem responseType_storageRead (slot : Word) :
    responseType (.storageRead slot) = .word :=
  rfl

@[simp] theorem responseValue_storageRead (slot response : Word) :
    responseValue (.storageRead slot) response = .word response :=
  rfl

@[simp] theorem responseType_storageWrite (slot value : Word) :
    responseType (.storageWrite slot value) = .unit :=
  rfl

@[simp] theorem responseValue_storageWrite
    (slot value : Word)
    (response : Unit) :
    responseValue (.storageWrite slot value) response = .unit :=
  rfl

@[simp] theorem responseType_storageAddress :
    responseType .storageAddress = .word :=
  rfl

@[simp] theorem responseValue_storageAddress (response : Word) :
    responseValue .storageAddress response = .word response :=
  rfl

@[simp] theorem responseType_codeAddress :
    responseType .codeAddress = .word :=
  rfl

@[simp] theorem responseValue_codeAddress (response : Word) :
    responseValue .codeAddress response = .word response :=
  rfl

@[simp] theorem responseType_callValue :
    responseType .callValue = .word :=
  rfl

@[simp] theorem responseValue_callValue (response : Word) :
    responseValue .callValue response = .word response :=
  rfl

@[simp] theorem responseType_callerAddress :
    responseType .callerAddress = .word :=
  rfl

@[simp] theorem responseValue_callerAddress (response : Word) :
    responseValue .callerAddress response = .word response :=
  rfl

@[simp] theorem responseType_inputDataByte? (offset : Word) :
    responseType (.inputDataByte? offset) = .sum .unit .word :=
  rfl

@[simp] theorem responseValue_inputDataByte?_none (offset : Word) :
    responseValue (.inputDataByte? offset) none = .inLeft .word .unit :=
  rfl

@[simp] theorem responseValue_inputDataByte?_some (offset byte : Word) :
    responseValue (.inputDataByte? offset) (some byte) =
      .inRight .unit (.word byte) :=
  rfl

@[simp] theorem responseType_inputDataSize :
    responseType .inputDataSize = .word :=
  rfl

@[simp] theorem responseValue_inputDataSize (response : Word) :
    responseValue .inputDataSize response = .word response :=
  rfl

@[simp] theorem responseType_inputDataWordBE? (offset : Word) :
    responseType (.inputDataWordBE? offset) = .sum .unit .word :=
  rfl

@[simp] theorem responseValue_inputDataWordBE?_none (offset : Word) :
    responseValue (.inputDataWordBE? offset) none = .inLeft .word .unit :=
  rfl

@[simp] theorem responseValue_inputDataWordBE?_some
    (offset word : Word) :
    responseValue (.inputDataWordBE? offset) (some word) =
      .inRight .unit (.word word) :=
  rfl

@[simp] theorem responseType_currentAddress :
    responseType .currentAddress = .word :=
  rfl

@[simp] theorem responseValue_currentAddress (response : Word) :
    responseValue .currentAddress response = .word response :=
  rfl

@[simp] theorem responseType_callContractWord (target input : Word) :
    responseType (.callContractWord target input) =
      ContractCallWordResult.resultType :=
  rfl

@[simp] theorem responseValue_callContractWord
    (target input : Word)
    (response : ContractCallWordResult) :
    responseValue (.callContractWord target input) response = response.value :=
  rfl

@[simp] theorem responseType_callContractWordWithValue
    (target value input : Word) :
    responseType (.callContractWordWithValue target value input) =
      ContractCallWordResult.resultType :=
  rfl

@[simp] theorem responseValue_callContractWordWithValue
    (target value input : Word)
    (response : ContractCallWordResult) :
    responseValue (.callContractWordWithValue target value input) response =
      response.value :=
  rfl

@[simp] theorem responseType_createContractWord
    (templateId value input : Word) :
    responseType (.createContractWord templateId value input) =
      ContractCallWordResult.resultType :=
  rfl

@[simp] theorem responseValue_createContractWord
    (templateId value input : Word)
    (response : ContractCallWordResult) :
    responseValue (.createContractWord templateId value input) response =
      response.value :=
  rfl

@[simp] theorem responseType_emitLogWord (topic payload : Word) :
    responseType (.emitLogWord topic payload) = .unit :=
  rfl

@[simp] theorem responseValue_emitLogWord
    (topic payload : Word)
    (response : Unit) :
    responseValue (.emitLogWord topic payload) response = .unit :=
  rfl

@[simp] theorem responseValue_type
    (request : HostRequest)
    (response : request.Response) :
    (request.responseValue response).type = request.responseType := by
  cases request <;> try rfl
  all_goals cases response <;> rfl

end HostRequest

namespace HostSuspension

@[simp] theorem resume_control
    (suspension : HostSuspension)
    (response : suspension.request.Response) :
    (suspension.resume response).control =
      .ret (suspension.request.responseValue response) :=
  rfl

@[simp] theorem resume_continuation
    (suspension : HostSuspension)
    (response : suspension.request.Response) :
    (suspension.resume response).continuation = suspension.continuation :=
  rfl

@[simp] theorem resume_store
    (suspension : HostSuspension)
    (response : suspension.request.Response) :
    (suspension.resume response).store = suspension.store :=
  rfl

@[simp] theorem resume_storageRead
    (slot response : Word)
    (continuation : List Frame)
    (store : Store) :
    (HostSuspension.mk (.storageRead slot) continuation store).resume response =
      ⟨.ret (.word response), continuation, store⟩ :=
  rfl

@[simp] theorem resume_storageWrite
    (slot value : Word)
    (response : Unit)
    (continuation : List Frame)
    (store : Store) :
    (HostSuspension.mk (.storageWrite slot value) continuation store).resume
        response =
      ⟨.ret .unit, continuation, store⟩ :=
  rfl

@[simp] theorem resume_storageAddress
    (response : Word)
    (continuation : List Frame)
    (store : Store) :
    (HostSuspension.mk .storageAddress continuation store).resume response =
      ⟨.ret (.word response), continuation, store⟩ :=
  rfl

@[simp] theorem resume_codeAddress
    (response : Word)
    (continuation : List Frame)
    (store : Store) :
    (HostSuspension.mk .codeAddress continuation store).resume response =
      ⟨.ret (.word response), continuation, store⟩ :=
  rfl

@[simp] theorem resume_callValue
    (response : Word)
    (continuation : List Frame)
    (store : Store) :
    (HostSuspension.mk .callValue continuation store).resume response =
      ⟨.ret (.word response), continuation, store⟩ :=
  rfl

@[simp] theorem resume_callerAddress
    (response : Word)
    (continuation : List Frame)
    (store : Store) :
    (HostSuspension.mk .callerAddress continuation store).resume response =
      ⟨.ret (.word response), continuation, store⟩ :=
  rfl

@[simp] theorem resume_inputDataByte?_none
    (offset : Word)
    (continuation : List Frame)
    (store : Store) :
    (HostSuspension.mk (.inputDataByte? offset) continuation store).resume none =
      ⟨.ret (.inLeft .word .unit), continuation, store⟩ :=
  rfl

@[simp] theorem resume_inputDataByte?_some
    (offset byte : Word)
    (continuation : List Frame)
    (store : Store) :
    (HostSuspension.mk (.inputDataByte? offset) continuation store).resume
        (some byte) =
      ⟨.ret (.inRight .unit (.word byte)), continuation, store⟩ :=
  rfl

@[simp] theorem resume_inputDataSize
    (response : Word)
    (continuation : List Frame)
    (store : Store) :
    (HostSuspension.mk .inputDataSize continuation store).resume response =
      ⟨.ret (.word response), continuation, store⟩ :=
  rfl

@[simp] theorem resume_inputDataWordBE?_none
    (offset : Word)
    (continuation : List Frame)
    (store : Store) :
    (HostSuspension.mk (.inputDataWordBE? offset) continuation store).resume
        none =
      ⟨.ret (.inLeft .word .unit), continuation, store⟩ :=
  rfl

@[simp] theorem resume_inputDataWordBE?_some
    (offset word : Word)
    (continuation : List Frame)
    (store : Store) :
    (HostSuspension.mk (.inputDataWordBE? offset) continuation store).resume
        (some word) =
      ⟨.ret (.inRight .unit (.word word)), continuation, store⟩ :=
  rfl

@[simp] theorem resume_currentAddress
    (response : Word)
    (continuation : List Frame)
    (store : Store) :
    (HostSuspension.mk .currentAddress continuation store).resume response =
      ⟨.ret (.word response), continuation, store⟩ :=
  rfl

@[simp] theorem resume_callContractWord
    (target input : Word)
    (response : ContractCallWordResult)
    (continuation : List Frame)
    (store : Store) :
    (HostSuspension.mk (.callContractWord target input) continuation store).resume
        response =
      ⟨.ret response.value, continuation, store⟩ :=
  rfl

@[simp] theorem resume_callContractWordWithValue
    (target value input : Word)
    (response : ContractCallWordResult)
    (continuation : List Frame)
    (store : Store) :
    (HostSuspension.mk
        (.callContractWordWithValue target value input) continuation store).resume
        response =
      ⟨.ret response.value, continuation, store⟩ :=
  rfl

@[simp] theorem resume_createContractWord
    (templateId value input : Word)
    (response : ContractCallWordResult)
    (continuation : List Frame)
    (store : Store) :
    (HostSuspension.mk
        (.createContractWord templateId value input) continuation store).resume
        response =
      ⟨.ret response.value, continuation, store⟩ :=
  rfl

@[simp] theorem resume_emitLogWord
    (topic payload : Word)
    (response : Unit)
    (continuation : List Frame)
    (store : Store) :
    (HostSuspension.mk
        (.emitLogWord topic payload) continuation store).resume response =
      ⟨.ret .unit, continuation, store⟩ :=
  rfl

end HostSuspension

namespace HostAdvanceResult

@[simp] theorem ofAdvance_next (state : State) :
    ofAdvance (.next state) = .next state :=
  rfl

@[simp] theorem ofAdvance_done (value : Value) :
    ofAdvance (.done value) = .done value :=
  rfl

@[simp] theorem ofAdvance_fault (error : MachineFault) :
    ofAdvance (.fault error) = .fault error :=
  rfl

end HostAdvanceResult

@[simp] theorem hostAdvance_begin_storageRead
    (argument : Expr)
    (environment : Environment)
    (continuation : List Frame)
    (store : Store) :
    hostAdvance
        ⟨.ret (.hostFunction .storageRead),
          .applyArgument argument environment :: continuation, store⟩ =
      .next
        ⟨.eval argument environment,
          .hostApply .storageRead :: continuation, store⟩ :=
  rfl

@[simp] theorem hostAdvance_suspend_storageRead
    (slot : Word)
    (continuation : List Frame)
    (store : Store) :
    hostAdvance
        ⟨.ret (.word slot), .hostApply .storageRead :: continuation, store⟩ =
      .suspended ⟨.storageRead slot, continuation, store⟩ :=
  rfl

@[simp] theorem hostAdvance_invalid_storageRead_argument
    (actual : Value)
    (notWord : ∀ slot, actual ≠ .word slot)
    (continuation : List Frame)
    (store : Store) :
    hostAdvance
        ⟨.ret actual, .hostApply .storageRead :: continuation, store⟩ =
      .fault (.invalidHostArgument .storageRead actual) := by
  cases actual <;> simp_all [hostAdvance]

@[simp] theorem hostAdvance_begin_storageWrite
    (argument : Expr)
    (environment : Environment)
    (continuation : List Frame)
    (store : Store) :
    hostAdvance
        ⟨.ret (.hostFunction .storageWrite),
          .applyArgument argument environment :: continuation, store⟩ =
      .next
        ⟨.eval argument environment,
          .hostApply .storageWrite :: continuation, store⟩ :=
  rfl

@[simp] theorem hostAdvance_suspend_storageWrite
    (slot value : Word)
    (continuation : List Frame)
    (store : Store) :
    hostAdvance
        ⟨.ret (.pair (.word slot) (.word value)),
          .hostApply .storageWrite :: continuation, store⟩ =
      .suspended ⟨.storageWrite slot value, continuation, store⟩ :=
  rfl

@[simp] theorem hostAdvance_invalid_storageWrite_argument
    (actual : Value)
    (notWordPair :
      ∀ slot value,
        actual ≠ .pair (.word slot) (.word value))
    (continuation : List Frame)
    (store : Store) :
    hostAdvance
        ⟨.ret actual, .hostApply .storageWrite :: continuation, store⟩ =
      .fault (.invalidHostArgument .storageWrite actual) := by
  cases actual with
  | pair left right =>
      cases left <;> cases right <;> simp_all [hostAdvance]
  | unit | bool | word | integer | hostFunction | closure | inLeft | inRight | cellRef |
      constructed =>
      rfl

@[simp] theorem hostAdvance_begin_storageAddress
    (argument : Expr)
    (environment : Environment)
    (continuation : List Frame)
    (store : Store) :
    hostAdvance
        ⟨.ret (.hostFunction .storageAddress),
          .applyArgument argument environment :: continuation, store⟩ =
      .next
        ⟨.eval argument environment,
          .hostApply .storageAddress :: continuation, store⟩ :=
  rfl

@[simp] theorem hostAdvance_suspend_storageAddress
    (continuation : List Frame)
    (store : Store) :
    hostAdvance
        ⟨.ret .unit, .hostApply .storageAddress :: continuation, store⟩ =
      .suspended ⟨.storageAddress, continuation, store⟩ :=
  rfl

@[simp] theorem hostAdvance_invalid_storageAddress_argument
    (actual : Value)
    (notUnit : actual ≠ .unit)
    (continuation : List Frame)
    (store : Store) :
    hostAdvance
        ⟨.ret actual, .hostApply .storageAddress :: continuation, store⟩ =
      .fault (.invalidHostArgument .storageAddress actual) := by
  cases actual with
  | unit => exact (notUnit rfl).elim
  | bool | word | integer | hostFunction | pair | closure | inLeft | inRight | cellRef |
      constructed =>
      rfl

@[simp] theorem hostAdvance_begin_codeAddress
    (argument : Expr)
    (environment : Environment)
    (continuation : List Frame)
    (store : Store) :
    hostAdvance
        ⟨.ret (.hostFunction .codeAddress),
          .applyArgument argument environment :: continuation, store⟩ =
      .next
        ⟨.eval argument environment,
          .hostApply .codeAddress :: continuation, store⟩ :=
  rfl

@[simp] theorem hostAdvance_suspend_codeAddress
    (continuation : List Frame)
    (store : Store) :
    hostAdvance
        ⟨.ret .unit, .hostApply .codeAddress :: continuation, store⟩ =
      .suspended ⟨.codeAddress, continuation, store⟩ :=
  rfl

@[simp] theorem hostAdvance_invalid_codeAddress_argument
    (actual : Value)
    (notUnit : actual ≠ .unit)
    (continuation : List Frame)
    (store : Store) :
    hostAdvance
        ⟨.ret actual, .hostApply .codeAddress :: continuation, store⟩ =
      .fault (.invalidHostArgument .codeAddress actual) := by
  cases actual with
  | unit => exact (notUnit rfl).elim
  | bool | word | integer | hostFunction | pair | closure | inLeft | inRight | cellRef |
      constructed =>
      rfl

@[simp] theorem hostAdvance_begin_callValue
    (argument : Expr)
    (environment : Environment)
    (continuation : List Frame)
    (store : Store) :
    hostAdvance
        ⟨.ret (.hostFunction .callValue),
          .applyArgument argument environment :: continuation, store⟩ =
      .next
        ⟨.eval argument environment,
          .hostApply .callValue :: continuation, store⟩ :=
  rfl

@[simp] theorem hostAdvance_suspend_callValue
    (continuation : List Frame)
    (store : Store) :
    hostAdvance
        ⟨.ret .unit, .hostApply .callValue :: continuation, store⟩ =
      .suspended ⟨.callValue, continuation, store⟩ :=
  rfl

@[simp] theorem hostAdvance_invalid_callValue_argument
    (actual : Value)
    (notUnit : actual ≠ .unit)
    (continuation : List Frame)
    (store : Store) :
    hostAdvance
        ⟨.ret actual, .hostApply .callValue :: continuation, store⟩ =
      .fault (.invalidHostArgument .callValue actual) := by
  cases actual with
  | unit => exact (notUnit rfl).elim
  | bool | word | integer | hostFunction | pair | closure | inLeft | inRight | cellRef |
      constructed =>
      rfl

@[simp] theorem hostAdvance_begin_callerAddress
    (argument : Expr)
    (environment : Environment)
    (continuation : List Frame)
    (store : Store) :
    hostAdvance
        ⟨.ret (.hostFunction .callerAddress),
          .applyArgument argument environment :: continuation, store⟩ =
      .next
        ⟨.eval argument environment,
          .hostApply .callerAddress :: continuation, store⟩ :=
  rfl

@[simp] theorem hostAdvance_suspend_callerAddress
    (continuation : List Frame)
    (store : Store) :
    hostAdvance
        ⟨.ret .unit, .hostApply .callerAddress :: continuation, store⟩ =
      .suspended ⟨.callerAddress, continuation, store⟩ :=
  rfl

@[simp] theorem hostAdvance_invalid_callerAddress_argument
    (actual : Value)
    (notUnit : actual ≠ .unit)
    (continuation : List Frame)
    (store : Store) :
    hostAdvance
        ⟨.ret actual, .hostApply .callerAddress :: continuation, store⟩ =
      .fault (.invalidHostArgument .callerAddress actual) := by
  cases actual with
  | unit => exact (notUnit rfl).elim
  | bool | word | integer | hostFunction | pair | closure | inLeft | inRight | cellRef |
      constructed =>
      rfl

@[simp] theorem hostAdvance_begin_inputDataByte?
    (argument : Expr)
    (environment : Environment)
    (continuation : List Frame)
    (store : Store) :
    hostAdvance
        ⟨.ret (.hostFunction .inputDataByte?),
          .applyArgument argument environment :: continuation, store⟩ =
      .next
        ⟨.eval argument environment,
          .hostApply .inputDataByte? :: continuation, store⟩ :=
  rfl

@[simp] theorem hostAdvance_suspend_inputDataByte?
    (offset : Word)
    (continuation : List Frame)
    (store : Store) :
    hostAdvance
        ⟨.ret (.word offset), .hostApply .inputDataByte? :: continuation, store⟩ =
      .suspended ⟨.inputDataByte? offset, continuation, store⟩ :=
  rfl

@[simp] theorem hostAdvance_invalid_inputDataByte?_argument
    (actual : Value)
    (notWord : ∀ offset, actual ≠ .word offset)
    (continuation : List Frame)
    (store : Store) :
    hostAdvance
        ⟨.ret actual, .hostApply .inputDataByte? :: continuation, store⟩ =
      .fault (.invalidHostArgument .inputDataByte? actual) := by
  cases actual <;> simp_all [hostAdvance]

@[simp] theorem hostAdvance_begin_inputDataSize
    (argument : Expr)
    (environment : Environment)
    (continuation : List Frame)
    (store : Store) :
    hostAdvance
        ⟨.ret (.hostFunction .inputDataSize),
          .applyArgument argument environment :: continuation, store⟩ =
      .next
        ⟨.eval argument environment,
          .hostApply .inputDataSize :: continuation, store⟩ :=
  rfl

@[simp] theorem hostAdvance_suspend_inputDataSize
    (continuation : List Frame)
    (store : Store) :
    hostAdvance
        ⟨.ret .unit, .hostApply .inputDataSize :: continuation, store⟩ =
      .suspended ⟨.inputDataSize, continuation, store⟩ :=
  rfl

@[simp] theorem hostAdvance_invalid_inputDataSize_argument
    (actual : Value)
    (notUnit : actual ≠ .unit)
    (continuation : List Frame)
    (store : Store) :
    hostAdvance
        ⟨.ret actual, .hostApply .inputDataSize :: continuation, store⟩ =
      .fault (.invalidHostArgument .inputDataSize actual) := by
  cases actual with
  | unit => exact (notUnit rfl).elim
  | bool | word | integer | hostFunction | pair | closure | inLeft | inRight | cellRef |
      constructed =>
      rfl

@[simp] theorem hostAdvance_begin_inputDataWordBE?
    (argument : Expr)
    (environment : Environment)
    (continuation : List Frame)
    (store : Store) :
    hostAdvance
        ⟨.ret (.hostFunction .inputDataWordBE?),
          .applyArgument argument environment :: continuation, store⟩ =
      .next
        ⟨.eval argument environment,
          .hostApply .inputDataWordBE? :: continuation, store⟩ :=
  rfl

@[simp] theorem hostAdvance_suspend_inputDataWordBE?
    (offset : Word)
    (continuation : List Frame)
    (store : Store) :
    hostAdvance
        ⟨.ret (.word offset),
          .hostApply .inputDataWordBE? :: continuation, store⟩ =
      .suspended ⟨.inputDataWordBE? offset, continuation, store⟩ :=
  rfl

@[simp] theorem hostAdvance_invalid_inputDataWordBE?_argument
    (actual : Value)
    (notWord : ∀ offset, actual ≠ .word offset)
    (continuation : List Frame)
    (store : Store) :
    hostAdvance
        ⟨.ret actual, .hostApply .inputDataWordBE? :: continuation, store⟩ =
      .fault (.invalidHostArgument .inputDataWordBE? actual) := by
  cases actual <;> simp_all [hostAdvance]

@[simp] theorem hostAdvance_begin_currentAddress
    (argument : Expr)
    (environment : Environment)
    (continuation : List Frame)
    (store : Store) :
    hostAdvance
        ⟨.ret (.hostFunction .currentAddress),
          .applyArgument argument environment :: continuation, store⟩ =
      .next
        ⟨.eval argument environment,
          .hostApply .currentAddress :: continuation, store⟩ :=
  rfl

@[simp] theorem hostAdvance_suspend_currentAddress
    (continuation : List Frame)
    (store : Store) :
    hostAdvance
        ⟨.ret .unit, .hostApply .currentAddress :: continuation, store⟩ =
      .suspended ⟨.currentAddress, continuation, store⟩ :=
  rfl

@[simp] theorem hostAdvance_invalid_currentAddress_argument
    (actual : Value)
    (notUnit : actual ≠ .unit)
    (continuation : List Frame)
    (store : Store) :
    hostAdvance
        ⟨.ret actual, .hostApply .currentAddress :: continuation, store⟩ =
      .fault (.invalidHostArgument .currentAddress actual) := by
  cases actual with
  | unit => exact (notUnit rfl).elim
  | bool | word | integer | hostFunction | pair | closure | inLeft | inRight | cellRef |
      constructed =>
      rfl

@[simp] theorem hostAdvance_begin_callContractWord
    (argument : Expr)
    (environment : Environment)
    (continuation : List Frame)
    (store : Store) :
    hostAdvance
        ⟨.ret (.hostFunction .callContractWord),
          .applyArgument argument environment :: continuation, store⟩ =
      .next
        ⟨.eval argument environment,
          .hostApply .callContractWord :: continuation, store⟩ :=
  rfl

@[simp] theorem hostAdvance_suspend_callContractWord
    (target input : Word)
    (continuation : List Frame)
    (store : Store) :
    hostAdvance
        ⟨.ret (.pair (.word target) (.word input)),
          .hostApply .callContractWord :: continuation, store⟩ =
      .suspended ⟨.callContractWord target input, continuation, store⟩ :=
  rfl

@[simp] theorem hostAdvance_invalid_callContractWord_argument
    (actual : Value)
    (notWordPair :
      ∀ target input, actual ≠ .pair (.word target) (.word input))
    (continuation : List Frame)
    (store : Store) :
    hostAdvance
        ⟨.ret actual, .hostApply .callContractWord :: continuation, store⟩ =
      .fault (.invalidHostArgument .callContractWord actual) := by
  cases actual <;> simp_all [hostAdvance]

@[simp] theorem hostAdvance_begin_callContractWordWithValue
    (argument : Expr)
    (environment : Environment)
    (continuation : List Frame)
    (store : Store) :
    hostAdvance
        ⟨.ret (.hostFunction .callContractWordWithValue),
          .applyArgument argument environment :: continuation, store⟩ =
      .next
        ⟨.eval argument environment,
          .hostApply .callContractWordWithValue :: continuation, store⟩ :=
  rfl

@[simp] theorem hostAdvance_suspend_callContractWordWithValue
    (target value input : Word)
    (continuation : List Frame)
    (store : Store) :
    hostAdvance
        ⟨.ret
            (.pair (.word target) (.pair (.word value) (.word input))),
          .hostApply .callContractWordWithValue :: continuation, store⟩ =
      .suspended
        ⟨.callContractWordWithValue target value input,
          continuation, store⟩ :=
  rfl

@[simp] theorem hostAdvance_invalid_callContractWordWithValue_argument
    (actual : Value)
    (notWordTriple :
      ∀ target value input,
        actual ≠
          .pair (.word target) (.pair (.word value) (.word input)))
    (continuation : List Frame)
    (store : Store) :
    hostAdvance
        ⟨.ret actual,
          .hostApply .callContractWordWithValue :: continuation, store⟩ =
      .fault
        (.invalidHostArgument .callContractWordWithValue actual) := by
  cases actual <;> simp_all [hostAdvance]

@[simp] theorem hostAdvance_begin_createContractWord
    (argument : Expr)
    (environment : Environment)
    (continuation : List Frame)
    (store : Store) :
    hostAdvance
        ⟨.ret (.hostFunction .createContractWord),
          .applyArgument argument environment :: continuation, store⟩ =
      .next
        ⟨.eval argument environment,
          .hostApply .createContractWord :: continuation, store⟩ :=
  rfl

@[simp] theorem hostAdvance_suspend_createContractWord
    (templateId value input : Word)
    (continuation : List Frame)
    (store : Store) :
    hostAdvance
        ⟨.ret
            (.pair (.word templateId) (.pair (.word value) (.word input))),
          .hostApply .createContractWord :: continuation, store⟩ =
      .suspended
        ⟨.createContractWord templateId value input,
          continuation, store⟩ :=
  rfl

@[simp] theorem hostAdvance_invalid_createContractWord_argument
    (actual : Value)
    (notWordTriple :
      ∀ templateId value input,
        actual ≠
          .pair (.word templateId) (.pair (.word value) (.word input)))
    (continuation : List Frame)
    (store : Store) :
    hostAdvance
        ⟨.ret actual,
          .hostApply .createContractWord :: continuation, store⟩ =
      .fault (.invalidHostArgument .createContractWord actual) := by
  cases actual <;> simp_all [hostAdvance]

@[simp] theorem hostAdvance_begin_emitLogWord
    (argument : Expr)
    (environment : Environment)
    (continuation : List Frame)
    (store : Store) :
    hostAdvance
        ⟨.ret (.hostFunction .emitLogWord),
          .applyArgument argument environment :: continuation, store⟩ =
      .next
        ⟨.eval argument environment,
          .hostApply .emitLogWord :: continuation, store⟩ :=
  rfl

@[simp] theorem hostAdvance_suspend_emitLogWord
    (topic payload : Word)
    (continuation : List Frame)
    (store : Store) :
    hostAdvance
        ⟨.ret (.pair (.word topic) (.word payload)),
          .hostApply .emitLogWord :: continuation, store⟩ =
      .suspended ⟨.emitLogWord topic payload, continuation, store⟩ :=
  rfl

@[simp] theorem hostAdvance_invalid_emitLogWord_argument
    (actual : Value)
    (notWordPair :
      ∀ topic payload,
        actual ≠ .pair (.word topic) (.word payload))
    (continuation : List Frame)
    (store : Store) :
    hostAdvance
        ⟨.ret actual, .hostApply .emitLogWord :: continuation, store⟩ =
      .fault (.invalidHostArgument .emitLogWord actual) := by
  cases actual <;> simp_all [hostAdvance]

end Solcore.Core

/-!
## Consolidated module: `Solcore.Core.HostMachineProperties`
-/

/-! Declarative one-step relations for the executable Core/host boundary. -/

set_option autoImplicit false

namespace Solcore.Core

theorem hostTransition_iff
    {state next : State} :
    HostTransition state next ↔
      Transition state next ∨
        ∃ function argument environment continuation store,
          state =
            ⟨.ret (.hostFunction function),
              .applyArgument argument environment :: continuation, store⟩ ∧
          next =
            ⟨.eval argument environment,
              .hostApply function :: continuation, store⟩ := by
  constructor
  · intro step
    cases step with
    | core coreStep => exact .inl coreStep
    | beginApplication => exact .inr ⟨_, _, _, _, _, rfl, rfl⟩
  · rintro (coreStep | ⟨function, argument, environment, continuation,
        store, rfl, rfl⟩)
    · exact .core coreStep
    · exact .beginApplication

theorem hostRequestEmission_iff
    {state : State}
    {suspension : HostSuspension} :
    HostRequestEmission state suspension ↔
      (∃ slot continuation store,
          state =
            ⟨.ret (.word slot),
              .hostApply .storageRead :: continuation, store⟩ ∧
          suspension = ⟨.storageRead slot, continuation, store⟩) ∨
        (∃ slot value continuation store,
            state =
              ⟨.ret (.pair (.word slot) (.word value)),
                .hostApply .storageWrite :: continuation, store⟩ ∧
            suspension = ⟨.storageWrite slot value, continuation, store⟩) ∨
          (∃ continuation store,
              state =
                ⟨.ret .unit,
                  .hostApply .storageAddress :: continuation, store⟩ ∧
              suspension = ⟨.storageAddress, continuation, store⟩) ∨
            (∃ continuation store,
                state =
                  ⟨.ret .unit,
                    .hostApply .codeAddress :: continuation, store⟩ ∧
                suspension = ⟨.codeAddress, continuation, store⟩) ∨
              (∃ continuation store,
                  state =
                    ⟨.ret .unit,
                      .hostApply .callValue :: continuation, store⟩ ∧
                  suspension = ⟨.callValue, continuation, store⟩) ∨
                (∃ continuation store,
                    state =
                      ⟨.ret .unit,
                        .hostApply .callerAddress :: continuation, store⟩ ∧
                    suspension = ⟨.callerAddress, continuation, store⟩) ∨
                  (∃ offset continuation store,
                      state =
                        ⟨.ret (.word offset),
                          .hostApply .inputDataByte? :: continuation, store⟩ ∧
                      suspension =
                        ⟨.inputDataByte? offset, continuation, store⟩) ∨
                    (∃ continuation store,
                        state =
                          ⟨.ret .unit,
                            .hostApply .inputDataSize :: continuation, store⟩ ∧
                        suspension =
                          ⟨.inputDataSize, continuation, store⟩) ∨
                      (∃ offset continuation store,
                          state =
                            ⟨.ret (.word offset),
                              .hostApply .inputDataWordBE? :: continuation, store⟩ ∧
                          suspension =
                            ⟨.inputDataWordBE? offset, continuation, store⟩) ∨
                        (∃ continuation store,
                            state =
                              ⟨.ret .unit,
                                .hostApply .currentAddress :: continuation, store⟩ ∧
                            suspension =
                              ⟨.currentAddress, continuation, store⟩) ∨
                          (∃ target input continuation store,
                              state =
                                ⟨.ret (.pair (.word target) (.word input)),
                                  .hostApply .callContractWord :: continuation,
                                  store⟩ ∧
                              suspension =
                                ⟨.callContractWord target input, continuation,
                                  store⟩) ∨
                            (∃ target value input continuation store,
                              state =
                                ⟨.ret
                                    (.pair (.word target)
                                      (.pair (.word value) (.word input))),
                                  .hostApply .callContractWordWithValue ::
                                    continuation, store⟩ ∧
                              suspension =
                                ⟨.callContractWordWithValue target value input,
                                  continuation, store⟩) ∨
                              (∃ templateId value input continuation store,
                                  state =
                                    ⟨.ret
                                        (.pair (.word templateId)
                                          (.pair (.word value) (.word input))),
                                      .hostApply .createContractWord ::
                                        continuation, store⟩ ∧
                                  suspension =
                                    ⟨.createContractWord templateId value input,
                                      continuation, store⟩) ∨
                                ∃ topic payload continuation store,
                                  state =
                                    ⟨.ret (.pair (.word topic) (.word payload)),
                                      .hostApply .emitLogWord :: continuation,
                                      store⟩ ∧
                                  suspension =
                                    ⟨.emitLogWord topic payload, continuation,
                                      store⟩ := by
  constructor
  · intro emission
    cases emission with
    | storageRead => exact .inl ⟨_, _, _, rfl, rfl⟩
    | storageWrite => exact .inr (.inl ⟨_, _, _, _, rfl, rfl⟩)
    | storageAddress => exact .inr (.inr (.inl ⟨_, _, rfl, rfl⟩))
    | codeAddress => exact .inr (.inr (.inr (.inl ⟨_, _, rfl, rfl⟩)))
    | callValue =>
        exact .inr (.inr (.inr (.inr (.inl ⟨_, _, rfl, rfl⟩))))
    | callerAddress =>
        exact .inr (.inr (.inr (.inr (.inr (.inl ⟨_, _, rfl, rfl⟩)))))
    | inputDataByte? =>
        exact
          .inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨_, _, _, rfl, rfl⟩))))))
    | inputDataSize =>
        exact
          .inr (.inr (.inr (.inr (.inr (.inr (.inr
            (.inl ⟨_, _, rfl, rfl⟩)))))))
    | inputDataWordBE? =>
        exact
          .inr (.inr (.inr (.inr (.inr (.inr (.inr
            (.inr (.inl ⟨_, _, _, rfl, rfl⟩))))))))
    | currentAddress =>
        exact
          .inr (.inr (.inr (.inr (.inr (.inr (.inr
            (.inr (.inr (.inl ⟨_, _, rfl, rfl⟩)))))))))
    | callContractWord =>
        exact
          .inr (.inr (.inr (.inr (.inr (.inr (.inr
            (.inr (.inr (.inr (.inl ⟨_, _, _, _, rfl, rfl⟩))))))))))
    | callContractWordWithValue =>
        exact
          .inr (.inr (.inr (.inr (.inr (.inr (.inr
            (.inr (.inr (.inr (.inr
              (.inl ⟨_, _, _, _, _, rfl, rfl⟩)))))))))))
    | createContractWord =>
        exact
          .inr (.inr (.inr (.inr (.inr (.inr (.inr
            (.inr (.inr (.inr (.inr
              (.inr (.inl ⟨_, _, _, _, _, rfl, rfl⟩))))))))))))
    | emitLogWord =>
        exact
          .inr (.inr (.inr (.inr (.inr (.inr (.inr
            (.inr (.inr (.inr (.inr
              (.inr (.inr ⟨_, _, _, _, rfl, rfl⟩))))))))))))
  · rintro (⟨slot, continuation, store, rfl, rfl⟩ |
        ⟨slot, value, continuation, store, rfl, rfl⟩ |
        ⟨continuation, store, rfl, rfl⟩ |
        ⟨continuation, store, rfl, rfl⟩ |
        ⟨continuation, store, rfl, rfl⟩ |
        ⟨continuation, store, rfl, rfl⟩ |
        ⟨offset, continuation, store, rfl, rfl⟩ |
        ⟨continuation, store, rfl, rfl⟩ |
        ⟨offset, continuation, store, rfl, rfl⟩ |
        ⟨continuation, store, rfl, rfl⟩ |
        ⟨target, input, continuation, store, rfl, rfl⟩ |
        ⟨target, value, input, continuation, store, rfl, rfl⟩ |
        ⟨templateId, value, input, continuation, store, rfl, rfl⟩ |
        ⟨topic, payload, continuation, store, rfl, rfl⟩)
    · exact .storageRead
    · exact .storageWrite
    · exact .storageAddress
    · exact .codeAddress
    · exact .callValue
    · exact .callerAddress
    · exact .inputDataByte?
    · exact .inputDataSize
    · exact .inputDataWordBE?
    · exact .currentAddress
    · exact .callContractWord
    · exact .callContractWordWithValue
    · exact .createContractWord
    · exact .emitLogWord

@[simp] theorem HostAdvanceResult.ofAdvance_eq_next_iff
    {result : AdvanceResult}
    {next : State} :
    HostAdvanceResult.ofAdvance result = .next next ↔
      result = .next next := by
  cases result <;> simp

@[simp] theorem HostAdvanceResult.ofAdvance_ne_suspended
    (result : AdvanceResult)
    (suspension : HostSuspension) :
    HostAdvanceResult.ofAdvance result ≠ .suspended suspension := by
  cases result <;> simp

theorem hostAdvance_next_iff
    {state next : State} :
    hostAdvance state = .next next ↔ HostTransition state next := by
  constructor
  · intro advanced
    rcases state with ⟨control, continuation, store⟩
    cases control with
    | eval expr environment =>
        exact .core (advance_next_iff.mp (by simpa [hostAdvance] using advanced))
    | ret value =>
        cases continuation with
        | nil =>
            exact .core (advance_next_iff.mp (by simpa [hostAdvance] using advanced))
        | cons frame continuation =>
            cases frame <;>
              try
                exact .core
                  (advance_next_iff.mp (by simpa [hostAdvance] using advanced))
            case applyArgument argument environment =>
              cases value with
              | hostFunction function =>
                  cases advanced
                  exact .beginApplication
              | unit | bool | word | integer | pair | closure | inLeft | inRight | cellRef |
                  constructed =>
                  exact .core
                    (advance_next_iff.mp (by simpa [hostAdvance] using advanced))
            case hostApply function =>
              cases function with
              | storageRead =>
                  cases value <;> simp [hostAdvance] at advanced
              | storageWrite =>
                  cases value with
                  | pair left right =>
                      cases left <;> cases right <;>
                        simp [hostAdvance] at advanced
                  | unit | bool | word | integer | hostFunction | closure | inLeft |
                      inRight | cellRef | constructed =>
                      simp [hostAdvance] at advanced
              | storageAddress =>
                  cases value <;> simp [hostAdvance] at advanced
              | codeAddress =>
                  cases value <;> simp [hostAdvance] at advanced
              | callValue =>
                  cases value <;> simp [hostAdvance] at advanced
              | callerAddress =>
                  cases value <;> simp [hostAdvance] at advanced
              | inputDataByte? =>
                  cases value <;> simp [hostAdvance] at advanced
              | inputDataSize =>
                  cases value <;> simp [hostAdvance] at advanced
              | inputDataWordBE? =>
                  cases value <;> simp [hostAdvance] at advanced
              | currentAddress =>
                  cases value <;> simp [hostAdvance] at advanced
              | callContractWord =>
                  cases value with
                  | pair left right =>
                      cases left <;> cases right <;>
                        simp [hostAdvance] at advanced
                  | unit | bool | word | integer | hostFunction | closure | inLeft |
                      inRight | cellRef | constructed =>
                      simp [hostAdvance] at advanced
              | callContractWordWithValue =>
                  cases value with
                  | pair left right =>
                      cases left with
                      | word target =>
                          cases right with
                          | pair middle last =>
                              cases middle <;> cases last <;>
                                simp [hostAdvance] at advanced
                          | unit | bool | word | integer | hostFunction | closure |
                              inLeft | inRight | cellRef | constructed =>
                              simp [hostAdvance] at advanced
                      | unit | bool | integer | hostFunction | pair | closure | inLeft |
                          inRight | cellRef | constructed =>
                          simp [hostAdvance] at advanced
                  | unit | bool | word | integer | hostFunction | closure | inLeft |
                      inRight | cellRef | constructed =>
                      simp [hostAdvance] at advanced
              | createContractWord =>
                  cases value with
                  | pair left right =>
                      cases left with
                      | word templateId =>
                          cases right with
                          | pair middle last =>
                              cases middle <;> cases last <;>
                                simp [hostAdvance] at advanced
                          | unit | bool | word | integer | hostFunction | closure |
                              inLeft | inRight | cellRef | constructed =>
                              simp [hostAdvance] at advanced
                      | unit | bool | integer | hostFunction | pair | closure | inLeft |
                          inRight | cellRef | constructed =>
                          simp [hostAdvance] at advanced
                  | unit | bool | word | integer | hostFunction | closure | inLeft |
                      inRight | cellRef | constructed =>
                      simp [hostAdvance] at advanced
              | emitLogWord =>
                  cases value with
                  | pair left right =>
                      cases left <;> cases right <;>
                        simp [hostAdvance] at advanced
                  | unit | bool | word | integer | hostFunction | closure | inLeft |
                      inRight | cellRef | constructed =>
                      simp [hostAdvance] at advanced
  · intro step
    cases step with
    | beginApplication => rfl
    | core coreStep =>
        cases coreStep <;> simp [hostAdvance, advance, *]

theorem hostAdvance_suspended_iff
    {state : State}
    {suspension : HostSuspension} :
    hostAdvance state = .suspended suspension ↔
      HostRequestEmission state suspension := by
  constructor
  · intro advanced
    rcases state with ⟨control, continuation, store⟩
    cases control with
    | eval expr environment =>
        simp [hostAdvance] at advanced
    | ret value =>
        cases continuation with
        | nil =>
            simp [hostAdvance] at advanced
        | cons frame continuation =>
            cases frame <;> try simp [hostAdvance] at advanced
            case applyArgument argument environment =>
              cases value <;> simp at advanced
            case hostApply function =>
              cases function with
              | storageRead =>
                  cases value with
                  | word slot =>
                      injection advanced with suspensionEquality
                      cases suspensionEquality
                      exact .storageRead
                  | unit | bool | integer | hostFunction | pair | closure | inLeft |
                      inRight | cellRef | constructed =>
                      simp at advanced
              | storageWrite =>
                  cases value with
                  | pair left right =>
                      cases left <;> cases right <;>
                        simp at advanced
                      case word.word slot value =>
                        cases advanced
                        exact .storageWrite
                  | unit | bool | word | integer | hostFunction | closure | inLeft |
                      inRight | cellRef | constructed =>
                      simp at advanced
              | storageAddress =>
                  cases value with
                  | unit =>
                      cases advanced
                      exact .storageAddress
                  | bool | word | integer | hostFunction | pair | closure | inLeft |
                      inRight | cellRef | constructed =>
                      simp at advanced
              | codeAddress =>
                  cases value with
                  | unit =>
                      cases advanced
                      exact .codeAddress
                  | bool | word | integer | hostFunction | pair | closure | inLeft |
                      inRight | cellRef | constructed =>
                      simp at advanced
              | callValue =>
                  cases value with
                  | unit =>
                      cases advanced
                      exact .callValue
                  | bool | word | integer | hostFunction | pair | closure | inLeft |
                      inRight | cellRef | constructed =>
                      simp at advanced
              | callerAddress =>
                  cases value with
                  | unit =>
                      cases advanced
                      exact .callerAddress
                  | bool | word | integer | hostFunction | pair | closure | inLeft |
                      inRight | cellRef | constructed =>
                      simp at advanced
              | inputDataByte? =>
                  cases value with
                  | word offset =>
                      injection advanced with suspensionEquality
                      cases suspensionEquality
                      exact .inputDataByte?
                  | unit | bool | integer | hostFunction | pair | closure | inLeft |
                      inRight | cellRef | constructed =>
                      simp at advanced
              | inputDataSize =>
                  cases value with
                  | unit =>
                      cases advanced
                      exact .inputDataSize
                  | bool | word | integer | hostFunction | pair | closure | inLeft |
                      inRight | cellRef | constructed =>
                      simp at advanced
              | inputDataWordBE? =>
                  cases value with
                  | word offset =>
                      injection advanced with suspensionEquality
                      cases suspensionEquality
                      exact .inputDataWordBE?
                  | unit | bool | integer | hostFunction | pair | closure | inLeft |
                      inRight | cellRef | constructed =>
                      simp at advanced
              | currentAddress =>
                  cases value with
                  | unit =>
                      cases advanced
                      exact .currentAddress
                  | bool | word | integer | hostFunction | pair | closure | inLeft |
                      inRight | cellRef | constructed =>
                      simp at advanced
              | callContractWord =>
                  cases value with
                  | pair left right =>
                      cases left <;> cases right <;>
                        simp at advanced
                      case word.word target input =>
                        cases advanced
                        exact .callContractWord
                  | unit | bool | word | integer | hostFunction | closure | inLeft |
                      inRight | cellRef | constructed =>
                      simp at advanced
              | callContractWordWithValue =>
                  cases value with
                  | pair left right =>
                      cases left with
                      | word target =>
                          cases right with
                          | pair middle last =>
                              cases middle <;> cases last <;>
                                simp at advanced
                              case word.word value input =>
                                cases advanced
                                exact .callContractWordWithValue
                          | unit | bool | word | integer | hostFunction | closure |
                              inLeft | inRight | cellRef | constructed =>
                              simp at advanced
                      | unit | bool | integer | hostFunction | pair | closure | inLeft |
                          inRight | cellRef | constructed =>
                          simp at advanced
                  | unit | bool | word | integer | hostFunction | closure | inLeft |
                      inRight | cellRef | constructed =>
                      simp at advanced
              | createContractWord =>
                  cases value with
                  | pair left right =>
                      cases left with
                      | word templateId =>
                          cases right with
                          | pair middle last =>
                              cases middle <;> cases last <;>
                                simp at advanced
                              case word.word value input =>
                                cases advanced
                                exact .createContractWord
                          | unit | bool | word | integer | hostFunction | closure |
                              inLeft | inRight | cellRef | constructed =>
                              simp at advanced
                      | unit | bool | integer | hostFunction | pair | closure | inLeft |
                          inRight | cellRef | constructed =>
                          simp at advanced
                  | unit | bool | word | integer | hostFunction | closure | inLeft |
                      inRight | cellRef | constructed =>
                      simp at advanced
              | emitLogWord =>
                  cases value with
                  | pair left right =>
                      cases left <;> cases right <;>
                        simp at advanced
                      case word.word topic payload =>
                        cases advanced
                        exact .emitLogWord
                  | unit | bool | word | integer | hostFunction | closure | inLeft |
                      inRight | cellRef | constructed =>
                      simp at advanced
  · intro emission
    cases emission <;> rfl

theorem hostTransition_deterministic
    {state left right : State}
    (leftStep : HostTransition state left)
    (rightStep : HostTransition state right) :
    left = right := by
  rw [← hostAdvance_next_iff] at leftStep rightStep
  rw [leftStep] at rightStep
  cases rightStep
  rfl

theorem hostRequestEmission_deterministic
    {state : State}
    {left right : HostSuspension}
    (leftEmission : HostRequestEmission state left)
    (rightEmission : HostRequestEmission state right) :
    left = right := by
  rw [← hostAdvance_suspended_iff] at leftEmission rightEmission
  rw [leftEmission] at rightEmission
  cases rightEmission
  rfl

theorem hostTransition_requestEmission_disjoint
    {state next suspension}
    (step : HostTransition state next)
    (emission : HostRequestEmission state suspension) :
    False := by
  rw [← hostAdvance_next_iff] at step
  rw [← hostAdvance_suspended_iff] at emission
  rw [step] at emission
  contradiction

end Solcore.Core
end
