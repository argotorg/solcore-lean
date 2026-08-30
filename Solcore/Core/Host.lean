import Solcore.Core.Renaming

/-! Fixed runtime capabilities and checking for Core programs that use them. -/

set_option autoImplicit false

namespace Solcore.Core

/-- Append-only types supplied to a host-aware Core program. -/
def hostContext : Context :=
  HostFunction.all.map HostFunction.functionType

/-- Runtime values corresponding positionally to `hostContext`. -/
def hostEnvironment : Environment :=
  HostFunction.all.map fun function => .hostFunction function

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

@[simp] theorem hostContext_length : hostContext.length = 13 :=
  hostContext_length_all.trans HostFunction.all_length

@[simp] theorem hostEnvironment_length : hostEnvironment.length = 13 :=
  hostEnvironment_length_all.trans HostFunction.all_length

namespace Program

/-- Declarative validity under the exact runtime capability context. -/
structure HostWellTyped (program : Program) : Prop where
  dataDefinitionsWellFormed : program.dataDefinitions.WellFormed
  resultTypeWellFormed : Ty.WellFormed program.dataDefinitions program.resultType
  bodyHasType :
    HasType hostContext program.body program.resultType program.dataDefinitions

/-- Check a Core program under the fixed host capability context. -/
def checkHost (program : Program) : Bool :=
  if program.dataDefinitions.isWellFormed then
    if program.resultType.isWellFormed program.dataDefinitions then
      match infer? hostContext program.body program.dataDefinitions with
      | some inferredType => decide (inferredType = program.resultType)
      | none => false
    else
      false
  else
    false

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
