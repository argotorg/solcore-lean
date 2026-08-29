import Solcore.Core.Renaming

/-! Fixed runtime capabilities and checking for Core programs that use them. -/

set_option autoImplicit false

namespace Solcore.Core

/-- Append-only types supplied to a host-aware Core program. -/
def hostContext : Context :=
  [HostFunction.functionType .storageRead,
    HostFunction.functionType .storageWrite,
    HostFunction.functionType .storageAddress,
    HostFunction.functionType .codeAddress,
    HostFunction.functionType .callValue]

/-- Runtime values corresponding positionally to `hostContext`. -/
def hostEnvironment : Environment :=
  [.hostFunction .storageRead, .hostFunction .storageWrite,
    .hostFunction .storageAddress, .hostFunction .codeAddress,
    .hostFunction .callValue]

@[simp] theorem hostContext_storageRead :
    hostContext[HostFunction.storageRead.index]? =
      some (HostFunction.functionType .storageRead) :=
  rfl

@[simp] theorem hostEnvironment_storageRead :
    hostEnvironment[HostFunction.storageRead.index]? =
      some (.hostFunction .storageRead) :=
  rfl

@[simp] theorem hostContext_storageWrite :
    hostContext[HostFunction.storageWrite.index]? =
      some (HostFunction.functionType .storageWrite) :=
  rfl

@[simp] theorem hostEnvironment_storageWrite :
    hostEnvironment[HostFunction.storageWrite.index]? =
      some (.hostFunction .storageWrite) :=
  rfl

@[simp] theorem hostContext_storageAddress :
    hostContext[HostFunction.storageAddress.index]? =
      some (HostFunction.functionType .storageAddress) :=
  rfl

@[simp] theorem hostEnvironment_storageAddress :
    hostEnvironment[HostFunction.storageAddress.index]? =
      some (.hostFunction .storageAddress) :=
  rfl

@[simp] theorem hostContext_codeAddress :
    hostContext[HostFunction.codeAddress.index]? =
      some (HostFunction.functionType .codeAddress) :=
  rfl

@[simp] theorem hostEnvironment_codeAddress :
    hostEnvironment[HostFunction.codeAddress.index]? =
      some (.hostFunction .codeAddress) :=
  rfl

@[simp] theorem hostContext_callValue :
    hostContext[HostFunction.callValue.index]? =
      some (HostFunction.functionType .callValue) :=
  rfl

@[simp] theorem hostEnvironment_callValue :
    hostEnvironment[HostFunction.callValue.index]? =
      some (.hostFunction .callValue) :=
  rfl

@[simp] theorem hostContext_length : hostContext.length = 5 :=
  rfl

@[simp] theorem hostEnvironment_length : hostEnvironment.length = 5 :=
  rfl

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
