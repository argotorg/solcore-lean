import Solcore.ContractRuntime.CheckedHostCoreProgram
import Solcore.ContractRuntime.CheckedHostCoreWordProgram
import Solcore.ContractRuntime.CoreContractEntryProfile
import Solcore.ContractRuntime.HostStorageExecutionInputs
import Solcore.ContractRuntime.WorldState

/-! Checked Core code with a fixed contract-level completion convention. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

/-- Checker-accepted Core code whose result type matches its entry convention. -/
structure CheckedCoreContract where
  code : CheckedHostCoreProgram
  entryProfile : CoreContractEntryProfile
  resultType_eq :
    code.program.resultType = entryProfile.resultType

namespace CheckedCoreContract

/-- Reuse the established checked-Word refinement as a return-Word contract. -/
def returnWord (code : CheckedHostCoreWordProgram) : CheckedCoreContract :=
  ⟨code.code, .returnWord, code.resultType_eq_word⟩

/-- Bind checked code with the exact typed three-way Word outcome convention. -/
def wordOutcomeV1
    (code : CheckedHostCoreProgram)
    (resultType_eq :
      code.program.resultType =
        CoreContractEntryProfile.wordOutcomeV1.resultType) :
    CheckedCoreContract :=
  ⟨code, .wordOutcomeV1, resultType_eq⟩

/-- Admit checked code only when its result type has a supported entry profile. -/
def ofCode? (code : CheckedHostCoreProgram) : Option CheckedCoreContract := do
  let profile ← CoreContractEntryProfile.ofResultType? code.program.resultType
  if compatible : code.program.resultType = profile.resultType then
    some ⟨code, profile, compatible⟩
  else
    none

/-- Execute the contract-owned decoder before using runtime typing to totalize it. -/
def decodeCompletion?
    (contract : CheckedCoreContract)
    (value : Core.Value) : Option (FrameOutcome Core.Word) :=
  contract.entryProfile.decode? value

/-- Decode an exact typed completion using the convention owned by the contract. -/
def decodeCompletion
    (contract : CheckedCoreContract)
    {world : Core.StoreTyping}
    {value : Core.Value}
    (typing :
      Core.HostRuntimeValueHasType world value
        contract.code.program.resultType
        contract.code.program.dataDefinitions) :
    FrameOutcome Core.Word :=
  (contract.decodeCompletion? value).get (by
    apply contract.entryProfile.decode?_isSome_of_hasType
    rw [← contract.resultType_eq]
    exact typing)

end CheckedCoreContract

/-- Evidence that the exact checked contract code is installed in the input world. -/
structure InstalledCheckedCoreContract
    (initialWorld : WorldState)
    (target : Address)
    (contract : CheckedCoreContract) where
  account : Account
  account_present : initialWorld.account? target = some account
  code_present : account.code? = some contract.code

/-- Immutable inputs for the initial direct top-level invocation profile. -/
structure TopLevelInvocation where
  target : Address
  caller : Address
  callValue : Core.Word
  inputData : HostStorageDriver.InputData

namespace TopLevelInvocation

/-- Derive every immutable driver input for a direct call to the target. -/
def executionInputs
    (invocation : TopLevelInvocation) :
    HostStorageDriver.ExecutionInputs := {
  codeAddress := invocation.target
  callValue := invocation.callValue
  callerAddress := invocation.caller
  inputData := invocation.inputData
  currentAddress := invocation.target
}

end TopLevelInvocation

end Solcore.ContractRuntime

/-!
## Consolidated module: `Solcore.ContractRuntime.CheckedCoreContractExtensionality`
-/

/-! Checked contracts are determined by their underlying checked program. -/
set_option autoImplicit false

namespace Solcore.ContractRuntime

theorem CheckedHostCoreProgram.eq_of_program_eq
    {left right : CheckedHostCoreProgram}
    (equal : left.program = right.program) : left = right := by
  cases left
  cases right
  simp only at equal
  subst_vars
  rfl

theorem CoreContractEntryProfile.eq_of_resultType_eq
    {left right : CoreContractEntryProfile}
    (equal : left.resultType = right.resultType) : left = right := by
  cases left <;> cases right <;> simp_all [CoreContractEntryProfile.resultType]

@[ext] theorem CheckedCoreContract.ext
    {left right : CheckedCoreContract}
    (programEq : left.code.program = right.code.program) : left = right := by
  cases left with
  | mk leftCode leftProfile leftType =>
      cases right with
      | mk rightCode rightProfile rightType =>
          change leftCode.program = rightCode.program at programEq
          have codeEq : leftCode = rightCode :=
            CheckedHostCoreProgram.eq_of_program_eq programEq
          subst rightCode
          have profileEq : leftProfile = rightProfile :=
            CoreContractEntryProfile.eq_of_resultType_eq
              (leftType.symm.trans rightType)
          subst rightProfile
          rfl

end Solcore.ContractRuntime
