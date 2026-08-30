import Solcore.Semantics.CheckedHostCoreProgram
import Solcore.Semantics.CoreContractEntryProfile
import Solcore.Semantics.HostStorageExecutionInputs
import Solcore.Semantics.WorldState

/-! Checked Core code with a fixed contract-level completion convention. -/

set_option autoImplicit false

namespace Solcore.Semantics

/-- Checker-accepted Core code whose result type matches its entry convention. -/
structure CheckedCoreContract where
  code : CheckedHostCoreProgram
  entryProfile : CoreContractEntryProfile
  resultType_eq :
    code.program.resultType = entryProfile.resultType

namespace CheckedCoreContract

/-- Admit checked code only when its result type has a supported entry profile. -/
def ofCode? (code : CheckedHostCoreProgram) : Option CheckedCoreContract := do
  let profile ← CoreContractEntryProfile.ofResultType? code.program.resultType
  if compatible : code.program.resultType = profile.resultType then
    some ⟨code, profile, compatible⟩
  else
    none

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

end Solcore.Semantics
