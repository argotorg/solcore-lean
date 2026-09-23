import Solcore.Core.ContractCallWordResultProperties
import Solcore.Core.HostProgress
import Solcore.ContractRuntime.CheckedContractRegistry
import Solcore.ContractRuntime.CheckedCoreWordOutcome
import Solcore.ContractRuntime.ContractCallFailure
import Solcore.ContractRuntime.HostStorageAccountPresence
import Solcore.ContractRuntime.HostStorageContext
import Solcore.ContractRuntime.NestedWordCall
import Solcore.ContractRuntime.WorldStateDelta

/-! External compile consumers for ADR-0146 boundary laws. -/

set_option autoImplicit false

namespace Tests.Adr0146BoundaryExternalProperties

example := Solcore.Core.ContractCallWordResult.ofValue?_value
example := Solcore.Core.ContractCallWordResult.value_injective
example := Solcore.Core.ContractCallWordResult.value_eq_iff
example := Solcore.Core.ContractCallWordResult.value_type

example := Solcore.Core.HostFunction.parameterType_callContractWord
example := Solcore.Core.HostFunction.resultType_callContractWord
example := Solcore.Core.HostFunction.index_callContractWord
example := Solcore.Core.hostContext_callContractWord
example := Solcore.Core.hostEnvironment_callContractWord

example := Solcore.Core.HostRequest.responseType_callContractWord
example := Solcore.Core.HostRequest.responseValue_callContractWord
example := Solcore.Core.HostSuspension.resume_callContractWord
example := Solcore.Core.hostAdvance_begin_callContractWord
example := Solcore.Core.hostAdvance_suspend_callContractWord
example := Solcore.Core.hostAdvance_invalid_callContractWord_argument
example := @Solcore.Core.typed_callContractWord_emits

example := Solcore.ContractRuntime.ContractCallFailure.code_injective
example := Solcore.ContractRuntime.ContractCallFailure.code_eq_iff
example := Solcore.ContractRuntime.ContractCallFailure.result_injective
example := Solcore.ContractRuntime.ContractCallFailure.result_value

example := Solcore.ContractRuntime.CheckedCoreWordOutcome.toFrameOutcome_returned
example := Solcore.ContractRuntime.CheckedCoreWordOutcome.toFrameOutcome_reverted
example := Solcore.ContractRuntime.CheckedCoreWordOutcome.toFrameOutcome_trapped

example :=
  Solcore.ContractRuntime.CoreContractEntryProfile.decodeWordOutcome?_returnWord
example :=
  Solcore.ContractRuntime.CoreContractEntryProfile.decodeWordOutcome?_wordOutcomeV1_returned
example :=
  Solcore.ContractRuntime.CoreContractEntryProfile.decodeWordOutcome?_wordOutcomeV1_reverted
example :=
  Solcore.ContractRuntime.CoreContractEntryProfile.decodeWordOutcome?_wordOutcomeV1_trapped
example :=
  Solcore.ContractRuntime.CoreContractEntryProfile.decode?_eq_map_decodeWordOutcome?
example :=
  Solcore.ContractRuntime.CoreContractEntryProfile.decodeTyped_eq_toFrameOutcome_decodeWordOutcome
example :=
  Solcore.ContractRuntime.CoreContractEntryProfile.decodeWordOutcome?_eq_some_decodeWordOutcome
example :=
  @Solcore.ContractRuntime.CoreContractEntryProfile.decodeWordOutcome?_ne_none_of_hasType
example :=
  @Solcore.ContractRuntime.CoreContractEntryProfile.decodeWordOutcome?_isSome_of_hasType

example :=
  Solcore.ContractRuntime.CheckedCoreContract.decodeCompletion?_eq_map_decodeWordOutcome?
example :=
  Solcore.ContractRuntime.CheckedCoreContract.decodeWordOutcome?_eq_some_decodeWordOutcome
example :=
  Solcore.ContractRuntime.CheckedCoreContract.decodeCompletion_eq_toFrameOutcome_decodeWordOutcome

example :=
  Solcore.ContractRuntime.CheckedContractRegistry.resolve?_of_lookup_none
example :=
  Solcore.ContractRuntime.CheckedContractRegistry.resolve?_of_account_absent
example :=
  Solcore.ContractRuntime.CheckedContractRegistry.resolve?_of_code_absent
example :=
  Solcore.ContractRuntime.CheckedContractRegistry.resolve?_of_code_mismatch
example :=
  Solcore.ContractRuntime.CheckedContractRegistry.resolve?_of_lookup_and_installed
example :=
  Solcore.ContractRuntime.CheckedContractRegistry.lookup_eq_some_of_resolve?_eq_some
example :=
  Solcore.ContractRuntime.CheckedContractRegistry.resolve?_eq_some_iff
example :=
  Solcore.ContractRuntime.CheckedContractRegistry.account_present_of_resolve?_eq_some
example :=
  Solcore.ContractRuntime.CheckedContractRegistry.code_present_of_resolve?_eq_some
example :=
  Solcore.ContractRuntime.CheckedContractRegistry.exists_resolve?_eq_some_iff
example :=
  Solcore.ContractRuntime.CheckedContractRegistry.resolve?_eq_none_iff

example {initialWorld finalWorld : Solcore.ContractRuntime.WorldState} :=
  Solcore.ContractRuntime.WorldStateDelta.unique
    (initialWorld := initialWorld) (finalWorld := finalWorld)
example := Solcore.ContractRuntime.WorldStateDelta.accountEndpoints_exact
example := Solcore.ContractRuntime.WorldStateDelta.storageEndpoints_exact
example := Solcore.ContractRuntime.WorldStateDelta.accountEndpoints_identity
example := Solcore.ContractRuntime.WorldStateDelta.storageEndpoints_identity
example := Solcore.ContractRuntime.WorldStateDelta.slotChange?_identity
example {initialWorld finalWorld : Solcore.ContractRuntime.WorldState} :=
  Solcore.ContractRuntime.WorldStateDelta.slotChange?_eq_none_iff
    (initialWorld := initialWorld) (finalWorld := finalWorld)
example {initialWorld finalWorld : Solcore.ContractRuntime.WorldState} :=
  Solcore.ContractRuntime.WorldStateDelta.slotChange?_eq_some_iff
    (initialWorld := initialWorld) (finalWorld := finalWorld)

example := Solcore.ContractRuntime.TopLevelInvocation.childWord_target
example := Solcore.ContractRuntime.TopLevelInvocation.childWord_caller
example := Solcore.ContractRuntime.TopLevelInvocation.childWord_callValue
example := Solcore.ContractRuntime.TopLevelInvocation.childWord_inputBytes
example := Solcore.ContractRuntime.TopLevelInvocation.childWord_executionInputs

example := Solcore.ContractRuntime.CheckedCoreWordOutcome.toContractCallResult
example := Solcore.ContractRuntime.HostStorageDriver.InputData.ofWord_bytes
example := Solcore.ContractRuntime.HostStorageDriver.InputData.ofWord_sizeWord_val
example := Solcore.ContractRuntime.HostStorageDriver.InputData.ofWord_wordBE?_zero

example :=
  @Solcore.ContractRuntime.HostStorageDriver.Context.rebaseWorking_storageAddress
    Unit Unit
example :=
  @Solcore.ContractRuntime.HostStorageDriver.Context.rebaseWorking_checkpoint
    Unit Unit
example :=
  @Solcore.ContractRuntime.HostStorageDriver.Context.rebaseWorking_workingWorld
    Unit Unit
example :=
  @Solcore.ContractRuntime.HostStorageDriver.Context.rebaseWorking_workingEffects
    Unit Unit

/-! The presence module currently exports constructors rather than theorems. -/
example :=
  @Solcore.ContractRuntime.HostStorageDriver.Context.selectedPresence Unit Unit
example :=
  @Solcore.ContractRuntime.HostStorageDriver.Context.rebaseFromPresence Unit Unit
example :=
  @Solcore.ContractRuntime.PresentAccountAt.afterHandleRequest Unit Unit

end Tests.Adr0146BoundaryExternalProperties
