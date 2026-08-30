import Solcore.Core.ContractCallWordResultProperties
import Solcore.Semantics.CheckedContractRegistryProperties
import Solcore.Semantics.CheckedCoreWordOutcomeProperties
import Solcore.Semantics.ContractCallFailureProperties
import Solcore.Semantics.HostStorageAccountPresence
import Solcore.Semantics.HostStorageContextRebase
import Solcore.Semantics.NestedWordCall
import Solcore.Semantics.WorldStateDeltaProperties

/-! External compile consumers for ADR-0146 boundary laws. -/

set_option autoImplicit false

namespace Tests.Adr0146BoundaryExternalProperties

example := Solcore.Core.ContractCallWordResult.ofValue?_value
example := Solcore.Core.ContractCallWordResult.value_injective
example := Solcore.Core.ContractCallWordResult.value_eq_iff

example := Solcore.Semantics.ContractCallFailure.code_injective
example := Solcore.Semantics.ContractCallFailure.code_eq_iff
example := Solcore.Semantics.ContractCallFailure.result_injective
example := Solcore.Semantics.ContractCallFailure.result_value

example := Solcore.Semantics.CheckedCoreWordOutcome.toFrameOutcome_returned
example := Solcore.Semantics.CheckedCoreWordOutcome.toFrameOutcome_reverted
example := Solcore.Semantics.CheckedCoreWordOutcome.toFrameOutcome_trapped

example :=
  Solcore.Semantics.CoreContractEntryProfile.decodeWordOutcome?_returnWord
example :=
  Solcore.Semantics.CoreContractEntryProfile.decodeWordOutcome?_wordOutcomeV1_returned
example :=
  Solcore.Semantics.CoreContractEntryProfile.decodeWordOutcome?_wordOutcomeV1_reverted
example :=
  Solcore.Semantics.CoreContractEntryProfile.decodeWordOutcome?_wordOutcomeV1_trapped
example :=
  Solcore.Semantics.CoreContractEntryProfile.decode?_eq_map_decodeWordOutcome?
example :=
  Solcore.Semantics.CoreContractEntryProfile.decodeTyped_eq_toFrameOutcome_decodeWordOutcome
example :=
  Solcore.Semantics.CoreContractEntryProfile.decodeWordOutcome?_eq_some_decodeWordOutcome

example :=
  Solcore.Semantics.CheckedCoreContract.decodeCompletion?_eq_map_decodeWordOutcome?
example :=
  Solcore.Semantics.CheckedCoreContract.decodeWordOutcome?_eq_some_decodeWordOutcome
example :=
  Solcore.Semantics.CheckedCoreContract.decodeCompletion_eq_toFrameOutcome_decodeWordOutcome

example :=
  Solcore.Semantics.CheckedContractRegistry.resolve?_of_lookup_none
example :=
  Solcore.Semantics.CheckedContractRegistry.resolve?_of_account_absent
example :=
  Solcore.Semantics.CheckedContractRegistry.resolve?_of_code_absent
example :=
  Solcore.Semantics.CheckedContractRegistry.resolve?_of_code_mismatch
example :=
  Solcore.Semantics.CheckedContractRegistry.resolve?_of_lookup_and_installed
example :=
  Solcore.Semantics.CheckedContractRegistry.lookup_eq_some_of_resolve?_eq_some
example :=
  Solcore.Semantics.CheckedContractRegistry.resolve?_eq_some_iff
example :=
  Solcore.Semantics.CheckedContractRegistry.account_present_of_resolve?_eq_some
example :=
  Solcore.Semantics.CheckedContractRegistry.code_present_of_resolve?_eq_some
example :=
  Solcore.Semantics.CheckedContractRegistry.exists_resolve?_eq_some_iff
example :=
  Solcore.Semantics.CheckedContractRegistry.resolve?_eq_none_iff

example {initialWorld finalWorld : Solcore.Semantics.WorldState} :=
  Solcore.Semantics.WorldStateDelta.unique
    (initialWorld := initialWorld) (finalWorld := finalWorld)
example := Solcore.Semantics.WorldStateDelta.accountEndpoints_exact
example := Solcore.Semantics.WorldStateDelta.storageEndpoints_exact
example := Solcore.Semantics.WorldStateDelta.accountEndpoints_identity
example := Solcore.Semantics.WorldStateDelta.storageEndpoints_identity
example := Solcore.Semantics.WorldStateDelta.slotChange?_identity
example {initialWorld finalWorld : Solcore.Semantics.WorldState} :=
  Solcore.Semantics.WorldStateDelta.slotChange?_eq_none_iff
    (initialWorld := initialWorld) (finalWorld := finalWorld)
example {initialWorld finalWorld : Solcore.Semantics.WorldState} :=
  Solcore.Semantics.WorldStateDelta.slotChange?_eq_some_iff
    (initialWorld := initialWorld) (finalWorld := finalWorld)

example := Solcore.Semantics.TopLevelInvocation.childWord_target
example := Solcore.Semantics.TopLevelInvocation.childWord_caller
example := Solcore.Semantics.TopLevelInvocation.childWord_callValue
example := Solcore.Semantics.TopLevelInvocation.childWord_inputBytes
example := Solcore.Semantics.TopLevelInvocation.childWord_executionInputs

example :=
  @Solcore.Semantics.HostStorageDriver.Context.rebaseWorking_storageAddress
    Unit Unit
example :=
  @Solcore.Semantics.HostStorageDriver.Context.rebaseWorking_checkpoint
    Unit Unit
example :=
  @Solcore.Semantics.HostStorageDriver.Context.rebaseWorking_workingWorld
    Unit Unit
example :=
  @Solcore.Semantics.HostStorageDriver.Context.rebaseWorking_workingEffects
    Unit Unit

/-! The presence module currently exports constructors rather than theorems. -/
example :=
  @Solcore.Semantics.HostStorageDriver.Context.selectedPresence Unit Unit
example :=
  @Solcore.Semantics.HostStorageDriver.Context.rebaseFromPresence Unit Unit
example :=
  @Solcore.Semantics.PresentAccountAt.afterHandleRequest Unit Unit

end Tests.Adr0146BoundaryExternalProperties
