import Solcore.ContractRuntime.CoreContractEntryProfileProperties
import Solcore.ContractRuntime.TopLevelExecutionContextProperties
import Solcore.ContractRuntime.TopLevelStorageDeltaProperties

/-! External compile consumers for ADR-0145 contract, context, and delta laws. -/

set_option autoImplicit false

namespace Tests.Adr0145ContractContextExternalProperties

open Solcore.Core
open Solcore.ContractRuntime

section EntryProfile

example
    (profile : CoreContractEntryProfile)
    {world : StoreTyping}
    {value : Value}
    {definitions : DataEnvironment}
    (typing :
      HostRuntimeValueHasType world value profile.resultType definitions) :
    profile.decode? value ≠ none :=
  CoreContractEntryProfile.decode?_ne_none_of_hasType profile typing

example
    (profile : CoreContractEntryProfile)
    {world : StoreTyping}
    {value : Value}
    {definitions : DataEnvironment}
    (typing :
      HostRuntimeValueHasType world value profile.resultType definitions) :
    (profile.decode? value).isSome = true :=
  CoreContractEntryProfile.decode?_isSome_of_hasType profile typing

example (profile : CoreContractEntryProfile) :
    CoreContractEntryProfile.ofResultType? profile.resultType = some profile :=
  CoreContractEntryProfile.ofResultType?_resultType profile

example : Function.Injective CoreContractEntryProfile.resultType :=
  CoreContractEntryProfile.resultType_injective

example (word : Word) :
    CoreContractEntryProfile.decode? .returnWord (.word word) =
      some (.returned (encodeWordBytesBE word)) :=
  CoreContractEntryProfile.decode?_returnWord word

example (word : Word) :
    CoreContractEntryProfile.decode? .wordOutcomeV1
        (.inLeft (.sum .word .word) (.word word)) =
      some (.returned (encodeWordBytesBE word)) :=
  CoreContractEntryProfile.decode?_wordOutcomeV1_returned word

example (word : Word) :
    CoreContractEntryProfile.decode? .wordOutcomeV1
        (.inRight .word (.inLeft .word (.word word))) =
      some (.reverted (encodeWordBytesBE word)) :=
  CoreContractEntryProfile.decode?_wordOutcomeV1_reverted word

example (reason : Word) :
    CoreContractEntryProfile.decode? .wordOutcomeV1
        (.inRight .word (.inRight .word (.word reason))) =
      some (.trapped reason) :=
  CoreContractEntryProfile.decode?_wordOutcomeV1_trapped reason

example
    (code : CheckedHostCoreProgram)
    (profile : CoreContractEntryProfile)
    (resultType_eq : code.program.resultType = profile.resultType) :
    CheckedCoreContract.ofCode? code =
      some ⟨code, profile, resultType_eq⟩ :=
  CheckedCoreContract.ofCode?_of_resultType code profile resultType_eq

example
    (contract : CheckedCoreContract)
    {world : StoreTyping}
    {value : Value}
    (typing :
      HostRuntimeValueHasType world value
        contract.code.program.resultType
        contract.code.program.dataDefinitions) :
    contract.decodeCompletion? value =
      some (contract.decodeCompletion typing) :=
  CheckedCoreContract.decodeCompletion?_eq_some_decodeCompletion
    contract typing

end EntryProfile

section InitialContext

variable {initialWorld : WorldState}
variable {target : Address}
variable {contract : CheckedCoreContract}
variable
  (installed : InstalledCheckedCoreContract initialWorld target contract)

example :
    (TopLevelExecution.initialContext installed).context.storageAddress =
      target :=
  TopLevelExecution.initialContext_storageAddress installed

example :
    (TopLevelExecution.initialContext installed).storageAccount =
      installed.account :=
  TopLevelExecution.initialContext_storageAccount installed

example :
    (TopLevelExecution.initialContext installed).context.values.checkpoint.state =
      initialWorld :=
  TopLevelExecution.initialContext_checkpointState installed

example :
    (TopLevelExecution.initialContext installed).context.values.working.1 =
      initialWorld :=
  TopLevelExecution.initialContext_workingState installed

example :
    (TopLevelExecution.initialContext installed).context.values.checkpoint.effects =
      TopLevelExecution.initialEffects :=
  TopLevelExecution.initialContext_checkpointEffects installed

example :
    (TopLevelExecution.initialContext installed).context.values.working.2 =
      TopLevelExecution.initialEffects :=
  TopLevelExecution.initialContext_workingEffects installed

example : initialWorld.code? target = some contract.code :=
  TopLevelExecution.initialWorld_code? installed

end InitialContext

section Invocation

variable (invocation : TopLevelInvocation)

example : invocation.executionInputs.codeAddress = invocation.target :=
  TopLevelInvocation.executionInputs_codeAddress invocation

example : invocation.executionInputs.currentAddress = invocation.target :=
  TopLevelInvocation.executionInputs_currentAddress invocation

example : invocation.executionInputs.callValue = invocation.callValue :=
  TopLevelInvocation.executionInputs_callValue invocation

example : invocation.executionInputs.callerAddress = invocation.caller :=
  TopLevelInvocation.executionInputs_callerAddress invocation

example : invocation.executionInputs.inputData = invocation.inputData :=
  TopLevelInvocation.executionInputs_inputData invocation

end Invocation

section StorageDelta

variable {initialWorld finalWorld : WorldState}
variable {target : Address}

example
    (world : WorldState)
    (address : Address)
    (account : Account)
    (present : world.account? address = some account)
    (slot : Word) :
    (TopLevelStorageDelta.identity world address account present).slotChange?
        slot = none :=
  TopLevelStorageDelta.slotChange?_identity
    world address account present slot

example
    (left right :
      TopLevelStorageDelta initialWorld finalWorld target) :
    left = right :=
  TopLevelStorageDelta.unique left right

example
    (delta : TopLevelStorageDelta initialWorld finalWorld target)
    (slot : Word) :
    delta.slotChange? slot = none ↔
      delta.initialAccount.storageRead slot =
        delta.finalAccount.storageRead slot :=
  TopLevelStorageDelta.slotChange?_eq_none_iff delta slot

example
    (delta : TopLevelStorageDelta initialWorld finalWorld target)
    (slot before after : Word) :
    delta.slotChange? slot = some (before, after) ↔
      delta.initialAccount.storageRead slot = before ∧
      delta.finalAccount.storageRead slot = after ∧
      before ≠ after :=
  TopLevelStorageDelta.slotChange?_eq_some_iff
    delta slot before after

example
    (delta : TopLevelStorageDelta initialWorld finalWorld target) :
    finalWorld.code? target = initialWorld.code? target :=
  TopLevelStorageDelta.finalWorld_code?_target delta

example
    (delta : TopLevelStorageDelta initialWorld finalWorld target)
    (slot : Word) :
    initialWorld.readStorage? target slot =
      some (delta.initialAccount.storageRead slot) :=
  TopLevelStorageDelta.initialWorld_readStorage?_target delta slot

example
    (delta : TopLevelStorageDelta initialWorld finalWorld target)
    (slot : Word) :
    finalWorld.readStorage? target slot =
      some (delta.finalAccount.storageRead slot) :=
  TopLevelStorageDelta.finalWorld_readStorage?_target delta slot

end StorageDelta

end Tests.Adr0145ContractContextExternalProperties
