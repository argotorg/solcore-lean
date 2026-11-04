import Solcore.ContractRuntime.CoreContractEntryProfileProperties
import Solcore.ContractRuntime.TopLevelExecution
import Solcore.ContractRuntime.TopLevelStorageDelta
import Solcore.Core.ContractCallWordResultProperties
import Solcore.Core.HostProgress
import Solcore.ContractRuntime.CheckedContractRegistry
import Solcore.ContractRuntime.CheckedCoreWordOutcome
import Solcore.ContractRuntime.ContractCallFailure
import Solcore.ContractRuntime.HostStorageAccountPresence
import Solcore.ContractRuntime.HostStorageContext
import Solcore.ContractRuntime.NestedWordCall
import Solcore.ContractRuntime.WorldStateDelta
import Solcore.ContractRuntime.OneLevelNestedExecution
import Solcore.ContractRuntime.BalanceTransfer
import Solcore.ContractRuntime.HostStorageHandler

/-!
# Value call boundary tests

Consumers of the ADR-0145 to ADR-0147 laws: contract context, finalization, the scheduler, prepared
contexts and value call boundaries.
-/

section
-- leanmerge: from Solcore.Test.Adr0145ContractContextExternalProperties
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
end

section
-- leanmerge: from Solcore.Test.Adr0145ExecutionExternalProperties
/-! External compile consumers for ADR-0145 finalization and resumption laws. -/

set_option autoImplicit false

namespace Tests.Adr0145ExecutionExternalProperties

open Solcore.Core
open Solcore.ContractRuntime

section Finalization

variable {initialWorld : WorldState}
variable (invocation : TopLevelInvocation)
variable (installedAccount : Account)
variable
  (installedAccount_present :
    initialWorld.account? invocation.target = some installedAccount)
variable (context : TransactionHostStorageDriver.Context)
variable (value : Value)
variable (store : Store)
variable
  (delta :
    TopLevelStorageDelta initialWorld
      context.context.values.working.1 invocation.target)
variable
  (checkpointJournal_eq :
    context.context.values.checkpoint.effects.rollback =
      TransactionJournal.empty)

example (outcome : FrameOutcome Word) :
    (TopLevelExecution.finalize invocation installedAccount
      installedAccount_present context value store outcome delta
        checkpointJournal_eq).outcome =
        outcome :=
  TopLevelExecution.outcome_finalize invocation installedAccount
    installedAccount_present context value store outcome delta
      checkpointJournal_eq

example (outcome : FrameOutcome Word) :
    (TopLevelExecution.finalize invocation installedAccount
      installedAccount_present context value store outcome delta
        checkpointJournal_eq).terminalContext =
        context :=
  TopLevelExecution.terminalContext_finalize invocation installedAccount
    installedAccount_present context value store outcome delta
      checkpointJournal_eq

example (data : Bytes) :
    (TopLevelExecution.finalize invocation installedAccount
      installedAccount_present context value store (.returned data) delta
        checkpointJournal_eq).finalWorld =
        context.context.values.working.1 :=
  TopLevelExecution.finalWorld_finalize_returned invocation installedAccount
    installedAccount_present context value store data delta checkpointJournal_eq

example (data : Bytes) :
    (TopLevelExecution.finalize invocation installedAccount
      installedAccount_present context value store (.reverted data) delta
        checkpointJournal_eq).finalWorld =
        initialWorld :=
  TopLevelExecution.finalWorld_finalize_reverted invocation installedAccount
    installedAccount_present context value store data delta checkpointJournal_eq

example (reason : Word) :
    (TopLevelExecution.finalize invocation installedAccount
      installedAccount_present context value store (.trapped reason) delta
        checkpointJournal_eq).finalWorld =
        initialWorld :=
  TopLevelExecution.finalWorld_finalize_trapped invocation installedAccount
    installedAccount_present context value store reason delta checkpointJournal_eq

example (data : Bytes) (slot : Word) :
    (TopLevelExecution.finalize invocation installedAccount
      installedAccount_present context value store (.returned data) delta
        checkpointJournal_eq).committedDelta.slotChange?
        slot = delta.slotChange? slot :=
  TopLevelExecution.committedSlotChange?_finalize_returned invocation
    installedAccount installedAccount_present context value store data delta
      checkpointJournal_eq slot

example (data : Bytes) (slot : Word) :
    (TopLevelExecution.finalize invocation installedAccount
      installedAccount_present context value store (.reverted data) delta
        checkpointJournal_eq).committedDelta.slotChange?
        slot = none :=
  TopLevelExecution.committedSlotChange?_finalize_reverted invocation
    installedAccount installedAccount_present context value store data delta
      checkpointJournal_eq slot

example (reason : Word) (slot : Word) :
    (TopLevelExecution.finalize invocation installedAccount
      installedAccount_present context value store (.trapped reason) delta
        checkpointJournal_eq).committedDelta.slotChange?
        slot = none :=
  TopLevelExecution.committedSlotChange?_finalize_trapped invocation
    installedAccount installedAccount_present context value store reason delta
      checkpointJournal_eq slot

end Finalization

section JournalSeals

variable {initialWorld : WorldState}
variable {contract : CheckedCoreContract}
variable {invocation : TopLevelInvocation}

example
    (result : TopLevelTerminalResult initialWorld invocation.target) :
    result.workingJournal = result.terminalContext.workingJournal :=
  result.workingJournal_eq

example
    (result : TopLevelTerminalResult initialWorld invocation.target) :
    result.committedJournal =
      match result.outcome with
      | .returned _ => result.terminalContext.workingJournal
      | .reverted _ =>
          result.terminalContext.context.values.checkpoint.effects.rollback
      | .trapped _ =>
          result.terminalContext.context.values.checkpoint.effects.rollback :=
  result.committedJournal_eq

example
    (execution : TopLevelRunResult initialWorld contract invocation) :
    execution.rootCheckpointJournal = TransactionJournal.empty :=
  execution.rootCheckpointJournal_eq_empty

end JournalSeals

section RawRun

variable {initialWorld : WorldState}
variable (contract : CheckedCoreContract)
variable (invocation : TopLevelInvocation)
variable
  (installed :
    InstalledCheckedCoreContract initialWorld invocation.target contract)

example (fuel : Nat) :
    (TopLevelExecution.rawRun contract invocation installed fuel).context.context.values.working.1.code?
        invocation.target = some contract.code :=
  TopLevelExecution.rawRun_working_code?
    contract invocation installed fuel

example (fuel : Nat) (error : MachineFault) (faultState : State) :
    (TopLevelExecution.rawRun contract invocation installed fuel).outcome ≠
      .fault error faultState :=
  TopLevelExecution.rawRun_ne_fault
    contract invocation installed fuel error faultState

end RawRun

section Resumption

variable {initialWorld : WorldState}
variable {contract : CheckedCoreContract}
variable {invocation : TopLevelInvocation}

example
    (left right :
      TopLevelExecution.ValidatedRawResult
        initialWorld contract invocation)
    (result_eq : left.result = right.result) :
    left = right :=
  TopLevelExecution.ValidatedRawResult.eq_of_result_eq
    left right result_eq

example
    (left right :
      TopLevelExecution.ValidatedRawResult
        initialWorld contract invocation)
    (result_eq : left.result = right.result) :
    TopLevelExecution.classifyRawResult contract invocation left =
      TopLevelExecution.classifyRawResult contract invocation right :=
  TopLevelExecution.classifyRawResult_unique
    contract invocation left right result_eq

example
    (result : TopLevelTerminalResult initialWorld invocation.target)
    (additional : Nat) :
    TopLevelExecution.resumeWithFuel
        (TopLevelRunResult.completed (contract := contract) result)
        additional =
      TopLevelRunResult.completed result :=
  TopLevelExecution.resumeWithFuel_completed result additional

variable
  (installed :
    InstalledCheckedCoreContract initialWorld invocation.target contract)

example (fuel additional : Nat) :
    TopLevelExecution.resumeWithFuel
        (TopLevelExecution.run contract invocation installed fuel) additional =
      TopLevelExecution.run contract invocation installed
        (fuel + additional) :=
  TopLevelExecution.resumeWithFuel_run
    contract invocation installed fuel additional

example (fuel : Nat) :
    TopLevelExecution.resumeWithFuel
        (TopLevelExecution.run contract invocation installed fuel) 0 =
      TopLevelExecution.run contract invocation installed fuel :=
  TopLevelExecution.resumeWithFuel_run_zero
    contract invocation installed fuel

example (fuel first second : Nat) :
    TopLevelExecution.resumeWithFuel
        (TopLevelExecution.resumeWithFuel
          (TopLevelExecution.run contract invocation installed fuel) first)
        second =
      TopLevelExecution.run contract invocation installed
        (fuel + first + second) :=
  TopLevelExecution.resumeWithFuel_run_add
    contract invocation installed fuel first second

end Resumption

end Tests.Adr0145ExecutionExternalProperties
end

section
-- leanmerge: from Solcore.Test.Adr0146BoundaryExternalProperties
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
end

section
-- leanmerge: from Solcore.Test.Adr0146SchedulerExternalProperties
/-! External compile consumers for the public ADR-0146 scheduler laws. -/

set_option autoImplicit false

namespace Tests.Adr0146SchedulerExternalProperties

open Solcore.Core
open Solcore.ContractRuntime
open OneLevelNestedExecution

example := @Result.eq_of_view_eq

example
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (mode : Mode initialWorld rootContract rootInvocation) :
    mode.rank ≤ 1 :=
  Mode.rank_le_one mode

section RootFinalization

variable {initialWorld : WorldState}
variable {rootContract : CheckedCoreContract}
variable {rootInvocation : TopLevelInvocation}
variable
  (frame : RootFrame initialWorld rootContract rootInvocation)
variable (value : Value) (store : Store)

example (data : Bytes) :
    (frame.finalize value store (.returned data)).finalWorld =
      frame.context.context.values.working.1 :=
  RootFrame.finalize_returned_finalWorld frame value store data

example (data : Bytes) :
    (frame.finalize value store (.reverted data)).finalWorld =
      initialWorld :=
  RootFrame.finalize_reverted_finalWorld frame value store data

example (reason : Word) :
    (frame.finalize value store (.trapped reason)).finalWorld =
      initialWorld :=
  RootFrame.finalize_trapped_finalWorld frame value store reason

example (outcome : FrameOutcome Word) :
    (frame.finalize value store outcome).outcome = outcome :=
  RootFrame.finalize_outcome frame value store outcome

example (outcome : FrameOutcome Word) :
    (frame.finalize value store outcome).workingDelta = .exact :=
  RootFrame.finalize_workingDelta frame value store outcome

end RootFinalization

section ChildResolution

variable {initialWorld : WorldState}
variable {rootContract : CheckedCoreContract}
variable {rootInvocation : TopLevelInvocation}
variable
  (frame : ChildFrame initialWorld rootContract rootInvocation)

example (data : Word) :
    (frame.selectedParentContext (.returned data)).context.values.working.1 =
      frame.childContext.context.values.working.1 :=
  ChildFrame.selectedParentContext_returned_workingWorld frame data

example (data : Word) :
    frame.selectedParentContext (.reverted data) =
      frame.suspendedRoot.parentContext :=
  ChildFrame.selectedParentContext_reverted frame data

example (reason : Word) :
    frame.selectedParentContext (.trapped reason) =
      frame.suspendedRoot.parentContext :=
  ChildFrame.selectedParentContext_trapped frame reason

example (data : Word) :
    (frame.resumeRoot (.returned data)).context.context.values.working.1 =
      frame.childContext.context.values.working.1 :=
  ChildFrame.resumeRoot_returned_workingWorld frame data

example (data : Word) :
    (frame.resumeRoot (.reverted data)).context =
      frame.suspendedRoot.parentContext :=
  ChildFrame.resumeRoot_reverted_context frame data

example (reason : Word) :
    (frame.resumeRoot (.trapped reason)).context =
      frame.suspendedRoot.parentContext :=
  ChildFrame.resumeRoot_trapped_context frame reason

example (data : Word) :
    (frame.resumeRoot (.returned data)).state =
      frame.suspendedRoot.suspension.resume
        (frame.suspendedRoot.call.response (.returned data)) :=
  ChildFrame.resumeRoot_returned_response frame data

example (data : Word) :
    (frame.resumeRoot (.reverted data)).state =
      frame.suspendedRoot.suspension.resume
        (frame.suspendedRoot.call.response (.reverted data)) :=
  ChildFrame.resumeRoot_reverted_response frame data

example (reason : Word) :
    (frame.resumeRoot (.trapped reason)).state =
      frame.suspendedRoot.suspension.resume
        (frame.suspendedRoot.call.response (.trapped reason)) :=
  ChildFrame.resumeRoot_trapped_response frame reason

end ChildResolution

section ReachabilitySeal

variable {initialWorld : WorldState}
variable {rootContract : CheckedCoreContract}
variable {rootInvocation : TopLevelInvocation}
variable {registry : ExecutionEnvironment}
variable {mode : Mode initialWorld rootContract rootInvocation}

example (reachable : Reachable registry mode) :
    Anchored registry mode :=
  reachable.anchored

end ReachabilitySeal

section ReachableRoot

variable {initialWorld : WorldState}
variable {rootContract : CheckedCoreContract}
variable {rootInvocation : TopLevelInvocation}
variable {registry : ExecutionEnvironment}
variable {frame : RootFrame initialWorld rootContract rootInvocation}
variable (reachable : Reachable registry (.root frame))

example :
    frame.context.context.storageAddress = rootInvocation.target :=
  reachable.root_storageAddress

example :
    frame.context.context.values.checkpoint.state = initialWorld :=
  reachable.root_checkpointState

example :
    frame.context.context.values.checkpoint.effects.rollback =
      TransactionJournal.empty :=
  reachable.root_checkpointJournal

end ReachableRoot

section ReachableChild

variable {initialWorld : WorldState}
variable {rootContract : CheckedCoreContract}
variable {rootInvocation : TopLevelInvocation}
variable {registry : ExecutionEnvironment}
variable {frame : ChildFrame initialWorld rootContract rootInvocation}
variable (reachable : Reachable registry (.child frame))

example :
    frame.suspendedRoot.parentContext.context.storageAddress =
      rootInvocation.target :=
  reachable.child_parentStorageAddress

example :
    frame.suspendedRoot.parentContext.context.values.checkpoint.state =
      initialWorld :=
  reachable.child_parentCheckpointState

example :
    frame.suspendedRoot.parentContext.context.values.checkpoint.effects.rollback =
      TransactionJournal.empty :=
  reachable.child_parentCheckpointJournal

example :
    frame.childContext.context.storageAddress = frame.childTarget :=
  reachable.child_storageAddress

example :
    frame.childContext.context.values.checkpoint.state =
      frame.childInitialWorld :=
  reachable.child_checkpointState

example :
    registry.callRegistry.resolve?
        frame.suspendedRoot.parentContext.context.values.working.1
        frame.childTarget =
      some ⟨frame.childContract, frame.preTransferInstalled⟩ :=
  reachable.child_registryResolution

end ReachableChild

end Tests.Adr0146SchedulerExternalProperties
end

section
-- leanmerge: from Solcore.Test.Adr0147PreparedContextExternalProperties
/-! External compile consumers for prepared root checkpoint projections. -/

set_option autoImplicit false

namespace Tests

open Solcore.ContractRuntime

example {checkpointWorld workingWorld : WorldState}
    {target : Address} {contract : CheckedCoreContract}
    (installed :
      InstalledCheckedCoreContract workingWorld target contract) :
    (TopLevelExecution.preparedContext
      (checkpointWorld := checkpointWorld) installed).context.storageAddress =
        target :=
  TopLevelExecution.preparedContext_storageAddress installed

example {checkpointWorld workingWorld : WorldState}
    {target : Address} {contract : CheckedCoreContract}
    (installed :
      InstalledCheckedCoreContract workingWorld target contract) :
    (TopLevelExecution.preparedContext
      (checkpointWorld := checkpointWorld) installed).storageAccount =
        installed.account :=
  TopLevelExecution.preparedContext_storageAccount installed

example {checkpointWorld workingWorld : WorldState}
    {target : Address} {contract : CheckedCoreContract}
    (installed :
      InstalledCheckedCoreContract workingWorld target contract) :
    (TopLevelExecution.preparedContext
      (checkpointWorld := checkpointWorld) installed).context.values.checkpoint.state =
        checkpointWorld :=
  TopLevelExecution.preparedContext_checkpointState installed

example {checkpointWorld workingWorld : WorldState}
    {target : Address} {contract : CheckedCoreContract}
    (installed :
      InstalledCheckedCoreContract workingWorld target contract) :
    (TopLevelExecution.preparedContext
      (checkpointWorld := checkpointWorld) installed).context.values.working.1 =
        workingWorld :=
  TopLevelExecution.preparedContext_workingState installed

example {checkpointWorld workingWorld : WorldState}
    {target : Address} {contract : CheckedCoreContract}
    (installed :
      InstalledCheckedCoreContract workingWorld target contract) :
    (TopLevelExecution.preparedContext
      (checkpointWorld := checkpointWorld) installed).context.values.checkpoint.effects =
        TopLevelExecution.initialEffects :=
  TopLevelExecution.preparedContext_checkpointEffects installed

example {checkpointWorld workingWorld : WorldState}
    {target : Address} {contract : CheckedCoreContract}
    (installed :
      InstalledCheckedCoreContract workingWorld target contract) :
    (TopLevelExecution.preparedContext
      (checkpointWorld := checkpointWorld) installed).context.values.working.2 =
        TopLevelExecution.initialEffects :=
  TopLevelExecution.preparedContext_workingEffects installed

end Tests
end

section
-- leanmerge: from Solcore.Test.Adr0147ValueCallBoundary
/-! External and executable regressions for the ADR-0147 value-call boundary. -/

set_option autoImplicit false

namespace Tests.Adr0147ValueCallBoundary

open Solcore.Core
open Solcore.ContractRuntime

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

/-! Public boundary laws remain usable outside their defining namespaces. -/
example := HostFunction.parameterType_callContractWordWithValue
example := HostFunction.resultType_callContractWordWithValue
example := HostFunction.index_callContractWordWithValue
example := hostContext_callContractWordWithValue
example := hostEnvironment_callContractWordWithValue
example := HostRequest.responseType_callContractWordWithValue
example := HostRequest.responseValue_callContractWordWithValue
example := HostSuspension.resume_callContractWordWithValue
example := hostAdvance_begin_callContractWordWithValue
example := hostAdvance_suspend_callContractWordWithValue
example := hostAdvance_invalid_callContractWordWithValue_argument
example := @HostRuntimeValueHasType.wordTriple_shape
example := @typed_callContractWordWithValue_emits

example := ContractCallFailure.code_insufficientBalance
example := ContractCallFailure.code_balanceOverflow
example := BalanceTransferFailure.toContractCallFailure_senderAbsent
example := BalanceTransferFailure.toContractCallFailure_recipientAbsent
example := BalanceTransferFailure.toContractCallFailure_insufficientBalance
example := BalanceTransferFailure.toContractCallFailure_recipientOverflow
example := BalanceTransferFailure.toContractCallResult_code

example := TopLevelInvocation.childWordWithValue_target
example := TopLevelInvocation.childWordWithValue_caller
example := TopLevelInvocation.childWordWithValue_callValue
example := TopLevelInvocation.childWordWithValue_inputBytes
example := TopLevelInvocation.childWordWithValue_executionInputs

private def targetWord : Word := ⟨0x1234, by decide⟩
private def targetAddress : Address := ⟨0x1234, by decide⟩
private def transferredValue : Word := ⟨0x45, by decide⟩
private def input : Word := ⟨0x6789, by decide⟩
private def payload : Word := ⟨0xab, by decide⟩

private def valueCallProgram : Program := {
  resultType := ContractCallWordResult.resultType
  body :=
    .apply
      (.var HostFunction.callContractWordWithValue.index)
      (.pair (.word targetWord)
        (.pair (.word transferredValue) (.word input)))
}

private theorem valueCallProgram_checked :
    valueCallProgram.checkHost = true := by
  decide

private def valueCallCode : CheckedHostCoreProgram :=
  ⟨valueCallProgram, valueCallProgram_checked⟩

/-- The checker-accepted program emits the exact target/value/input request. -/
private def checkedValueCallEmitsAndResumes : Bool :=
  match valueCallCode.program.runHostStateful 32 with
  | .suspended
      ⟨.callContractWordWithValue actualTarget actualValue actualInput,
        continuation, store⟩
      remainingFuel =>
      actualTarget == targetWord && actualValue == transferredValue &&
        actualInput == input &&
        let suspension : HostSuspension :=
          ⟨.callContractWordWithValue actualTarget actualValue actualInput,
            continuation, store⟩
        match hostRun remainingFuel
            (suspension.resume (.returned payload)) with
        | .done result finalStore =>
            result == (ContractCallWordResult.returned payload).value &&
              finalStore == []
        | _ => false
  | _ => false

private theorem compileTimeCheckedValueCall :
    checkedValueCallEmitsAndResumes = true := by
  native_decide

private def insufficientCode : Word := ⟨3, by decide⟩
private def overflowCode : Word := ⟨4, by decide⟩

private def failureMappingExact : Bool :=
  ContractCallFailure.insufficientBalance.code == insufficientCode &&
    ContractCallFailure.balanceOverflow.code == overflowCode &&
    BalanceTransferFailure.insufficientBalance.toContractCallResult ==
      ContractCallWordResult.failed insufficientCode &&
    BalanceTransferFailure.recipientOverflow.toContractCallResult ==
      ContractCallWordResult.failed overflowCode

private theorem compileTimeFailureMapping : failureMappingExact = true := by
  native_decide

private def storageAddress : Address := ⟨0x20, by decide⟩
private def callerAddress : Address := ⟨0x30, by decide⟩
private def account : Account := Account.empty
private def world : WorldState :=
  WorldState.empty.putAccount storageAddress account

private def context : HostStorageDriver.Context Unit Unit :=
  ⟨⟨storageAddress,
      ⟨⟨world, ⟨(), ()⟩⟩, (world, ⟨(), ()⟩)⟩⟩,
    account,
    by rfl⟩

private def inputs : HostStorageDriver.ExecutionInputs := {
  codeAddress := storageAddress
  callValue := Word.zero
  callerAddress := callerAddress
  inputData := HostStorageDriver.InputData.ofWord input
  currentAddress := storageAddress
}

private def flatHandled :
    HostStorageDriver.Context Unit Unit × ContractCallWordResult :=
  HostStorageDriver.handleRequest inputs context
    (.callContractWordWithValue targetWord transferredValue input)

private theorem compileTimeFlatHandlerExact :
    flatHandled =
      (context, ContractCallFailure.depthExceeded.result) := by
  rfl

private def childInvocationExact : Bool :=
  let child := TopLevelInvocation.childWordWithValue
    inputs targetAddress transferredValue input
  child.target == targetAddress &&
    child.caller == inputs.currentAddress &&
    child.callValue == transferredValue &&
    child.inputData.bytes == encodeWordBytesBE input

private theorem compileTimeChildInvocationExact :
    childInvocationExact = true := by
  native_decide

def testAdr0147ValueCallBoundary : IO Unit := do
  assertTrue checkedValueCallEmitsAndResumes
    "checked value call did not preserve target/value/input order"
  assertTrue failureMappingExact
    "balance transfer failures did not use stable call failure codes"
  assertTrue
    (flatHandled.2 == ContractCallFailure.depthExceeded.result)
    "flat handler changed context or accepted nested value call"
  assertTrue childInvocationExact
    "value-bearing child invocation did not preserve caller or call value"

end Tests.Adr0147ValueCallBoundary
end
