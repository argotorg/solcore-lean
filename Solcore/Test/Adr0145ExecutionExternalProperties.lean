import Solcore.Semantics.TopLevelExecutionProperties
import Solcore.Semantics.TopLevelExecutionResumptionProperties

/-! External compile consumers for ADR-0145 finalization and resumption laws. -/

set_option autoImplicit false

namespace Tests.Adr0145ExecutionExternalProperties

open Solcore.Core
open Solcore.Semantics

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
