import Solcore.Semantics.ParentIndexedSelectedCheckedWordExecutionDelegationProperties
import Solcore.Semantics.ParentIndexedSelectedCheckedWordExecutionResumptionProperties

/-! Compile-only consumers for ADR-0144 provenance and resumption laws. -/

set_option autoImplicit false

namespace Solcore.Test.ParentIndexedSelectedCheckedWordExecutionProperties

open Semantics
open Semantics.ParentIndexedSelectedCheckedWordExecution

universe u v

variable {RollbackState : Type u} {Event : Type v}
variable {parentWorking :
  WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
variable (initialization : ParentIndexedFrameInitialization
  RollbackState Event parentWorking)
variable (storageAddress : Address)
variable (inputs : HostStorageDriver.ExecutionInputs)
variable (fuel additional first second : Nat)

abbrev Entry := ParentIndexedSelectedCheckedWordExecution
  initialization storageAddress inputs

variable (entry left right : Entry initialization storageAddress inputs)
variable (context : HostStorageDriver.Context
  RollbackState (FrameTrace Event))
variable (refined :
  initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
      storageAddress = some context)

example : start? initialization storageAddress inputs fuel = none ↔
    initialization.initialWorld.account? storageAddress = none :=
  start?_eq_none_iff initialization storageAddress inputs fuel

example : start? initialization storageAddress inputs fuel =
    some
      (ParentIndexedSelectedCheckedWordExecution.mk context refined
        (SelectedCheckedWordExecution.start context inputs fuel)) :=
  start?_of_present initialization storageAddress inputs fuel context refined

example :
    (start? initialization storageAddress inputs fuel).map toExecutionSigma =
      (initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
        storageAddress).map fun selected =>
          ⟨selected,
            SelectedCheckedWordExecution.start selected inputs fuel⟩ :=
  toExecutionSigma_start? initialization storageAddress inputs fuel

variable (initialContextEq : left.initialContext = right.initialContext)
variable (executionHeq : HEq left.execution right.execution)

example : left = right :=
  ext initialContextEq executionHeq

example : start? initialization storageAddress inputs fuel = some entry ↔
    entry.execution =
      SelectedCheckedWordExecution.start entry.initialContext inputs fuel :=
  start?_eq_some_iff initialization storageAddress inputs fuel entry

example : start? initialization storageAddress inputs
      entry.execution.providedFuel = some entry :=
  start?_canonical entry

example : entry.initialContext.context.values =
    initialization.toCheckpointedWorkingPair :=
  initialContext_values entry

example : entry.initialContext.context.storageAddress = storageAddress :=
  initialContext_storageAddress entry

example : entry.execution.selection =
    initialization.initialWorld.selectWordCode inputs.codeAddress :=
  selection_eq_initialWorld entry

example : entry.initialContext.context.values.checkpoint =
    FrameCheckpointSnapshot.fromWorkingPair parentWorking :=
  initialContext_checkpoint entry

example : entry.initialContext.context.values.working.2 =
    ⟨initialization.workingRollback, parentWorking.2.trace⟩ :=
  initialContext_workingEffects entry

example : entry.initialContext.context.values.working.2.rollback =
    initialization.workingRollback :=
  initialContext_workingRollback entry

example : entry.initialContext.context.values.working.2.trace =
    parentWorking.2.trace :=
  initialContext_parentTrace entry

example : (entry.resumeWithFuel additional).initialContext =
    entry.initialContext :=
  resumeWithFuel_initialContext entry additional

example : (entry.resumeWithFuel additional).execution =
    entry.execution.resumeWithFuel additional :=
  resumeWithFuel_execution entry additional

example : (entry.resumeWithFuel additional).execution.providedFuel =
    entry.execution.providedFuel + additional :=
  resumeWithFuel_providedFuel entry additional

example : (entry.resumeWithFuel additional).execution.selection =
    entry.execution.selection :=
  resumeWithFuel_selection entry additional

example : some (entry.resumeWithFuel additional) =
    start? initialization storageAddress inputs
      (entry.execution.providedFuel + additional) :=
  some_resumeWithFuel_eq_start? entry additional

example : (start? initialization storageAddress inputs fuel).map
      (fun selected => selected.resumeWithFuel additional) =
    start? initialization storageAddress inputs (fuel + additional) :=
  start?_map_resumeWithFuel initialization storageAddress inputs
    fuel additional

example : entry.resumeWithFuel 0 = entry :=
  resumeWithFuel_zero entry

example : (entry.resumeWithFuel first).resumeWithFuel second =
    entry.resumeWithFuel (first + second) :=
  resumeWithFuel_add entry first second

example : (entry.resumeWithFuel additional).execution.completion? =
    (SelectedCheckedWordExecution.start entry.initialContext inputs
      (entry.execution.providedFuel + additional)).completion? :=
  completion?_resumeWithFuel entry additional

variable (completion :
  WordReturnedFrameCompletion RollbackState (FrameTrace Event))
variable (completed : entry.execution.completion? = some completion)

example : (entry.resumeWithFuel additional).execution.completion? =
    some completion :=
  completion?_resumeWithFuel_of_some entry additional completion completed

example : entry.execution.execution? = none ↔
    entry.execution.selection = .codeAbsent ∨
      ∃ code resultTypeNe,
        entry.execution.selection = .nonWord code resultTypeNe :=
  execution?_eq_none_iff_branches entry

example : entry.execution.completion? = some completion ↔
    ∃ code,
      entry.execution.execution? =
        some (code, completion.toHostDriverResult) :=
  completion?_eq_some_iff entry completion

example : entry.execution.completion? = none ↔
    entry.execution.execution? = none ∨
      (∃ code finalContext exhausted,
        entry.execution.execution? =
          some (code, ⟨finalContext, .outOfFuel exhausted⟩)) ∨
      ∃ code finalContext suspension remainingFuel,
        entry.execution.execution? =
          some (code,
            ⟨finalContext, .unsupported suspension remainingFuel⟩) :=
  completion?_eq_none_iff entry

end Solcore.Test.ParentIndexedSelectedCheckedWordExecutionProperties
