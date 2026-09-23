import Solcore.ContractRuntime.FrameContinuationContextFromCheckpointedWorkingPair
import Solcore.ContractRuntime.HostDriver
import Solcore.ContractRuntime.HostStorageContext
import Solcore.ContractRuntime.ParentIndexedFrameContinuationConstruction
import Solcore.ContractRuntime.ParentIndexedFrameInitialization
import Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccountCodeExecution
import Solcore.ContractRuntime.HostStorageDriver
import Solcore.ContractRuntime.ParentIndexedFrameResolutionFold

/-! Parent-indexed selected execution, initialization, resumption, and session laws. -/

/-!
## Consolidated module: `Solcore.ContractRuntime.ParentIndexedSelectedExecutionResult`
-/

/-! Branch-complete results for parent-indexed selected execution. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

universe u v w

/--
Every branch of parent-indexed selected execution. Exhaustion and fault retain
the exact driver state; completion also retains its canonical parent context.
-/
inductive ParentIndexedSelectedExecutionResult
    (RollbackState : Type u) (Event : Type v) (TrapReason : Type w)
    (parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)) where
  | storageAbsent
  | codeAbsent
  | outOfFuel
      (context : HostStorageDriver.Context RollbackState (FrameTrace Event))
      (state : Core.State)
  | fault
      (context : HostStorageDriver.Context RollbackState (FrameTrace Event))
      (error : Core.MachineFault)
      (state : Core.State)
  | unsupported
      (context : HostStorageDriver.Context RollbackState (FrameTrace Event))
      (suspension : Core.HostSuspension)
      (remainingFuel : Nat)
  | completed
      (context : HostStorageDriver.Context RollbackState (FrameTrace Event))
      (value : Core.Value)
      (store : Core.Store)
      (continuation : ParentIndexedFrameContinuationContext
        RollbackState Event TrapReason parentWorking)

namespace ParentIndexedSelectedExecutionResult

variable {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
variable {parentWorking :
  WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}

/-- Short name for a result at one fixed parent working pair. -/
abbrev Result
    (RollbackState : Type u) (Event : Type v) (TrapReason : Type w)
    (parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)) :=
  ParentIndexedSelectedExecutionResult
    RollbackState Event TrapReason parentWorking

/-- Canonical completed parent context built from an exact driver result. -/
def completedContinuation
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    (context : HostStorageDriver.Context RollbackState (FrameTrace Event))
    (value : Core.Value)
    (store : Core.Store) :
    ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking :=
  ParentIndexedFrameContinuationContext.fromTraceExtension
    parentWorking initialization.workingRollback
    initialization.initialTraceExtension
    (FrameContinuationContext.fromCheckpointedWorkingPair
      context.context.values (doneOutcome context value store)).result

/-- Classify every terminal shape of an exact handled-driver result. -/
def classify
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    (result : HostDriverResult
      (HostStorageDriver.Context RollbackState (FrameTrace Event))) :
    Result RollbackState Event TrapReason parentWorking :=
  match result with
  | ⟨context, .done value store⟩ =>
      .completed context value store
        (completedContinuation initialization doneOutcome context value store)
  | ⟨context, .outOfFuel state⟩ => .outOfFuel context state
  | ⟨context, .fault error state⟩ => .fault context error state
  | ⟨context, .unsupported suspension remainingFuel⟩ =>
      .unsupported context suspension remainingFuel

@[simp] theorem classify_done
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    (context : HostStorageDriver.Context RollbackState (FrameTrace Event))
    (value : Core.Value)
    (store : Core.Store) :
    classify initialization doneOutcome ⟨context, .done value store⟩ =
      .completed context value store
        (completedContinuation initialization doneOutcome context value store) :=
  rfl

@[simp] theorem classify_outOfFuel
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    (context : HostStorageDriver.Context RollbackState (FrameTrace Event))
    (state : Core.State) :
    classify initialization doneOutcome ⟨context, .outOfFuel state⟩ =
      .outOfFuel context state :=
  rfl

@[simp] theorem classify_fault
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    (context : HostStorageDriver.Context RollbackState (FrameTrace Event))
    (error : Core.MachineFault)
    (state : Core.State) :
    classify initialization doneOutcome ⟨context, .fault error state⟩ =
      .fault context error state :=
  rfl

@[simp] theorem classify_unsupported
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    (context : HostStorageDriver.Context RollbackState (FrameTrace Event))
    (suspension : Core.HostSuspension)
    (remainingFuel : Nat) :
    classify initialization doneOutcome
        ⟨context, .unsupported suspension remainingFuel⟩ =
      .unsupported context suspension remainingFuel :=
  rfl

end ParentIndexedSelectedExecutionResult

end Solcore.ContractRuntime

/-!
## Consolidated module: `Solcore.ContractRuntime.ParentIndexedFrameInitializationSelectedExecution`
-/

/-! Total parent-indexed selection into the branch-complete result. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ParentIndexedFrameInitialization

universe u v w

open ParentIndexedSelectedExecutionResult

/--
Refine storage, select code, and retain every handled execution branch.
-/
def runCodeWithStorageParentIndexedResult
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason) :
    ParentIndexedSelectedExecutionResult
      RollbackState Event TrapReason parentWorking :=
  match initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
      storageAddress with
  | none => .storageAbsent
  | some context =>
      match context.runCodeWithStorage? inputs fuel with
      | none => .codeAbsent
      | some result => classify initialization doneOutcome result

end Solcore.ContractRuntime.ParentIndexedFrameInitialization

/-!
## Consolidated module: `Solcore.ContractRuntime.ParentIndexedFrameInitializationSelectedExecutionProperties`
-/

/-! Exact branch laws for branch-complete parent-indexed execution. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ParentIndexedFrameInitialization

universe u v w

open ParentIndexedSelectedExecutionResult

variable {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
variable {parentWorking :
  WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}

@[simp] theorem runCodeWithStorageParentIndexedResult_eq_storageAbsent_iff
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason) :
    initialization.runCodeWithStorageParentIndexedResult
        storageAddress inputs fuel doneOutcome = .storageAbsent ↔
      initialization.initialWorld.account? storageAddress = none := by
  cases observed : initialization.initialWorld.account? storageAddress with
  | none =>
      unfold runCodeWithStorageParentIndexedResult
      rw [toCheckpointedWorkingPairWithPresentStorageAccount?_of_absent
        initialization storageAddress observed]
      simp
  | some account =>
      unfold runCodeWithStorageParentIndexedResult
      rw [toCheckpointedWorkingPairWithPresentStorageAccount?_of_present
        initialization storageAddress account observed]
      simp only
      let context : HostStorageDriver.Context
          RollbackState (FrameTrace Event) :=
        ⟨initialization.toCheckpointedWorkingPairWithStorageAddress
            storageAddress,
          account,
          observed⟩
      cases execution : context.runCodeWithStorage? inputs fuel with
      | none => simp
      | some result =>
          cases result with
          | mk finalContext outcome => cases outcome <;> simp [classify]

theorem runCodeWithStorageParentIndexedResult_eq_codeAbsent_iff
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason) :
    initialization.runCodeWithStorageParentIndexedResult
        storageAddress inputs fuel doneOutcome = .codeAbsent ↔
      ∃ context,
        initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
            storageAddress = some context ∧
        context.context.values.working.1.code? inputs.codeAddress = none := by
  unfold runCodeWithStorageParentIndexedResult
  cases refined :
      initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
        storageAddress with
  | none => simp
  | some context =>
      simp only
      cases execution : context.runCodeWithStorage? inputs fuel with
      | none =>
          have codeAbsent :=
            (FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorage?_eq_none_iff
              context inputs fuel).mp execution
          simp [codeAbsent]
      | some result =>
          have codePresent :
              context.context.values.working.1.code? inputs.codeAddress ≠ none := by
            intro codeAbsent
            have absentRun :=
              (FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorage?_eq_none_iff
                context inputs fuel).mpr codeAbsent
            rw [execution] at absentRun
            contradiction
          cases result with
          | mk finalContext outcome =>
              cases outcome <;> simp [classify, codePresent]

theorem runCodeWithStorageParentIndexedResult_eq_outOfFuel_iff
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    (finalContext :
      HostStorageDriver.Context RollbackState (FrameTrace Event))
    (state : Core.State) :
    initialization.runCodeWithStorageParentIndexedResult
        storageAddress inputs fuel doneOutcome =
      .outOfFuel finalContext state ↔
    ∃ context,
      initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
          storageAddress = some context ∧
      context.runCodeWithStorage? inputs fuel =
        some ⟨finalContext, .outOfFuel state⟩ := by
  unfold runCodeWithStorageParentIndexedResult
  cases refined :
      initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
        storageAddress with
  | none => simp
  | some context =>
      simp only
      cases execution : context.runCodeWithStorage? inputs fuel with
      | none => simp [execution]
      | some result =>
          cases result with
          | mk resultContext outcome =>
              cases outcome <;> simp [classify, execution, eq_comm]

theorem runCodeWithStorageParentIndexedResult_eq_fault_iff
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    (finalContext :
      HostStorageDriver.Context RollbackState (FrameTrace Event))
    (error : Core.MachineFault)
    (state : Core.State) :
    initialization.runCodeWithStorageParentIndexedResult
        storageAddress inputs fuel doneOutcome =
      .fault finalContext error state ↔
    ∃ context,
      initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
          storageAddress = some context ∧
      context.runCodeWithStorage? inputs fuel =
        some ⟨finalContext, .fault error state⟩ := by
  unfold runCodeWithStorageParentIndexedResult
  cases refined :
      initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
        storageAddress with
  | none => simp
  | some context =>
      simp only
      cases execution : context.runCodeWithStorage? inputs fuel with
      | none => simp [execution]
      | some result =>
          cases result with
          | mk resultContext outcome =>
              cases outcome <;> simp [classify, execution]

theorem runCodeWithStorageParentIndexedResult_eq_unsupported_iff
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    (finalContext :
      HostStorageDriver.Context RollbackState (FrameTrace Event))
    (suspension : Core.HostSuspension)
    (remainingFuel : Nat) :
    initialization.runCodeWithStorageParentIndexedResult
        storageAddress inputs fuel doneOutcome =
      .unsupported finalContext suspension remainingFuel ↔
    ∃ context,
      initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
          storageAddress = some context ∧
      context.runCodeWithStorage? inputs fuel =
        some ⟨finalContext, .unsupported suspension remainingFuel⟩ := by
  unfold runCodeWithStorageParentIndexedResult
  cases refined :
      initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
        storageAddress with
  | none => simp
  | some context =>
      simp only
      cases execution : context.runCodeWithStorage? inputs fuel with
      | none => simp [execution]
      | some result =>
          cases result with
          | mk resultContext outcome =>
              cases outcome <;> simp [classify, execution]

theorem runCodeWithStorageParentIndexedResult_eq_completed_iff
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    (finalContext :
      HostStorageDriver.Context RollbackState (FrameTrace Event))
    (value : Core.Value)
    (store : Core.Store)
    (continuation : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking) :
    initialization.runCodeWithStorageParentIndexedResult
        storageAddress inputs fuel doneOutcome =
      .completed finalContext value store continuation ↔
    ∃ context,
      initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
          storageAddress = some context ∧
      context.runCodeWithStorage? inputs fuel =
        some ⟨finalContext, .done value store⟩ ∧
      continuation = completedContinuation
        initialization doneOutcome finalContext value store := by
  unfold runCodeWithStorageParentIndexedResult
  cases refined :
      initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
        storageAddress with
  | none => simp
  | some context =>
      simp only
      cases execution : context.runCodeWithStorage? inputs fuel with
      | none => simp [execution]
      | some result =>
          cases result with
          | mk resultContext outcome =>
              cases outcome with
              | done resultValue resultStore =>
                  simp [classify, execution, eq_comm, and_assoc]
                  intro contextEq valueEq storeEq
                  cases contextEq
                  cases valueEq
                  cases storeEq
                  rfl
              | outOfFuel state => simp [classify, execution]
              | fault error state => simp [classify, execution]
              | unsupported suspension remainingFuel =>
                  simp [classify, execution]

theorem runCodeWithStorageParentIndexedResult_ne_fault
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    (finalContext :
      HostStorageDriver.Context RollbackState (FrameTrace Event))
    (error : Core.MachineFault)
    (state : Core.State) :
    initialization.runCodeWithStorageParentIndexedResult
        storageAddress inputs fuel doneOutcome ≠
      .fault finalContext error state := by
  intro fault
  obtain ⟨context, _refined, execution⟩ :=
    (runCodeWithStorageParentIndexedResult_eq_fault_iff
      initialization storageAddress inputs fuel doneOutcome
      finalContext error state).mp fault
  exact
    FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorage?_ne_some_fault
      context inputs fuel finalContext error state execution

end Solcore.ContractRuntime.ParentIndexedFrameInitialization

/-!
## Consolidated module: `Solcore.ContractRuntime.ParentIndexedSelectedExecutionCompatibility`
-/

/-! Lossy compatibility erasure for branch-complete selected execution. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ParentIndexedSelectedExecutionResult

universe u v w

variable {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
variable {parentWorking :
  WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}

/-- Reproduce the legacy three-`Option` observation exactly. -/
def toLegacy : Result RollbackState Event TrapReason parentWorking →
    Option (Option (Option (ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)))
  | .storageAbsent => none
  | .codeAbsent => some none
  | .outOfFuel _ _ => some (some none)
  | .fault _ _ _ => some (some none)
  | .unsupported _ _ _ => some (some none)
  | .completed _ _ _ continuation => some (some (some continuation))

@[simp] theorem toLegacy_storageAbsent :
    (storageAbsent : Result
      RollbackState Event TrapReason parentWorking).toLegacy = none :=
  rfl

@[simp] theorem toLegacy_codeAbsent :
    (codeAbsent : Result
      RollbackState Event TrapReason parentWorking).toLegacy = some none :=
  rfl

@[simp] theorem toLegacy_outOfFuel
    (context : HostStorageDriver.Context RollbackState (FrameTrace Event))
    (state : Core.State) :
    (outOfFuel context state : Result
      RollbackState Event TrapReason parentWorking).toLegacy =
      some (some none) :=
  rfl

@[simp] theorem toLegacy_fault
    (context : HostStorageDriver.Context RollbackState (FrameTrace Event))
    (error : Core.MachineFault)
    (state : Core.State) :
    (fault context error state : Result
      RollbackState Event TrapReason parentWorking).toLegacy =
      some (some none) :=
  rfl

@[simp] theorem toLegacy_unsupported
    (context : HostStorageDriver.Context RollbackState (FrameTrace Event))
    (suspension : Core.HostSuspension)
    (remainingFuel : Nat) :
    (unsupported context suspension remainingFuel : Result
      RollbackState Event TrapReason parentWorking).toLegacy =
      some (some none) :=
  rfl

@[simp] theorem toLegacy_completed
    (context : HostStorageDriver.Context RollbackState (FrameTrace Event))
    (value : Core.Value)
    (store : Core.Store)
    (continuation : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking) :
    (completed context value store continuation : Result
      RollbackState Event TrapReason parentWorking).toLegacy =
      some (some (some continuation)) :=
  rfl

end Solcore.ContractRuntime.ParentIndexedSelectedExecutionResult

/-!
## Consolidated module: `Solcore.ContractRuntime.ParentIndexedSelectedExecutionCompatibilityProperties`
-/

/-! Exact compatibility with the existing nested-option parent entry point. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ParentIndexedFrameInitialization

universe u v w

open ParentIndexedSelectedExecutionResult

/-- Erasing a branch-complete run gives the unchanged legacy result exactly. -/
theorem runCodeWithStorageParentIndexedResult_toLegacy
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason) :
    (initialization.runCodeWithStorageParentIndexedResult
      storageAddress inputs fuel doneOutcome).toLegacy =
      initialization.runCodeWithStorageParentIndexedContinuationContext?
        storageAddress inputs fuel doneOutcome := by
  unfold runCodeWithStorageParentIndexedResult
  unfold runCodeWithStorageParentIndexedContinuationContext?
  cases initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
      storageAddress with
  | none => rfl
  | some context =>
      simp only [Option.map_some]
      unfold FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorageContinuationContext?
      cases context.runCodeWithStorage? inputs fuel with
      | none => rfl
      | some result =>
          cases result with
          | mk finalContext outcome => cases outcome <;> rfl

end Solcore.ContractRuntime.ParentIndexedFrameInitialization

/-!
## Consolidated module: `Solcore.ContractRuntime.ParentIndexedSelectedExecutionResumption`
-/

/-! Fuel continuation for branch-complete selected execution. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ParentIndexedSelectedExecutionResult

universe u v w

variable {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
variable {parentWorking :
  WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}

/--
Continue only retained exhaustion. Unsupported requests remain suspended and
only accumulate offered fuel; they are never passed to the rejecting handler.
Absence, raw fault, and completion are terminal identities.
-/
def resumeWithFuel
    (result : Result RollbackState Event TrapReason parentWorking)
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (inputs : HostStorageDriver.ExecutionInputs)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    (additional : Nat) :
    Result RollbackState Event TrapReason parentWorking :=
  match result with
  | .outOfFuel context state =>
      classify initialization doneOutcome
        (HostStorageDriver.run context inputs additional state)
  | .unsupported context suspension remainingFuel =>
      .unsupported context suspension (remainingFuel + additional)
  | terminal => terminal

@[simp] theorem resumeWithFuel_storageAbsent
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (inputs : HostStorageDriver.ExecutionInputs)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    (additional : Nat) :
    resumeWithFuel (.storageAbsent : Result
        RollbackState Event TrapReason parentWorking)
        initialization inputs doneOutcome additional = .storageAbsent :=
  rfl

@[simp] theorem resumeWithFuel_codeAbsent
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (inputs : HostStorageDriver.ExecutionInputs)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    (additional : Nat) :
    resumeWithFuel (.codeAbsent : Result
        RollbackState Event TrapReason parentWorking)
        initialization inputs doneOutcome additional = .codeAbsent :=
  rfl

@[simp] theorem resumeWithFuel_outOfFuel
    (context : HostStorageDriver.Context RollbackState (FrameTrace Event))
    (state : Core.State)
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (inputs : HostStorageDriver.ExecutionInputs)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    (additional : Nat) :
    resumeWithFuel (.outOfFuel context state)
        initialization inputs doneOutcome additional =
      classify initialization doneOutcome
        (HostStorageDriver.run context inputs additional state) :=
  rfl

@[simp] theorem resumeWithFuel_fault
    (context : HostStorageDriver.Context RollbackState (FrameTrace Event))
    (error : Core.MachineFault)
    (state : Core.State)
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (inputs : HostStorageDriver.ExecutionInputs)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    (additional : Nat) :
    resumeWithFuel (.fault context error state)
        initialization inputs doneOutcome additional =
      .fault context error state :=
  rfl

@[simp] theorem resumeWithFuel_unsupported
    (context : HostStorageDriver.Context RollbackState (FrameTrace Event))
    (suspension : Core.HostSuspension)
    (remainingFuel : Nat)
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (inputs : HostStorageDriver.ExecutionInputs)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    (additional : Nat) :
    resumeWithFuel (.unsupported context suspension remainingFuel)
        initialization inputs doneOutcome additional =
      .unsupported context suspension (remainingFuel + additional) :=
  rfl

@[simp] theorem resumeWithFuel_completed
    (context : HostStorageDriver.Context RollbackState (FrameTrace Event))
    (value : Core.Value)
    (store : Core.Store)
    (continuation : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (inputs : HostStorageDriver.ExecutionInputs)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    (additional : Nat) :
    resumeWithFuel (.completed context value store continuation)
        initialization inputs doneOutcome additional =
      .completed context value store continuation :=
  rfl

end Solcore.ContractRuntime.ParentIndexedSelectedExecutionResult

/-!
## Consolidated module: `Solcore.ContractRuntime.ParentIndexedSelectedExecutionResumptionProperties`
-/

/-! Algebra and exact inversion for branch-complete resumption. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ParentIndexedSelectedExecutionResult

universe u v w

variable {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
variable {parentWorking :
  WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}

/-- Classifying before or after generic resumption gives the same result. -/
theorem resumeWithFuel_classify
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (inputs : HostStorageDriver.ExecutionInputs)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    (result : HostDriverResult
      (HostStorageDriver.Context RollbackState (FrameTrace Event)))
    (additional : Nat) :
    resumeWithFuel (classify initialization doneOutcome result)
        initialization inputs doneOutcome additional =
      classify initialization doneOutcome
        (result.resumeWithFuel
          (@HostStorageDriver.handler RollbackState (FrameTrace Event) inputs)
          additional) := by
  cases result with
  | mk context outcome => cases outcome <;> rfl

/-- Sequential additions associate under one fixed initialization and policy. -/
theorem resumeWithFuel_add
    (result : Result RollbackState Event TrapReason parentWorking)
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (inputs : HostStorageDriver.ExecutionInputs)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    (first second : Nat) :
    resumeWithFuel
        (resumeWithFuel result initialization inputs doneOutcome first)
        initialization inputs doneOutcome second =
      resumeWithFuel result initialization inputs doneOutcome
        (first + second) := by
  cases result with
  | storageAbsent => rfl
  | codeAbsent => rfl
  | fault context error state => rfl
  | unsupported context suspension remainingFuel =>
      simp only [resumeWithFuel_unsupported]
      rw [Nat.add_assoc]
  | completed context value store continuation => rfl
  | outOfFuel context state =>
      rw [resumeWithFuel, resumeWithFuel_classify]
      change classify initialization doneOutcome
          ((HostStorageDriver.run context inputs first state).resumeWithFuel
            (@HostStorageDriver.handler RollbackState (FrameTrace Event) inputs)
            second) =
        classify initialization doneOutcome
          (HostStorageDriver.run context inputs (first + second) state)
      rw [HostStorageDriver.resumeWithFuel_run]

/-- Exact completion inversion from one retained exhausted context and state. -/
theorem resumeWithFuel_outOfFuel_eq_completed_iff
    (context : HostStorageDriver.Context RollbackState (FrameTrace Event))
    (state : Core.State)
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (inputs : HostStorageDriver.ExecutionInputs)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    (additional : Nat)
    (finalContext :
      HostStorageDriver.Context RollbackState (FrameTrace Event))
    (value : Core.Value)
    (store : Core.Store)
    (continuation : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking) :
    resumeWithFuel (.outOfFuel context state)
        initialization inputs doneOutcome additional =
      .completed finalContext value store continuation ↔
    HostStorageDriver.run context inputs additional state =
        ⟨finalContext, .done value store⟩ ∧
      continuation = completedContinuation
        initialization doneOutcome finalContext value store := by
  simp only [resumeWithFuel_outOfFuel]
  cases execution : HostStorageDriver.run context inputs additional state with
  | mk resultContext outcome =>
      cases outcome with
      | done resultValue resultStore =>
          simp [classify, eq_comm, and_assoc]
          intro contextEq valueEq storeEq
          cases contextEq
          cases valueEq
          cases storeEq
          rfl
      | outOfFuel exhausted => simp [classify]
      | fault error faultState => simp [classify]
      | unsupported suspension remainingFuel => simp [classify]

end Solcore.ContractRuntime.ParentIndexedSelectedExecutionResult

/-!
## Consolidated module: `Solcore.ContractRuntime.ParentIndexedFrameInitializationSelectedExecutionResumptionProperties`
-/

/-! Split and summed-budget laws for actual parent-indexed selected runs. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ParentIndexedFrameInitialization

universe u v w

open ParentIndexedSelectedExecutionResult

/-- Resuming an actual selected run is exactly one run at summed fuel. -/
theorem runCodeWithStorageParentIndexedResult_resumeWithFuel
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel additional : Nat)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason) :
    (initialization.runCodeWithStorageParentIndexedResult
      storageAddress inputs fuel doneOutcome).resumeWithFuel
        initialization inputs doneOutcome additional =
      initialization.runCodeWithStorageParentIndexedResult
        storageAddress inputs (fuel + additional) doneOutcome := by
  unfold runCodeWithStorageParentIndexedResult
  cases refined :
      initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
        storageAddress with
  | none => rfl
  | some context =>
      cases selected : context.context.values.working.1.code?
          inputs.codeAddress with
      | none =>
          simp [FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorage?,
            selected]
      | some code =>
          simp only [FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorage?,
            selected, Option.map_some]
          rw [ParentIndexedSelectedExecutionResult.resumeWithFuel_classify]
          rw [CheckedHostCoreProgram.runWithStorage_resumeWithFuel]

/-- Zero additional fuel is an identity for every actual selected run. -/
@[simp] theorem runCodeWithStorageParentIndexedResult_resumeWithFuel_zero
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason) :
    (initialization.runCodeWithStorageParentIndexedResult
      storageAddress inputs fuel doneOutcome).resumeWithFuel
        initialization inputs doneOutcome 0 =
      initialization.runCodeWithStorageParentIndexedResult
        storageAddress inputs fuel doneOutcome := by
  simpa using runCodeWithStorageParentIndexedResult_resumeWithFuel
    initialization storageAddress inputs fuel 0 doneOutcome

/-- Two additions after an actual run retain its selector and exact policy. -/
theorem runCodeWithStorageParentIndexedResult_resumeWithFuel_add
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel first second : Nat)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason) :
    ((initialization.runCodeWithStorageParentIndexedResult
        storageAddress inputs fuel doneOutcome).resumeWithFuel
          initialization inputs doneOutcome first).resumeWithFuel
        initialization inputs doneOutcome second =
      initialization.runCodeWithStorageParentIndexedResult
        storageAddress inputs (fuel + (first + second)) doneOutcome := by
  rw [ParentIndexedSelectedExecutionResult.resumeWithFuel_add]
  exact runCodeWithStorageParentIndexedResult_resumeWithFuel
    initialization storageAddress inputs fuel (first + second) doneOutcome

/-- Resuming an actual checked selected run cannot expose a raw fault. -/
theorem runCodeWithStorageParentIndexedResult_resumeWithFuel_ne_fault
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel additional : Nat)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    (finalContext :
      HostStorageDriver.Context RollbackState (FrameTrace Event))
    (error : Core.MachineFault)
    (state : Core.State) :
    (initialization.runCodeWithStorageParentIndexedResult
      storageAddress inputs fuel doneOutcome).resumeWithFuel
        initialization inputs doneOutcome additional ≠
      .fault finalContext error state := by
  rw [runCodeWithStorageParentIndexedResult_resumeWithFuel]
  exact runCodeWithStorageParentIndexedResult_ne_fault
    initialization storageAddress inputs (fuel + additional) doneOutcome
      finalContext error state

end Solcore.ContractRuntime.ParentIndexedFrameInitialization

/-!
## Consolidated module: `Solcore.ContractRuntime.ParentIndexedSelectedExecutionContinuationCoherenceProperties`
-/

/-! Completed continuation coherence for branch-complete selected execution. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ParentIndexedFrameInitialization

universe u v w

open ParentIndexedSelectedExecutionResult

/--
The canonical completed parent context forgets to the exact plain context from
the final driver values. This uses actual refinement and execution evidence.
-/
theorem completedContinuation_toFrameContinuationContext
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs)
    (initialContext finalContext :
      HostStorageDriver.Context RollbackState (FrameTrace Event))
    (refined :
      initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
          storageAddress = some initialContext)
    (fuel : Nat)
    (value : Core.Value)
    (store : Core.Store)
    (execution :
      initialContext.runCodeWithStorage? inputs fuel =
        some ⟨finalContext, .done value store⟩)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason) :
    (completedContinuation initialization doneOutcome
      finalContext value store).toFrameContinuationContext =
      FrameContinuationContext.fromCheckpointedWorkingPair
        finalContext.context.values
        (doneOutcome finalContext value store) := by
  have initialValues :
      initialContext.context.values = initialization.toCheckpointedWorkingPair := by
    unfold toCheckpointedWorkingPairWithPresentStorageAccount? at refined
    unfold FrameCheckpointedWorkingPairWithStorageAddress.withPresentStorageAccount?
      at refined
    split at refined
    · contradiction
    · have exactContext := Option.some.inj refined
      subst initialContext
      rfl
  have checkpointPreserved :=
    FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorage?_some_checkpoint
      initialContext inputs fuel
      (HostDriverResult.mk finalContext (.done value store)) execution
  have effectsPreserved :=
    FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorage?_some_workingEffects
      initialContext inputs fuel
      (HostDriverResult.mk finalContext (.done value store)) execution
  have finalCheckpoint :
      finalContext.context.values.checkpoint =
        FrameCheckpointSnapshot.fromWorkingPair parentWorking := by
    rw [checkpointPreserved, initialValues, toCheckpointedWorkingPair_eq]
  have finalEffects :
      finalContext.context.values.working.2 =
        ⟨initialization.workingRollback, parentWorking.2.trace⟩ := by
    rw [effectsPreserved, initialValues, toCheckpointedWorkingPair_eq]
  unfold completedContinuation
  unfold ParentIndexedFrameContinuationContext.fromTraceExtension
  unfold FrameContinuationContext.fromCheckpointedWorkingPair
  simp only [initialTraceExtension_toTrace]
  rw [finalCheckpoint, finalEffects]
  rfl

/-- An actual completed producer exposes its exact final plain context. -/
theorem runCodeWithStorageParentIndexedResult_completed_toFrameContinuationContext
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    (finalContext :
      HostStorageDriver.Context RollbackState (FrameTrace Event))
    (value : Core.Value)
    (store : Core.Store)
    (continuation : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (completed :
      initialization.runCodeWithStorageParentIndexedResult
          storageAddress inputs fuel doneOutcome =
        .completed finalContext value store continuation) :
    continuation.toFrameContinuationContext =
      FrameContinuationContext.fromCheckpointedWorkingPair
        finalContext.context.values
        (doneOutcome finalContext value store) := by
  obtain ⟨initialContext, refined, execution, continuationEq⟩ :=
    (runCodeWithStorageParentIndexedResult_eq_completed_iff
      initialization storageAddress inputs fuel doneOutcome finalContext
      value store continuation).mp completed
  subst continuation
  exact completedContinuation_toFrameContinuationContext
    initialization storageAddress inputs initialContext finalContext refined
    fuel value store execution doneOutcome

/-- The legacy API exposes the same proof-bearing completed continuation. -/
theorem runCodeWithStorageParentIndexedResult_completed_toLegacy
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    (finalContext :
      HostStorageDriver.Context RollbackState (FrameTrace Event))
    (value : Core.Value)
    (store : Core.Store)
    (continuation : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (completed :
      initialization.runCodeWithStorageParentIndexedResult
          storageAddress inputs fuel doneOutcome =
        .completed finalContext value store continuation) :
    initialization.runCodeWithStorageParentIndexedContinuationContext?
        storageAddress inputs fuel doneOutcome =
      some (some (some continuation)) := by
  calc
    _ = (initialization.runCodeWithStorageParentIndexedResult
          storageAddress inputs fuel doneOutcome).toLegacy :=
        (runCodeWithStorageParentIndexedResult_toLegacy
          initialization storageAddress inputs fuel doneOutcome).symm
    _ = some (some (some continuation)) := by rw [completed]; rfl

end Solcore.ContractRuntime.ParentIndexedFrameInitialization

/-!
## Consolidated module: `Solcore.ContractRuntime.ParentIndexedSelectedExecutionFoldCoherenceProperties`
-/

/-! Existing return, revert, and trap folds for branch-complete completion. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ParentIndexedFrameInitialization

universe u v w x

open ParentIndexedSelectedExecutionResult

/--
An actual completed carrier feeds the existing fold with its exact final
working values and its exact indexed parent checkpoint.
-/
theorem runCodeWithStorageParentIndexedResult_completed_fold
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {Next : Type x}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    (finalContext :
      HostStorageDriver.Context RollbackState (FrameTrace Event))
    (value : Core.Value)
    (store : Core.Store)
    (continuation : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (completed :
      initialization.runCodeWithStorageParentIndexedResult
          storageAddress inputs fuel doneOutcome =
        .completed finalContext value store continuation)
    (onReturned onReverted :
      (WorldState ×
        FrameEffectJournal RollbackState (FrameTrace Event)) → Bytes → Next)
    (onTrapped :
      (WorldState ×
        FrameEffectJournal RollbackState (FrameTrace Event)) →
          TrapReason → Next) :
    continuation.foldResolutionWithTrapRollback
        onReturned onReverted onTrapped =
      match doneOutcome finalContext value store with
      | .returned data =>
          onReturned finalContext.context.values.working data
      | .reverted data =>
          onReverted
            (parentWorking.1,
              ⟨parentWorking.2.rollback,
                finalContext.context.values.working.2.trace⟩)
            data
      | .trapped reason =>
          onTrapped
            (parentWorking.1,
              ⟨parentWorking.2.rollback,
                finalContext.context.values.working.2.trace⟩)
            reason := by
  have plainEq :=
    runCodeWithStorageParentIndexedResult_completed_toFrameContinuationContext
      initialization storageAddress inputs fuel doneOutcome finalContext
      value store continuation completed
  have effectWorkingEq := congrArg
    (fun current : FrameContinuationContext
        RollbackState (FrameTrace Event) TrapReason => current.effectWorking)
    plainEq
  have resultEq := congrArg
    (fun current : FrameContinuationContext
        RollbackState (FrameTrace Event) TrapReason => current.result)
    plainEq
  have stateCheckpointEq :
      continuation.stateCheckpoint = parentWorking.1 :=
    congrArg Prod.fst continuation.checkpoint_eq_parentWorking
  have effectCheckpointEq :
      continuation.effectCheckpoint = parentWorking.2 :=
    congrArg Prod.snd continuation.checkpoint_eq_parentWorking
  unfold ParentIndexedFrameContinuationContext.foldResolutionWithTrapRollback
  rw [stateCheckpointEq, effectCheckpointEq, effectWorkingEq, resultEq]
  cases outcomeEq : doneOutcome finalContext value store <;>
    simp [FrameContinuationContext.fromCheckpointedWorkingPair]

theorem runCodeWithStorageParentIndexedResult_completed_fold_returned
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {Next : Type x}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    (finalContext :
      HostStorageDriver.Context RollbackState (FrameTrace Event))
    (value : Core.Value) (store : Core.Store)
    (continuation : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (completed :
      initialization.runCodeWithStorageParentIndexedResult
          storageAddress inputs fuel doneOutcome =
        .completed finalContext value store continuation)
    (data : Bytes)
    (policy : doneOutcome finalContext value store = .returned data)
    (onReturned onReverted :
      (WorldState ×
        FrameEffectJournal RollbackState (FrameTrace Event)) → Bytes → Next)
    (onTrapped :
      (WorldState ×
        FrameEffectJournal RollbackState (FrameTrace Event)) →
          TrapReason → Next) :
    continuation.foldResolutionWithTrapRollback
        onReturned onReverted onTrapped =
      onReturned finalContext.context.values.working data := by
  rw [runCodeWithStorageParentIndexedResult_completed_fold
    initialization storageAddress inputs fuel doneOutcome finalContext
    value store continuation completed onReturned onReverted onTrapped,
    policy]

theorem runCodeWithStorageParentIndexedResult_completed_fold_reverted
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {Next : Type x}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    (finalContext :
      HostStorageDriver.Context RollbackState (FrameTrace Event))
    (value : Core.Value) (store : Core.Store)
    (continuation : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (completed :
      initialization.runCodeWithStorageParentIndexedResult
          storageAddress inputs fuel doneOutcome =
        .completed finalContext value store continuation)
    (data : Bytes)
    (policy : doneOutcome finalContext value store = .reverted data)
    (onReturned onReverted :
      (WorldState ×
        FrameEffectJournal RollbackState (FrameTrace Event)) → Bytes → Next)
    (onTrapped :
      (WorldState ×
        FrameEffectJournal RollbackState (FrameTrace Event)) →
          TrapReason → Next) :
    continuation.foldResolutionWithTrapRollback
        onReturned onReverted onTrapped =
      onReverted
        (parentWorking.1,
          ⟨parentWorking.2.rollback,
            finalContext.context.values.working.2.trace⟩)
        data := by
  rw [runCodeWithStorageParentIndexedResult_completed_fold
    initialization storageAddress inputs fuel doneOutcome finalContext
    value store continuation completed onReturned onReverted onTrapped,
    policy]

theorem runCodeWithStorageParentIndexedResult_completed_fold_trapped
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {Next : Type x}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    (finalContext :
      HostStorageDriver.Context RollbackState (FrameTrace Event))
    (value : Core.Value) (store : Core.Store)
    (continuation : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (completed :
      initialization.runCodeWithStorageParentIndexedResult
          storageAddress inputs fuel doneOutcome =
        .completed finalContext value store continuation)
    (reason : TrapReason)
    (policy : doneOutcome finalContext value store = .trapped reason)
    (onReturned onReverted :
      (WorldState ×
        FrameEffectJournal RollbackState (FrameTrace Event)) → Bytes → Next)
    (onTrapped :
      (WorldState ×
        FrameEffectJournal RollbackState (FrameTrace Event)) →
          TrapReason → Next) :
    continuation.foldResolutionWithTrapRollback
        onReturned onReverted onTrapped =
      onTrapped
        (parentWorking.1,
          ⟨parentWorking.2.rollback,
            finalContext.context.values.working.2.trace⟩)
        reason := by
  rw [runCodeWithStorageParentIndexedResult_completed_fold
    initialization storageAddress inputs fuel doneOutcome finalContext
    value store continuation completed onReturned onReverted onTrapped,
    policy]

end Solcore.ContractRuntime.ParentIndexedFrameInitialization

namespace Solcore.ContractRuntime.ParentIndexedSelectedExecutionResult

universe u v w x

variable {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
variable {Next : Type x}
variable {parentWorking :
  WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}

/-- Exact terminal identity also preserves every existing fold observation. -/
theorem resumeWithFuel_completed_fold
    (context : HostStorageDriver.Context RollbackState (FrameTrace Event))
    (value : Core.Value)
    (store : Core.Store)
    (continuation resumedContinuation : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (inputs : HostStorageDriver.ExecutionInputs)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    (additional : Nat)
    (resumed :
      resumeWithFuel (.completed context value store continuation)
          initialization inputs doneOutcome additional =
        .completed context value store resumedContinuation)
    (onReturned onReverted :
      (WorldState ×
        FrameEffectJournal RollbackState (FrameTrace Event)) → Bytes → Next)
    (onTrapped :
      (WorldState ×
        FrameEffectJournal RollbackState (FrameTrace Event)) →
          TrapReason → Next) :
    resumedContinuation.foldResolutionWithTrapRollback
        onReturned onReverted onTrapped =
      continuation.foldResolutionWithTrapRollback
        onReturned onReverted onTrapped := by
  rw [resumeWithFuel_completed] at resumed
  cases resumed
  rfl

end Solcore.ContractRuntime.ParentIndexedSelectedExecutionResult

/-!
## Consolidated module: `Solcore.ContractRuntime.ParentIndexedSelectedExecutionSession`
-/

/-! Certified configuration and result for one parent-indexed selected run. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

universe u v w

/--
One selected run together with the exact configuration and total fuel budget
that produced its retained branch-complete result.
-/
structure ParentIndexedSelectedExecutionSession
    (RollbackState : Type u) (Event : Type v) (TrapReason : Type w)
    (parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)) where
  initialization : ParentIndexedFrameInitialization
    RollbackState Event parentWorking
  storageAddress : Address
  inputs : HostStorageDriver.ExecutionInputs
  doneOutcome :
    HostStorageDriver.Context RollbackState (FrameTrace Event) →
      Core.Value → Core.Store → FrameOutcome TrapReason
  providedFuel : Nat
  result : ParentIndexedSelectedExecutionResult
    RollbackState Event TrapReason parentWorking
  result_eq_run :
    result = initialization.runCodeWithStorageParentIndexedResult
      storageAddress inputs providedFuel doneOutcome

namespace ParentIndexedSelectedExecutionSession

variable {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
variable {parentWorking :
  WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}

/-- Short name for a session at one fixed parent working pair. -/
abbrev Session := ParentIndexedSelectedExecutionSession
  RollbackState Event TrapReason parentWorking

/-- Start one certified session from the existing branch-complete producer. -/
def start
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    (providedFuel : Nat) :
    ParentIndexedSelectedExecutionSession
      RollbackState Event TrapReason parentWorking := {
  initialization := initialization
  storageAddress := storageAddress
  inputs := inputs
  doneOutcome := doneOutcome
  providedFuel := providedFuel
  result := initialization.runCodeWithStorageParentIndexedResult
    storageAddress inputs providedFuel doneOutcome
  result_eq_run := rfl
}

@[simp] theorem start_initialization
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    (providedFuel : Nat) :
    (start initialization storageAddress inputs doneOutcome providedFuel).initialization =
      initialization :=
  rfl

@[simp] theorem start_storageAddress
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    (providedFuel : Nat) :
    (start initialization storageAddress inputs doneOutcome providedFuel).storageAddress =
      storageAddress :=
  rfl

@[simp] theorem start_inputs
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    (providedFuel : Nat) :
    (start initialization storageAddress inputs doneOutcome providedFuel).inputs =
      inputs :=
  rfl

@[simp] theorem start_doneOutcome
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    (providedFuel : Nat) :
    (start initialization storageAddress inputs doneOutcome providedFuel).doneOutcome =
      doneOutcome :=
  rfl

@[simp] theorem start_providedFuel
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    (providedFuel : Nat) :
    (start initialization storageAddress inputs doneOutcome providedFuel).providedFuel =
      providedFuel :=
  rfl

@[simp] theorem start_result
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    (providedFuel : Nat) :
    (start initialization storageAddress inputs doneOutcome providedFuel).result =
      initialization.runCodeWithStorageParentIndexedResult
        storageAddress inputs providedFuel doneOutcome :=
  rfl

end ParentIndexedSelectedExecutionSession

end Solcore.ContractRuntime

/-!
## Consolidated module: `Solcore.ContractRuntime.ParentIndexedSelectedExecutionSessionResumption`
-/

/-! Closed resumption for certified parent-indexed selected sessions. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ParentIndexedSelectedExecutionSession

universe u v w

variable {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
variable {parentWorking :
  WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}

/--
Offer more fuel without accepting any replacement for the session's fixed
configuration. The stored proof is advanced by the actual-run split law.
-/
def resumeWithFuel
    (session : ParentIndexedSelectedExecutionSession
      RollbackState Event TrapReason parentWorking)
    (additional : Nat) : ParentIndexedSelectedExecutionSession
      RollbackState Event TrapReason parentWorking := {
  initialization := session.initialization
  storageAddress := session.storageAddress
  inputs := session.inputs
  doneOutcome := session.doneOutcome
  providedFuel := session.providedFuel + additional
  result := session.result.resumeWithFuel
    session.initialization session.inputs session.doneOutcome additional
  result_eq_run := by
    rw [session.result_eq_run]
    exact
      ParentIndexedFrameInitialization.runCodeWithStorageParentIndexedResult_resumeWithFuel
        session.initialization session.storageAddress session.inputs
        session.providedFuel additional session.doneOutcome
}

@[simp] theorem resumeWithFuel_initialization
    (session : ParentIndexedSelectedExecutionSession
      RollbackState Event TrapReason parentWorking)
    (additional : Nat) :
    (session.resumeWithFuel additional).initialization =
      session.initialization :=
  rfl

@[simp] theorem resumeWithFuel_storageAddress
    (session : ParentIndexedSelectedExecutionSession
      RollbackState Event TrapReason parentWorking)
    (additional : Nat) :
    (session.resumeWithFuel additional).storageAddress =
      session.storageAddress :=
  rfl

@[simp] theorem resumeWithFuel_inputs
    (session : ParentIndexedSelectedExecutionSession
      RollbackState Event TrapReason parentWorking)
    (additional : Nat) :
    (session.resumeWithFuel additional).inputs = session.inputs :=
  rfl

@[simp] theorem resumeWithFuel_doneOutcome
    (session : ParentIndexedSelectedExecutionSession
      RollbackState Event TrapReason parentWorking)
    (additional : Nat) :
    (session.resumeWithFuel additional).doneOutcome =
      session.doneOutcome :=
  rfl

@[simp] theorem resumeWithFuel_providedFuel
    (session : ParentIndexedSelectedExecutionSession
      RollbackState Event TrapReason parentWorking)
    (additional : Nat) :
    (session.resumeWithFuel additional).providedFuel =
      session.providedFuel + additional :=
  rfl

@[simp] theorem resumeWithFuel_result
    (session : ParentIndexedSelectedExecutionSession
      RollbackState Event TrapReason parentWorking)
    (additional : Nat) :
    (session.resumeWithFuel additional).result =
      session.result.resumeWithFuel session.initialization session.inputs
        session.doneOutcome additional :=
  rfl

/-- Every resumed session still denotes its fixed one-shot run exactly. -/
theorem resumeWithFuel_result_eq_run
    (session : ParentIndexedSelectedExecutionSession
      RollbackState Event TrapReason parentWorking)
    (additional : Nat) :
    (session.resumeWithFuel additional).result =
      session.initialization.runCodeWithStorageParentIndexedResult
        session.storageAddress session.inputs
        (session.providedFuel + additional) session.doneOutcome :=
  (session.resumeWithFuel additional).result_eq_run

end Solcore.ContractRuntime.ParentIndexedSelectedExecutionSession

/-!
## Consolidated module: `Solcore.ContractRuntime.ParentIndexedSelectedExecutionSessionProperties`
-/

/-! Canonicality and fuel algebra for certified selected sessions. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ParentIndexedSelectedExecutionSession

universe u v w

variable {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
variable {parentWorking :
  WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}

/-- Computational fields determine a certified session; its proof is irrelevant. -/
@[ext] theorem ext
    (left right : ParentIndexedSelectedExecutionSession
      RollbackState Event TrapReason parentWorking)
    (initialization : left.initialization = right.initialization)
    (storageAddress : left.storageAddress = right.storageAddress)
    (inputs : left.inputs = right.inputs)
    (doneOutcome : left.doneOutcome = right.doneOutcome)
    (providedFuel : left.providedFuel = right.providedFuel)
    (result : left.result = right.result) :
    left = right := by
  cases left
  cases right
  cases initialization
  cases storageAddress
  cases inputs
  cases doneOutcome
  cases providedFuel
  cases result
  rfl

/-- A certified session is exactly the canonical start at its stored budget. -/
theorem eq_start
    (session : ParentIndexedSelectedExecutionSession
      RollbackState Event TrapReason parentWorking) :
    session = start session.initialization session.storageAddress
      session.inputs session.doneOutcome session.providedFuel := by
  apply ext <;> simp
  exact session.result_eq_run

/-- Resuming a session is the canonical one-shot session at summed fuel. -/
theorem resumeWithFuel_eq_start
    (session : ParentIndexedSelectedExecutionSession
      RollbackState Event TrapReason parentWorking)
    (additional : Nat) :
    session.resumeWithFuel additional =
      start session.initialization session.storageAddress session.inputs
        session.doneOutcome (session.providedFuel + additional) := by
  exact eq_start (session.resumeWithFuel additional)

/-- Starting and then resuming agrees as a complete certified value. -/
theorem start_resumeWithFuel
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    (providedFuel additional : Nat) :
    (start initialization storageAddress inputs doneOutcome providedFuel).resumeWithFuel
        additional =
      start initialization storageAddress inputs doneOutcome
        (providedFuel + additional) :=
  resumeWithFuel_eq_start _ additional

/-- Offering zero additional budget preserves the entire certified session. -/
@[simp] theorem resumeWithFuel_zero
    (session : ParentIndexedSelectedExecutionSession
      RollbackState Event TrapReason parentWorking) :
    session.resumeWithFuel 0 = session := by
  rw [resumeWithFuel_eq_start]
  simpa using (eq_start session).symm

/-- Two closed resumptions equal one resumption by their summed budget. -/
theorem resumeWithFuel_add
    (session : ParentIndexedSelectedExecutionSession
      RollbackState Event TrapReason parentWorking)
    (first second : Nat) :
    (session.resumeWithFuel first).resumeWithFuel second =
      session.resumeWithFuel (first + second) := by
  apply ext <;>
    simp only [resumeWithFuel_initialization, resumeWithFuel_storageAddress,
      resumeWithFuel_inputs, resumeWithFuel_doneOutcome,
      resumeWithFuel_providedFuel, resumeWithFuel_result]
  · rw [Nat.add_assoc]
  · exact ParentIndexedSelectedExecutionResult.resumeWithFuel_add
      session.result session.initialization session.inputs
      session.doneOutcome first second

end Solcore.ContractRuntime.ParentIndexedSelectedExecutionSession

/-!
## Consolidated module: `Solcore.ContractRuntime.ParentIndexedSelectedExecutionSessionBranchProperties`
-/

/-! Exact branch laws inherited by every certified selected session. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ParentIndexedSelectedExecutionSession

universe u v w

open ParentIndexedSelectedExecutionResult

variable {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
variable {parentWorking :
  WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}

theorem result_eq_storageAbsent_iff
    (session : ParentIndexedSelectedExecutionSession
      RollbackState Event TrapReason parentWorking) :
    session.result = .storageAbsent ↔
      session.initialization.initialWorld.account? session.storageAddress =
        none := by
  rw [session.result_eq_run]
  exact
    ParentIndexedFrameInitialization.runCodeWithStorageParentIndexedResult_eq_storageAbsent_iff
      session.initialization session.storageAddress session.inputs
      session.providedFuel session.doneOutcome

theorem result_eq_codeAbsent_iff
    (session : ParentIndexedSelectedExecutionSession
      RollbackState Event TrapReason parentWorking) :
    session.result = .codeAbsent ↔
      ∃ context,
        session.initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
            session.storageAddress = some context ∧
        context.context.values.working.1.code? session.inputs.codeAddress =
          none := by
  rw [session.result_eq_run]
  exact
    ParentIndexedFrameInitialization.runCodeWithStorageParentIndexedResult_eq_codeAbsent_iff
      session.initialization session.storageAddress session.inputs
      session.providedFuel session.doneOutcome

theorem result_eq_outOfFuel_iff
    (session : ParentIndexedSelectedExecutionSession
      RollbackState Event TrapReason parentWorking)
    (finalContext :
      HostStorageDriver.Context RollbackState (FrameTrace Event))
    (state : Core.State) :
    session.result = .outOfFuel finalContext state ↔
      ∃ context,
        session.initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
            session.storageAddress = some context ∧
        context.runCodeWithStorage? session.inputs session.providedFuel =
          some ⟨finalContext, .outOfFuel state⟩ := by
  rw [session.result_eq_run]
  exact
    ParentIndexedFrameInitialization.runCodeWithStorageParentIndexedResult_eq_outOfFuel_iff
      session.initialization session.storageAddress session.inputs
      session.providedFuel session.doneOutcome finalContext state

theorem result_eq_fault_iff
    (session : ParentIndexedSelectedExecutionSession
      RollbackState Event TrapReason parentWorking)
    (finalContext :
      HostStorageDriver.Context RollbackState (FrameTrace Event))
    (error : Core.MachineFault)
    (state : Core.State) :
    session.result = .fault finalContext error state ↔
      ∃ context,
        session.initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
            session.storageAddress = some context ∧
        context.runCodeWithStorage? session.inputs session.providedFuel =
          some ⟨finalContext, .fault error state⟩ := by
  rw [session.result_eq_run]
  exact
    ParentIndexedFrameInitialization.runCodeWithStorageParentIndexedResult_eq_fault_iff
      session.initialization session.storageAddress session.inputs
      session.providedFuel session.doneOutcome finalContext error state

theorem result_eq_unsupported_iff
    (session : ParentIndexedSelectedExecutionSession
      RollbackState Event TrapReason parentWorking)
    (finalContext :
      HostStorageDriver.Context RollbackState (FrameTrace Event))
    (suspension : Core.HostSuspension)
    (remainingFuel : Nat) :
    session.result = .unsupported finalContext suspension remainingFuel ↔
      ∃ context,
        session.initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
            session.storageAddress = some context ∧
        context.runCodeWithStorage? session.inputs session.providedFuel =
          some ⟨finalContext, .unsupported suspension remainingFuel⟩ := by
  rw [session.result_eq_run]
  exact
    ParentIndexedFrameInitialization.runCodeWithStorageParentIndexedResult_eq_unsupported_iff
      session.initialization session.storageAddress session.inputs
      session.providedFuel session.doneOutcome finalContext suspension
      remainingFuel

theorem result_eq_completed_iff
    (session : ParentIndexedSelectedExecutionSession
      RollbackState Event TrapReason parentWorking)
    (finalContext :
      HostStorageDriver.Context RollbackState (FrameTrace Event))
    (value : Core.Value)
    (store : Core.Store)
    (continuation : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking) :
    session.result = .completed finalContext value store continuation ↔
      ∃ context,
        session.initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
            session.storageAddress = some context ∧
        context.runCodeWithStorage? session.inputs session.providedFuel =
          some ⟨finalContext, .done value store⟩ ∧
        continuation = completedContinuation session.initialization
          session.doneOutcome finalContext value store := by
  rw [session.result_eq_run]
  exact
    ParentIndexedFrameInitialization.runCodeWithStorageParentIndexedResult_eq_completed_iff
      session.initialization session.storageAddress session.inputs
      session.providedFuel session.doneOutcome finalContext value store
      continuation

/-- Checked selected sessions cannot contain a raw Core machine fault. -/
theorem result_ne_fault
    (session : ParentIndexedSelectedExecutionSession
      RollbackState Event TrapReason parentWorking)
    (finalContext :
      HostStorageDriver.Context RollbackState (FrameTrace Event))
    (error : Core.MachineFault)
    (state : Core.State) :
    session.result ≠ .fault finalContext error state := by
  rw [session.result_eq_run]
  exact
    ParentIndexedFrameInitialization.runCodeWithStorageParentIndexedResult_ne_fault
      session.initialization session.storageAddress session.inputs
      session.providedFuel session.doneOutcome finalContext error state

end Solcore.ContractRuntime.ParentIndexedSelectedExecutionSession

/-!
## Consolidated module: `Solcore.ContractRuntime.ParentIndexedSelectedExecutionSessionCompatibilityProperties`
-/

/-! Legacy and completed-continuation coherence for certified sessions. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ParentIndexedSelectedExecutionSession

universe u v w

variable {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
variable {parentWorking :
  WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}

/-- Erasing a session result reproduces the unchanged nested-option API. -/
theorem result_toLegacy
    (session : ParentIndexedSelectedExecutionSession
      RollbackState Event TrapReason parentWorking) :
    session.result.toLegacy =
      session.initialization.runCodeWithStorageParentIndexedContinuationContext?
        session.storageAddress session.inputs session.providedFuel
        session.doneOutcome := by
  rw [session.result_eq_run]
  exact
    ParentIndexedFrameInitialization.runCodeWithStorageParentIndexedResult_toLegacy
      session.initialization session.storageAddress session.inputs
      session.providedFuel session.doneOutcome

/-- A completed session carries the exact existing plain continuation. -/
theorem completed_toFrameContinuationContext
    (session : ParentIndexedSelectedExecutionSession
      RollbackState Event TrapReason parentWorking)
    (finalContext :
      HostStorageDriver.Context RollbackState (FrameTrace Event))
    (value : Core.Value)
    (store : Core.Store)
    (continuation : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (completed :
      session.result = .completed finalContext value store continuation) :
    continuation.toFrameContinuationContext =
      FrameContinuationContext.fromCheckpointedWorkingPair
        finalContext.context.values
        (session.doneOutcome finalContext value store) := by
  rw [session.result_eq_run] at completed
  exact
    ParentIndexedFrameInitialization.runCodeWithStorageParentIndexedResult_completed_toFrameContinuationContext
      session.initialization session.storageAddress session.inputs
      session.providedFuel session.doneOutcome finalContext value store
      continuation completed

/-- The legacy entry point exposes the same completed indexed continuation. -/
theorem completed_toLegacy
    (session : ParentIndexedSelectedExecutionSession
      RollbackState Event TrapReason parentWorking)
    (finalContext :
      HostStorageDriver.Context RollbackState (FrameTrace Event))
    (value : Core.Value)
    (store : Core.Store)
    (continuation : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (completed :
      session.result = .completed finalContext value store continuation) :
    session.initialization.runCodeWithStorageParentIndexedContinuationContext?
        session.storageAddress session.inputs session.providedFuel
        session.doneOutcome =
      some (some (some continuation)) := by
  rw [session.result_eq_run] at completed
  exact
    ParentIndexedFrameInitialization.runCodeWithStorageParentIndexedResult_completed_toLegacy
      session.initialization session.storageAddress session.inputs
      session.providedFuel session.doneOutcome finalContext value store
      continuation completed

end Solcore.ContractRuntime.ParentIndexedSelectedExecutionSession

/-!
## Consolidated module: `Solcore.ContractRuntime.ParentIndexedSelectedExecutionSessionFoldProperties`
-/

/-! Existing return, revert, and trap folds for completed certified sessions. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ParentIndexedSelectedExecutionSession

universe u v w x

variable {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
variable {Next : Type x}
variable {parentWorking :
  WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}

/-- A completed session feeds the existing fold with its exact final values. -/
theorem completed_fold
    (session : ParentIndexedSelectedExecutionSession
      RollbackState Event TrapReason parentWorking)
    (finalContext :
      HostStorageDriver.Context RollbackState (FrameTrace Event))
    (value : Core.Value)
    (store : Core.Store)
    (continuation : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (completed :
      session.result = .completed finalContext value store continuation)
    (onReturned onReverted :
      (WorldState ×
        FrameEffectJournal RollbackState (FrameTrace Event)) → Bytes → Next)
    (onTrapped :
      (WorldState ×
        FrameEffectJournal RollbackState (FrameTrace Event)) →
          TrapReason → Next) :
    continuation.foldResolutionWithTrapRollback
        onReturned onReverted onTrapped =
      match session.doneOutcome finalContext value store with
      | .returned data =>
          onReturned finalContext.context.values.working data
      | .reverted data =>
          onReverted
            (parentWorking.1,
              ⟨parentWorking.2.rollback,
                finalContext.context.values.working.2.trace⟩)
            data
      | .trapped reason =>
          onTrapped
            (parentWorking.1,
              ⟨parentWorking.2.rollback,
                finalContext.context.values.working.2.trace⟩)
            reason := by
  rw [session.result_eq_run] at completed
  exact
    ParentIndexedFrameInitialization.runCodeWithStorageParentIndexedResult_completed_fold
      session.initialization session.storageAddress session.inputs
      session.providedFuel session.doneOutcome finalContext value store
      continuation completed onReturned onReverted onTrapped

theorem completed_fold_returned
    (session : ParentIndexedSelectedExecutionSession
      RollbackState Event TrapReason parentWorking)
    (finalContext :
      HostStorageDriver.Context RollbackState (FrameTrace Event))
    (value : Core.Value) (store : Core.Store)
    (continuation : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (completed :
      session.result = .completed finalContext value store continuation)
    (data : Bytes)
    (policy : session.doneOutcome finalContext value store = .returned data)
    (onReturned onReverted :
      (WorldState ×
        FrameEffectJournal RollbackState (FrameTrace Event)) → Bytes → Next)
    (onTrapped :
      (WorldState ×
        FrameEffectJournal RollbackState (FrameTrace Event)) →
          TrapReason → Next) :
    continuation.foldResolutionWithTrapRollback
        onReturned onReverted onTrapped =
      onReturned finalContext.context.values.working data := by
  rw [completed_fold session finalContext value store continuation completed
    onReturned onReverted onTrapped, policy]

theorem completed_fold_reverted
    (session : ParentIndexedSelectedExecutionSession
      RollbackState Event TrapReason parentWorking)
    (finalContext :
      HostStorageDriver.Context RollbackState (FrameTrace Event))
    (value : Core.Value) (store : Core.Store)
    (continuation : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (completed :
      session.result = .completed finalContext value store continuation)
    (data : Bytes)
    (policy : session.doneOutcome finalContext value store = .reverted data)
    (onReturned onReverted :
      (WorldState ×
        FrameEffectJournal RollbackState (FrameTrace Event)) → Bytes → Next)
    (onTrapped :
      (WorldState ×
        FrameEffectJournal RollbackState (FrameTrace Event)) →
          TrapReason → Next) :
    continuation.foldResolutionWithTrapRollback
        onReturned onReverted onTrapped =
      onReverted
        (parentWorking.1,
          ⟨parentWorking.2.rollback,
            finalContext.context.values.working.2.trace⟩)
        data := by
  rw [completed_fold session finalContext value store continuation completed
    onReturned onReverted onTrapped, policy]

theorem completed_fold_trapped
    (session : ParentIndexedSelectedExecutionSession
      RollbackState Event TrapReason parentWorking)
    (finalContext :
      HostStorageDriver.Context RollbackState (FrameTrace Event))
    (value : Core.Value) (store : Core.Store)
    (continuation : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (completed :
      session.result = .completed finalContext value store continuation)
    (reason : TrapReason)
    (policy : session.doneOutcome finalContext value store = .trapped reason)
    (onReturned onReverted :
      (WorldState ×
        FrameEffectJournal RollbackState (FrameTrace Event)) → Bytes → Next)
    (onTrapped :
      (WorldState ×
        FrameEffectJournal RollbackState (FrameTrace Event)) →
          TrapReason → Next) :
    continuation.foldResolutionWithTrapRollback
        onReturned onReverted onTrapped =
      onTrapped
        (parentWorking.1,
          ⟨parentWorking.2.rollback,
            finalContext.context.values.working.2.trace⟩)
        reason := by
  rw [completed_fold session finalContext value store continuation completed
    onReturned onReverted onTrapped, policy]

end Solcore.ContractRuntime.ParentIndexedSelectedExecutionSession
