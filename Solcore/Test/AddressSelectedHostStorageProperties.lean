import Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccountCodeFrameContinuationProperties
import Solcore.ContractRuntime.HostStorageHandlerProperties

/-! Compile-time use of the public storage-driver proof interface. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.ContractRuntime

universe u v w x

private def frameContinuationData : Bytes := [0xa1, 0xb2].toByteArray

private def returnedFrameOutcome
    {Context : Type x}
    (_ : Context) (_ : Value) (_ : Store) : FrameOutcome Unit :=
  .returned frameContinuationData

private def revertedFrameOutcome
    {Context : Type x}
    (_ : Context) (_ : Value) (_ : Store) : FrameOutcome Unit :=
  .reverted frameContinuationData

private def trappedFrameOutcome
    {Context : Type x}
    (_ : Context) (_ : Value) (_ : Store) : FrameOutcome Unit :=
  .trapped ()

/-- The public handler API exposes the exact write update and resumed Core state. -/
private theorem compileTimeWriteResumeRegression
    {RollbackState : Type u}
    {TraceState : Type v}
    (inputs : HostStorageDriver.ExecutionInputs)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (slot value : Word)
    (continuation : List Frame)
    (store : Store) :
    (HostStorageDriver.handleSuspension inputs context
        ⟨.storageWrite slot value, continuation, store⟩).1 =
          context.writeStorage slot value ∧
      (HostStorageDriver.handleSuspension inputs context
          ⟨.storageWrite slot value, continuation, store⟩).2.control =
        .ret .unit ∧
      (HostStorageDriver.handleSuspension inputs context
          ⟨.storageWrite slot value, continuation, store⟩).2.continuation =
        continuation ∧
      (HostStorageDriver.handleSuspension inputs context
          ⟨.storageWrite slot value, continuation, store⟩).2.store = store := by
  exact
    ⟨HostStorageDriver.handleSuspension_storageWrite_context
        inputs context slot value continuation store,
      HostStorageDriver.handleSuspension_storageWrite_control
        inputs context slot value continuation store,
      HostStorageDriver.handleSuspension_storageWrite_continuation
        inputs context slot value continuation store,
      HostStorageDriver.handleSuspension_storageWrite_store
        inputs context slot value continuation store⟩

/-- The selector handler exposes its exact lossless, context-preserving response. -/
private theorem compileTimeStorageAddressResumeRegression
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : HostStorageDriver.ExecutionInputs)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (continuation : List Frame) (store : Store) :
    (HostStorageDriver.handleSuspension inputs context
        ⟨.storageAddress, continuation, store⟩).1 = context ∧
      (HostStorageDriver.handleSuspension inputs context
        ⟨.storageAddress, continuation, store⟩).2.control =
          .ret (.word (addressToWord context.context.storageAddress)) ∧
      (HostStorageDriver.handleSuspension inputs context
        ⟨.storageAddress, continuation, store⟩).2.continuation = continuation ∧
      (HostStorageDriver.handleSuspension inputs context
        ⟨.storageAddress, continuation, store⟩).2.store = store ∧
      wordToAddress?
          ((HostStorageDriver.handler inputs).handle
            context .storageAddress).2 =
        some context.context.storageAddress := by
  exact
    ⟨HostStorageDriver.handleSuspension_storageAddress_context
        inputs context continuation store,
      HostStorageDriver.handleSuspension_storageAddress_control
        inputs context continuation store,
      HostStorageDriver.handleSuspension_storageAddress_continuation
        inputs context continuation store,
      HostStorageDriver.handleSuspension_storageAddress_store
        inputs context continuation store,
      HostStorageDriver.wordToAddress?_handler_storageAddress
        inputs context⟩

/-- The public selector rule reuses Core's exact remaining fuel. -/
private theorem compileTimeStorageAddressRemainingFuelRegression
    {RollbackState : Type u} {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel remainingFuel : Nat) (state : State)
    (continuation : List Frame) (store : Store)
    (execution :
      hostRun fuel state =
        .suspended ⟨.storageAddress, continuation, store⟩ remainingFuel) :
    HostStorageDriver.run context inputs fuel state =
      HostStorageDriver.run context inputs remainingFuel
        ⟨.ret (.word (addressToWord context.context.storageAddress)),
          continuation, store⟩ :=
  HostStorageDriver.run_of_suspended_storageAddress
    context inputs fuel remainingFuel state continuation store execution

/-- The code-selector handler exposes its exact lossless response and state. -/
private theorem compileTimeCodeAddressResumeRegression
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : HostStorageDriver.ExecutionInputs)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (continuation : List Frame) (store : Store) :
    (HostStorageDriver.handleSuspension inputs context
        ⟨.codeAddress, continuation, store⟩).1 = context ∧
      (HostStorageDriver.handleSuspension inputs context
        ⟨.codeAddress, continuation, store⟩).2.control =
          .ret (.word (addressToWord inputs.codeAddress)) ∧
      (HostStorageDriver.handleSuspension inputs context
        ⟨.codeAddress, continuation, store⟩).2.continuation = continuation ∧
      (HostStorageDriver.handleSuspension inputs context
        ⟨.codeAddress, continuation, store⟩).2.store = store ∧
      wordToAddress?
          ((HostStorageDriver.handler inputs).handle
            context .codeAddress).2 = some inputs.codeAddress := by
  exact
    ⟨HostStorageDriver.handleSuspension_codeAddress_context
        inputs context continuation store,
      HostStorageDriver.handleSuspension_codeAddress_control
        inputs context continuation store,
      HostStorageDriver.handleSuspension_codeAddress_continuation
        inputs context continuation store,
      HostStorageDriver.handleSuspension_codeAddress_store
        inputs context continuation store,
      HostStorageDriver.wordToAddress?_handler_codeAddress
        inputs context⟩

/-- The public code-selector rule reuses Core's exact remaining fuel. -/
private theorem compileTimeCodeAddressRemainingFuelRegression
    {RollbackState : Type u} {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel remainingFuel : Nat) (state : State)
    (continuation : List Frame) (store : Store)
    (execution :
      hostRun fuel state =
        .suspended ⟨.codeAddress, continuation, store⟩ remainingFuel) :
    HostStorageDriver.run context inputs fuel state =
      HostStorageDriver.run context inputs remainingFuel
        ⟨.ret (.word (addressToWord inputs.codeAddress)), continuation, store⟩ :=
  HostStorageDriver.run_of_suspended_codeAddress
    context inputs fuel remainingFuel state continuation store execution

/-- Public handler observations fix read-after-write and sparse zero deletion. -/
private theorem compileTimeWriteObservationRegression
    {RollbackState : Type u}
    {TraceState : Type v}
    (inputs : HostStorageDriver.ExecutionInputs)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (slot value : Word) :
    (((HostStorageDriver.handler inputs).handle context
      (.storageWrite slot value)).1).readStorage slot = value ∧
      (((HostStorageDriver.handler inputs).handle context
        (.storageWrite slot Word.zero)).1).storageAccount.storageValue?
          slot = none := by
  exact
    ⟨HostStorageDriver.handler_storageWrite_readStorage_same
        inputs context slot value,
      HostStorageDriver.handler_storageWrite_zero_storageValue?
        inputs context slot⟩

/-- A successful selected run exposes both typing and exact fuel evidence. -/
private theorem compileTimeSelectedEvidenceRegression
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (result :
      HostDriverResult (HostStorageDriver.Context RollbackState TraceState))
    (executed :
      context.runCodeWithStorage? inputs fuel = some result) :
    (∃ code,
      context.context.values.working.1.code? inputs.codeAddress = some code ∧
        result.outcome.HasType
          code.program.resultType code.program.dataDefinitions) ∧
    (∃ code,
      context.context.values.working.1.code? inputs.codeAddress = some code ∧
        HostStorageDriver.FuelSound result inputs fuel context
          (State.initial code.program.body hostEnvironment)) := by
  exact
    ⟨FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorage?_some_hasType
        context inputs fuel result executed,
      FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorage?_some_fuelSound
        context inputs fuel result executed⟩

/-- The public selected entry point exposes its complete successful specification. -/
private theorem compileTimeSelectedCompletenessRegression
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (result :
      HostDriverResult (HostStorageDriver.Context RollbackState TraceState)) :
    context.runCodeWithStorage? inputs fuel = some result ↔
      ∃ code,
        context.context.values.working.1.code? inputs.codeAddress = some code ∧
          HostStorageDriver.FuelSound result inputs fuel context
            (State.initial code.program.body hostEnvironment) :=
  FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorage?_eq_some_iff_fuelSound
    context inputs fuel result

/-- The forward iff direction recovers the selected code and exact fuel evidence. -/
private theorem compileTimeSelectedCompletenessForwardRegression
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (result :
      HostDriverResult (HostStorageDriver.Context RollbackState TraceState))
    (executed :
      context.runCodeWithStorage? inputs fuel = some result) :
    ∃ code,
      context.context.values.working.1.code? inputs.codeAddress = some code ∧
        HostStorageDriver.FuelSound result inputs fuel context
          (State.initial code.program.body hostEnvironment) :=
  (compileTimeSelectedCompletenessRegression
    context inputs fuel result).mp executed

/-- Selected-code fuel evidence replays to the exact optional execution result. -/
private theorem compileTimeSelectedCompletenessReplayRegression
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (result :
      HostDriverResult (HostStorageDriver.Context RollbackState TraceState))
    (code : CheckedHostCoreProgram)
    (selected :
      context.context.values.working.1.code? inputs.codeAddress = some code)
    (sound :
      HostStorageDriver.FuelSound result inputs fuel context
        (State.initial code.program.body hostEnvironment)) :
    context.runCodeWithStorage? inputs fuel = some result :=
  (compileTimeSelectedCompletenessRegression
    context inputs fuel result).mpr ⟨code, selected, sound⟩

/-- Optional failure is exactly failure of the existing code lookup. -/
private theorem compileTimeSelectedNoneCompletenessRegression
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat) :
    context.runCodeWithStorage? inputs fuel = none ↔
      context.context.values.working.1.code? inputs.codeAddress = none :=
  FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorage?_eq_none_iff
    context inputs fuel

/-- A selected exhausted run remains an attempted execution, never `none`. -/
private theorem compileTimeSelectedOutOfFuelIsSomeRegression
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (code : CheckedHostCoreProgram)
    (selected :
      context.context.values.working.1.code? inputs.codeAddress = some code)
    (finalContext : HostStorageDriver.Context RollbackState TraceState)
    (state : State)
    (exhausted :
      code.runWithStorage context inputs fuel =
        ⟨finalContext, .outOfFuel state⟩) :
    context.runCodeWithStorage? inputs fuel =
      some ⟨finalContext, .outOfFuel state⟩ := by
  unfold FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorage?
  rw [selected]
  simp only [Option.map_some]
  exact congrArg some exhausted

/-- A selected checked run cannot expose the raw driver fault branch. -/
private theorem compileTimeSelectedNoFaultRegression
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (resultContext :
      HostStorageDriver.Context RollbackState TraceState)
    (error : MachineFault)
    (faultState : State) :
    context.runCodeWithStorage? inputs fuel ≠
      some ⟨resultContext, .fault error faultState⟩ :=
  FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorage?_ne_some_fault
    context inputs fuel resultContext error faultState

/-- Public selected-run laws retain every frame projection outside storage. -/
private theorem compileTimeSelectedInvariantRegression
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (result :
      HostDriverResult (HostStorageDriver.Context RollbackState TraceState))
    (executed :
      context.runCodeWithStorage? inputs fuel = some result)
    (otherAddress : Address)
    (different : otherAddress ≠ context.context.storageAddress) :
    result.context.context.storageAddress = context.context.storageAddress ∧
      result.context.context.values.checkpoint =
        context.context.values.checkpoint ∧
      result.context.context.values.working.2 =
        context.context.values.working.2 ∧
      result.context.context.values.working.1.account? otherAddress =
        context.context.values.working.1.account? otherAddress ∧
      result.context.context.values.working.1.code? inputs.codeAddress =
        context.context.values.working.1.code? inputs.codeAddress := by
  exact
    ⟨FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorage?_some_storageAddress
        context inputs fuel result executed,
      FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorage?_some_checkpoint
        context inputs fuel result executed,
      FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorage?_some_workingEffects
        context inputs fuel result executed,
      FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorage?_some_workingAccount?_of_ne_storageAddress
        context inputs fuel result executed otherAddress different,
      FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorage?_some_workingCode?
        context inputs fuel result executed inputs.codeAddress⟩

/-- The specialized driver exposes the generic executable/specification iff. -/
private theorem compileTimeStorageDriverCompletenessRegression
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (state : State)
    (result :
      HostDriverResult
        (HostStorageDriver.Context RollbackState TraceState)) :
    HostStorageDriver.run context inputs fuel state = result ↔
      HostStorageDriver.FuelSound result inputs fuel context state :=
  HostStorageDriver.run_eq_iff_fuelSound
    context inputs fuel state result

/-- Combined storage done stability retains the exact full driver result. -/
private theorem compileTimeStorageDriverDoneStabilityRegression
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    {fuel largerFuel : Nat}
    (state : State)
    {finalContext :
      HostStorageDriver.Context RollbackState TraceState}
    {value : Value}
    {store : Store}
    (execution :
      HostStorageDriver.run context inputs fuel state =
        ⟨finalContext, .done value store⟩)
    (more : fuel ≤ largerFuel) :
    HostStorageDriver.run context inputs largerFuel state =
      ⟨finalContext, .done value store⟩ :=
  HostStorageDriver.run_done_stable
    context inputs state execution more

/-- Checked execution exposes the same exact executable/specification iff. -/
private theorem compileTimeCheckedCompletenessRegression
    {RollbackState : Type u}
    {TraceState : Type v}
    (code : CheckedHostCoreProgram)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (result :
      HostDriverResult
        (HostStorageDriver.Context RollbackState TraceState)) :
    code.runWithStorage context inputs fuel = result ↔
      HostStorageDriver.FuelSound result inputs fuel context
        (State.initial code.program.body hostEnvironment) :=
  CheckedHostCoreProgram.runWithStorage_eq_iff_fuelSound
    code context inputs fuel result

/-- Checked done stability retains the exact full driver result. -/
private theorem compileTimeCheckedDoneStabilityRegression
    {RollbackState : Type u}
    {TraceState : Type v}
    (code : CheckedHostCoreProgram)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    {fuel largerFuel : Nat}
    {finalContext :
      HostStorageDriver.Context RollbackState TraceState}
    {value : Value}
    {store : Store}
    (execution :
      code.runWithStorage context inputs fuel =
        ⟨finalContext, .done value store⟩)
    (more : fuel ≤ largerFuel) :
    code.runWithStorage context inputs largerFuel =
      ⟨finalContext, .done value store⟩ :=
  CheckedHostCoreProgram.runWithStorage_done_stable
    code context inputs execution more

/-- Address-selected done stability retains the exact optional full result. -/
private theorem compileTimeSelectedDoneStabilityRegression
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    {fuel largerFuel : Nat}
    {finalContext :
      HostStorageDriver.Context RollbackState TraceState}
    {value : Value}
    {store : Store}
    (execution :
      context.runCodeWithStorage? inputs fuel =
        some ⟨finalContext, .done value store⟩)
    (more : fuel ≤ largerFuel) :
    context.runCodeWithStorage? inputs largerFuel =
      some ⟨finalContext, .done value store⟩ :=
  FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorage?_some_done_stable
    context inputs execution more

/-- The generic adapter distinguishes completion from exhaustion and raw faults. -/
private theorem compileTimeFrameContinuationBranchRegression
    {Context : Type x}
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : Context)
    (value : Value)
    (store : Store)
    (state : State)
    (error : MachineFault)
    (values :
      Context → FrameCheckpointedWorkingPair RollbackState TraceState) :
    (HostDriverResult.mk context (.done value store)).toFrameContinuationContext?
          values returnedFrameOutcome =
        some (FrameContinuationContext.fromCheckpointedWorkingPair
          (values context) (returnedFrameOutcome context value store)) ∧
      (HostDriverResult.mk context (.outOfFuel state)).toFrameContinuationContext?
          values returnedFrameOutcome = none ∧
      (HostDriverResult.mk context (.fault error state)).toFrameContinuationContext?
          values returnedFrameOutcome = none := by
  exact
    ⟨HostDriverResult.toFrameContinuationContext?_done
        context value store values returnedFrameOutcome,
      HostDriverResult.toFrameContinuationContext?_outOfFuel
        context state values returnedFrameOutcome,
      HostDriverResult.toFrameContinuationContext?_fault
        context error state values returnedFrameOutcome⟩

/-- Completion retains every terminal checkpoint, working, and outcome input. -/
private theorem compileTimeFrameContinuationProjectionRegression
    {Context : Type x}
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : Context)
    (value : Value)
    (store : Store)
    (values :
      Context → FrameCheckpointedWorkingPair RollbackState TraceState) :
    Option.map FrameContinuationContext.stateCheckpoint
        ((HostDriverResult.mk context (.done value store)).toFrameContinuationContext?
          values returnedFrameOutcome) =
        some (values context).checkpoint.state ∧
      Option.map FrameContinuationContext.effectCheckpoint
        ((HostDriverResult.mk context (.done value store)).toFrameContinuationContext?
          values returnedFrameOutcome) =
        some (values context).checkpoint.effects ∧
      Option.map FrameContinuationContext.effectWorking
        ((HostDriverResult.mk context (.done value store)).toFrameContinuationContext?
          values returnedFrameOutcome) =
        some (values context).working.2 ∧
      Option.map FrameContinuationContext.result
        ((HostDriverResult.mk context (.done value store)).toFrameContinuationContext?
          values returnedFrameOutcome) =
        some ⟨(values context).working.1,
          returnedFrameOutcome context value store⟩ := by
  exact
    ⟨HostDriverResult.stateCheckpoint_toFrameContinuationContext?_done
        context value store values returnedFrameOutcome,
      HostDriverResult.effectCheckpoint_toFrameContinuationContext?_done
        context value store values returnedFrameOutcome,
      HostDriverResult.effectWorking_toFrameContinuationContext?_done
        context value store values returnedFrameOutcome,
      HostDriverResult.result_toFrameContinuationContext?_done
        context value store values returnedFrameOutcome⟩

/-- Return, revert, and policy-selected trap resolution remain branch exact. -/
private theorem compileTimeFrameContinuationResolutionRegression
    {Context : Type x}
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : Context)
    (value : Value)
    (store : Store)
    (values :
      Context → FrameCheckpointedWorkingPair RollbackState TraceState) :
    Option.map FrameContinuationContext.resolve
        ((HostDriverResult.mk context (.done value store)).toFrameContinuationContext?
          values returnedFrameOutcome) =
        some (FrameResolutionResult.returned
          (values context).working.1 (values context).working.2
          frameContinuationData) ∧
      Option.map FrameContinuationContext.resolve
        ((HostDriverResult.mk context (.done value store)).toFrameContinuationContext?
          values revertedFrameOutcome) =
        some (FrameResolutionResult.reverted
          (values context).checkpoint.state
          ⟨(values context).checkpoint.effects.rollback,
            (values context).working.2.trace⟩
          frameContinuationData) ∧
      Option.map FrameContinuationContext.resolve
        ((HostDriverResult.mk context (.done value store)).toFrameContinuationContext?
          values trappedFrameOutcome) =
        some (FrameResolutionResult.trapped ()) := by
  exact
    ⟨HostDriverResult.resolve_toFrameContinuationContext?_done_returned
        context value store values returnedFrameOutcome
        frameContinuationData rfl,
      HostDriverResult.resolve_toFrameContinuationContext?_done_reverted
        context value store values revertedFrameOutcome
        frameContinuationData rfl,
      HostDriverResult.resolve_toFrameContinuationContext?_done_trapped
        context value store values trappedFrameOutcome () rfl⟩

/-- Checked adaptation exposes exhaustion exactly and preserves completed output. -/
private theorem compileTimeCheckedFrameContinuationRegression
    {RollbackState : Type u}
    {TraceState : Type v}
    {TrapReason : Type w}
    (code : CheckedHostCoreProgram)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (doneOutcome :
      HostStorageDriver.Context RollbackState TraceState →
        Value → Store → FrameOutcome TrapReason) :
    (code.runWithStorage context inputs fuel).toFrameContinuationContext?
          (fun current => current.context.values) doneOutcome = none ↔
      (∃ finalContext exhausted,
        code.runWithStorage context inputs fuel =
          ⟨finalContext, .outOfFuel exhausted⟩) ∨
      ∃ finalContext suspension remainingFuel,
        code.runWithStorage context inputs fuel =
          ⟨finalContext, .unsupported suspension remainingFuel⟩ :=
  code.runWithStorage_toFrameContinuationContext?_eq_none_iff
    context inputs fuel doneOutcome

private theorem compileTimeCheckedFrameContinuationStabilityRegression
    {RollbackState : Type u}
    {TraceState : Type v}
    {TrapReason : Type w}
    (code : CheckedHostCoreProgram)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (doneOutcome :
      HostStorageDriver.Context RollbackState TraceState →
        Value → Store → FrameOutcome TrapReason)
    {fuel largerFuel : Nat}
    {continuation :
      FrameContinuationContext RollbackState TraceState TrapReason}
    (completed :
      (code.runWithStorage context inputs fuel).toFrameContinuationContext?
          (fun current => current.context.values) doneOutcome =
        some continuation)
    (more : fuel ≤ largerFuel) :
    (code.runWithStorage context inputs largerFuel).toFrameContinuationContext?
        (fun current => current.context.values) doneOutcome =
      some continuation :=
  code.runWithStorage_toFrameContinuationContext?_some_stable
    context inputs doneOutcome completed more

/-- Selected adaptation keeps code absence distinct from selected exhaustion. -/
private theorem compileTimeSelectedFrameContinuationBoundaryRegression
    {RollbackState : Type u}
    {TraceState : Type v}
    {TrapReason : Type w}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (doneOutcome :
      HostStorageDriver.Context RollbackState TraceState →
        Value → Store → FrameOutcome TrapReason) :
    (context.runCodeWithStorageContinuationContext?
          inputs fuel doneOutcome = none ↔
        context.context.values.working.1.code? inputs.codeAddress = none) ∧
      (context.runCodeWithStorageContinuationContext?
          inputs fuel doneOutcome = some none ↔
        (∃ resultContext exhausted,
          context.runCodeWithStorage? inputs fuel =
            some ⟨resultContext, .outOfFuel exhausted⟩) ∨
        ∃ resultContext suspension remainingFuel,
          context.runCodeWithStorage? inputs fuel =
            some ⟨resultContext,
              .unsupported suspension remainingFuel⟩) := by
  exact
    ⟨FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorageContinuationContext?_eq_none_iff
        context inputs fuel doneOutcome,
      FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorageContinuationContext?_eq_some_none_iff
        context inputs fuel doneOutcome⟩

/-- A nested selected completion retains the exact continuation at larger fuel. -/
private theorem compileTimeSelectedFrameContinuationStabilityRegression
    {RollbackState : Type u}
    {TraceState : Type v}
    {TrapReason : Type w}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (doneOutcome :
      HostStorageDriver.Context RollbackState TraceState →
        Value → Store → FrameOutcome TrapReason)
    {fuel largerFuel : Nat}
    {continuation :
      FrameContinuationContext RollbackState TraceState TrapReason}
    (completed :
      context.runCodeWithStorageContinuationContext?
        inputs fuel doneOutcome = some (some continuation))
    (more : fuel ≤ largerFuel) :
    context.runCodeWithStorageContinuationContext?
      inputs largerFuel doneOutcome = some (some continuation) :=
  FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorageContinuationContext?_some_some_stable
    context inputs doneOutcome completed more

end Tests
