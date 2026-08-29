import Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccountCodeExecutionProperties
import Solcore.Semantics.HostStorageHandlerProperties

/-! Compile-time use of the public storage-driver proof interface. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.Semantics

universe u v

/-- The public handler API exposes the exact write update and resumed Core state. -/
private theorem compileTimeWriteResumeRegression
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (slot value : Word)
    (continuation : List Frame)
    (store : Store) :
    (HostStorageDriver.handleSuspension context
        ⟨.storageWrite slot value, continuation, store⟩).1 =
          context.writeStorage slot value ∧
      (HostStorageDriver.handleSuspension context
          ⟨.storageWrite slot value, continuation, store⟩).2.control =
        .ret .unit ∧
      (HostStorageDriver.handleSuspension context
          ⟨.storageWrite slot value, continuation, store⟩).2.continuation =
        continuation ∧
      (HostStorageDriver.handleSuspension context
          ⟨.storageWrite slot value, continuation, store⟩).2.store = store := by
  exact
    ⟨HostStorageDriver.handleSuspension_storageWrite_context
        context slot value continuation store,
      HostStorageDriver.handleSuspension_storageWrite_control
        context slot value continuation store,
      HostStorageDriver.handleSuspension_storageWrite_continuation
        context slot value continuation store,
      HostStorageDriver.handleSuspension_storageWrite_store
        context slot value continuation store⟩

/-- Public handler observations fix read-after-write and sparse zero deletion. -/
private theorem compileTimeWriteObservationRegression
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (slot value : Word) :
    ((HostStorageDriver.handler.handle context
      (.storageWrite slot value)).1).readStorage slot = value ∧
      ((HostStorageDriver.handler.handle context
        (.storageWrite slot Word.zero)).1).storageAccount.storageValue?
          slot = none := by
  exact
    ⟨HostStorageDriver.handler_storageWrite_readStorage_same
        context slot value,
      HostStorageDriver.handler_storageWrite_zero_storageValue?
        context slot⟩

/-- A successful selected run exposes both typing and exact fuel evidence. -/
private theorem compileTimeSelectedEvidenceRegression
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (codeAddress : Address)
    (fuel : Nat)
    (result :
      HostDriverResult (HostStorageDriver.Context RollbackState TraceState))
    (executed :
      context.runCodeWithStorage? codeAddress fuel = some result) :
    (∃ code,
      context.context.values.working.1.code? codeAddress = some code ∧
        result.outcome.HasType
          code.program.resultType code.program.dataDefinitions) ∧
    (∃ code,
      context.context.values.working.1.code? codeAddress = some code ∧
        HostStorageDriver.FuelSound result fuel context
          (State.initial code.program.body hostEnvironment)) := by
  exact
    ⟨FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorage?_some_hasType
        context codeAddress fuel result executed,
      FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorage?_some_fuelSound
        context codeAddress fuel result executed⟩

/-- A selected checked run cannot expose the raw driver fault branch. -/
private theorem compileTimeSelectedNoFaultRegression
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (codeAddress : Address)
    (fuel : Nat)
    (resultContext :
      HostStorageDriver.Context RollbackState TraceState)
    (error : MachineFault)
    (faultState : State) :
    context.runCodeWithStorage? codeAddress fuel ≠
      some ⟨resultContext, .fault error faultState⟩ :=
  FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorage?_ne_some_fault
    context codeAddress fuel resultContext error faultState

/-- Public selected-run laws retain every frame projection outside storage. -/
private theorem compileTimeSelectedInvariantRegression
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (codeAddress : Address)
    (fuel : Nat)
    (result :
      HostDriverResult (HostStorageDriver.Context RollbackState TraceState))
    (executed :
      context.runCodeWithStorage? codeAddress fuel = some result)
    (otherAddress : Address)
    (different : otherAddress ≠ context.context.storageAddress) :
    result.context.context.storageAddress = context.context.storageAddress ∧
      result.context.context.values.checkpoint =
        context.context.values.checkpoint ∧
      result.context.context.values.working.2 =
        context.context.values.working.2 ∧
      result.context.context.values.working.1.account? otherAddress =
        context.context.values.working.1.account? otherAddress ∧
      result.context.context.values.working.1.code? codeAddress =
        context.context.values.working.1.code? codeAddress := by
  exact
    ⟨FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorage?_some_storageAddress
        context codeAddress fuel result executed,
      FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorage?_some_checkpoint
        context codeAddress fuel result executed,
      FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorage?_some_workingEffects
        context codeAddress fuel result executed,
      FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorage?_some_workingAccount?_of_ne_storageAddress
        context codeAddress fuel result executed otherAddress different,
      FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorage?_some_workingCode?
        context codeAddress fuel result executed codeAddress⟩

/-- The specialized driver exposes the generic executable/specification iff. -/
private theorem compileTimeStorageDriverCompletenessRegression
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (fuel : Nat)
    (state : State)
    (result :
      HostDriverResult
        (HostStorageDriver.Context RollbackState TraceState)) :
    HostStorageDriver.run context fuel state = result ↔
      HostStorageDriver.FuelSound result fuel context state :=
  HostStorageDriver.run_eq_iff_fuelSound context fuel state result

/-- Combined storage done stability retains the exact full driver result. -/
private theorem compileTimeStorageDriverDoneStabilityRegression
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    {fuel largerFuel : Nat}
    (state : State)
    {finalContext :
      HostStorageDriver.Context RollbackState TraceState}
    {value : Value}
    {store : Store}
    (execution :
      HostStorageDriver.run context fuel state =
        ⟨finalContext, .done value store⟩)
    (more : fuel ≤ largerFuel) :
    HostStorageDriver.run context largerFuel state =
      ⟨finalContext, .done value store⟩ :=
  HostStorageDriver.run_done_stable context state execution more

/-- Checked execution exposes the same exact executable/specification iff. -/
private theorem compileTimeCheckedCompletenessRegression
    {RollbackState : Type u}
    {TraceState : Type v}
    (code : CheckedHostCoreProgram)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (fuel : Nat)
    (result :
      HostDriverResult
        (HostStorageDriver.Context RollbackState TraceState)) :
    code.runWithStorage context fuel = result ↔
      HostStorageDriver.FuelSound result fuel context
        (State.initial code.program.body hostEnvironment) :=
  CheckedHostCoreProgram.runWithStorage_eq_iff_fuelSound
    code context fuel result

/-- Checked done stability retains the exact full driver result. -/
private theorem compileTimeCheckedDoneStabilityRegression
    {RollbackState : Type u}
    {TraceState : Type v}
    (code : CheckedHostCoreProgram)
    (context : HostStorageDriver.Context RollbackState TraceState)
    {fuel largerFuel : Nat}
    {finalContext :
      HostStorageDriver.Context RollbackState TraceState}
    {value : Value}
    {store : Store}
    (execution :
      code.runWithStorage context fuel =
        ⟨finalContext, .done value store⟩)
    (more : fuel ≤ largerFuel) :
    code.runWithStorage context largerFuel =
      ⟨finalContext, .done value store⟩ :=
  CheckedHostCoreProgram.runWithStorage_done_stable
    code context execution more

/-- Address-selected done stability retains the exact optional full result. -/
private theorem compileTimeSelectedDoneStabilityRegression
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (codeAddress : Address)
    {fuel largerFuel : Nat}
    {finalContext :
      HostStorageDriver.Context RollbackState TraceState}
    {value : Value}
    {store : Store}
    (execution :
      context.runCodeWithStorage? codeAddress fuel =
        some ⟨finalContext, .done value store⟩)
    (more : fuel ≤ largerFuel) :
    context.runCodeWithStorage? codeAddress largerFuel =
      some ⟨finalContext, .done value store⟩ :=
  FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorage?_some_done_stable
    context codeAddress execution more

end Tests
