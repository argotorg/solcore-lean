import Solcore.ContractRuntime.CheckedHostCoreProgram
import Solcore.ContractRuntime.HostStorageDriver
import Solcore.ContractRuntime.WordReturnedFrameCompletion

/-! Checker-accepted host-aware Core programs with Word result type. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

/-- A checked host-aware program whose declared result is exactly Word. -/
structure CheckedHostCoreWordProgram where
  code : CheckedHostCoreProgram
  resultType_eq_word : code.program.resultType = .word

namespace CheckedHostCoreWordProgram

/-- Refine checked code exactly when its declared result type is Word. -/
def ofChecked? (code : CheckedHostCoreProgram) :
    Option CheckedHostCoreWordProgram :=
  if resultTypeEq : code.program.resultType = .word then
    some ⟨code, resultTypeEq⟩
  else
    none

/-- Check host admission and the Word result refinement together. -/
def ofProgram? (program : Core.Program) :
    Option CheckedHostCoreWordProgram := do
  let code ← CheckedHostCoreProgram.ofProgram? program
  ofChecked? code

end CheckedHostCoreWordProgram

end Solcore.ContractRuntime

/-!
## Consolidated module: `Solcore.ContractRuntime.CheckedHostCoreWordProgramProperties`
-/

/-! Admission and projection laws for checked Word-result programs. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.CheckedHostCoreWordProgram

@[simp] theorem mk_code
    (code : CheckedHostCoreProgram)
    (resultTypeEq : code.program.resultType = .word) :
    (CheckedHostCoreWordProgram.mk code resultTypeEq).code = code :=
  rfl

@[simp] theorem mk_resultType
    (code : CheckedHostCoreProgram)
    (resultTypeEq : code.program.resultType = .word) :
    (CheckedHostCoreWordProgram.mk code resultTypeEq).code.program.resultType =
      .word :=
  resultTypeEq

@[simp] theorem ofChecked?_of_word
    (code : CheckedHostCoreProgram)
    (resultTypeEq : code.program.resultType = .word) :
    ofChecked? code = some ⟨code, resultTypeEq⟩ := by
  simp [ofChecked?, resultTypeEq]

@[simp] theorem ofChecked?_of_nonword
    (code : CheckedHostCoreProgram)
    (resultTypeNe : code.program.resultType ≠ .word) :
    ofChecked? code = none := by
  simp [ofChecked?, resultTypeNe]

@[simp] theorem ofProgram?_of_checked_word
    (program : Core.Program)
    (checked : program.checkHost = true)
    (resultTypeEq : program.resultType = .word) :
    ofProgram? program = some ⟨⟨program, checked⟩, resultTypeEq⟩ := by
  simp [ofProgram?, checked, resultTypeEq]

@[simp] theorem ofProgram?_of_rejected
    (program : Core.Program)
    (rejected : program.checkHost = false) :
    ofProgram? program = none := by
  simp [ofProgram?, CheckedHostCoreProgram.ofProgram?, rejected]

@[simp] theorem ofProgram?_of_checked_nonword
    (program : Core.Program)
    (checked : program.checkHost = true)
    (resultTypeNe : program.resultType ≠ .word) :
    ofProgram? program = none := by
  simp [ofProgram?, checked, ofChecked?, resultTypeNe]

end Solcore.ContractRuntime.CheckedHostCoreWordProgram

/-!
## Consolidated module: `Solcore.ContractRuntime.CheckedHostCoreWordProgramExecution`
-/

/-! Storage-backed execution specialized to checked Word-result programs. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

universe u v

namespace CheckedHostCoreWordProgram

/-- Run checked Word-result code with one immutable storage-host input. -/
def runWithStorage
    {RollbackState : Type u} {TraceState : Type v}
    (code : CheckedHostCoreWordProgram)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat) :
    HostDriverResult
      (HostStorageDriver.Context RollbackState TraceState) :=
  code.code.runWithStorage context inputs fuel

/-- Project the successful Word branch while keeping raw execution separate. -/
def runWithStorageReturnedFrameCompletion?
    {RollbackState : Type u} {TraceState : Type v}
    (code : CheckedHostCoreWordProgram)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat) :
    Option (WordReturnedFrameCompletion RollbackState TraceState) :=
  (code.runWithStorage context inputs fuel).toWordReturnedFrameCompletion?

end CheckedHostCoreWordProgram

end Solcore.ContractRuntime

/-!
## Consolidated module: `Solcore.ContractRuntime.CheckedHostCoreWordProgramExecutionProperties`
-/

/-! Safety, projection, stability, and fuel laws for checked Word execution. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

universe u v

namespace CheckedHostCoreWordProgram

theorem runWithStorage_hasType
    {RollbackState : Type u} {TraceState : Type v}
    (code : CheckedHostCoreWordProgram)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat) :
    (code.runWithStorage context inputs fuel).outcome.HasType
      .word code.code.program.dataDefinitions := by
  have typing := code.code.runWithStorage_hasType context inputs fuel
  rw [code.resultType_eq_word] at typing
  exact typing

theorem runWithStorage_ne_fault
    {RollbackState : Type u} {TraceState : Type v}
    (code : CheckedHostCoreWordProgram)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (error : Core.MachineFault)
    (faultState : Core.State) :
    (code.runWithStorage context inputs fuel).outcome ≠
      .fault error faultState := by
  simpa only [runWithStorage] using
    code.code.runWithStorage_ne_fault
      context inputs fuel error faultState

/-- Exact raw fault results are impossible for checked Word execution. -/
theorem runWithStorage_ne_fault_result
    {RollbackState : Type u} {TraceState : Type v}
    (code : CheckedHostCoreWordProgram)
    (context finalContext :
      HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (error : Core.MachineFault)
    (faultState : Core.State) :
    code.runWithStorage context inputs fuel ≠
      ⟨finalContext, .fault error faultState⟩ := by
  intro execution
  apply code.runWithStorage_ne_fault context inputs fuel error faultState
  exact congrArg HostDriverResult.outcome execution

/-- Every completed checked Word execution contains exactly a Word value. -/
theorem runWithStorage_done_word
    {RollbackState : Type u} {TraceState : Type v}
    (code : CheckedHostCoreWordProgram)
    (context finalContext :
      HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    {fuel : Nat} {value : Core.Value} {store : Core.Store}
    (execution :
      code.runWithStorage context inputs fuel =
        ⟨finalContext, .done value store⟩) :
    ∃ word, value = .word word := by
  have outcome :
      (code.code.runWithStorage context inputs fuel).outcome =
        .done value store := by
    simpa only [runWithStorage] using
      congrArg HostDriverResult.outcome execution
  obtain ⟨world, _storeTyping, valueTyping⟩ :=
    code.code.runWithStorage_done_hasType context inputs outcome
  rw [code.resultType_eq_word] at valueTyping
  exact valueTyping.word_shape

theorem runWithStorageReturnedFrameCompletion?_eq_some_iff
    {RollbackState : Type u} {TraceState : Type v}
    (code : CheckedHostCoreWordProgram)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (completion : WordReturnedFrameCompletion RollbackState TraceState) :
    code.runWithStorageReturnedFrameCompletion? context inputs fuel =
        some completion ↔
      code.runWithStorage context inputs fuel =
        completion.toHostDriverResult := by
  exact HostDriverResult.toWordReturnedFrameCompletion?_eq_some_iff
    (code.runWithStorage context inputs fuel) completion

/-- A checked Word projection is absent at exhaustion or a policy boundary. -/
theorem runWithStorageReturnedFrameCompletion?_eq_none_iff
    {RollbackState : Type u} {TraceState : Type v}
    (code : CheckedHostCoreWordProgram)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat) :
    code.runWithStorageReturnedFrameCompletion? context inputs fuel = none ↔
      (∃ finalContext exhausted,
        code.runWithStorage context inputs fuel =
          ⟨finalContext, .outOfFuel exhausted⟩) ∨
      ∃ finalContext suspension remainingFuel,
        code.runWithStorage context inputs fuel =
          ⟨finalContext, .unsupported suspension remainingFuel⟩ := by
  exact
    HostDriverResult.toWordReturnedFrameCompletion?_eq_none_iff_of_hasType
      (code.runWithStorage context inputs fuel)
      (code.runWithStorage_hasType context inputs fuel)

/-- Once a Word completion is available, every larger budget returns it. -/
theorem runWithStorageReturnedFrameCompletion?_some_stable
    {RollbackState : Type u} {TraceState : Type v}
    (code : CheckedHostCoreWordProgram)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    {fuel largerFuel : Nat}
    {completion : WordReturnedFrameCompletion RollbackState TraceState}
    (completed :
      code.runWithStorageReturnedFrameCompletion? context inputs fuel =
        some completion)
    (more : fuel ≤ largerFuel) :
    code.runWithStorageReturnedFrameCompletion?
        context inputs largerFuel = some completion := by
  have execution :=
    (code.runWithStorageReturnedFrameCompletion?_eq_some_iff
      context inputs fuel completion).mp completed
  have stable := code.code.runWithStorage_done_stable
    context inputs execution more
  exact
    (code.runWithStorageReturnedFrameCompletion?_eq_some_iff
      context inputs largerFuel completion).mpr stable

/-- Raw resumption uses the same immutable inputs and exact summed budget. -/
theorem runWithStorage_resumeWithFuel
    {RollbackState : Type u} {TraceState : Type v}
    (code : CheckedHostCoreWordProgram)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel additional : Nat) :
    (code.runWithStorage context inputs fuel).resumeWithFuel
        (@HostStorageDriver.handler RollbackState TraceState inputs)
        additional =
      code.runWithStorage context inputs (fuel + additional) := by
  simpa only [runWithStorage] using
    code.code.runWithStorage_resumeWithFuel
      context inputs fuel additional

/-- Classifying a resumed raw run agrees with classifying one summed run. -/
theorem toWordReturnedFrameCompletion?_resumeWithFuel_runWithStorage
    {RollbackState : Type u} {TraceState : Type v}
    (code : CheckedHostCoreWordProgram)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel additional : Nat) :
    ((code.runWithStorage context inputs fuel).resumeWithFuel
        (@HostStorageDriver.handler RollbackState TraceState inputs)
        additional).toWordReturnedFrameCompletion? =
      code.runWithStorageReturnedFrameCompletion?
        context inputs (fuel + additional) := by
  rw [code.runWithStorage_resumeWithFuel context inputs fuel additional]
  rfl

end CheckedHostCoreWordProgram

end Solcore.ContractRuntime
