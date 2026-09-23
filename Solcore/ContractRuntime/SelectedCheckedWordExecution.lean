import Solcore.ContractRuntime.CheckedHostCoreWordProgram
import Solcore.ContractRuntime.WorldStateWordCodeSelection
import Solcore.ContractRuntime.CheckedHostCoreWordCodeSelection

/-! Proof-refined execution of address-selected checked Word code. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

universe u v

/--
One address selection and its optional checked Word execution, indexed by the
exact initial context and immutable execution inputs.
-/
structure SelectedCheckedWordExecution
    {RollbackState : Type u} {TraceState : Type v}
    (initialContext : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs) where
  providedFuel : Nat
  selection : CheckedHostCoreWordCodeSelection
  selection_eq :
    selection =
      initialContext.context.values.working.1.selectWordCode
        inputs.codeAddress
  execution? :
    Option
      (CheckedHostCoreWordProgram ×
        HostDriverResult
          (HostStorageDriver.Context RollbackState TraceState))
  execution_eq_run :
    execution? =
      selection.toWordCode?.map fun code =>
        (code, code.runWithStorage initialContext inputs providedFuel)

namespace SelectedCheckedWordExecution

/-- Select once and run exactly the selected Word code, when one exists. -/
def start
    {RollbackState : Type u} {TraceState : Type v}
    (initialContext : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat) :
    SelectedCheckedWordExecution initialContext inputs :=
  let selection :=
    initialContext.context.values.working.1.selectWordCode
      inputs.codeAddress
  {
    providedFuel := fuel
    selection := selection
    selection_eq := rfl
    execution? :=
      selection.toWordCode?.map fun code =>
        (code, code.runWithStorage initialContext inputs fuel)
    execution_eq_run := rfl
  }

/-- Project only the existing successful checked Word completion. -/
def completion?
    {RollbackState : Type u} {TraceState : Type v}
    {initialContext : HostStorageDriver.Context RollbackState TraceState}
    {inputs : HostStorageDriver.ExecutionInputs}
    (execution : SelectedCheckedWordExecution initialContext inputs) :
    Option (WordReturnedFrameCompletion RollbackState TraceState) :=
  execution.execution?.bind fun selectedRun =>
    selectedRun.2.toWordReturnedFrameCompletion?

end SelectedCheckedWordExecution

end Solcore.ContractRuntime

/-!
## Consolidated module: `Solcore.ContractRuntime.SelectedCheckedWordExecutionProperties`
-/

/-! Canonical selection and execution laws for selected checked Word code. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.SelectedCheckedWordExecution

universe u v

@[simp] theorem start_providedFuel
    {RollbackState : Type u} {TraceState : Type v}
    (initialContext : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat) :
    (start initialContext inputs fuel).providedFuel = fuel :=
  rfl

@[simp] theorem start_selection
    {RollbackState : Type u} {TraceState : Type v}
    (initialContext : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat) :
    (start initialContext inputs fuel).selection =
      initialContext.context.values.working.1.selectWordCode
        inputs.codeAddress :=
  rfl

@[simp] theorem start_execution?
    {RollbackState : Type u} {TraceState : Type v}
    (initialContext : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat) :
    (start initialContext inputs fuel).execution? =
      (initialContext.context.values.working.1.selectWordCode
          inputs.codeAddress).toWordCode?.map fun code =>
        (code, code.runWithStorage initialContext inputs fuel) :=
  rfl

/-- The three computational fields determine the proof-refined execution. -/
@[ext] theorem ext
    {RollbackState : Type u} {TraceState : Type v}
    {initialContext : HostStorageDriver.Context RollbackState TraceState}
    {inputs : HostStorageDriver.ExecutionInputs}
    {left right : SelectedCheckedWordExecution initialContext inputs}
    (providedFuel : left.providedFuel = right.providedFuel)
    (selection : left.selection = right.selection)
    (execution : left.execution? = right.execution?) :
    left = right := by
  cases left
  cases right
  simp_all

/-- Every certified value is the canonical start at its recorded total fuel. -/
theorem eq_start
    {RollbackState : Type u} {TraceState : Type v}
    {initialContext : HostStorageDriver.Context RollbackState TraceState}
    {inputs : HostStorageDriver.ExecutionInputs}
    (execution : SelectedCheckedWordExecution initialContext inputs) :
    execution = start initialContext inputs execution.providedFuel := by
  apply ext
  · rfl
  · exact execution.selection_eq
  · rw [execution.execution_eq_run]
    simp only [start_execution?, execution.selection_eq]

/-- Erasing the retained branch recovers the exact selected checked code. -/
theorem selection_toCheckedCode?
    {RollbackState : Type u} {TraceState : Type v}
    {initialContext : HostStorageDriver.Context RollbackState TraceState}
    {inputs : HostStorageDriver.ExecutionInputs}
    (execution : SelectedCheckedWordExecution initialContext inputs) :
    execution.selection.toCheckedCode? =
      initialContext.context.values.working.1.code? inputs.codeAddress := by
  rw [execution.selection_eq]
  exact WorldState.toCheckedCode?_selectWordCode _ _

/-- Word projection is the existing optional refinement of selected code. -/
theorem selection_toWordCode?
    {RollbackState : Type u} {TraceState : Type v}
    {initialContext : HostStorageDriver.Context RollbackState TraceState}
    {inputs : HostStorageDriver.ExecutionInputs}
    (execution : SelectedCheckedWordExecution initialContext inputs) :
    execution.selection.toWordCode? =
      (initialContext.context.values.working.1.code?
        inputs.codeAddress).bind CheckedHostCoreWordProgram.ofChecked? := by
  rw [execution.selection_eq]
  exact WorldState.toWordCode?_selectWordCode _ _

/-- No raw execution exists exactly when no Word program was selected. -/
theorem execution?_eq_none_iff_toWordCode?_eq_none
    {RollbackState : Type u} {TraceState : Type v}
    {initialContext : HostStorageDriver.Context RollbackState TraceState}
    {inputs : HostStorageDriver.ExecutionInputs}
    (execution : SelectedCheckedWordExecution initialContext inputs) :
    execution.execution? = none ↔
      execution.selection.toWordCode? = none := by
  rw [execution.execution_eq_run]
  simp

theorem execution?_eq_none_of_codeAbsent
    {RollbackState : Type u} {TraceState : Type v}
    {initialContext : HostStorageDriver.Context RollbackState TraceState}
    {inputs : HostStorageDriver.ExecutionInputs}
    (execution : SelectedCheckedWordExecution initialContext inputs)
    (selected : execution.selection = .codeAbsent) :
    execution.execution? = none := by
  rw [execution.execution_eq_run, selected]
  rfl

theorem execution?_eq_none_of_nonWord
    {RollbackState : Type u} {TraceState : Type v}
    {initialContext : HostStorageDriver.Context RollbackState TraceState}
    {inputs : HostStorageDriver.ExecutionInputs}
    (execution : SelectedCheckedWordExecution initialContext inputs)
    (code : CheckedHostCoreProgram)
    (resultTypeNe : code.program.resultType ≠ .word)
    (selected : execution.selection = .nonWord code resultTypeNe) :
    execution.execution? = none := by
  rw [execution.execution_eq_run, selected]
  rfl

theorem execution?_eq_some_of_word
    {RollbackState : Type u} {TraceState : Type v}
    {initialContext : HostStorageDriver.Context RollbackState TraceState}
    {inputs : HostStorageDriver.ExecutionInputs}
    (execution : SelectedCheckedWordExecution initialContext inputs)
    (code : CheckedHostCoreWordProgram)
    (selected : execution.selection = .word code) :
    execution.execution? =
      some
        (code,
          code.runWithStorage initialContext inputs execution.providedFuel) := by
  rw [execution.execution_eq_run, selected]
  rfl

/-- Exact retained runs characterize the Word selection branch. -/
theorem execution?_eq_some_iff
    {RollbackState : Type u} {TraceState : Type v}
    {initialContext : HostStorageDriver.Context RollbackState TraceState}
    {inputs : HostStorageDriver.ExecutionInputs}
    (execution : SelectedCheckedWordExecution initialContext inputs)
    (code : CheckedHostCoreWordProgram)
    (result :
      HostDriverResult
        (HostStorageDriver.Context RollbackState TraceState)) :
    execution.execution? = some (code, result) ↔
      execution.selection = .word code ∧
        result =
          code.runWithStorage
            initialContext inputs execution.providedFuel := by
  rw [execution.execution_eq_run]
  cases selectionEq : execution.selection with
  | codeAbsent => simp
  | nonWord selectedCode resultTypeNe => simp
  | word selectedCode =>
      simp only [CheckedHostCoreWordCodeSelection.toWordCode?_word, Option.map_some,
        Option.some.injEq, Prod.mk.injEq,
        CheckedHostCoreWordCodeSelection.word.injEq]
      constructor
      · rintro ⟨rfl, rfl⟩
        exact ⟨rfl, rfl⟩
      · rintro ⟨rfl, rfl⟩
        exact ⟨rfl, rfl⟩

/-- Missing execution is exactly one of the two non-Word-execution branches. -/
theorem execution?_eq_none_iff_branches
    {RollbackState : Type u} {TraceState : Type v}
    {initialContext : HostStorageDriver.Context RollbackState TraceState}
    {inputs : HostStorageDriver.ExecutionInputs}
    (execution : SelectedCheckedWordExecution initialContext inputs) :
    execution.execution? = none ↔
      execution.selection = .codeAbsent ∨
        ∃ code resultTypeNe,
          execution.selection = .nonWord code resultTypeNe := by
  rw [execution.execution_eq_run]
  cases selectionEq : execution.selection with
  | codeAbsent => simp
  | nonWord code resultTypeNe =>
      exact ⟨fun _ => Or.inr ⟨code, resultTypeNe, rfl⟩, fun _ => rfl⟩
  | word code => simp

end Solcore.ContractRuntime.SelectedCheckedWordExecution

/-!
## Consolidated module: `Solcore.ContractRuntime.SelectedCheckedWordExecutionSafetyProperties`
-/

/-! Safety and exact completion laws for selected checked Word execution. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.SelectedCheckedWordExecution

universe u v

/-- At fixed indices, the cumulative offered fuel determines the whole value. -/
theorem eq_of_providedFuel_eq
    {RollbackState : Type u} {TraceState : Type v}
    {initialContext : HostStorageDriver.Context RollbackState TraceState}
    {inputs : HostStorageDriver.ExecutionInputs}
    (left right : SelectedCheckedWordExecution initialContext inputs)
    (providedFuel : left.providedFuel = right.providedFuel) :
    left = right := by
  calc
    left = start initialContext inputs left.providedFuel := eq_start left
    _ = start initialContext inputs right.providedFuel :=
      congrArg (start initialContext inputs) providedFuel
    _ = right := (eq_start right).symm

/-- Every retained raw run has the declared checked Word type. -/
theorem execution?_some_hasType
    {RollbackState : Type u} {TraceState : Type v}
    {initialContext : HostStorageDriver.Context RollbackState TraceState}
    {inputs : HostStorageDriver.ExecutionInputs}
    (execution : SelectedCheckedWordExecution initialContext inputs)
    (code : CheckedHostCoreWordProgram)
    (result :
      HostDriverResult
        (HostStorageDriver.Context RollbackState TraceState))
    (retained : execution.execution? = some (code, result)) :
    result.outcome.HasType .word code.code.program.dataDefinitions := by
  have exactRun :=
    (execution.execution?_eq_some_iff code result).mp retained
  rw [exactRun.2]
  exact code.runWithStorage_hasType
    initialContext inputs execution.providedFuel

/-- A retained checked Word run can never be an exact raw fault result. -/
theorem execution?_ne_some_fault
    {RollbackState : Type u} {TraceState : Type v}
    {initialContext : HostStorageDriver.Context RollbackState TraceState}
    {inputs : HostStorageDriver.ExecutionInputs}
    (execution : SelectedCheckedWordExecution initialContext inputs)
    (code : CheckedHostCoreWordProgram)
    (finalContext :
      HostStorageDriver.Context RollbackState TraceState)
    (error : Core.MachineFault)
    (faultState : Core.State) :
    execution.execution? ≠
      some (code, ⟨finalContext, .fault error faultState⟩) := by
  intro retained
  have exactRun :=
    (execution.execution?_eq_some_iff
      code ⟨finalContext, .fault error faultState⟩).mp retained
  exact code.runWithStorage_ne_fault_result
    initialContext finalContext inputs execution.providedFuel
      error faultState exactRun.2.symm

/-- Every completed retained execution contains exactly a Word value. -/
theorem execution?_some_done_word
    {RollbackState : Type u} {TraceState : Type v}
    {initialContext : HostStorageDriver.Context RollbackState TraceState}
    {inputs : HostStorageDriver.ExecutionInputs}
    (execution : SelectedCheckedWordExecution initialContext inputs)
    (code : CheckedHostCoreWordProgram)
    (finalContext :
      HostStorageDriver.Context RollbackState TraceState)
    (value : Core.Value)
    (store : Core.Store)
    (retained :
      execution.execution? =
        some (code, ⟨finalContext, .done value store⟩)) :
    ∃ word, value = .word word := by
  have exactRun :=
    (execution.execution?_eq_some_iff
      code ⟨finalContext, .done value store⟩).mp retained
  exact code.runWithStorage_done_word
    initialContext finalContext inputs exactRun.2.symm

/-- Successful selected projection reconstructs the exact retained raw run. -/
theorem completion?_eq_some_iff
    {RollbackState : Type u} {TraceState : Type v}
    {initialContext : HostStorageDriver.Context RollbackState TraceState}
    {inputs : HostStorageDriver.ExecutionInputs}
    (execution : SelectedCheckedWordExecution initialContext inputs)
    (completion :
      WordReturnedFrameCompletion RollbackState TraceState) :
    execution.completion? = some completion ↔
      ∃ code,
        execution.execution? =
          some (code, completion.toHostDriverResult) := by
  unfold completion?
  cases retained : execution.execution? with
  | none => simp
  | some selectedRun =>
      cases selectedRun with
      | mk code result =>
          simp only [Option.bind_some]
          rw [HostDriverResult.toWordReturnedFrameCompletion?_eq_some_iff]
          simp

/-- Successful projection exposes the exact selected code and canonical run. -/
theorem completion?_eq_some_iff_selected_run
    {RollbackState : Type u} {TraceState : Type v}
    {initialContext : HostStorageDriver.Context RollbackState TraceState}
    {inputs : HostStorageDriver.ExecutionInputs}
    (execution : SelectedCheckedWordExecution initialContext inputs)
    (completion :
      WordReturnedFrameCompletion RollbackState TraceState) :
    execution.completion? = some completion ↔
      ∃ code,
        execution.selection = .word code ∧
          code.runWithStorage
              initialContext inputs execution.providedFuel =
            completion.toHostDriverResult := by
  rw [execution.completion?_eq_some_iff completion]
  constructor
  · rintro ⟨code, retained⟩
    have exactRun :=
      (execution.execution?_eq_some_iff
        code completion.toHostDriverResult).mp retained
    exact ⟨code, exactRun.1, exactRun.2.symm⟩
  · rintro ⟨code, selected, exactRun⟩
    exact ⟨code,
      (execution.execution?_eq_some_iff
        code completion.toHostDriverResult).mpr
          ⟨selected, exactRun.symm⟩⟩

/--
Globally, missing completion means no Word execution, exact exhaustion, or an
explicit unsupported-policy boundary.
-/
theorem completion?_eq_none_iff
    {RollbackState : Type u} {TraceState : Type v}
    {initialContext : HostStorageDriver.Context RollbackState TraceState}
    {inputs : HostStorageDriver.ExecutionInputs}
    (execution : SelectedCheckedWordExecution initialContext inputs) :
    execution.completion? = none ↔
      execution.execution? = none ∨
        (∃ code finalContext exhausted,
          execution.execution? =
            some (code, ⟨finalContext, .outOfFuel exhausted⟩)) ∨
        ∃ code finalContext suspension remainingFuel,
          execution.execution? =
            some (code,
              ⟨finalContext, .unsupported suspension remainingFuel⟩) := by
  unfold completion?
  cases retained : execution.execution? with
  | none => simp
  | some selectedRun =>
      cases selectedRun with
      | mk code result =>
          have typing :=
            execution.execution?_some_hasType code result retained
          simp only [Option.bind_some]
          rw [HostDriverResult.toWordReturnedFrameCompletion?_eq_none_iff_of_hasType
            result typing]
          simp

/-- Under an exact Word selection, absence is exhaustion or policy rejection. -/
theorem completion?_eq_none_iff_of_word
    {RollbackState : Type u} {TraceState : Type v}
    {initialContext : HostStorageDriver.Context RollbackState TraceState}
    {inputs : HostStorageDriver.ExecutionInputs}
    (execution : SelectedCheckedWordExecution initialContext inputs)
    (code : CheckedHostCoreWordProgram)
    (selected : execution.selection = .word code) :
    execution.completion? = none ↔
      (∃ finalContext exhausted,
        execution.execution? =
          some (code, ⟨finalContext, .outOfFuel exhausted⟩)) ∨
      ∃ finalContext suspension remainingFuel,
        execution.execution? =
          some (code,
            ⟨finalContext, .unsupported suspension remainingFuel⟩) := by
  unfold completion?
  rw [execution.execution?_eq_some_of_word code selected]
  simp only [Option.bind_some]
  simpa only [CheckedHostCoreWordProgram.runWithStorageReturnedFrameCompletion?,
    Option.some.injEq, Prod.mk.injEq, true_and] using
      code.runWithStorageReturnedFrameCompletion?_eq_none_iff
        initialContext inputs execution.providedFuel

end Solcore.ContractRuntime.SelectedCheckedWordExecution

/-!
## Consolidated module: `Solcore.ContractRuntime.SelectedCheckedWordExecutionResumption`
-/

/-! Fixed-input fuel resumption for selected checked Word execution. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.SelectedCheckedWordExecution

universe u v

/--
Offer more fuel while preserving the exact selected code, initial context, and
immutable execution inputs.
-/
def resumeWithFuel
    {RollbackState : Type u} {TraceState : Type v}
    {initialContext : HostStorageDriver.Context RollbackState TraceState}
    {inputs : HostStorageDriver.ExecutionInputs}
    (execution : SelectedCheckedWordExecution initialContext inputs)
    (additional : Nat) :
    SelectedCheckedWordExecution initialContext inputs :=
  {
    providedFuel := execution.providedFuel + additional
    selection := execution.selection
    selection_eq := execution.selection_eq
    execution? := execution.execution?.map fun selectedRun =>
      (selectedRun.1,
        selectedRun.2.resumeWithFuel
          (@HostStorageDriver.handler RollbackState TraceState inputs)
          additional)
    execution_eq_run := by
      rw [execution.execution_eq_run]
      cases execution.selection with
      | codeAbsent => rfl
      | nonWord code resultTypeNe => rfl
      | word code =>
          simp only [CheckedHostCoreWordCodeSelection.toWordCode?_word,
            Option.map_some]
          rw [code.runWithStorage_resumeWithFuel
            initialContext inputs execution.providedFuel additional]
  }

@[simp] theorem resumeWithFuel_providedFuel
    {RollbackState : Type u} {TraceState : Type v}
    {initialContext : HostStorageDriver.Context RollbackState TraceState}
    {inputs : HostStorageDriver.ExecutionInputs}
    (execution : SelectedCheckedWordExecution initialContext inputs)
    (additional : Nat) :
    (execution.resumeWithFuel additional).providedFuel =
      execution.providedFuel + additional :=
  rfl

@[simp] theorem resumeWithFuel_selection
    {RollbackState : Type u} {TraceState : Type v}
    {initialContext : HostStorageDriver.Context RollbackState TraceState}
    {inputs : HostStorageDriver.ExecutionInputs}
    (execution : SelectedCheckedWordExecution initialContext inputs)
    (additional : Nat) :
    (execution.resumeWithFuel additional).selection = execution.selection :=
  rfl

@[simp] theorem resumeWithFuel_execution?
    {RollbackState : Type u} {TraceState : Type v}
    {initialContext : HostStorageDriver.Context RollbackState TraceState}
    {inputs : HostStorageDriver.ExecutionInputs}
    (execution : SelectedCheckedWordExecution initialContext inputs)
    (additional : Nat) :
    (execution.resumeWithFuel additional).execution? =
      execution.execution?.map fun selectedRun =>
        (selectedRun.1,
          selectedRun.2.resumeWithFuel
            (@HostStorageDriver.handler RollbackState TraceState inputs)
            additional) :=
  rfl

end Solcore.ContractRuntime.SelectedCheckedWordExecution

/-!
## Consolidated module: `Solcore.ContractRuntime.SelectedCheckedWordExecutionResumptionProperties`
-/

/-! Canonicality, algebra, and terminal stability of selected Word resumption. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.SelectedCheckedWordExecution

universe u v

/-- Resumption is the canonical one-shot selected run at the summed budget. -/
theorem resumeWithFuel_eq_start
    {RollbackState : Type u} {TraceState : Type v}
    {initialContext : HostStorageDriver.Context RollbackState TraceState}
    {inputs : HostStorageDriver.ExecutionInputs}
    (execution : SelectedCheckedWordExecution initialContext inputs)
    (additional : Nat) :
    execution.resumeWithFuel additional =
      start initialContext inputs
        (execution.providedFuel + additional) := by
  simpa using eq_start (execution.resumeWithFuel additional)

/-- Starting and then resuming agrees with one start at summed fuel. -/
theorem start_resumeWithFuel
    {RollbackState : Type u} {TraceState : Type v}
    (initialContext : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel additional : Nat) :
    (start initialContext inputs fuel).resumeWithFuel additional =
      start initialContext inputs (fuel + additional) := by
  simpa using
    resumeWithFuel_eq_start
      (start initialContext inputs fuel) additional

/-- Offering zero additional fuel is the identity on the whole value. -/
@[simp] theorem resumeWithFuel_zero
    {RollbackState : Type u} {TraceState : Type v}
    {initialContext : HostStorageDriver.Context RollbackState TraceState}
    {inputs : HostStorageDriver.ExecutionInputs}
    (execution : SelectedCheckedWordExecution initialContext inputs) :
    execution.resumeWithFuel 0 = execution := by
  apply eq_of_providedFuel_eq
  simp

/-- Successive fuel offers combine by addition on the whole value. -/
theorem resumeWithFuel_add
    {RollbackState : Type u} {TraceState : Type v}
    {initialContext : HostStorageDriver.Context RollbackState TraceState}
    {inputs : HostStorageDriver.ExecutionInputs}
    (execution : SelectedCheckedWordExecution initialContext inputs)
    (first second : Nat) :
    (execution.resumeWithFuel first).resumeWithFuel second =
      execution.resumeWithFuel (first + second) := by
  apply eq_of_providedFuel_eq
  simp [Nat.add_assoc]

/-- Resumption cannot create a raw run for either non-executing branch. -/
theorem resumeWithFuel_execution?_eq_none_iff
    {RollbackState : Type u} {TraceState : Type v}
    {initialContext : HostStorageDriver.Context RollbackState TraceState}
    {inputs : HostStorageDriver.ExecutionInputs}
    (execution : SelectedCheckedWordExecution initialContext inputs)
    (additional : Nat) :
    (execution.resumeWithFuel additional).execution? = none ↔
      execution.execution? = none := by
  simp

/-- Selected completion after resumption equals the summed one-shot view. -/
theorem completion?_resumeWithFuel_eq_start
    {RollbackState : Type u} {TraceState : Type v}
    {initialContext : HostStorageDriver.Context RollbackState TraceState}
    {inputs : HostStorageDriver.ExecutionInputs}
    (execution : SelectedCheckedWordExecution initialContext inputs)
    (additional : Nat) :
    (execution.resumeWithFuel additional).completion? =
      (start initialContext inputs
        (execution.providedFuel + additional)).completion? := by
  rw [execution.resumeWithFuel_eq_start additional]

/-- The exact successful raw run is terminal under every later fuel offer. -/
theorem execution?_resumeWithFuel_of_completion
    {RollbackState : Type u} {TraceState : Type v}
    {initialContext : HostStorageDriver.Context RollbackState TraceState}
    {inputs : HostStorageDriver.ExecutionInputs}
    (execution : SelectedCheckedWordExecution initialContext inputs)
    (additional : Nat)
    (code : CheckedHostCoreWordProgram)
    (completion :
      WordReturnedFrameCompletion RollbackState TraceState)
    (retained :
      execution.execution? =
        some (code, completion.toHostDriverResult)) :
    (execution.resumeWithFuel additional).execution? =
      some (code, completion.toHostDriverResult) := by
  rw [resumeWithFuel_execution?, retained]
  rfl

/-- Once selected Word completion exists, every resumption returns it exactly. -/
theorem completion?_resumeWithFuel_of_some
    {RollbackState : Type u} {TraceState : Type v}
    {initialContext : HostStorageDriver.Context RollbackState TraceState}
    {inputs : HostStorageDriver.ExecutionInputs}
    (execution : SelectedCheckedWordExecution initialContext inputs)
    (additional : Nat)
    (completion :
      WordReturnedFrameCompletion RollbackState TraceState)
    (completed : execution.completion? = some completion) :
    (execution.resumeWithFuel additional).completion? = some completion := by
  obtain ⟨code, retained⟩ :=
    (execution.completion?_eq_some_iff completion).mp completed
  apply (execution.resumeWithFuel additional).completion?_eq_some_iff
    completion |>.mpr
  exact ⟨code,
    execution.execution?_resumeWithFuel_of_completion
      additional code completion retained⟩

end Solcore.ContractRuntime.SelectedCheckedWordExecution
