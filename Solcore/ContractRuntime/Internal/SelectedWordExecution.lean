import Solcore.ContractRuntime.Internal.ContractLaws
import Solcore.ContractRuntime.Internal.WorldStateLaws
import Solcore.ContractRuntime.Internal.ParentIndexedFrames
import Solcore.ContractRuntime.Internal.StorageDriverLaws
import Solcore.ContractRuntime.Internal.ParentIndexedExecution

/-!
# Selected word execution

Code selected by address and classified as Word code, executed with its proof, with or without
parent-indexed provenance. Tests use this refinement layer; the top-level runners do not.
-/

section
-- leanmerge: from Solcore.ContractRuntime.CheckedHostCoreWordCodeSelection
/-! Branch-complete refinement of optional checked code by Word result type. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

/-- Exact absence, non-Word code, or Word-refined checked code. -/
inductive CheckedHostCoreWordCodeSelection where
  | codeAbsent
  | nonWord
      (code : CheckedHostCoreProgram)
      (resultType_ne_word : code.program.resultType ≠ .word)
  | word (code : CheckedHostCoreWordProgram)

namespace CheckedHostCoreWordCodeSelection

/-- Classify an existing optional checked-code observation without rerunning a checker. -/
def classify
    (selected : Option CheckedHostCoreProgram) :
    CheckedHostCoreWordCodeSelection :=
  match selected with
  | none => .codeAbsent
  | some code =>
      if resultTypeEq : code.program.resultType = .word then
        .word ⟨code, resultTypeEq⟩
      else
        .nonWord code resultTypeEq

/-- Erase only the Word-result refinement and recover existing code selection. -/
def toCheckedCode? :
    CheckedHostCoreWordCodeSelection → Option CheckedHostCoreProgram
  | .codeAbsent => none
  | .nonWord code _ => some code
  | .word code => some code.code

/-- Project checked Word code only from the exact Word branch. -/
def toWordCode? :
    CheckedHostCoreWordCodeSelection → Option CheckedHostCoreWordProgram
  | .word code => some code
  | .codeAbsent | .nonWord .. => none

end CheckedHostCoreWordCodeSelection

end Solcore.ContractRuntime

/-!
## Consolidated module: `Solcore.ContractRuntime.CheckedHostCoreWordCodeSelectionProperties`
-/

/-! Exact branches and erasure laws for checked Word-code classification. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.CheckedHostCoreWordCodeSelection

@[simp] theorem classify_none :
    classify none = .codeAbsent :=
  rfl

@[simp] theorem classify_some_word
    (code : CheckedHostCoreProgram)
    (resultTypeEq : code.program.resultType = .word) :
    classify (some code) = .word ⟨code, resultTypeEq⟩ := by
  simp [classify, resultTypeEq]

@[simp] theorem classify_some_nonWord
    (code : CheckedHostCoreProgram)
    (resultTypeNe : code.program.resultType ≠ .word) :
    classify (some code) = .nonWord code resultTypeNe := by
  simp [classify, resultTypeNe]

@[simp] theorem toCheckedCode?_codeAbsent :
    toCheckedCode? .codeAbsent = none :=
  rfl

@[simp] theorem toCheckedCode?_nonWord
    (code : CheckedHostCoreProgram)
    (resultTypeNe : code.program.resultType ≠ .word) :
    toCheckedCode? (.nonWord code resultTypeNe) = some code :=
  rfl

@[simp] theorem toCheckedCode?_word
    (code : CheckedHostCoreWordProgram) :
    toCheckedCode? (.word code) = some code.code :=
  rfl

@[simp] theorem toWordCode?_codeAbsent :
    toWordCode? .codeAbsent = none :=
  rfl

@[simp] theorem toWordCode?_nonWord
    (code : CheckedHostCoreProgram)
    (resultTypeNe : code.program.resultType ≠ .word) :
    toWordCode? (.nonWord code resultTypeNe) = none :=
  rfl

@[simp] theorem toWordCode?_word
    (code : CheckedHostCoreWordProgram) :
    toWordCode? (.word code) = some code :=
  rfl

/-- Classification erases to the exact optional checked-code observation. -/
@[simp] theorem toCheckedCode?_classify
    (selected : Option CheckedHostCoreProgram) :
    toCheckedCode? (classify selected) = selected := by
  cases selected with
  | none => rfl
  | some code =>
      by_cases resultTypeEq : code.program.resultType = .word
      · simp [classify, resultTypeEq]
      · simp [classify, resultTypeEq]

/-- Every explicitly constructed branch is canonical after erasure. -/
@[simp] theorem classify_toCheckedCode?
    (selection : CheckedHostCoreWordCodeSelection) :
    classify selection.toCheckedCode? = selection := by
  cases selection with
  | codeAbsent => rfl
  | nonWord code resultTypeNe =>
      exact classify_some_nonWord code resultTypeNe
  | word code =>
      cases code with
      | mk checked resultTypeEq =>
          exact classify_some_word checked resultTypeEq

/-- Checked-code erasure is injective because classification is canonical. -/
theorem toCheckedCode?_injective :
    Function.Injective toCheckedCode? := by
  intro left right erased
  calc
    left = classify left.toCheckedCode? :=
      (classify_toCheckedCode? left).symm
    _ = classify right.toCheckedCode? := congrArg classify erased
    _ = right := classify_toCheckedCode? right

/-- Word projection agrees exactly with the ADR-0141 optional refinement. -/
@[simp] theorem toWordCode?_classify
    (selected : Option CheckedHostCoreProgram) :
    toWordCode? (classify selected) =
      selected.bind CheckedHostCoreWordProgram.ofChecked? := by
  cases selected with
  | none => rfl
  | some code =>
      by_cases resultTypeEq : code.program.resultType = .word
      · simp [classify, CheckedHostCoreWordProgram.ofChecked?, resultTypeEq]
      · simp [classify, CheckedHostCoreWordProgram.ofChecked?, resultTypeEq]

theorem classify_eq_codeAbsent_iff
    (selected : Option CheckedHostCoreProgram) :
    classify selected = .codeAbsent ↔ selected = none := by
  constructor
  · intro classified
    have erased := congrArg toCheckedCode? classified
    simpa using erased
  · intro absent
    subst selected
    rfl

theorem classify_eq_nonWord_iff
    (selected : Option CheckedHostCoreProgram)
    (code : CheckedHostCoreProgram)
    (resultTypeNe : code.program.resultType ≠ .word) :
    classify selected = .nonWord code resultTypeNe ↔
      selected = some code := by
  constructor
  · intro classified
    have erased := congrArg toCheckedCode? classified
    simpa using erased
  · intro selectedEq
    subst selected
    exact classify_some_nonWord code resultTypeNe

theorem classify_eq_word_iff
    (selected : Option CheckedHostCoreProgram)
    (code : CheckedHostCoreWordProgram) :
    classify selected = .word code ↔
      selected = some code.code := by
  constructor
  · intro classified
    have erased := congrArg toCheckedCode? classified
    simpa using erased
  · intro selectedEq
    subst selected
    cases code with
    | mk checked resultTypeEq =>
        exact classify_some_word checked resultTypeEq

theorem codeAbsent_ne_nonWord
    (code : CheckedHostCoreProgram)
    (resultTypeNe : code.program.resultType ≠ .word) :
    CheckedHostCoreWordCodeSelection.codeAbsent ≠
      CheckedHostCoreWordCodeSelection.nonWord code resultTypeNe := by
  simp

theorem codeAbsent_ne_word
    (code : CheckedHostCoreWordProgram) :
    CheckedHostCoreWordCodeSelection.codeAbsent ≠
      CheckedHostCoreWordCodeSelection.word code := by
  simp

theorem nonWord_ne_word
    (nonWordCode : CheckedHostCoreProgram)
    (resultTypeNe : nonWordCode.program.resultType ≠ .word)
    (wordCode : CheckedHostCoreWordProgram) :
    CheckedHostCoreWordCodeSelection.nonWord nonWordCode resultTypeNe ≠
      CheckedHostCoreWordCodeSelection.word wordCode := by
  simp

/-- The total classifier always exposes one and only one constructor shape. -/
theorem classify_exhaustive
    (selected : Option CheckedHostCoreProgram) :
    classify selected = .codeAbsent ∨
      (∃ code resultTypeNe,
        classify selected = .nonWord code resultTypeNe) ∨
      ∃ code, classify selected = .word code := by
  cases classified : classify selected with
  | codeAbsent => exact Or.inl rfl
  | nonWord code resultTypeNe =>
      exact Or.inr (Or.inl ⟨code, resultTypeNe, rfl⟩)
  | word code => exact Or.inr (Or.inr ⟨code, rfl⟩)

end Solcore.ContractRuntime.CheckedHostCoreWordCodeSelection
end

section
-- leanmerge: from Solcore.ContractRuntime.WorldStateWordCodeSelection
/-! Address-selected checked Word-code classification in WorldState. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.WorldState

/-- Classify the existing checked-code observation at one exact Address. -/
def selectWordCode
    (state : WorldState)
    (codeAddress : Address) :
    CheckedHostCoreWordCodeSelection :=
  CheckedHostCoreWordCodeSelection.classify
    (state.code? codeAddress)

end Solcore.ContractRuntime.WorldState

/-!
## Consolidated module: `Solcore.ContractRuntime.WorldStateWordCodeSelectionProperties`
-/

/-! Exact lookup and preservation laws for selected checked Word code. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.WorldState

open CheckedHostCoreWordCodeSelection

/-- Erasing refinement recovers the canonical address-selected code lookup. -/
@[simp] theorem toCheckedCode?_selectWordCode
    (state : WorldState)
    (codeAddress : Address) :
    (state.selectWordCode codeAddress).toCheckedCode? =
      state.code? codeAddress := by
  exact toCheckedCode?_classify (state.code? codeAddress)

/-- Word projection is exactly optional refinement of the selected code. -/
@[simp] theorem toWordCode?_selectWordCode
    (state : WorldState)
    (codeAddress : Address) :
    (state.selectWordCode codeAddress).toWordCode? =
      (state.code? codeAddress).bind
        CheckedHostCoreWordProgram.ofChecked? := by
  exact toWordCode?_classify (state.code? codeAddress)

theorem selectWordCode_eq_codeAbsent_iff
    (state : WorldState)
    (codeAddress : Address) :
    state.selectWordCode codeAddress = .codeAbsent ↔
      state.code? codeAddress = none := by
  exact classify_eq_codeAbsent_iff (state.code? codeAddress)

theorem selectWordCode_eq_nonWord_iff
    (state : WorldState)
    (codeAddress : Address)
    (code : CheckedHostCoreProgram)
    (resultTypeNe : code.program.resultType ≠ .word) :
    state.selectWordCode codeAddress = .nonWord code resultTypeNe ↔
      state.code? codeAddress = some code := by
  exact classify_eq_nonWord_iff
    (state.code? codeAddress) code resultTypeNe

theorem selectWordCode_eq_word_iff
    (state : WorldState)
    (codeAddress : Address)
    (code : CheckedHostCoreWordProgram) :
    state.selectWordCode codeAddress = .word code ↔
      state.code? codeAddress = some code.code := by
  exact classify_eq_word_iff (state.code? codeAddress) code

@[simp] theorem selectWordCode_of_absent
    (state : WorldState)
    (codeAddress : Address)
    (absent : state.account? codeAddress = none) :
    state.selectWordCode codeAddress = .codeAbsent := by
  apply (state.selectWordCode_eq_codeAbsent_iff codeAddress).2
  exact state.code?_of_absent codeAddress absent

@[simp] theorem selectWordCode_of_account_without_code
    (state : WorldState)
    (codeAddress : Address)
    (account : Account)
    (present : state.account? codeAddress = some account)
    (withoutCode : account.code? = none) :
    state.selectWordCode codeAddress = .codeAbsent := by
  apply (state.selectWordCode_eq_codeAbsent_iff codeAddress).2
  exact state.code?_of_account_without_code
    codeAddress account present withoutCode

@[simp] theorem selectWordCode_of_present_nonWord
    (state : WorldState)
    (codeAddress : Address)
    (account : Account)
    (code : CheckedHostCoreProgram)
    (resultTypeNe : code.program.resultType ≠ .word)
    (accountPresent : state.account? codeAddress = some account)
    (codePresent : account.code? = some code) :
    state.selectWordCode codeAddress = .nonWord code resultTypeNe := by
  apply (state.selectWordCode_eq_nonWord_iff
    codeAddress code resultTypeNe).2
  exact state.code?_of_present
    codeAddress account code accountPresent codePresent

@[simp] theorem selectWordCode_of_present_word
    (state : WorldState)
    (codeAddress : Address)
    (account : Account)
    (code : CheckedHostCoreWordProgram)
    (accountPresent : state.account? codeAddress = some account)
    (codePresent : account.code? = some code.code) :
    state.selectWordCode codeAddress = .word code := by
  apply (state.selectWordCode_eq_word_iff codeAddress code).2
  exact state.code?_of_present
    codeAddress account code.code accountPresent codePresent

@[simp] theorem selectWordCode_putAccount_same
    (state : WorldState)
    (codeAddress : Address)
    (account : Account) :
    (state.putAccount codeAddress account).selectWordCode codeAddress =
      classify account.code? := by
  simp [selectWordCode, code?, putAccount, account?]

/-- Writing Account storage cannot change its selected Word-code branch. -/
@[simp] theorem selectWordCode_putAccount_storageWrite_same
    (state : WorldState)
    (codeAddress : Address)
    (account : Account)
    (slot value : Core.Word) :
    (state.putAccount codeAddress
        (account.storageWrite slot value)).selectWordCode codeAddress =
      (state.putAccount codeAddress account).selectWordCode codeAddress := by
  simp [Account.code?_storageWrite]

end Solcore.ContractRuntime.WorldState
end

section
-- leanmerge: from Solcore.ContractRuntime.SelectedCheckedWordExecution
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
end

section
-- leanmerge: from Solcore.ContractRuntime.ParentIndexedSelectedCheckedWordExecution
/-! Parent-indexed storage provenance for selected checked Word execution. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

universe u v

/--
A selected checked Word execution whose initial storage context is proven to
come from one exact parent initialization and storage Address.
-/
structure ParentIndexedSelectedCheckedWordExecution
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs) where
  initialContext :
    HostStorageDriver.Context RollbackState (FrameTrace Event)
  context_refined :
    initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
        storageAddress =
      some initialContext
  execution : SelectedCheckedWordExecution initialContext inputs

namespace ParentIndexedSelectedCheckedWordExecution

/-- Erase only the named parent provenance wrapper to its dependent pair. -/
def toExecutionSigma
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs) :
    Σ context : HostStorageDriver.Context
        RollbackState (FrameTrace Event),
      SelectedCheckedWordExecution context inputs :=
  ⟨entry.initialContext, entry.execution⟩

/--
Refine storage once and start ADR-0143 in exactly the resulting present
context. Outer absence means only that the storage Account is absent.
-/
def start?
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat) :
    Option
      (ParentIndexedSelectedCheckedWordExecution
        initialization storageAddress inputs) :=
  match contextRefined :
      initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
        storageAddress with
  | none => none
  | some context =>
      some {
        initialContext := context
        context_refined := contextRefined
        execution := SelectedCheckedWordExecution.start context inputs fuel
      }

end ParentIndexedSelectedCheckedWordExecution

end Solcore.ContractRuntime

/-!
## Consolidated module: `Solcore.ContractRuntime.ParentIndexedSelectedCheckedWordExecutionProperties`
-/

/-! Exact storage refinement and provenance laws for ADR-0144. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ParentIndexedSelectedCheckedWordExecution

universe u v

/-- Outer absence means exactly that the selected storage Account is absent. -/
theorem start?_eq_none_iff
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat) :
    start? initialization storageAddress inputs fuel = none ↔
      initialization.initialWorld.account? storageAddress = none := by
  cases observed : initialization.initialWorld.account? storageAddress with
  | none =>
      have refinedNone :=
        ParentIndexedFrameInitialization.toCheckpointedWorkingPairWithPresentStorageAccount?_of_absent
          initialization storageAddress observed
      unfold start?
      split
      · simp
      · rename_i context refinedSome
        rw [refinedNone] at refinedSome
        contradiction
  | some account =>
      have refinedSome :=
        ParentIndexedFrameInitialization.toCheckpointedWorkingPairWithPresentStorageAccount?_of_present
          initialization storageAddress account observed
      unfold start?
      split
      · rename_i refinedNone
        rw [refinedSome] at refinedNone
        contradiction
      · simp

/-- Exact present storage refinement starts the exact ADR-0143 execution. -/
@[simp] theorem start?_of_present
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (context : HostStorageDriver.Context RollbackState (FrameTrace Event))
    (refined :
      initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
          storageAddress = some context) :
    start? initialization storageAddress inputs fuel =
      some
        (ParentIndexedSelectedCheckedWordExecution.mk context refined
          (SelectedCheckedWordExecution.start context inputs fuel)) := by
  unfold start?
  split
  · rename_i refinedNone
    rw [refined] at refinedNone
    contradiction
  · rename_i selectedContext selected
    have contextEq : selectedContext = context :=
      Option.some.inj (selected.symm.trans refined)
    subst selectedContext
    rfl

/-- The named carrier erases to exactly the existing refinement and inner start. -/
theorem toExecutionSigma_start?
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat) :
    (start? initialization storageAddress inputs fuel).map toExecutionSigma =
      (initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
        storageAddress).map fun context =>
          ⟨context,
            SelectedCheckedWordExecution.start context inputs fuel⟩ := by
  let erasedStart :
      (context : HostStorageDriver.Context
        RollbackState (FrameTrace Event)) →
        (Σ context : HostStorageDriver.Context
            RollbackState (FrameTrace Event),
          SelectedCheckedWordExecution context inputs) :=
    fun context =>
      ⟨context,
        SelectedCheckedWordExecution.start context inputs fuel⟩
  unfold start?
  split
  · rename_i refinedNone
    simpa [erasedStart, toExecutionSigma] using
      (congrArg (Option.map erasedStart) refinedNone).symm
  · rename_i context refinedSome
    simpa [erasedStart, toExecutionSigma] using
      (congrArg (Option.map erasedStart) refinedSome).symm

/-- The initial context and inner execution determine the provenance carrier. -/
@[ext] theorem ext
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    {left right : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs}
    (initialContext : left.initialContext = right.initialContext)
    (execution : HEq left.execution right.execution) :
    left = right := by
  cases left
  cases right
  simp_all

/-- A returned carrier is exact iff its inner value is the canonical start. -/
theorem start?_eq_some_iff
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs) :
    start? initialization storageAddress inputs fuel = some entry ↔
      entry.execution =
        SelectedCheckedWordExecution.start
          entry.initialContext inputs fuel := by
  constructor
  · intro started
    cases entry with
    | mk context refined execution =>
        rw [start?_of_present initialization storageAddress inputs fuel
          context refined] at started
        have entryEq := Option.some.inj started
        cases entryEq
        rfl
  · intro executionEq
    cases entry with
    | mk context refined execution =>
        rw [start?_of_present initialization storageAddress inputs fuel
          context refined]
        simp only [Option.some.injEq]
        apply ext
        · rfl
        · exact heq_of_eq executionEq.symm

/-- Every provenance carrier is the canonical start at its inner total fuel. -/
theorem start?_canonical
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs) :
    start? initialization storageAddress inputs
        entry.execution.providedFuel =
      some entry := by
  apply (start?_eq_some_iff initialization storageAddress inputs
    entry.execution.providedFuel entry).2
  exact SelectedCheckedWordExecution.eq_start entry.execution

/-- The retained context contains exactly the initialization's frame values. -/
theorem initialContext_values
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs) :
    entry.initialContext.context.values =
      initialization.toCheckpointedWorkingPair := by
  cases entry with
  | mk context refined execution =>
      unfold ParentIndexedFrameInitialization.toCheckpointedWorkingPairWithPresentStorageAccount?
        at refined
      unfold FrameCheckpointedWorkingPairWithStorageAddress.withPresentStorageAccount?
        at refined
      split at refined
      · contradiction
      · have contextEq := Option.some.inj refined
        cases contextEq
        rfl

/-- The retained initial selector is the requested storage Address. -/
theorem initialContext_storageAddress
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs) :
    entry.initialContext.context.storageAddress = storageAddress := by
  cases entry with
  | mk context refined execution =>
      unfold ParentIndexedFrameInitialization.toCheckpointedWorkingPairWithPresentStorageAccount?
        at refined
      unfold FrameCheckpointedWorkingPairWithStorageAddress.withPresentStorageAccount?
        at refined
      split at refined
      · contradiction
      · have contextEq := Option.some.inj refined
        cases contextEq
        rfl

/-- Inner code selection observes exactly the initialization's working world. -/
theorem selection_eq_initialWorld
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs) :
    entry.execution.selection =
      initialization.initialWorld.selectWordCode inputs.codeAddress := by
  rw [entry.execution.selection_eq, entry.initialContext_values]
  rfl

/-- The initial checkpoint is exactly the indexed parent working pair. -/
theorem initialContext_checkpoint
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs) :
    entry.initialContext.context.values.checkpoint =
      FrameCheckpointSnapshot.fromWorkingPair parentWorking := by
  rw [entry.initialContext_values,
    ParentIndexedFrameInitialization.toCheckpointedWorkingPair_eq]

/-- Initial working effects retain the supplied rollback and parent trace. -/
theorem initialContext_workingEffects
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs) :
    entry.initialContext.context.values.working.2 =
      ⟨initialization.workingRollback, parentWorking.2.trace⟩ := by
  rw [entry.initialContext_values,
    ParentIndexedFrameInitialization.toCheckpointedWorkingPair_eq]

end Solcore.ContractRuntime.ParentIndexedSelectedCheckedWordExecution

/-!
## Consolidated module: `Solcore.ContractRuntime.ParentIndexedSelectedCheckedWordExecutionResumption`
-/

/-! Closed fuel resumption for parent-indexed selected checked Word execution. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ParentIndexedSelectedCheckedWordExecution

universe u v

/--
Offer more fuel without replacing the parent initialization, storage Address,
immutable execution inputs, or the exact refined initial context.
-/
def resumeWithFuel
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs)
    (additional : Nat) :
    ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs :=
  {
    initialContext := entry.initialContext
    context_refined := entry.context_refined
    execution := entry.execution.resumeWithFuel additional
  }

@[simp] theorem resumeWithFuel_initialContext
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs)
    (additional : Nat) :
    (entry.resumeWithFuel additional).initialContext =
      entry.initialContext :=
  rfl

@[simp] theorem resumeWithFuel_execution
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs)
    (additional : Nat) :
    (entry.resumeWithFuel additional).execution =
      entry.execution.resumeWithFuel additional :=
  rfl

@[simp] theorem resumeWithFuel_providedFuel
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs)
    (additional : Nat) :
    (entry.resumeWithFuel additional).execution.providedFuel =
      entry.execution.providedFuel + additional :=
  rfl

@[simp] theorem resumeWithFuel_selection
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs)
    (additional : Nat) :
    (entry.resumeWithFuel additional).execution.selection =
      entry.execution.selection :=
  rfl

end Solcore.ContractRuntime.ParentIndexedSelectedCheckedWordExecution

/-!
## Consolidated module: `Solcore.ContractRuntime.ParentIndexedSelectedCheckedWordExecutionResumptionProperties`
-/

/-! Canonicality and algebra for parent-indexed selected Word resumption. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ParentIndexedSelectedCheckedWordExecution

universe u v

/-- A resumed carrier is the exact parent start at its summed budget. -/
theorem some_resumeWithFuel_eq_start?
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs)
    (additional : Nat) :
    some (entry.resumeWithFuel additional) =
      start? initialization storageAddress inputs
        (entry.execution.providedFuel + additional) := by
  rw [start?_of_present initialization storageAddress inputs
    (entry.execution.providedFuel + additional) entry.initialContext
    entry.context_refined]
  congr 1
  apply ext
  · rfl
  · exact heq_of_eq
      (SelectedCheckedWordExecution.resumeWithFuel_eq_start
        entry.execution additional)

/-- Starting and then resuming agrees with one parent start at summed fuel. -/
theorem start?_map_resumeWithFuel
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel additional : Nat) :
    (start? initialization storageAddress inputs fuel).map
        (fun entry => entry.resumeWithFuel additional) =
      start? initialization storageAddress inputs (fuel + additional) := by
  cases started : start? initialization storageAddress inputs fuel with
  | none =>
      have absent :=
        (start?_eq_none_iff initialization storageAddress inputs fuel).mp
          started
      simpa [started] using
        ((start?_eq_none_iff initialization storageAddress inputs
          (fuel + additional)).mpr absent).symm
  | some entry =>
      have fuelEq : entry.execution.providedFuel = fuel := by
        have canonical :=
          (start?_eq_some_iff initialization storageAddress inputs fuel
            entry).mp started
        rw [canonical]
        rfl
      simpa [started, fuelEq] using entry.some_resumeWithFuel_eq_start? additional

/-- Offering zero additional fuel preserves the entire provenance carrier. -/
@[simp] theorem resumeWithFuel_zero
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs) :
    entry.resumeWithFuel 0 = entry := by
  apply ext
  · rfl
  · exact heq_of_eq entry.execution.resumeWithFuel_zero

/-- Successive fuel offers combine by addition on the whole carrier. -/
theorem resumeWithFuel_add
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs)
    (first second : Nat) :
    (entry.resumeWithFuel first).resumeWithFuel second =
      entry.resumeWithFuel (first + second) := by
  apply ext
  · rfl
  · exact heq_of_eq
      (SelectedCheckedWordExecution.resumeWithFuel_add
        entry.execution first second)

/-- Completion after resumption is exactly the inner fixed-input view. -/
theorem completion?_resumeWithFuel
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs)
    (additional : Nat) :
    (entry.resumeWithFuel additional).execution.completion? =
      (SelectedCheckedWordExecution.start entry.initialContext inputs
        (entry.execution.providedFuel + additional)).completion? := by
  exact SelectedCheckedWordExecution.completion?_resumeWithFuel_eq_start
    entry.execution additional

/-- Once completion exists, parent resumption retains that exact completion. -/
theorem completion?_resumeWithFuel_of_some
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs)
    (additional : Nat)
    (completion :
      WordReturnedFrameCompletion RollbackState (FrameTrace Event))
    (completed : entry.execution.completion? = some completion) :
    (entry.resumeWithFuel additional).execution.completion? =
      some completion :=
  SelectedCheckedWordExecution.completion?_resumeWithFuel_of_some
    entry.execution additional completion completed

end Solcore.ContractRuntime.ParentIndexedSelectedCheckedWordExecution

/-!
## Consolidated module: `Solcore.ContractRuntime.ParentIndexedSelectedCheckedWordExecutionDelegationProperties`
-/

/-! Direct parent-carrier access to retained ADR-0143 branches and provenance. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ParentIndexedSelectedCheckedWordExecution

universe u v

/-- The retained initial working rollback is exactly the initialization input. -/
theorem initialContext_workingRollback
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs) :
    entry.initialContext.context.values.working.2.rollback =
      initialization.workingRollback := by
  rw [entry.initialContext_workingEffects]

/-- The retained initial working trace is exactly the indexed parent trace. -/
theorem initialContext_parentTrace
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs) :
    entry.initialContext.context.values.working.2.trace =
      parentWorking.2.trace := by
  rw [entry.initialContext_workingEffects]

/-- Missing raw execution is exactly code absence or checked non-Word code. -/
theorem execution?_eq_none_iff_branches
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs) :
    entry.execution.execution? = none ↔
      entry.execution.selection = .codeAbsent ∨
        ∃ code resultTypeNe,
          entry.execution.selection = .nonWord code resultTypeNe :=
  entry.execution.execution?_eq_none_iff_branches

/-- Exact completion reconstructs the exact selected checked Word raw result. -/
theorem completion?_eq_some_iff
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs)
    (completion :
      WordReturnedFrameCompletion RollbackState (FrameTrace Event)) :
    entry.execution.completion? = some completion ↔
      ∃ code,
        entry.execution.execution? =
          some (code, completion.toHostDriverResult) :=
  entry.execution.completion?_eq_some_iff completion

/-- Missing completion retains absence, exhaustion, and policy rejection. -/
theorem completion?_eq_none_iff
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs) :
    entry.execution.completion? = none ↔
      entry.execution.execution? = none ∨
        (∃ code finalContext exhausted,
          entry.execution.execution? =
            some (code, ⟨finalContext, .outOfFuel exhausted⟩)) ∨
        ∃ code finalContext suspension remainingFuel,
          entry.execution.execution? =
            some (code,
              ⟨finalContext, .unsupported suspension remainingFuel⟩) :=
  entry.execution.completion?_eq_none_iff

end Solcore.ContractRuntime.ParentIndexedSelectedCheckedWordExecution

/-!
## Consolidated module: `Solcore.ContractRuntime.ParentIndexedSelectedCheckedWordExecutionContinuation`
-/

/-! Canonical returned-parent projection for selected checked Word execution. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ParentIndexedSelectedCheckedWordExecution

universe u v w

/--
Build the returned parent continuation only from the exact completion projected
by this execution. The equality prevents unrelated completion data from being
assigned this carrier's provenance.
-/
def toReturnedContinuation
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs)
    (completion :
      WordReturnedFrameCompletion RollbackState (FrameTrace Event))
    (_completed : entry.execution.completion? = some completion) :
    ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking :=
  ParentIndexedFrameContinuationContext.fromTraceExtension
    parentWorking initialization.workingRollback
    initialization.initialTraceExtension
    completion.toFrameContinuationContext.result

/--
Retain the exact canonical Word completion together with its proof-linked
returned parent continuation.
-/
def returnedCompletion?
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs) :
    Option
      (WordReturnedFrameCompletion RollbackState (FrameTrace Event) ×
        ParentIndexedFrameContinuationContext
          RollbackState Event TrapReason parentWorking) :=
  match completed : entry.execution.completion? with
  | none => none
  | some completion =>
      some (completion, entry.toReturnedContinuation completion completed)

/-- Forget only the retained completion; this is not a second producer. -/
def returnedContinuation?
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs) :
    Option
      (ParentIndexedFrameContinuationContext
        RollbackState Event TrapReason parentWorking) :=
  (entry.returnedCompletion? (TrapReason := TrapReason)).map Prod.snd

end Solcore.ContractRuntime.ParentIndexedSelectedCheckedWordExecution

/-!
## Consolidated module: `Solcore.ContractRuntime.ParentIndexedSelectedCheckedWordExecutionContinuationProperties`
-/

/-! Exact branch and projection laws for canonical returned-parent completion. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ParentIndexedSelectedCheckedWordExecution

universe u v w

/-- A missing pair is exactly a missing inner Word completion. -/
theorem returnedCompletion?_eq_none_iff
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs) :
    entry.returnedCompletion? (TrapReason := TrapReason) = none ↔
      entry.execution.completion? = none := by
  unfold returnedCompletion?
  split <;> simp_all

/-- Exact inner completion constructs the proof-linked pair. -/
theorem returnedCompletion?_of_completion
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs)
    (completion :
      WordReturnedFrameCompletion RollbackState (FrameTrace Event))
    (completed : entry.execution.completion? = some completion) :
    entry.returnedCompletion? (TrapReason := TrapReason) =
      some (completion, entry.toReturnedContinuation completion completed) := by
  unfold returnedCompletion?
  split
  · rename_i missing
    rw [completed] at missing
    contradiction
  · rename_i actual observed
    have completionEq : actual = completion :=
      Option.some.inj (observed.symm.trans completed)
    subst actual
    rfl

/-- Forgetting the parent continuation recovers the exact inner completion. -/
theorem returnedCompletion?_map_fst
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs) :
    (entry.returnedCompletion? (TrapReason := TrapReason)).map Prod.fst =
      entry.execution.completion? := by
  unfold returnedCompletion?
  split <;> simp_all

/-- The continuation-only view is definitionally derived from the pair. -/
theorem returnedContinuation?_eq_map_snd
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs) :
    entry.returnedContinuation? (TrapReason := TrapReason) =
      (entry.returnedCompletion? (TrapReason := TrapReason)).map Prod.snd :=
  rfl

/-- Exact inner completion constructs the exact continuation-only view. -/
theorem returnedContinuation?_of_completion
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs)
    (completion :
      WordReturnedFrameCompletion RollbackState (FrameTrace Event))
    (completed : entry.execution.completion? = some completion) :
    entry.returnedContinuation? (TrapReason := TrapReason) =
      some (entry.toReturnedContinuation completion completed) := by
  rw [returnedContinuation?_eq_map_snd,
    entry.returnedCompletion?_of_completion
      (TrapReason := TrapReason) completion completed]
  rfl

/-- The parent continuation always carries canonical returned Word bytes. -/
@[simp] theorem result_toReturnedContinuation
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs)
    (completion :
      WordReturnedFrameCompletion RollbackState (FrameTrace Event))
    (completed : entry.execution.completion? = some completion) :
    (entry.toReturnedContinuation
      (TrapReason := TrapReason) completion completed).result =
      ⟨completion.context.context.values.working.1,
        .returned completion.returnData⟩ := by
  simp [toReturnedContinuation]

/-- The returned parent context resolves to final working values and bytes. -/
theorem resolve_toReturnedContinuation
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs)
    (completion :
      WordReturnedFrameCompletion RollbackState (FrameTrace Event))
    (completed : entry.execution.completion? = some completion) :
    (entry.toReturnedContinuation
        (TrapReason := TrapReason) completion completed).resolve =
      .returned completion.context.context.values.working.1
        ⟨initialization.workingRollback, parentWorking.2.trace⟩
        completion.returnData := by
  simp [toReturnedContinuation, FrameContinuationContext.resolve]

/-- The indexed parent trace prefixes every canonical returned continuation. -/
theorem parentWorking_tracePrefix_toReturnedContinuation
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs)
    (completion :
      WordReturnedFrameCompletion RollbackState (FrameTrace Event))
    (completed : entry.execution.completion? = some completion) :
    FrameTrace.IsPrefixOf parentWorking.2.trace
      (entry.toReturnedContinuation
        (TrapReason := TrapReason) completion completed).effectWorking.trace :=
  (entry.toReturnedContinuation
    (TrapReason := TrapReason) completion completed).parentWorking_tracePrefix

end Solcore.ContractRuntime.ParentIndexedSelectedCheckedWordExecution

/-!
## Consolidated module: `Solcore.ContractRuntime.ParentIndexedSelectedCheckedWordExecutionContinuationCoherenceProperties`
-/

/-! Final-context and plain-continuation coherence for parent Word return. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ParentIndexedSelectedCheckedWordExecution

universe u v w

/-- The canonical parent continuation keeps the indexed parent state checkpoint. -/
@[simp] theorem stateCheckpoint_toReturnedContinuation
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs)
    (completion :
      WordReturnedFrameCompletion RollbackState (FrameTrace Event))
    (completed : entry.execution.completion? = some completion) :
    (entry.toReturnedContinuation
      (TrapReason := TrapReason) completion completed).stateCheckpoint =
      parentWorking.1 :=
  rfl

/-- The canonical parent continuation keeps the indexed parent effect checkpoint. -/
@[simp] theorem effectCheckpoint_toReturnedContinuation
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs)
    (completion :
      WordReturnedFrameCompletion RollbackState (FrameTrace Event))
    (completed : entry.execution.completion? = some completion) :
    (entry.toReturnedContinuation
      (TrapReason := TrapReason) completion completed).effectCheckpoint =
      parentWorking.2 :=
  rfl

/-- Working effects retain the initialized rollback and exact parent trace. -/
@[simp] theorem effectWorking_toReturnedContinuation
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs)
    (completion :
      WordReturnedFrameCompletion RollbackState (FrameTrace Event))
    (completed : entry.execution.completion? = some completion) :
    (entry.toReturnedContinuation
      (TrapReason := TrapReason) completion completed).effectWorking =
      ⟨initialization.workingRollback, parentWorking.2.trace⟩ := by
  simp [toReturnedContinuation]

/-- Successful completion preserves the exact indexed parent checkpoint. -/
theorem completion_context_checkpoint
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs)
    (completion :
      WordReturnedFrameCompletion RollbackState (FrameTrace Event))
    (completed : entry.execution.completion? = some completion) :
    completion.context.context.values.checkpoint =
      FrameCheckpointSnapshot.fromWorkingPair parentWorking := by
  obtain ⟨code, retained⟩ :=
    (entry.execution.completion?_eq_some_iff completion).mp completed
  have exactRun :=
    (entry.execution.execution?_eq_some_iff
      code completion.toHostDriverResult).mp retained
  have preserved :
      (code.runWithStorage entry.initialContext inputs
          entry.execution.providedFuel).context.context.values.checkpoint =
        entry.initialContext.context.values.checkpoint := by
    simpa only [CheckedHostCoreWordProgram.runWithStorage,
      CheckedHostCoreProgram.runWithStorage] using
      HostStorageDriver.run_checkpoint entry.initialContext inputs
        entry.execution.providedFuel
        (Core.State.initial code.code.program.body Core.hostEnvironment)
  rw [exactRun.2.symm] at preserved
  simpa [WordReturnedFrameCompletion.toHostDriverResult] using
    preserved.trans entry.initialContext_checkpoint

/-- Successful completion preserves the initialized rollback and parent trace. -/
theorem completion_context_workingEffects
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs)
    (completion :
      WordReturnedFrameCompletion RollbackState (FrameTrace Event))
    (completed : entry.execution.completion? = some completion) :
    completion.context.context.values.working.2 =
      ⟨initialization.workingRollback, parentWorking.2.trace⟩ := by
  obtain ⟨code, retained⟩ :=
    (entry.execution.completion?_eq_some_iff completion).mp completed
  have exactRun :=
    (entry.execution.execution?_eq_some_iff
      code completion.toHostDriverResult).mp retained
  have preserved :
      (code.runWithStorage entry.initialContext inputs
          entry.execution.providedFuel).context.context.values.working.2 =
        entry.initialContext.context.values.working.2 := by
    simpa only [CheckedHostCoreWordProgram.runWithStorage,
      CheckedHostCoreProgram.runWithStorage] using
      HostStorageDriver.run_workingEffects entry.initialContext inputs
        entry.execution.providedFuel
        (Core.State.initial code.code.program.body Core.hostEnvironment)
  rw [exactRun.2.symm] at preserved
  simpa [WordReturnedFrameCompletion.toHostDriverResult] using
    preserved.trans entry.initialContext_workingEffects

/-- Forgetting the parent index recovers the exact canonical plain context. -/
theorem toFrameContinuationContext_toReturnedContinuation
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs)
    (completion :
      WordReturnedFrameCompletion RollbackState (FrameTrace Event))
    (completed : entry.execution.completion? = some completion) :
    (entry.toReturnedContinuation
        (TrapReason := TrapReason) completion completed).toFrameContinuationContext =
      (completion.toFrameContinuationContext :
        FrameContinuationContext
          RollbackState (FrameTrace Event) TrapReason) := by
  have checkpoint := entry.completion_context_checkpoint completion completed
  have workingEffects :=
    entry.completion_context_workingEffects completion completed
  unfold toReturnedContinuation
  unfold ParentIndexedFrameContinuationContext.fromTraceExtension
  unfold WordReturnedFrameCompletion.toFrameContinuationContext
  unfold FrameContinuationContext.fromCheckpointedWorkingPair
  simp only [initialization.initialTraceExtension_toTrace]
  rw [checkpoint, workingEffects]
  rfl

/-- Exact pair output is equivalent to exact completion plus its constructor. -/
theorem returnedCompletion?_eq_some_iff
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs)
    (completion :
      WordReturnedFrameCompletion RollbackState (FrameTrace Event))
    (continuation : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking) :
    entry.returnedCompletion? (TrapReason := TrapReason) =
        some (completion, continuation) ↔
      ∃ completed : entry.execution.completion? = some completion,
        continuation = entry.toReturnedContinuation completion completed := by
  constructor
  · intro returned
    have completed : entry.execution.completion? = some completion := by
      have first := congrArg (Option.map Prod.fst) returned
      simpa [entry.returnedCompletion?_map_fst
        (TrapReason := TrapReason)] using first
    refine ⟨completed, ?_⟩
    rw [entry.returnedCompletion?_of_completion
      (TrapReason := TrapReason) completion completed] at returned
    exact congrArg Prod.snd (Option.some.inj returned).symm
  · rintro ⟨completed, rfl⟩
    exact entry.returnedCompletion?_of_completion
      (TrapReason := TrapReason) completion completed

end Solcore.ContractRuntime.ParentIndexedSelectedCheckedWordExecution

/-!
## Consolidated module: `Solcore.ContractRuntime.ParentIndexedSelectedCheckedWordExecutionContinuationResumptionProperties`
-/

/-! Terminal parent-return stability under additional fuel. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ParentIndexedSelectedCheckedWordExecution

universe u v w

/-- Resumption rebuilds the same parent continuation from retained completion. -/
theorem toReturnedContinuation_resumeWithFuel
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs)
    (additional : Nat)
    (completion :
      WordReturnedFrameCompletion RollbackState (FrameTrace Event))
    (completed : entry.execution.completion? = some completion) :
    (entry.resumeWithFuel additional).toReturnedContinuation
        (TrapReason := TrapReason) completion
        (entry.completion?_resumeWithFuel_of_some
          additional completion completed) =
      entry.toReturnedContinuation completion completed :=
  rfl

/-- A successful completion/parent pair is terminal under more fuel. -/
theorem returnedCompletion?_resumeWithFuel_of_completion
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs)
    (additional : Nat)
    (completion :
      WordReturnedFrameCompletion RollbackState (FrameTrace Event))
    (completed : entry.execution.completion? = some completion) :
    (entry.resumeWithFuel additional).returnedCompletion?
        (TrapReason := TrapReason) =
      some (completion, entry.toReturnedContinuation completion completed) := by
  have resumed := entry.completion?_resumeWithFuel_of_some
    additional completion completed
  rw [(entry.resumeWithFuel additional).returnedCompletion?_of_completion
    (TrapReason := TrapReason) completion resumed]
  rw [entry.toReturnedContinuation_resumeWithFuel
    (TrapReason := TrapReason) additional completion completed]

/-- Once successful, the complete optional pair is unchanged by more fuel. -/
theorem returnedCompletion?_resumeWithFuel_stable
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs)
    (additional : Nat)
    (completion :
      WordReturnedFrameCompletion RollbackState (FrameTrace Event))
    (completed : entry.execution.completion? = some completion) :
    (entry.resumeWithFuel additional).returnedCompletion?
        (TrapReason := TrapReason) =
      entry.returnedCompletion? (TrapReason := TrapReason) := by
  rw [entry.returnedCompletion?_resumeWithFuel_of_completion
    (TrapReason := TrapReason) additional completion completed]
  rw [entry.returnedCompletion?_of_completion
    (TrapReason := TrapReason) completion completed]

/-- The derived continuation-only view is likewise terminal. -/
theorem returnedContinuation?_resumeWithFuel_stable
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs)
    (additional : Nat)
    (completion :
      WordReturnedFrameCompletion RollbackState (FrameTrace Event))
    (completed : entry.execution.completion? = some completion) :
    (entry.resumeWithFuel additional).returnedContinuation?
        (TrapReason := TrapReason) =
      entry.returnedContinuation? (TrapReason := TrapReason) := by
  unfold returnedContinuation?
  rw [entry.returnedCompletion?_resumeWithFuel_stable
    (TrapReason := TrapReason) additional completion completed]

end Solcore.ContractRuntime.ParentIndexedSelectedCheckedWordExecution

/-!
## Consolidated module: `Solcore.ContractRuntime.ParentIndexedSelectedCheckedWordExecutionCompatibilityProperties`
-/

/-! Meaning-preserving branch-local coherence with generic selected execution. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ParentIndexedSelectedCheckedWordExecution

universe u v w

/-- Outer storage absence agrees exactly with the generic parent producer. -/
theorem start?_eq_none_iff_legacy_storageAbsent
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
    start? initialization storageAddress inputs fuel = none ↔
      initialization.runCodeWithStorageParentIndexedResult
          storageAddress inputs fuel doneOutcome =
        .storageAbsent := by
  rw [start?_eq_none_iff]
  exact
    (ParentIndexedFrameInitialization.runCodeWithStorageParentIndexedResult_eq_storageAbsent_iff
      initialization storageAddress inputs fuel doneOutcome).symm

/-- Generic selected execution is absent exactly on this carrier's code branch. -/
theorem legacy_runCodeWithStorage?_eq_none_iff_codeAbsent
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs)
    (fuel : Nat) :
    entry.initialContext.runCodeWithStorage? inputs fuel = none ↔
      entry.execution.selection = .codeAbsent := by
  rw [FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorage?_eq_none_iff]
  rw [← entry.execution.selection_toCheckedCode?]
  cases entry.execution.selection <;> simp

/-- On the Word branch, the retained raw run is the generic selected run. -/
theorem execution?_map_snd_eq_legacy_runCodeWithStorage?_of_word
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs)
    (code : CheckedHostCoreWordProgram)
    (selected : entry.execution.selection = .word code) :
    entry.execution.execution?.map Prod.snd =
      entry.initialContext.runCodeWithStorage?
        inputs entry.execution.providedFuel := by
  rw [entry.execution.execution?_eq_some_of_word code selected]
  unfold FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorage?
  rw [← entry.execution.selection_toCheckedCode?, selected]
  rfl

/--
The old branch-complete producer agrees only when its completion policy returns
the exact canonical bytes for this exact completed Word.
-/
theorem legacy_parent_result_eq_completed_of_canonical_word
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs)
    (completion :
      WordReturnedFrameCompletion RollbackState (FrameTrace Event))
    (completed : entry.execution.completion? = some completion)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    (canonical :
      doneOutcome completion.context (.word completion.word)
          completion.store =
        .returned completion.returnData) :
    initialization.runCodeWithStorageParentIndexedResult
        storageAddress inputs entry.execution.providedFuel doneOutcome =
      .completed completion.context (.word completion.word) completion.store
        (entry.toReturnedContinuation completion completed) := by
  apply (ParentIndexedFrameInitialization.runCodeWithStorageParentIndexedResult_eq_completed_iff
    initialization storageAddress inputs entry.execution.providedFuel
    doneOutcome completion.context (.word completion.word) completion.store
    (entry.toReturnedContinuation completion completed)).mpr
  refine ⟨entry.initialContext, entry.context_refined, ?_, ?_⟩
  · obtain ⟨code, selected, exactRun⟩ :=
      (entry.execution.completion?_eq_some_iff_selected_run completion).mp
        completed
    unfold FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorage?
    rw [← entry.execution.selection_toCheckedCode?, selected]
    simpa only [CheckedHostCoreWordCodeSelection.toCheckedCode?_word,
      Option.map_some, CheckedHostCoreWordProgram.runWithStorage,
      WordReturnedFrameCompletion.toHostDriverResult] using
      congrArg some exactRun
  · unfold ParentIndexedSelectedExecutionResult.completedContinuation
    unfold toReturnedContinuation
    rw [canonical]
    rfl

end Solcore.ContractRuntime.ParentIndexedSelectedCheckedWordExecution
end
