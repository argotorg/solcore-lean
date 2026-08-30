import Solcore.Semantics.CheckedHostCoreWordCodeSelection
import Solcore.Semantics.CheckedHostCoreWordProgramProperties

/-! Exact branches and erasure laws for checked Word-code classification. -/

set_option autoImplicit false

namespace Solcore.Semantics.CheckedHostCoreWordCodeSelection

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

end Solcore.Semantics.CheckedHostCoreWordCodeSelection
