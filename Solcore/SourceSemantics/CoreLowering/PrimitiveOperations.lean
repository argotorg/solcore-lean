import Solcore.Frontend.SourceCorePrimitive
import Solcore.SourceSemantics.CoreLowering.ControlExpressions

/-! Source primitive relations agree with the exact Core bodies used by the
primitive compiler. These lemmas inspect neither the executable source runtime
nor an assumed child evaluation result. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.PrimitiveExpressions

open Frontend Frontend.SourceInference TypeSystem LocalCell

theorem unary_value (operator : Syntax.UnaryOp) (value : SourceStagedValue.Value)
    (typed : SourceStagedValue.coreType value = (SourceCorePrimitive.unaryOperator operator).operandType) :
    ∃ result : SourceStagedValue.Value,
      SourceStagedValue.coreType result = (SourceCorePrimitive.unaryOperator operator).resultType ∧
      Dynamic.UnaryPrimitiveApplies operator (StagedValue.toSource value) (StagedValue.toSource result) ∧
      (SourceCorePrimitive.unaryOperator operator).apply (SourceStagedValue.toCore value) =
        some (SourceStagedValue.toCore result) := by
  cases operator <;> cases value <;>
    simp only [SourceCorePrimitive.unaryOperator, Core.UnaryOp.operandType, SourceStagedValue.coreType] at typed <;>
    try contradiction
  · exact ⟨.bool _, rfl, .logicalNot _, rfl⟩
  · exact ⟨.word _, rfl, .wordBitNot _, rfl⟩

theorem strict_operand_word {operator : Syntax.BinaryOp}
    (strict : Dynamic.StrictBinaryOperator operator) : SourceCorePrimitive.binaryOperandType operator = .word := by
  cases strict <;> rfl

theorem binary_result_payload (operator : Syntax.BinaryOp) :
    Core.CellPayload (SourceCorePrimitive.binaryResultType operator) := by
  cases operator <;> constructor

theorem unary_result_payload (operator : Syntax.UnaryOp) :
    Core.CellPayload (SourceCorePrimitive.unaryOperator operator).resultType := by
  cases operator <;> constructor

theorem binary_strict {operator : Syntax.BinaryOp} (strict : Dynamic.StrictBinaryOperator operator)
    (left right : Core.Expr) :
    SourceCorePrimitive.binary operator left right = Core.LocalPrimitiveResults.binaryWith
      (SourceCorePrimitive.binaryResultType operator) left right (SourceCorePrimitive.strictBinaryBody operator) := by
  cases strict <;> rfl

theorem binary_left_failure {operator : Syntax.BinaryOp} {environment : Core.Environment}
    {store : Core.Store} {left right : Core.Expr} {reason : Core.Word}
    (evaluation : Core.Evaluates environment store left
      (.inLeft (SourceCorePrimitive.binaryOperandType operator) (.word reason)) store) :
    Core.Evaluates environment store (SourceCorePrimitive.binary operator left right)
      (.inLeft (SourceCorePrimitive.binaryResultType operator) (.word reason)) store := by
  cases operator <;> first
    | exact Core.LocalPrimitiveResults.logicalAnd_failure evaluation
    | exact Core.LocalPrimitiveResults.logicalOr_failure evaluation
    | exact Core.LocalPrimitiveResults.binaryWith_left_failure evaluation

theorem binary_nonstrict {operator : Syntax.BinaryOp}
    (nonstrict : ¬ Dynamic.StrictBinaryOperator operator) :
    operator = .logicalAnd ∨ operator = .logicalOr := by
  cases operator <;> first
    | exact Or.inl rfl
    | exact Or.inr rfl
    | exact False.elim (nonstrict (by constructor))

theorem bool_of_type (value : SourceStagedValue.Value)
    (typed : SourceStagedValue.coreType value = .bool) : ∃ boolean, value = .bool boolean := by
  cases value <;> simp_all [SourceStagedValue.coreType]

theorem word_of_type (value : SourceStagedValue.Value)
    (typed : SourceStagedValue.coreType value = .word) : ∃ word, value = .word word := by
  cases value <;> simp_all [SourceStagedValue.coreType]

private theorem not_gt (left right : Core.Word) :
    (!decide (left > right)) = decide (left ≤ right) := by
  rw [← decide_not]
  exact decide_eq_decide.mpr Fin.not_lt

private theorem not_lt (left right : Core.Word) :
    (!decide (right > left)) = decide (left ≥ right) := by
  rw [← decide_not]
  exact decide_eq_decide.mpr Fin.not_lt

/-- Swapped comparisons operate on already evaluated payloads. The source
operand order is independent of the Core comparison's argument order. -/
theorem strict_binary_value {operator : Syntax.BinaryOp}
    (strict : Dynamic.StrictBinaryOperator operator) (left right : Core.Word) :
    ∃ result : SourceStagedValue.Value,
      SourceStagedValue.coreType result = SourceCorePrimitive.binaryResultType operator ∧
      Dynamic.BinaryPrimitiveApplies operator (.word left) (.word right) (StagedValue.toSource result) ∧
      ∀ environment store, Core.Evaluates (.word right :: .word left :: environment) store
        (SourceCorePrimitive.strictBinaryBody operator) (SourceStagedValue.toCore result) store := by
  cases strict with
  | multiply => exact ⟨.word _, rfl, .wordMultiply _ _, fun _ _ => .binary (.var rfl) (.var rfl) rfl⟩
  | divide => exact ⟨.word _, rfl, .wordDivide _ _, fun _ _ => .binary (.var rfl) (.var rfl) rfl⟩
  | modulo => exact ⟨.word _, rfl, .wordModulo _ _, fun _ _ => .binary (.var rfl) (.var rfl) rfl⟩
  | add => exact ⟨.word _, rfl, .wordAdd _ _, fun _ _ => .binary (.var rfl) (.var rfl) rfl⟩
  | subtract => exact ⟨.word _, rfl, .wordSubtract _ _, fun _ _ => .binary (.var rfl) (.var rfl) rfl⟩
  | bitAnd => exact ⟨.word _, rfl, .wordBitAnd _ _, fun _ _ => .binary (.var rfl) (.var rfl) rfl⟩
  | bitXor => exact ⟨.word _, rfl, .wordBitXor _ _, fun _ _ => .binary (.var rfl) (.var rfl) rfl⟩
  | bitOr => exact ⟨.word _, rfl, .wordBitOr _ _, fun _ _ => .binary (.var rfl) (.var rfl) rfl⟩
  | greater => exact ⟨.bool _, rfl, .wordGreater _ _, fun _ _ => .binary (.var rfl) (.var rfl) rfl⟩
  | less => exact ⟨.bool _, rfl, .wordLess _ _, fun _ _ => .binary (.var rfl) (.var rfl) rfl⟩
  | lessEqual =>
      refine ⟨.bool _, rfl, .wordLessEqual _ _, fun _ _ => .unary (.binary (.var rfl) (.var rfl) rfl) ?_⟩
      simp [Core.UnaryOp.apply, SourceStagedValue.toCore, not_gt]
  | greaterEqual =>
      refine ⟨.bool _, rfl, .wordGreaterEqual _ _, fun _ _ => .unary (.binary (.var rfl) (.var rfl) rfl) ?_⟩
      simp [Core.UnaryOp.apply, SourceStagedValue.toCore, not_lt]
  | equal =>
      by_cases same : left = right
      · subst right
        exact ⟨.bool true, rfl, .equalTrue ⟨rfl, .word _⟩,
          fun _ _ => .binary (.var rfl) (.var rfl) (by simp [Core.BinaryOp.apply, SourceStagedValue.toCore])⟩
      · exact ⟨.bool false, rfl, .equalFalse (fun equivalent => same (Dynamic.Value.word.inj equivalent.1)),
          fun _ _ => .binary (.var rfl) (.var rfl) (by simp [Core.BinaryOp.apply, SourceStagedValue.toCore, beq_eq_false_iff_ne.mpr same])⟩
  | notEqual =>
      by_cases same : left = right
      · subst right
        exact ⟨.bool false, rfl, .notEqualFalse ⟨rfl, .word _⟩,
          fun _ _ => .unary (.binary (result := .bool true) (.var rfl) (.var rfl) (by simp [Core.BinaryOp.apply])) rfl⟩
      · exact ⟨.bool true, rfl, .notEqualTrue (fun equivalent => same (Dynamic.Value.word.inj equivalent.1)),
          fun _ _ => .unary (.binary (result := .bool false) (.var rfl) (.var rfl) (by simp [Core.BinaryOp.apply, beq_eq_false_iff_ne.mpr same])) rfl⟩

end Solcore.SourceSemantics.CoreLowering.PrimitiveExpressions
