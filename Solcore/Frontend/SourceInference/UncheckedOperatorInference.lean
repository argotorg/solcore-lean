import Solcore.Frontend.SourceInference.Resolution

/-! The unchecked branch of binary-operator inference: the operands' types
unify, an open literal operand then becomes a Word, and the operator's meaning
is selected as for a checked operator whose operands are not open literals. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceInference.Detail

open TypeSystem

theorem isShiftOperator_of_unchecked {operator : Syntax.BinaryOp}
    (unchecked : isUncheckedOperator operator = true) : isShiftOperator operator = false := by
  cases operator <;> simp_all [isUncheckedOperator, isShiftOperator]

theorem inferBinaryOperator_unchecked_result {context : Context}
    {operator : Syntax.BinaryOp} {left right : Ty} {expected : Option Ty}
    {integerLiterals : List IntegerLiteralOrigin} {state : State}
    {result : OperatorInferenceResult}
    (unchecked : isUncheckedOperator operator = true)
    (success : inferBinaryOperator context operator left right expected
      integerLiterals state = .ok result) :
    ∃ unified prepared, unify state left right = .ok unified ∧
      (prepared = unified ∨ unify unified (unified.resolve left) .word = .ok prepared) ∧
      binaryOperatorTail context operator left false prepared = .ok result := by
  unfold inferBinaryOperator at success
  rw [if_neg (by simp [isShiftOperator_of_unchecked unchecked]), if_pos unchecked] at success
  cases unifyResult : unify state left right with
  | error error => simp [unifyResult, bind, Except.bind] at success
  | ok unified =>
      by_cases literal : isOpenIntegerLiteralTarget unified integerLiterals left = true
      · cases wordResult : unify unified (unified.resolve left) .word with
        | error error => simp [unifyResult, literal, wordResult, bind, Except.bind] at success
        | ok prepared =>
            exact ⟨unified, prepared, rfl, .inr wordResult, by
              simpa [unifyResult, literal, wordResult, bind, Except.bind] using success⟩
      · exact ⟨unified, unified, rfl, .inl rfl, by
          simpa [unifyResult, literal, bind, Except.bind, pure, Except.pure] using success⟩

/-- A projection of the inference state that unification and the operator
tail without open literals preserve is also preserved by an unchecked
operator. -/
theorem inferBinaryOperator_unchecked_projection {α : Type} {context : Context}
    {operator : Syntax.BinaryOp} {left right : Ty} {expected : Option Ty}
    {integerLiterals : List IntegerLiteralOrigin} {state : State}
    {result : OperatorInferenceResult} (projection : State → α)
    (unified : ∀ {before after : State} {first second : Ty},
      unify before first second = .ok after → projection after = projection before)
    (tail : ∀ {before : State} {finished : OperatorInferenceResult},
      binaryOperatorTail context operator left false before = .ok finished →
        projection finished.state = projection before)
    (unchecked : isUncheckedOperator operator = true)
    (success : inferBinaryOperator context operator left right expected
      integerLiterals state = .ok result) :
    projection result.state = projection state := by
  obtain ⟨middle, prepared, unifyResult, prepare, tailResult⟩ :=
    inferBinaryOperator_unchecked_result unchecked success
  rw [tail tailResult]
  rcases prepare with rfl | wordResult
  · exact unified unifyResult
  · rw [unified wordResult, unified unifyResult]

end Solcore.Frontend.SourceInference.Detail
