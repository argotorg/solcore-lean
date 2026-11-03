import Solcore.Frontend.SourceInference.Resolution

/-! The shift branch of binary-operator inference: a shift unifies its value's
type and then its amount's type with Word, adds no requirement, and has a Word
result. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceInference.Detail

open TypeSystem

theorem inferBinaryOperator_shift_result {context : Context}
    {operator : Syntax.BinaryOp} {left right : Ty} {expected : Option Ty}
    {integerLiterals : List IntegerLiteralOrigin} {state : State}
    {result : OperatorInferenceResult}
    (shift : isShiftOperator operator = true)
    (success : inferBinaryOperator context operator left right expected
      integerLiterals state = .ok result) :
    result.requirements = [] ∧ result.type = .word ∧
      ∃ valued, unify state left .word = .ok valued ∧
        unify valued right .word = .ok result.state := by
  unfold inferBinaryOperator at success
  rw [if_pos shift] at success
  cases valueResult : unify state left .word with
  | error error => simp [valueResult, bind, Except.bind] at success
  | ok valued =>
      cases amountResult : unify valued right .word with
      | error error => simp [valueResult, amountResult, bind, Except.bind] at success
      | ok amounted =>
          simp only [valueResult, amountResult, bind, Except.bind, pure, Except.pure,
            Except.ok.injEq] at success
          subst success
          exact ⟨rfl, rfl, valued, rfl, amountResult⟩

/-- A projection of the inference state that unification preserves is also
preserved by a shift. -/
theorem inferBinaryOperator_shift_projection {α : Type} {context : Context}
    {operator : Syntax.BinaryOp} {left right : Ty} {expected : Option Ty}
    {integerLiterals : List IntegerLiteralOrigin} {state : State}
    {result : OperatorInferenceResult} (projection : State → α)
    (unified : ∀ {before after : State} {first second : Ty},
      unify before first second = .ok after → projection after = projection before)
    (shift : isShiftOperator operator = true)
    (success : inferBinaryOperator context operator left right expected
      integerLiterals state = .ok result) :
    projection result.state = projection state := by
  obtain ⟨_, _, valued, valueResult, amountResult⟩ :=
    inferBinaryOperator_shift_result shift success
  rw [unified amountResult, unified valueResult]

end Solcore.Frontend.SourceInference.Detail
