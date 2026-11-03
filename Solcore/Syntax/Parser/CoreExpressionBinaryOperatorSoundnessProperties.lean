import Solcore.Syntax.DeclarativeCoreExpressionLayerGrammar
import Solcore.Syntax.Parser.DeclarativePrimitiveProperties
import Solcore.Syntax.Parser.DiagnosticReflectionProperties
import Solcore.Syntax.Parser.ExpressionProperties

/-!
Exact declarative bridges for Core binary-operator lookahead and consumption.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionInternals

/-- Successful precedence lookahead records the selected precedence exactly. -/
theorem binaryAtPrecedence?_some_precedence {input : State}
    {precedence : Nat} {operator : Located BinaryOp}
    (result : binaryAtPrecedence? input precedence = some operator) :
    operator.value.precedence = precedence :=
  (binaryAtPrecedence?_some_state_shape result).choose_spec.2.2.1

/--
A successful lookup followed by consumption is one exact declarative binary
operator transition.
-/
theorem consumeBinary_success_sound_of_binaryAtPrecedence?_some
    {input next : State} {precedence : Nat}
    {operator : Located BinaryOp}
    (recognized : binaryAtPrecedence? input precedence = some operator)
    (consumed : consumeBinary operator input = .ok () next) :
    DeclarativeGrammar.BinaryOperatorAtPrecedenceParses precedence
      input.declarativeRemainder operator next.declarativeRemainder := by
  rcases binaryAtPrecedence?_some_state_shape recognized with
    ⟨_token, _found, decoded, precedenceEq, _bound⟩
  rw [consumeBinary_ok_state_shape operator input] at consumed
  cases consumed
  exact ⟨precedenceEq, decoded, rfl⟩

/-- Failed precedence lookahead excludes that exact operator class. -/
theorem binaryAtPrecedence?_none_absentAt {input : State}
    {precedence : Nat}
    (result : binaryAtPrecedence? input precedence = none) :
    DeclarativeGrammar.BinaryOperatorAtPrecedenceAbsentAt precedence
      input.declarativeRemainder := by
  rintro ⟨operator, operatorPrecedence, decoded⟩
  have found : BinaryOp.at? input.tokens input.window.endIndex input.cursor =
      some operator := decoded
  unfold binaryAtPrecedence? at result
  rw [found] at result
  have selected : (operator.value.precedence == precedence) = true :=
    beq_iff_eq.mpr operatorPrecedence
  simp only [selected, if_true] at result
  contradiction

/-- Binary consumption preserves the diagnostic stack exactly on success. -/
theorem consumeBinary_reflectsDiagnosticFreeOnSuccess
    (operator : Located BinaryOp) :
    Parser.ReflectsDiagnosticFreeOnSuccess (consumeBinary operator) := by
  intro input value next result diagnosticFree
  unfold consumeBinary modifyState at result
  cases result
  exact diagnosticFree

end Solcore.Syntax.Parser.ExpressionInternals
