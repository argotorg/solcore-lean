import Solcore.Syntax.DeclarativeCoreExpressionLayerGrammar
import Solcore.Syntax.Parser.DeclarativePrimitiveProperties
import Solcore.Syntax.Parser.DiagnosticReflectionProperties
import Solcore.Syntax.Parser.ExpressionProperties

/-!
Exact declarative bridges for Core binary-operator lookahead and consumption.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionInternals

private theorem binaryOp?_some_kind {kind : TokenKind} {operator : BinaryOp}
    (result : binaryOp? kind = some operator) :
    kind = .symbol operator.symbol := by
  cases kind with
  | symbol symbol =>
      cases symbol <;> cases operator <;>
        simp [binaryOp?, BinaryOp.symbol] at result ⊢
  | keyword keyword => simp [binaryOp?] at result
  | identifier text => simp [binaryOp?] at result
  | yulIdentifier text => simp [binaryOp?] at result
  | decimalLiteral spelling => simp [binaryOp?] at result
  | hexadecimalLiteral spelling => simp [binaryOp?] at result
  | stringLiteral spelling => simp [binaryOp?] at result
  | yulMetaBacktick spelling => simp [binaryOp?] at result
  | yulMetaInterpolation spelling => simp [binaryOp?] at result

@[simp] private theorem binaryOp?_symbol (operator : BinaryOp) :
    binaryOp? (.symbol operator.symbol) = some operator := by
  cases operator <;> rfl

/-- Successful precedence lookahead records the selected precedence exactly. -/
theorem binaryAtPrecedence?_some_precedence {input : State}
    {precedence : Nat} {operator : Located BinaryOp}
    (result : binaryAtPrecedence? input precedence = some operator) :
    operator.value.precedence = precedence := by
  unfold binaryAtPrecedence? at result
  cases found : input.peek? with
  | none => simp [found] at result
  | some token =>
      simp only [found] at result
      cases decoded : binaryOp? token.value with
      | none => simp [decoded] at result
      | some value =>
          simp only [decoded] at result
          split at result
          next selected =>
            cases result
            exact beq_iff_eq.mp selected
          next skipped => contradiction

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
    ⟨token, found, decoded, spanEq⟩
  have kindEq : token.value = .symbol operator.value.symbol :=
    binaryOp?_some_kind decoded
  have tokenAt := tokenAt_of_peek?_eq_some found
  have exactToken : DeclarativeGrammar.TokenAt input.tokens
      input.window.endIndex input.cursor {
        span := operator.span
        value := .symbol operator.value.symbol
      } := by
    simpa only [← spanEq, ← kindEq] using tokenAt
  rw [consumeBinary_ok_state_shape operator input] at consumed
  cases consumed
  refine ⟨binaryAtPrecedence?_some_precedence recognized, exactToken, ?_⟩
  rfl

/-- Failed precedence lookahead excludes that exact operator class. -/
theorem binaryAtPrecedence?_none_absentAt {input : State}
    {precedence : Nat}
    (result : binaryAtPrecedence? input precedence = none) :
    DeclarativeGrammar.BinaryOperatorAtPrecedenceAbsentAt precedence
      input.declarativeRemainder := by
  rintro ⟨span, operator, operatorPrecedence, tokenAt⟩
  have found : input.peek? = some {
      span
      value := .symbol operator.symbol
    } := by
    change input.cursor < input.window.endIndex ∧
      input.tokens[input.cursor]? = some {
        span
        value := .symbol operator.symbol
      } at tokenAt
    unfold State.peek?
    rw [if_pos tokenAt.1, tokenAt.2]
  unfold binaryAtPrecedence? at result
  rw [found] at result
  have selected : (operator.precedence == precedence) = true :=
    beq_iff_eq.mpr operatorPrecedence
  simp only [binaryOp?_symbol, selected, if_true] at result
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
