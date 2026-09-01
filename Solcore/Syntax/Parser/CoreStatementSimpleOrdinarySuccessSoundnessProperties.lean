import Solcore.Syntax.Parser.CoreIdentifierOutcomeSoundnessProperties
import Solcore.Syntax.Parser.CoreStatementSimpleOptionalOrdinaryOutcomeSoundnessProperties

/-! Ordinary executable success for canonical Core `let` and `return`. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem bind_ok_components {alpha beta : Type}
    {first : Parser alpha} {next : alpha → Parser beta}
    {input output : State} {value : beta}
    (result : (first >>= next) input = .ok value output) :
    ∃ firstValue afterFirst,
      first input = .ok firstValue afterFirst ∧
        next firstValue afterFirst = .ok value output := by
  change (match first input with
    | .ok firstValue afterFirst => next firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value output at result
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      rw [firstResult] at result
      exact ⟨firstValue, afterFirst, rfl, result⟩
  | reject failure rejected => rw [firstResult] at result; contradiction
  | invariant error => rw [firstResult] at result; contradiction

/-- Every executable `let` success records its exact marker, checked name,
optional type, optional initializer, semicolon, AST, span, and remainder. -/
theorem letStatement_success_ordinary_sound
    (expression : Parser Expr)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSuccessSound : ∀ {input output : State} {value : Expr},
      expression input = .ok value output → expressionOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    {input output : State} {statement : Statement}
    (result : letStatement expression input = .ok statement output) :
    DeclarativeGrammar.LetStatementOrdinaryParses expressionOrdinary
      input.declarativeRemainder statement output.declarativeRemainder := by
  unfold letStatement at result
  rcases bind_ok_components result with
    ⟨marker, afterMarker, markerResult, nameStage⟩
  rcases bind_ok_components nameStage with
    ⟨name, afterName, nameResult, typeStage⟩
  rcases bind_ok_components typeStage with
    ⟨type, afterType, typeResult, initializerStage⟩
  rcases bind_ok_components initializerStage with
    ⟨initializer, afterInitializer, initializerResult, semicolonStage⟩
  rcases bind_ok_components semicolonStage with
    ⟨semicolon, afterSemicolon, semicolonResult, finished⟩
  cases finished
  exact .parsed marker.span semicolon.span
    (keyword_success_exactTokenParses .letKw .statement markerResult)
    (identifier_success_sound .statement nameResult)
    (StatementSimpleInternals.optionalLetType_success_ordinary_sound
      typeResult)
    (StatementSimpleInternals.optionalLetInitializer_success_ordinary_sound
      expression expressionOrdinary expressionSuccessSound initializerResult)
    (symbol_success_exactTokenParses .semicolon .statement semicolonResult)

/-- Every executable `return` success records the semicolon-prioritized
optional value, exact terminator, AST, span, and remainder. -/
theorem returnStatement_success_ordinary_sound
    (expression : Parser Expr)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSuccessSound : ∀ {input output : State} {value : Expr},
      expression input = .ok value output → expressionOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    {input output : State} {statement : Statement}
    (result : returnStatement expression input = .ok statement output) :
    DeclarativeGrammar.ReturnStatementOrdinaryParses expressionOrdinary
      input.declarativeRemainder statement output.declarativeRemainder := by
  unfold returnStatement at result
  rcases bind_ok_components result with
    ⟨marker, afterMarker, markerResult, valueStage⟩
  rcases bind_ok_components valueStage with
    ⟨value, afterValue, valueResult, semicolonStage⟩
  rcases bind_ok_components semicolonStage with
    ⟨semicolon, afterSemicolon, semicolonResult, finished⟩
  cases finished
  exact .parsed marker.span semicolon.span
    (keyword_success_exactTokenParses .returnKw .statement markerResult)
    (StatementSimpleInternals.optionalReturnValue_success_ordinary_sound
      expression expressionOrdinary expressionSuccessSound valueResult)
    (symbol_success_exactTokenParses .semicolon .statement semicolonResult)

end Solcore.Syntax.Parser
