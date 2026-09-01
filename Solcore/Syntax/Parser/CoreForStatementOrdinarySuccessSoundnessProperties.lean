import Solcore.Syntax.DeclarativeCoreForStatementOutcomeProperties
import Solcore.Syntax.Parser.CoreBlockOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.CoreForItemsOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.Statement.Control

/-! Executable ordinary success for complete Core `for` statements. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem bind_ok_components {alpha beta : Type} {first : Parser alpha}
    {next : alpha → Parser beta} {input output : State} {value : beta}
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

/-- Every executable Core `for` success retains its exact header, recursive
body, AST spans, item order, and final remainder. -/
theorem forStatement_success_ordinary_sound
    (statement : Parser Statement) (expression : Parser Expr)
    (statementOrdinary : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop)
    (statementRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (statementSuccessSound : ∀ {input output : State} {value : Statement},
      statement input = .ok value output → statementOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (statementRejectSound : ∀ {input rejected : State} {failure : Failure},
      statement input = .reject failure rejected → statementRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    (expressionSuccessSound : ∀ {input output : State} {value : Expr},
      expression input = .ok value output → expressionOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (expressionStrict : ∀ {input output : State} {value : Expr},
      expression input = .ok value output → input.cursor < output.cursor)
    {input output : State} {value : Statement}
    (result : forStatement statement expression input = .ok value output) :
    DeclarativeGrammar.ForStatementOrdinaryParses statementOrdinary
      expressionOrdinary input.declarativeRemainder value
        output.declarativeRemainder := by
  unfold forStatement at result
  rcases bind_ok_components result with
    ⟨marker, afterMarker, markerResult, openingStage⟩
  rcases bind_ok_components openingStage with
    ⟨opening, afterOpening, openingResult, initializerStage⟩
  rcases bind_ok_components initializerStage with
    ⟨initializer, afterInitializer, initializerResult,
      firstSemicolonStage⟩
  rcases bind_ok_components firstSemicolonStage with
    ⟨firstSemicolon, afterFirstSemicolon, firstSemicolonResult,
      conditionStage⟩
  rcases bind_ok_components conditionStage with
    ⟨condition, afterCondition, conditionResult, secondSemicolonStage⟩
  rcases bind_ok_components secondSemicolonStage with
    ⟨secondSemicolon, afterSecondSemicolon, secondSemicolonResult,
      postStage⟩
  rcases bind_ok_components postStage with
    ⟨post, afterPost, postResult, closingStage⟩
  rcases bind_ok_components closingStage with
    ⟨closing, afterClosing, closingResult, bodyStage⟩
  rcases bind_ok_components bodyStage with
    ⟨body, afterBody, bodyResult, finished⟩
  cases finished
  exact .parsed marker.span opening.span firstSemicolon.span
    secondSemicolon.span closing.span
    (keyword_success_exactTokenParses .forKw .statement markerResult)
    (symbol_success_exactTokenParses .leftParen .statement openingResult)
    (ControlInternals.forItems_success_ordinary_sound expression .semicolon
      expressionOrdinary expressionSuccessSound expressionStrict
        initializerResult)
    (symbol_success_exactTokenParses .semicolon .statement
      firstSemicolonResult)
    (expressionSuccessSound conditionResult)
    (symbol_success_exactTokenParses .semicolon .statement
      secondSemicolonResult)
    (ControlInternals.forItems_success_ordinary_sound expression .rightParen
      expressionOrdinary expressionSuccessSound expressionStrict postResult)
    (symbol_success_exactTokenParses .rightParen .statement closingResult)
    ((coreBlock_ordinaryOutcome_sound statement .require statementOrdinary
      statementRejects statementSuccessSound statementRejectSound).1
        bodyResult)

end Solcore.Syntax.Parser
