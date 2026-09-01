import Solcore.Syntax.DeclarativeCoreForItemOutcomeProperties
import Solcore.Syntax.Parser.CoreAssignmentTailOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.CoreIdentifierOutcomeSoundnessProperties
import Solcore.Syntax.Parser.CoreStatementSimpleOptionalOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.Statement.Simple

/-! Ordinary executable success for one Core `for`-header item. -/

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

namespace StatementSimpleInternals

/-- Executable `for let` success follows the diagnostic-inclusive ordinary
grammar with the fixed public Core type outcome. -/
theorem forLetItem_success_ordinary_sound
    (expression : Parser Expr)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSuccessSound : ∀ {input output : State} {value : Expr},
      expression input = .ok value output → expressionOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    {input output : State} {item : ForItem}
    (result : forLetItem expression input = .ok item output) :
    DeclarativeGrammar.ForLetItemOrdinaryParses expressionOrdinary
      input.declarativeRemainder item output.declarativeRemainder := by
  unfold forLetItem at result
  rcases bind_ok_components result with
    ⟨marker, afterMarker, markerResult, nameStage⟩
  rcases bind_ok_components nameStage with
    ⟨name, afterName, nameResult, typeStage⟩
  rcases bind_ok_components typeStage with
    ⟨type, afterType, typeResult, initializerStage⟩
  rcases bind_ok_components initializerStage with
    ⟨initializer, afterInitializer, initializerResult, finished⟩
  cases finished
  exact .parsed marker.span
    (keyword_success_exactTokenParses .letKw .statement markerResult)
    (identifier_success_sound .statement nameResult)
    (optionalLetType_success_ordinary_sound typeResult)
    (optionalLetInitializer_success_ordinary_sound expression
      expressionOrdinary expressionSuccessSound initializerResult)

/-- Executable fallback success preserves the initial expression, maximal
optional assignment tail, AST, span, and final remainder. -/
theorem forAssignmentOrExpression_success_ordinary_sound
    (expression : Parser Expr)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSuccessSound : ∀ {input output : State} {value : Expr},
      expression input = .ok value output → expressionOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    {input output : State} {item : ForItem}
    (result : forAssignmentOrExpression expression input = .ok item output) :
    DeclarativeGrammar.ForAssignmentOrExpressionOrdinaryParses
      expressionOrdinary input.declarativeRemainder item
        output.declarativeRemainder := by
  unfold forAssignmentOrExpression at result
  rcases bind_ok_components result with
    ⟨left, afterLeft, leftResult, tailStage⟩
  rcases bind_ok_components tailStage with
    ⟨tail, afterTail, tailResult, finished⟩
  have leftParsed := expressionSuccessSound leftResult
  have tailParsed := optionalAssignmentTail_success_ordinary_sound expression
    expressionOrdinary expressionSuccessSound tailResult
  cases tail with
  | none =>
      cases finished
      exact ⟨left, afterLeft.declarativeRemainder, none, leftParsed,
        tailParsed, .expression left⟩
  | some tail =>
      cases tail with
      | value operator right =>
          cases finished
          exact ⟨left, afterLeft.declarativeRemainder,
            some (.value operator right), leftParsed, tailParsed,
            .value left right operator⟩
      | bitNot operator =>
          cases finished
          exact ⟨left, afterLeft.declarativeRemainder,
            some (.bitNot operator), leftParsed, tailParsed,
            .bitNot left operator⟩

end StatementSimpleInternals

/-- The public dispatcher commits to `let` exactly when its guard succeeds. -/
theorem forItem_success_ordinary_sound
    (expression : Parser Expr)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSuccessSound : ∀ {input output : State} {value : Expr},
      expression input = .ok value output → expressionOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    {input output : State} {item : ForItem}
    (result : forItem expression input = .ok item output) :
    DeclarativeGrammar.ForItemOrdinaryParses expressionOrdinary
      input.declarativeRemainder item output.declarativeRemainder := by
  unfold forItem at result
  by_cases letPresent : isKeyword input .letKw
  · simp only [letPresent, if_true] at result
    exact .letItem
      (StatementSimpleInternals.forLetItem_success_ordinary_sound expression
        expressionOrdinary expressionSuccessSound result)
  · have letAbsent : isKeyword input .letKw = false :=
      Bool.eq_false_iff.mpr letPresent
    simp only [letAbsent, Bool.false_eq_true, if_false] at result
    exact .assignmentOrExpression
      (keywordAbsentAt_of_isKeyword_eq_false .letKw letAbsent)
      (StatementSimpleInternals.forAssignmentOrExpression_success_ordinary_sound
        expression expressionOrdinary expressionSuccessSound result)

end Solcore.Syntax.Parser
