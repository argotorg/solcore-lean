import Solcore.Syntax.Parser.CoreStatementOptionalElseOrdinaryOutcomeSoundnessProperties

/-! Executable diagnostic-inclusive success for canonical Core `if`. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every executable `if` success retains its exact condition, raw then block,
prioritized optional else, AST, span, and final remainder. -/
theorem ifStatement_success_ordinary_sound
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
    {input output : State} {value : Statement}
    (result : ifStatement statement expression input = .ok value output) :
    DeclarativeGrammar.IfStatementOrdinaryParses expressionOrdinary
      statementOrdinary input.declarativeRemainder value
        output.declarativeRemainder := by
  unfold ifStatement at result
  cases markerResult : keyword .ifKw .statement input with
  | invariant error => simp [bind, markerResult] at result
  | reject failure rejected => simp [bind, markerResult] at result
  | ok marker afterMarker =>
      simp only [bind, markerResult] at result
      cases openingResult : symbol .leftParen .statement afterMarker with
      | invariant error => simp [openingResult] at result
      | reject failure rejected => simp [openingResult] at result
      | ok opening afterOpening =>
          simp only [openingResult] at result
          cases conditionResult : expression afterOpening with
          | invariant error => simp [conditionResult] at result
          | reject failure rejected => simp [conditionResult] at result
          | ok condition afterCondition =>
              simp only [conditionResult] at result
              cases closingResult : symbol .rightParen .statement
                  afterCondition with
              | invariant error => simp [closingResult] at result
              | reject failure rejected => simp [closingResult] at result
              | ok closing afterClosing =>
                  simp only [closingResult] at result
                  cases thenResult : coreBlock statement .require afterClosing
                      with
                  | invariant error => simp [thenResult] at result
                  | reject failure rejected => simp [thenResult] at result
                  | ok thenBody afterThen =>
                      simp only [thenResult] at result
                      cases elseResult : ControlInternals.optionalElseBody
                          statement afterThen with
                      | invariant error => simp [elseResult] at result
                      | reject failure rejected => simp [elseResult] at result
                      | ok elseBody afterElse =>
                          simp only [elseResult, pure] at result
                          cases result
                          exact .parsed marker.span opening.span closing.span
                            (keyword_success_exactTokenParses .ifKw .statement
                              markerResult)
                            (symbol_success_exactTokenParses .leftParen
                              .statement openingResult)
                            (expressionSuccessSound conditionResult)
                            (symbol_success_exactTokenParses .rightParen
                              .statement closingResult)
                            ((coreBlock_ordinaryOutcome_sound statement
                              .require statementOrdinary statementRejects
                                statementSuccessSound statementRejectSound).1
                                  thenResult)
                            (ControlInternals.optionalElseBody_success_ordinary_sound
                              statement statementOrdinary statementRejects
                                statementSuccessSound statementRejectSound
                                  elseResult)

end Solcore.Syntax.Parser
