import Solcore.Syntax.Parser.CoreStatementIfOrdinarySuccessSoundnessProperties
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties
import Solcore.Syntax.Parser.YulKeywordRejectionSoundnessProperties

/-! Executable exact rejection for canonical Core `if`. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every executable `if` rejection records its first failing sequential
stage and exact rejected remainder. -/
theorem ifStatement_reject_ordinary_sound
    (statement : Parser Statement) (expression : Parser Expr)
    (statementOrdinary : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop)
    (statementRejects expressionRejects : DeclarativeGrammar.Remainder →
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
    (expressionRejectSound : ∀ {input rejected : State} {failure : Failure},
      expression input = .reject failure rejected → expressionRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : ifStatement statement expression input =
      .reject failure rejected) :
    DeclarativeGrammar.IfStatementRejects expressionOrdinary
      expressionRejects statementOrdinary statementRejects
        input.declarativeRemainder rejected.declarativeRemainder := by
  unfold ifStatement at result
  cases markerResult : keyword .ifKw .statement input with
  | invariant error => simp [bind, markerResult] at result
  | reject markerFailure markerRejected =>
      have markerRejectedEq := keyword_reject_state_eq .ifKw .statement
        markerResult
      subst markerRejected
      simp only [bind, markerResult] at result
      cases result
      exact .markerMissing
        (keyword_reject_tokenKindAbsentAt .ifKw .statement markerResult)
  | ok marker afterMarker =>
      simp only [bind, markerResult] at result
      have markerParsed := keyword_success_exactTokenParses .ifKw .statement
        markerResult
      cases openingResult : symbol .leftParen .statement afterMarker with
      | invariant error => simp [openingResult] at result
      | reject openingFailure openingRejected =>
          have openingRejectedEq := symbol_reject_state_eq .leftParen
            .statement openingResult
          subst openingRejected
          simp only [openingResult] at result
          cases result
          exact .openingMissing marker.span markerParsed
            (symbol_reject_tokenKindAbsentAt .leftParen .statement
              openingResult)
      | ok opening afterOpening =>
          simp only [openingResult] at result
          have openingParsed := symbol_success_exactTokenParses .leftParen
            .statement openingResult
          cases conditionResult : expression afterOpening with
          | invariant error => simp [conditionResult] at result
          | reject conditionFailure conditionRejected =>
              simp only [conditionResult] at result
              cases result
              exact .conditionRejected marker.span opening.span markerParsed
                openingParsed (expressionRejectSound conditionResult)
          | ok condition afterCondition =>
              simp only [conditionResult] at result
              have conditionParsed := expressionSuccessSound conditionResult
              cases closingResult : symbol .rightParen .statement
                  afterCondition with
              | invariant error => simp [closingResult] at result
              | reject closingFailure closingRejected =>
                  have closingRejectedEq := symbol_reject_state_eq .rightParen
                    .statement closingResult
                  subst closingRejected
                  simp only [closingResult] at result
                  cases result
                  exact .closingMissing marker.span opening.span markerParsed
                    openingParsed conditionParsed
                      (symbol_reject_tokenKindAbsentAt .rightParen .statement
                        closingResult)
              | ok closing afterClosing =>
                  simp only [closingResult] at result
                  have closingParsed := symbol_success_exactTokenParses
                    .rightParen .statement closingResult
                  cases thenResult : coreBlock statement .require afterClosing
                      with
                  | invariant error => simp [thenResult] at result
                  | reject thenFailure thenRejected =>
                      simp only [thenResult] at result
                      cases result
                      exact .thenRejected marker.span opening.span closing.span
                        markerParsed openingParsed conditionParsed
                          closingParsed
                            ((coreBlock_ordinaryOutcome_sound statement
                              .require statementOrdinary statementRejects
                                statementSuccessSound statementRejectSound).2
                                  thenResult)
                  | ok thenBody afterThen =>
                      simp only [thenResult] at result
                      have thenParsed :=
                        (coreBlock_ordinaryOutcome_sound statement .require
                          statementOrdinary statementRejects
                            statementSuccessSound statementRejectSound).1
                              thenResult
                      cases elseResult : ControlInternals.optionalElseBody
                          statement afterThen with
                      | invariant error => simp [elseResult] at result
                      | ok elseBody output => simp [elseResult, pure] at result
                      | reject elseFailure elseRejected =>
                          simp only [elseResult] at result
                          cases result
                          exact .elseRejected marker.span opening.span
                            closing.span markerParsed openingParsed
                              conditionParsed closingParsed thenParsed
                                (ControlInternals.optionalElseBody_reject_ordinary_sound
                                  statement statementOrdinary statementRejects
                                    statementSuccessSound statementRejectSound
                                      elseResult)

end Solcore.Syntax.Parser
