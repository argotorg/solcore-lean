import Solcore.Syntax.Parser.CoreMatchStatementOrdinarySuccessSoundnessProperties
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties
import Solcore.Syntax.Parser.YulKeywordRejectionSoundnessProperties

/-! Exact executable rejection for complete Core matches. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every executable match rejection records the first rejecting structural
stage; diagnostic-only validation cannot reject. -/
theorem matchStatement_reject_ordinary_sound
    (statement : Parser Statement) (expression : Parser Expr)
    (pattern : Parser Pattern)
    (statementOrdinary : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop)
    (statementRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (patternOrdinary : DeclarativeGrammar.Remainder → Pattern →
      DeclarativeGrammar.Remainder → Prop)
    (patternRejects : DeclarativeGrammar.Remainder →
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
    (expressionWindow : Parser.PreservesTokenWindow expression)
    (patternSuccessSound : ∀ {input output : State} {value : Pattern},
      pattern input = .ok value output → patternOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (patternRejectSound : ∀ {input rejected : State} {failure : Failure},
      pattern input = .reject failure rejected → patternRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : matchStatement statement expression pattern input =
      .reject failure rejected) :
    DeclarativeGrammar.MatchStatementRejects statementOrdinary
      statementRejects expressionOrdinary expressionRejects patternOrdinary
        patternRejects input.declarativeRemainder
          rejected.declarativeRemainder := by
  unfold matchStatement at result
  cases markerResult : keyword .matchKw .statement input with
  | invariant error => simp [bind, markerResult] at result
  | reject markerFailure markerRejected =>
      have rejectedEq := keyword_reject_state_eq .matchKw .statement
        markerResult
      subst markerRejected
      simp only [bind, markerResult] at result
      cases result
      exact .markerMissing
        (keyword_reject_tokenKindAbsentAt .matchKw .statement markerResult)
  | ok marker afterMarker =>
      simp only [bind, markerResult] at result
      have markerParsed := keyword_success_exactTokenParses .matchKw
        .statement markerResult
      cases valuesResult : delimited .leftParen .rightParen false expression
          .expression .statement afterMarker with
      | invariant error => simp [valuesResult] at result
      | reject valuesFailure valuesRejected =>
          simp only [valuesResult] at result
          cases result
          exact .valuesRejected marker.span markerParsed
            (MatchInternals.matchScrutineeList_reject_ordinary_sound
              expression expressionOrdinary expressionRejects
                expressionSuccessSound expressionRejectSound valuesResult)
      | ok values afterValues =>
          simp only [valuesResult] at result
          have valuesParsed :=
            MatchInternals.matchScrutineeList_success_ordinary_sound expression
              expressionOrdinary expressionSuccessSound expressionWindow
                valuesResult
          cases scrutineesResult : MatchInternals.requireScrutinees values
              afterValues with
          | invariant error => simp [scrutineesResult] at result
          | reject scrutineeFailure scrutineesRejected =>
              simp only [scrutineesResult] at result
              cases result
              exact .scrutineesRejected marker.span markerParsed valuesParsed
                (MatchInternals.requireScrutinees_reject_ordinary_sound values
                  scrutineesResult)
          | ok scrutinees afterScrutinees =>
              simp only [scrutineesResult] at result
              have scrutineesRequired :=
                MatchInternals.requireScrutinees_success_ordinary_sound values
                  scrutineesResult
              cases openingResult : symbol .leftBrace .statement
                  afterScrutinees with
              | invariant error => simp [openingResult] at result
              | reject openingFailure openingRejected =>
                  have rejectedEq := symbol_reject_state_eq .leftBrace
                    .statement openingResult
                  subst openingRejected
                  simp only [openingResult] at result
                  cases result
                  exact .openingMissing marker.span markerParsed valuesParsed
                    scrutineesRequired
                    (symbol_reject_tokenKindAbsentAt .leftBrace .statement
                      openingResult)
              | ok opening afterOpening =>
                  simp only [openingResult] at result
                  have openingParsed := symbol_success_exactTokenParses
                    .leftBrace .statement openingResult
                  cases casesResult : MatchInternals.matchCases statement
                      pattern (afterOpening.remainingCount + 1) []
                        afterOpening with
                  | invariant error => simp [casesResult] at result
                  | reject casesFailure casesRejected =>
                      simp only [casesResult] at result
                      cases result
                      exact .casesRejected marker.span opening.span
                        markerParsed valuesParsed scrutineesRequired
                          openingParsed
                          (MatchInternals.matchCases_reject_ordinary_sound
                            statement pattern statementOrdinary
                              statementRejects patternOrdinary patternRejects
                                statementSuccessSound statementRejectSound
                                  patternSuccessSound patternRejectSound
                                    casesResult)
                  | ok cases afterCases =>
                      simp only [casesResult] at result
                      have casesParsed :=
                        MatchInternals.matchCases_success_ordinary_sound
                          statement pattern statementOrdinary statementRejects
                            patternOrdinary statementSuccessSound
                              statementRejectSound patternSuccessSound
                                casesResult
                      cases defaultResult :
                          MatchInternals.optionalDefaultBody statement
                            afterCases with
                      | invariant error => simp [defaultResult] at result
                      | reject defaultFailure defaultRejected =>
                          simp only [defaultResult] at result
                          cases result
                          exact .defaultRejected marker.span opening.span
                            markerParsed valuesParsed scrutineesRequired
                              openingParsed casesParsed
                              (MatchInternals.optionalDefaultBody_reject_ordinary_sound
                                statement statementOrdinary statementRejects
                                  statementSuccessSound statementRejectSound
                                    defaultResult)
                      | ok defaultBody afterDefault =>
                          simp only [defaultResult] at result
                          have defaultParsed :=
                            MatchInternals.optionalDefaultBody_success_ordinary_sound
                              statement statementOrdinary statementRejects
                                statementSuccessSound statementRejectSound
                                  defaultResult
                          cases closingResult : symbol .rightBrace .statement
                              afterDefault with
                          | invariant error => simp [closingResult] at result
                          | reject closingFailure closingRejected =>
                              have rejectedEq := symbol_reject_state_eq
                                .rightBrace .statement closingResult
                              subst closingRejected
                              simp only [closingResult] at result
                              cases result
                              exact .closingMissing marker.span opening.span
                                markerParsed valuesParsed scrutineesRequired
                                  openingParsed casesParsed defaultParsed
                                  (symbol_reject_tokenKindAbsentAt .rightBrace
                                    .statement closingResult)
                          | ok closing afterClosing =>
                              simp only [closingResult] at result
                              rcases MatchInternals.validateMatchArities_succeeds_stable
                                  scrutinees.elements.toList.length cases
                                    afterClosing with
                                ⟨afterValidation, validationResult,
                                  validationStable⟩
                              rw [validationResult] at result
                              by_cases missing :
                                  (cases.isEmpty && defaultBody.isNone) = true
                              · simp [missing, emitDiagnostic, modifyState,
                                  pure] at result
                              · have missingFalse :
                                    (cases.isEmpty && defaultBody.isNone) =
                                      false := Bool.eq_false_iff.mpr missing
                                simp [missingFalse, pure] at result

end Solcore.Syntax.Parser
