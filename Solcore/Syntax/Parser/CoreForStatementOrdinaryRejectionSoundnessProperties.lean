import Solcore.Syntax.Parser.CoreForStatementOrdinarySuccessSoundnessProperties
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties
import Solcore.Syntax.Parser.YulKeywordRejectionSoundnessProperties

/-! Executable exact rejection for complete Core `for` statements. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every executable Core `for` rejection records its first rejected stage. -/
theorem forStatement_reject_ordinary_sound
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
    (expressionRejectSound : ∀ {input rejected : State}
      {failure : Failure}, expression input = .reject failure rejected →
        expressionRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    (expressionStrict : ∀ {input output : State} {value : Expr},
      expression input = .ok value output → input.cursor < output.cursor)
    {input rejected : State} {failure : Failure}
    (result : forStatement statement expression input =
      .reject failure rejected) :
    DeclarativeGrammar.ForStatementRejects statementOrdinary statementRejects
      expressionOrdinary expressionRejects input.declarativeRemainder
        rejected.declarativeRemainder := by
  unfold forStatement at result
  cases markerResult : keyword .forKw .statement input with
  | invariant error => simp [bind, markerResult] at result
  | reject markerFailure markerRejected =>
      have rejectedEq := keyword_reject_state_eq .forKw .statement
        markerResult
      subst markerRejected
      simp only [bind, markerResult] at result
      cases result
      exact .markerMissing
        (keyword_reject_tokenKindAbsentAt .forKw .statement markerResult)
  | ok marker afterMarker =>
      simp only [bind, markerResult] at result
      have markerParsed := keyword_success_exactTokenParses .forKw .statement
        markerResult
      cases openingResult : symbol .leftParen .statement afterMarker with
      | invariant error => simp [openingResult] at result
      | reject openingFailure openingRejected =>
          have rejectedEq := symbol_reject_state_eq .leftParen .statement
            openingResult
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
          cases initializerResult : ControlInternals.forItems expression
              .semicolon afterOpening with
          | invariant error => simp [initializerResult] at result
          | reject initializerFailure initializerRejected =>
              simp only [initializerResult] at result
              cases result
              exact .initializerRejected marker.span opening.span markerParsed
                openingParsed
                (ControlInternals.forItems_reject_ordinary_sound expression
                  .semicolon expressionOrdinary expressionRejects
                    expressionSuccessSound expressionRejectSound
                      expressionStrict initializerResult)
          | ok initializer afterInitializer =>
              simp only [initializerResult] at result
              have initializerParsed :=
                ControlInternals.forItems_success_ordinary_sound expression
                  .semicolon expressionOrdinary expressionSuccessSound
                    expressionStrict initializerResult
              cases firstSemicolonResult : symbol .semicolon .statement
                  afterInitializer with
              | invariant error => simp [firstSemicolonResult] at result
              | reject semicolonFailure semicolonRejected =>
                  have rejectedEq := symbol_reject_state_eq .semicolon
                    .statement firstSemicolonResult
                  subst semicolonRejected
                  simp only [firstSemicolonResult] at result
                  cases result
                  exact .firstSemicolonMissing marker.span opening.span
                    markerParsed openingParsed initializerParsed
                    (symbol_reject_tokenKindAbsentAt .semicolon .statement
                      firstSemicolonResult)
              | ok firstSemicolon afterFirstSemicolon =>
                  simp only [firstSemicolonResult] at result
                  have firstSemicolonParsed :=
                    symbol_success_exactTokenParses .semicolon .statement
                      firstSemicolonResult
                  cases conditionResult : expression afterFirstSemicolon with
                  | invariant error => simp [conditionResult] at result
                  | reject conditionFailure conditionRejected =>
                      simp only [conditionResult] at result
                      cases result
                      exact .conditionRejected marker.span opening.span
                        firstSemicolon.span markerParsed openingParsed
                        initializerParsed firstSemicolonParsed
                        (expressionRejectSound conditionResult)
                  | ok condition afterCondition =>
                      simp only [conditionResult] at result
                      have conditionParsed := expressionSuccessSound
                        conditionResult
                      cases secondSemicolonResult :
                          symbol .semicolon .statement afterCondition with
                      | invariant error =>
                          simp [secondSemicolonResult] at result
                      | reject semicolonFailure semicolonRejected =>
                          have rejectedEq := symbol_reject_state_eq .semicolon
                            .statement secondSemicolonResult
                          subst semicolonRejected
                          simp only [secondSemicolonResult] at result
                          cases result
                          exact .secondSemicolonMissing marker.span
                            opening.span firstSemicolon.span markerParsed
                            openingParsed initializerParsed
                            firstSemicolonParsed conditionParsed
                            (symbol_reject_tokenKindAbsentAt .semicolon
                              .statement secondSemicolonResult)
                      | ok secondSemicolon afterSecondSemicolon =>
                          simp only [secondSemicolonResult] at result
                          have secondSemicolonParsed :=
                            symbol_success_exactTokenParses .semicolon
                              .statement secondSemicolonResult
                          cases postResult : ControlInternals.forItems
                              expression .rightParen afterSecondSemicolon with
                          | invariant error => simp [postResult] at result
                          | reject postFailure postRejected =>
                              simp only [postResult] at result
                              cases result
                              exact .postRejected marker.span opening.span
                                firstSemicolon.span secondSemicolon.span
                                markerParsed openingParsed initializerParsed
                                firstSemicolonParsed conditionParsed
                                secondSemicolonParsed
                                (ControlInternals.forItems_reject_ordinary_sound
                                  expression .rightParen expressionOrdinary
                                  expressionRejects expressionSuccessSound
                                  expressionRejectSound expressionStrict
                                  postResult)
                          | ok post afterPost =>
                              simp only [postResult] at result
                              have postParsed :=
                                ControlInternals.forItems_success_ordinary_sound
                                  expression .rightParen expressionOrdinary
                                  expressionSuccessSound expressionStrict
                                  postResult
                              cases closingResult : symbol .rightParen
                                  .statement afterPost with
                              | invariant error =>
                                  simp [closingResult] at result
                              | reject closingFailure closingRejected =>
                                  have rejectedEq := symbol_reject_state_eq
                                    .rightParen .statement closingResult
                                  subst closingRejected
                                  simp only [closingResult] at result
                                  cases result
                                  exact .closingMissing marker.span
                                    opening.span firstSemicolon.span
                                    secondSemicolon.span markerParsed
                                    openingParsed initializerParsed
                                    firstSemicolonParsed conditionParsed
                                    secondSemicolonParsed postParsed
                                    (symbol_reject_tokenKindAbsentAt
                                      .rightParen .statement closingResult)
                              | ok closing afterClosing =>
                                  simp only [closingResult] at result
                                  have closingParsed :=
                                    symbol_success_exactTokenParses
                                      .rightParen .statement closingResult
                                  cases bodyResult : coreBlock statement
                                      .require afterClosing with
                                  | invariant error =>
                                      simp [bodyResult] at result
                                  | ok body output =>
                                      simp [bodyResult, pure] at result
                                  | reject bodyFailure bodyRejected =>
                                      simp only [bodyResult] at result
                                      cases result
                                      exact .bodyRejected marker.span
                                        opening.span firstSemicolon.span
                                        secondSemicolon.span closing.span
                                        markerParsed openingParsed
                                        initializerParsed firstSemicolonParsed
                                        conditionParsed secondSemicolonParsed
                                        postParsed closingParsed
                                        ((coreBlock_ordinaryOutcome_sound
                                          statement .require
                                          statementOrdinary statementRejects
                                          statementSuccessSound
                                          statementRejectSound).2 bodyResult)

end Solcore.Syntax.Parser
