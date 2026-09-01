import Solcore.Syntax.DeclarativeCoreStatementWhileOutcomeProperties
import Solcore.Syntax.Parser.CoreBlockOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.CoreTypeOutcomePrimitiveProperties
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties
import Solcore.Syntax.Parser.Statement.Control

/-! Executable ordinary success and exact rejection for Core `while`. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem contextual_reject_tokenKindAbsentAt
    (value : ContextualKeyword) (context : ParseContext)
    {input rejected : State} {failure : Failure}
    (result : contextual value context input = .reject failure rejected) :
    DeclarativeGrammar.TokenKindAbsentAt input.tokens input.window.endIndex
      input.cursor (.identifier value.spelling) := by
  by_cases present : isContextual input value = true
  · rcases contextual_eq_ok_of_isContextual_eq_true value context present with
      ⟨token, parsed⟩
    rw [parsed] at result
    contradiction
  · exact contextualAbsentAt_of_isContextual_eq_false value
      (Bool.eq_false_iff.mpr present)

private theorem contextual_reject_state_eq
    (value : ContextualKeyword) (context : ParseContext)
    {input rejected : State} {failure : Failure}
    (result : contextual value context input = .reject failure rejected) :
    rejected = input :=
  acceptToken_reject_state_shape (.contextual value) context
    (·.isContextual value) result

/-- Every executable `while` success retains all exact sequential stages. -/
theorem whileStatement_success_ordinary_sound
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
    (result : whileStatement statement expression input = .ok value output) :
    DeclarativeGrammar.WhileStatementOrdinaryParses expressionOrdinary
      statementOrdinary input.declarativeRemainder value
        output.declarativeRemainder := by
  unfold whileStatement at result
  cases markerResult : contextual .while .statement input with
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
                  cases bodyResult : coreBlock statement .require afterClosing
                      with
                  | invariant error => simp [bodyResult] at result
                  | reject failure rejected => simp [bodyResult] at result
                  | ok body afterBody =>
                      simp only [bodyResult, pure] at result
                      cases result
                      exact .parsed marker.span opening.span closing.span
                        (contextual_success_exactTokenParses .while .statement
                          markerResult)
                        (symbol_success_exactTokenParses .leftParen .statement
                          openingResult)
                        (expressionSuccessSound conditionResult)
                        (symbol_success_exactTokenParses .rightParen .statement
                          closingResult)
                        ((coreBlock_ordinaryOutcome_sound statement .require
                          statementOrdinary statementRejects
                            statementSuccessSound statementRejectSound).1
                              bodyResult)

/-- Every executable `while` rejection records its first failing stage. -/
theorem whileStatement_reject_ordinary_sound
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
    (result : whileStatement statement expression input =
      .reject failure rejected) :
    DeclarativeGrammar.WhileStatementRejects expressionOrdinary
      expressionRejects statementOrdinary statementRejects
        input.declarativeRemainder rejected.declarativeRemainder := by
  unfold whileStatement at result
  cases markerResult : contextual .while .statement input with
  | invariant error => simp [bind, markerResult] at result
  | reject markerFailure markerRejected =>
      have markerRejectedEq := contextual_reject_state_eq .while .statement
        markerResult
      subst markerRejected
      simp only [bind, markerResult] at result
      cases result
      exact .markerMissing
        (contextual_reject_tokenKindAbsentAt .while .statement markerResult)
  | ok marker afterMarker =>
      simp only [bind, markerResult] at result
      have markerParsed := contextual_success_exactTokenParses .while
        .statement markerResult
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
                  cases bodyResult : coreBlock statement .require afterClosing
                      with
                  | invariant error => simp [bodyResult] at result
                  | ok body output => simp [bodyResult, pure] at result
                  | reject bodyFailure bodyRejected =>
                      simp only [bodyResult] at result
                      cases result
                      exact .bodyRejected marker.span opening.span closing.span
                        markerParsed openingParsed conditionParsed
                          closingParsed
                            ((coreBlock_ordinaryOutcome_sound statement
                              .require statementOrdinary statementRejects
                                statementSuccessSound statementRejectSound).2
                                  bodyResult)

/-- Package both executable Core `while` outcomes. -/
theorem whileStatement_ordinaryOutcome_sound
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
        input.declarativeRemainder rejected.declarativeRemainder) :
    (∀ {input output : State} {value : Statement},
      whileStatement statement expression input = .ok value output →
        DeclarativeGrammar.WhileStatementOrdinaryParses expressionOrdinary
          statementOrdinary input.declarativeRemainder value
            output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      whileStatement statement expression input = .reject failure rejected →
        DeclarativeGrammar.WhileStatementRejects expressionOrdinary
          expressionRejects statementOrdinary statementRejects
            input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨whileStatement_success_ordinary_sound statement expression
      statementOrdinary statementRejects expressionOrdinary
        statementSuccessSound statementRejectSound expressionSuccessSound,
    whileStatement_reject_ordinary_sound statement expression
      statementOrdinary statementRejects expressionRejects expressionOrdinary
        statementSuccessSound statementRejectSound expressionSuccessSound
          expressionRejectSound⟩

/-- Re-export deterministic Core `while` outcomes. -/
theorem whileStatement_ordinaryOutcomeSpec
    {expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop}
    {expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    {statementOrdinary : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop}
    {statementRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (expressionOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      expressionOrdinary expressionRejects)
    (statementOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      statementOrdinary statementRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.WhileStatementOrdinaryParses expressionOrdinary
        statementOrdinary)
      (DeclarativeGrammar.WhileStatementRejects expressionOrdinary
        expressionRejects statementOrdinary statementRejects) :=
  DeclarativeGrammar.whileStatementDeterministicOutcomeSpec
    expressionOutcomes statementOutcomes

end Solcore.Syntax.Parser
