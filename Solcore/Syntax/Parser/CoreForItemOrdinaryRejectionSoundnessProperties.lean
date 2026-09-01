import Solcore.Syntax.Parser.CoreForItemOrdinarySuccessSoundnessProperties
import Solcore.Syntax.Parser.YulKeywordRejectionSoundnessProperties

/-! Exact executable rejection for one Core `for`-header item. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.StatementSimpleInternals

/-- Executable `for let` rejection identifies the first rejected stage. -/
theorem forLetItem_reject_ordinary_sound
    (expression : Parser Expr)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (expressionRejectSound : ∀ {input rejected : State}
      {failure : Failure}, expression input = .reject failure rejected →
        expressionRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : forLetItem expression input = .reject failure rejected) :
    DeclarativeGrammar.ForLetItemRejects expressionOrdinary
      expressionRejects DeclarativeGrammar.TypeExprRejects
        input.declarativeRemainder rejected.declarativeRemainder := by
  unfold forLetItem at result
  cases markerResult : keyword .letKw .statement input with
  | invariant error => simp [bind, markerResult] at result
  | reject markerFailure markerRejected =>
      have markerRejectedEq := keyword_reject_state_eq .letKw .statement
        markerResult
      subst markerRejected
      simp only [bind, markerResult] at result
      cases result
      exact .markerRejected
        (keyword_reject_tokenKindAbsentAt .letKw .statement markerResult)
  | ok marker afterMarker =>
      simp only [bind, markerResult] at result
      have markerParsed := keyword_success_exactTokenParses .letKw .statement
        markerResult
      cases nameResult : identifier .statement afterMarker with
      | invariant error => simp [nameResult] at result
      | reject nameFailure nameRejected =>
          simp only [nameResult] at result
          cases result
          exact .nameRejected marker.span markerParsed
            (identifier_reject_sound .statement nameResult)
      | ok name afterName =>
          simp only [nameResult] at result
          have nameParsed := identifier_success_sound .statement nameResult
          cases typeResult : optionalLetType afterName with
          | invariant error => simp [typeResult] at result
          | reject typeFailure typeRejected =>
              simp only [typeResult] at result
              cases result
              exact .typeRejected marker.span markerParsed nameParsed
                (optionalLetType_reject_ordinary_sound typeResult)
          | ok type afterType =>
              simp only [typeResult] at result
              have typeParsed := optionalLetType_success_ordinary_sound
                typeResult
              cases initializerResult : optionalLetInitializer expression
                  afterType with
              | invariant error => simp [initializerResult] at result
              | reject initializerFailure initializerRejected =>
                  simp only [initializerResult] at result
                  cases result
                  exact .initializerRejected marker.span markerParsed
                    nameParsed typeParsed
                    (optionalLetInitializer_reject_ordinary_sound expression
                      expressionRejects expressionRejectSound
                        initializerResult)
              | ok initializer afterInitializer =>
                  simp [initializerResult, pure] at result

/-- The fallback can reject only in its initial expression or the right side
of a committed value-assignment suffix. -/
theorem forAssignmentOrExpression_reject_ordinary_sound
    (expression : Parser Expr)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSuccessSound : ∀ {input output : State} {value : Expr},
      expression input = .ok value output → expressionOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (expressionRejectSound : ∀ {input rejected : State}
      {failure : Failure}, expression input = .reject failure rejected →
        expressionRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : forAssignmentOrExpression expression input =
      .reject failure rejected) :
    DeclarativeGrammar.ForAssignmentOrExpressionRejects expressionOrdinary
      expressionRejects input.declarativeRemainder
        rejected.declarativeRemainder := by
  unfold forAssignmentOrExpression at result
  cases leftResult : expression input with
  | invariant error => simp [bind, leftResult] at result
  | reject leftFailure leftRejected =>
      simp only [bind, leftResult] at result
      cases result
      exact .leftRejected (expressionRejectSound leftResult)
  | ok left afterLeft =>
      simp only [bind, leftResult] at result
      have leftParsed := expressionSuccessSound leftResult
      cases tailResult : optionalAssignmentTail expression afterLeft with
      | invariant error => simp [tailResult] at result
      | reject tailFailure tailRejected =>
          simp only [tailResult] at result
          rcases optionalAssignmentTail_reject_ordinary_sound expression
              expressionRejects expressionRejectSound tailResult with
            ⟨afterOperator, operator, tildeAbsent, operatorParsed,
              rightRejected⟩
          cases result
          exact .rightRejected leftParsed tildeAbsent operatorParsed
            rightRejected
      | ok tail afterTail =>
          cases tail with
          | none => simp [tailResult, pure] at result
          | some tail => cases tail <;> simp [tailResult, pure] at result

end Solcore.Syntax.Parser.StatementSimpleInternals

namespace Solcore.Syntax.Parser

/-- Public rejection follows the same positive-`let` commitment as the
executable dispatcher and carries exact negative evidence on fallback. -/
theorem forItem_reject_ordinary_sound
    (expression : Parser Expr)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSuccessSound : ∀ {input output : State} {value : Expr},
      expression input = .ok value output → expressionOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (expressionRejectSound : ∀ {input rejected : State}
      {failure : Failure}, expression input = .reject failure rejected →
        expressionRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : forItem expression input = .reject failure rejected) :
    DeclarativeGrammar.ForItemRejects expressionOrdinary expressionRejects
      DeclarativeGrammar.TypeExprRejects input.declarativeRemainder
        rejected.declarativeRemainder := by
  unfold forItem at result
  by_cases letPresent : isKeyword input .letKw
  · simp only [letPresent, if_true] at result
    rcases keyword_eq_ok_of_isKeyword_eq_true .letKw .statement letPresent
      with ⟨marker, markerResult⟩
    exact .letItem
      (keyword_success_exactTokenParses .letKw .statement markerResult).1
      (StatementSimpleInternals.forLetItem_reject_ordinary_sound expression
        expressionOrdinary expressionRejects expressionRejectSound result)
  · have letAbsent : isKeyword input .letKw = false :=
      Bool.eq_false_iff.mpr letPresent
    simp only [letAbsent, Bool.false_eq_true, if_false] at result
    exact .assignmentOrExpression
      (keywordAbsentAt_of_isKeyword_eq_false .letKw letAbsent)
      (StatementSimpleInternals.forAssignmentOrExpression_reject_ordinary_sound
        expression expressionOrdinary expressionRejects
          expressionSuccessSound expressionRejectSound result)

end Solcore.Syntax.Parser
