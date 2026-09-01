import Solcore.Syntax.DeclarativeCorePatternComptimeOutcomeProperties
import Solcore.Syntax.Parser.CoreTypeOutcomePrimitiveProperties
import Solcore.Syntax.Parser.Pattern

/-! Executable ordinary outcomes for Core compile-time patterns. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PatternInternals

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

/-- Every executable compile-time-pattern success follows the supplied
ordinary expression relation. -/
theorem comptimePattern_success_ordinary_sound
    (expression : Parser Expr)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSuccessSound : ∀ {input output : State} {value : Expr},
      expression input = .ok value output → expressionOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    {input output : State} {pattern : Pattern}
    (result : comptimePattern expression input = .ok pattern output) :
    DeclarativeGrammar.ComptimePatternOrdinaryParses expressionOrdinary
      input.declarativeRemainder pattern output.declarativeRemainder := by
  unfold comptimePattern at result
  cases markerResult : contextual .comptime .pattern input with
  | invariant error => simp [markerResult] at result
  | reject failure rejected => simp [markerResult] at result
  | ok marker afterMarker =>
      simp only [markerResult] at result
      cases expressionResult : expression afterMarker with
      | invariant error => simp [expressionResult] at result
      | reject failure rejected => simp [expressionResult] at result
      | ok value afterExpression =>
          simp only [expressionResult] at result
          cases result
          exact .parsed marker.span
            (contextual_success_exactTokenParses .comptime .pattern
              markerResult)
            (expressionSuccessSound expressionResult)

/-- Every executable compile-time-pattern rejection is the missing marker or
the exact supplied-expression rejection after that marker. -/
theorem comptimePattern_reject_ordinary_sound
    (expression : Parser Expr)
    (expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (expressionRejectSound : ∀ {input rejected : State} {failure : Failure},
      expression input = .reject failure rejected → expressionRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : comptimePattern expression input = .reject failure rejected) :
    DeclarativeGrammar.ComptimePatternRejects expressionRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold comptimePattern at result
  cases markerResult : contextual .comptime .pattern input with
  | invariant error => simp [markerResult] at result
  | reject markerFailure afterMarker =>
      simp only [markerResult] at result
      have rejectedEq : afterMarker = rejected := by injection result
      subst rejected
      have stateEq := contextual_reject_state_eq .comptime .pattern
        markerResult
      rw [stateEq]
      exact .markerMissing
        (contextual_reject_tokenKindAbsentAt .comptime .pattern markerResult)
  | ok marker afterMarker =>
      simp only [markerResult] at result
      cases expressionResult : expression afterMarker with
      | invariant error => simp [expressionResult] at result
      | ok value afterExpression => simp [expressionResult] at result
      | reject expressionFailure afterExpression =>
          simp only [expressionResult] at result
          have rejectedEq : afterExpression = rejected := by injection result
          subst rejected
          exact .expressionRejected marker.span
            (contextual_success_exactTokenParses .comptime .pattern
              markerResult)
            (expressionRejectSound expressionResult)

/-- Package both executable compile-time-pattern outcomes. -/
theorem comptimePattern_ordinaryOutcome_sound
    (expression : Parser Expr)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSuccessSound : ∀ {input output : State} {value : Expr},
      expression input = .ok value output → expressionOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (expressionRejectSound : ∀ {input rejected : State} {failure : Failure},
      expression input = .reject failure rejected → expressionRejects
        input.declarativeRemainder rejected.declarativeRemainder) :
    (∀ {input output : State} {pattern : Pattern},
      comptimePattern expression input = .ok pattern output →
        DeclarativeGrammar.ComptimePatternOrdinaryParses expressionOrdinary
          input.declarativeRemainder pattern output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      comptimePattern expression input = .reject failure rejected →
        DeclarativeGrammar.ComptimePatternRejects expressionRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨comptimePattern_success_ordinary_sound expression expressionOrdinary
      expressionSuccessSound,
    comptimePattern_reject_ordinary_sound expression expressionRejects
      expressionRejectSound⟩

/-- Re-export deterministic compile-time-pattern outcomes. -/
theorem comptimePattern_ordinaryOutcomeSpec
    {expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop}
    {expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (expressionOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      expressionOrdinary expressionRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.ComptimePatternOrdinaryParses expressionOrdinary)
      (DeclarativeGrammar.ComptimePatternRejects expressionRejects) :=
  DeclarativeGrammar.comptimePatternDeterministicOutcomeSpec
    expressionOutcomes

end Solcore.Syntax.Parser.PatternInternals
