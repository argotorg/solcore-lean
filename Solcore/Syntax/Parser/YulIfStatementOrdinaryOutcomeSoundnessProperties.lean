import Solcore.Syntax.DeclarativeYulStatementControlOutcomeProperties
import Solcore.Syntax.Parser.Yul.Control
import Solcore.Syntax.Parser.YulBlockOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.YulExpressionPublicFuelSoundnessProperties
import Solcore.Syntax.Parser.YulKeywordRejectionSoundnessProperties

/-! Executable ordinary-success and rejection bridges for Yul `if`. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every executable `if` success follows the ordinary expression and block
relations without a diagnostic-freedom premise. -/
theorem yulIfStatement_success_ordinary_sound
    (statement : Parser YulStmt)
    (statementOrdinary : DeclarativeGrammar.Remainder → YulStmt →
      DeclarativeGrammar.Remainder → Prop)
    (statementSuccessSound : ∀ {input output : State} {value : YulStmt},
      statement input = .ok value output →
        statementOrdinary input.declarativeRemainder value
          output.declarativeRemainder)
    {input output : State} {value : YulStmt}
    (result : yulIfStatement statement input = .ok value output) :
    DeclarativeGrammar.YulIfStatementOrdinaryParses statementOrdinary
      input.declarativeRemainder value output.declarativeRemainder := by
  unfold yulIfStatement at result
  cases markerResult : keyword .ifKw .yulStatement input with
  | invariant error => simp [bind, markerResult] at result
  | reject failure rejected => simp [bind, markerResult] at result
  | ok marker afterMarker =>
      simp only [bind, markerResult] at result
      cases conditionResult : yulExpression afterMarker with
      | invariant error => simp [conditionResult] at result
      | reject failure rejected => simp [conditionResult] at result
      | ok condition afterCondition =>
          simp only [conditionResult] at result
          cases bodyResult : yulBlock statement afterCondition with
          | invariant error => simp [bodyResult] at result
          | reject failure rejected => simp [bodyResult] at result
          | ok body afterBody =>
              simp only [bodyResult, pure] at result
              cases result
              exact .parsed marker.span
                (keyword_success_exactTokenParses .ifKw .yulStatement
                  markerResult)
                (yulExpression_success_ordinary_sound conditionResult)
                (yulBlock_success_ordinary_sound statement statementOrdinary
                  statementSuccessSound bodyResult)

/-- Every executable `if` rejection identifies its exact sequential stage and
retains the rejected remainder reported there. -/
theorem yulIfStatement_reject_ordinary_sound
    (statement : Parser YulStmt)
    (statementOrdinary : DeclarativeGrammar.Remainder → YulStmt →
      DeclarativeGrammar.Remainder → Prop)
    (statementRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (statementSuccessSound : ∀ {input output : State} {value : YulStmt},
      statement input = .ok value output →
        statementOrdinary input.declarativeRemainder value
          output.declarativeRemainder)
    (statementRejectSound : ∀ {input rejected : State} {failure : Failure},
      statement input = .reject failure rejected →
        statementRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : yulIfStatement statement input = .reject failure rejected) :
    DeclarativeGrammar.YulIfStatementRejects statementOrdinary
      statementRejects input.declarativeRemainder
        rejected.declarativeRemainder := by
  unfold yulIfStatement at result
  cases markerResult : keyword .ifKw .yulStatement input with
  | invariant error => simp [bind, markerResult] at result
  | reject markerFailure markerRejected =>
      have rejectedEq := keyword_reject_state_eq .ifKw .yulStatement
        markerResult
      subst markerRejected
      simp only [bind, markerResult] at result
      cases result
      exact .markerMissing
        (keyword_reject_tokenKindAbsentAt .ifKw .yulStatement markerResult)
  | ok marker afterMarker =>
      simp only [bind, markerResult] at result
      cases conditionResult : yulExpression afterMarker with
      | invariant error => simp [conditionResult] at result
      | reject conditionFailure conditionRejected =>
          simp only [conditionResult] at result
          cases result
          exact .conditionRejected marker.span
            (keyword_success_exactTokenParses .ifKw .yulStatement
              markerResult)
            (yulExpression_reject_sound conditionResult)
      | ok condition afterCondition =>
          simp only [conditionResult] at result
          cases bodyResult : yulBlock statement afterCondition with
          | invariant error => simp [bodyResult] at result
          | reject bodyFailure bodyRejected =>
              simp only [bodyResult] at result
              cases result
              exact .bodyRejected marker.span
                (keyword_success_exactTokenParses .ifKw .yulStatement
                  markerResult)
                (yulExpression_success_ordinary_sound conditionResult)
                (yulBlock_reject_ordinary_sound statement statementOrdinary
                  statementRejects statementSuccessSound statementRejectSound
                  bodyResult)
          | ok body afterBody => simp [bodyResult, pure] at result

end Solcore.Syntax.Parser
