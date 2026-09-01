import Solcore.Syntax.DeclarativeYulStatementControlOutcomeProperties
import Solcore.Syntax.Parser.Yul.Control
import Solcore.Syntax.Parser.YulBlockOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.YulExpressionPublicFuelSoundnessProperties
import Solcore.Syntax.Parser.YulKeywordRejectionSoundnessProperties

/-! Executable ordinary-success and rejection bridges for Yul `for`. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every executable `for` success follows the ordinary expression and block
relations without a diagnostic-freedom premise. -/
theorem yulForStatement_success_ordinary_sound
    (statement : Parser YulStmt)
    (statementOrdinary : DeclarativeGrammar.Remainder → YulStmt →
      DeclarativeGrammar.Remainder → Prop)
    (statementSuccessSound : ∀ {input output : State} {value : YulStmt},
      statement input = .ok value output →
        statementOrdinary input.declarativeRemainder value
          output.declarativeRemainder)
    {input output : State} {value : YulStmt}
    (result : yulForStatement statement input = .ok value output) :
    DeclarativeGrammar.YulForStatementOrdinaryParses statementOrdinary
      input.declarativeRemainder value output.declarativeRemainder := by
  unfold yulForStatement at result
  cases markerResult : keyword .forKw .yulStatement input with
  | invariant error => simp [bind, markerResult] at result
  | reject failure rejected => simp [bind, markerResult] at result
  | ok marker afterMarker =>
      simp only [bind, markerResult] at result
      cases initializerResult : yulBlock statement afterMarker with
      | invariant error => simp [initializerResult] at result
      | reject failure rejected => simp [initializerResult] at result
      | ok initializer afterInitializer =>
          simp only [initializerResult] at result
          cases conditionResult : yulExpression afterInitializer with
          | invariant error => simp [conditionResult] at result
          | reject failure rejected => simp [conditionResult] at result
          | ok condition afterCondition =>
              simp only [conditionResult] at result
              cases postResult : yulBlock statement afterCondition with
              | invariant error => simp [postResult] at result
              | reject failure rejected => simp [postResult] at result
              | ok post afterPost =>
                  simp only [postResult] at result
                  cases bodyResult : yulBlock statement afterPost with
                  | invariant error => simp [bodyResult] at result
                  | reject failure rejected => simp [bodyResult] at result
                  | ok body afterBody =>
                      simp only [bodyResult, pure] at result
                      cases result
                      exact .parsed marker.span
                        (keyword_success_exactTokenParses .forKw .yulStatement
                          markerResult)
                        (yulBlock_success_ordinary_sound statement
                          statementOrdinary statementSuccessSound
                          initializerResult)
                        (yulExpression_success_ordinary_sound conditionResult)
                        (yulBlock_success_ordinary_sound statement
                          statementOrdinary statementSuccessSound postResult)
                        (yulBlock_success_ordinary_sound statement
                          statementOrdinary statementSuccessSound bodyResult)

/-- Every executable `for` rejection identifies its exact sequential stage and
retains the rejected remainder reported there. -/
theorem yulForStatement_reject_ordinary_sound
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
    (result : yulForStatement statement input = .reject failure rejected) :
    DeclarativeGrammar.YulForStatementRejects statementOrdinary
      statementRejects input.declarativeRemainder
        rejected.declarativeRemainder := by
  unfold yulForStatement at result
  cases markerResult : keyword .forKw .yulStatement input with
  | invariant error => simp [bind, markerResult] at result
  | reject markerFailure markerRejected =>
      have rejectedEq := keyword_reject_state_eq .forKw .yulStatement
        markerResult
      subst markerRejected
      simp only [bind, markerResult] at result
      cases result
      exact .markerMissing
        (keyword_reject_tokenKindAbsentAt .forKw .yulStatement markerResult)
  | ok marker afterMarker =>
      simp only [bind, markerResult] at result
      cases initializerResult : yulBlock statement afterMarker with
      | invariant error => simp [initializerResult] at result
      | reject initializerFailure initializerRejected =>
          simp only [initializerResult] at result
          cases result
          exact .initializerRejected marker.span
            (keyword_success_exactTokenParses .forKw .yulStatement
              markerResult)
            (yulBlock_reject_ordinary_sound statement statementOrdinary
              statementRejects statementSuccessSound statementRejectSound
              initializerResult)
      | ok initializer afterInitializer =>
          simp only [initializerResult] at result
          cases conditionResult : yulExpression afterInitializer with
          | invariant error => simp [conditionResult] at result
          | reject conditionFailure conditionRejected =>
              simp only [conditionResult] at result
              cases result
              exact .conditionRejected marker.span
                (keyword_success_exactTokenParses .forKw .yulStatement
                  markerResult)
                (yulBlock_success_ordinary_sound statement statementOrdinary
                  statementSuccessSound initializerResult)
                (yulExpression_reject_sound conditionResult)
          | ok condition afterCondition =>
              simp only [conditionResult] at result
              cases postResult : yulBlock statement afterCondition with
              | invariant error => simp [postResult] at result
              | reject postFailure postRejected =>
                  simp only [postResult] at result
                  cases result
                  exact .postRejected marker.span
                    (keyword_success_exactTokenParses .forKw .yulStatement
                      markerResult)
                    (yulBlock_success_ordinary_sound statement
                      statementOrdinary statementSuccessSound
                      initializerResult)
                    (yulExpression_success_ordinary_sound conditionResult)
                    (yulBlock_reject_ordinary_sound statement
                      statementOrdinary statementRejects statementSuccessSound
                      statementRejectSound postResult)
              | ok post afterPost =>
                  simp only [postResult] at result
                  cases bodyResult : yulBlock statement afterPost with
                  | invariant error => simp [bodyResult] at result
                  | reject bodyFailure bodyRejected =>
                      simp only [bodyResult] at result
                      cases result
                      exact .bodyRejected marker.span
                        (keyword_success_exactTokenParses .forKw .yulStatement
                          markerResult)
                        (yulBlock_success_ordinary_sound statement
                          statementOrdinary statementSuccessSound
                          initializerResult)
                        (yulExpression_success_ordinary_sound conditionResult)
                        (yulBlock_success_ordinary_sound statement
                          statementOrdinary statementSuccessSound postResult)
                        (yulBlock_reject_ordinary_sound statement
                          statementOrdinary statementRejects
                          statementSuccessSound statementRejectSound
                          bodyResult)
                  | ok body afterBody => simp [bodyResult, pure] at result

end Solcore.Syntax.Parser
