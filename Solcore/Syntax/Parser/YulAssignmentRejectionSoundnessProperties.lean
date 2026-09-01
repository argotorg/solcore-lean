import Solcore.Syntax.DeclarativeYulAssignmentOutcomeProperties
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties
import Solcore.Syntax.Parser.YulExpressionRejectionSoundnessProperties
import Solcore.Syntax.Parser.YulNamesOutcomeProperties
import Solcore.Syntax.Parser.Yul.Statement

/-!
Exact executable rejection bridges for transactional inline-Yul assignment
attempts.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every executable assignment rejection records the exact names, operator,
or expression stage that rejected. -/
theorem yulAssignment_reject_sound
    (expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (expressionRejectSound : ∀ {input rejected : State}
      {failure : Failure},
      yulExpression input = .reject failure rejected →
        expressionRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : yulAssignment input = .reject failure rejected) :
    DeclarativeGrammar.YulAssignmentRejects expressionRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold yulAssignment at result
  cases namesResult : yulNames input with
  | invariant error => simp [bind, namesResult] at result
  | reject namesFailure namesRejected =>
      simp only [bind, namesResult] at result
      cases result
      exact .namesRejected (yulNames_reject_sound namesResult)
  | ok names afterNames =>
      simp only [bind, namesResult] at result
      have namesParsed := yulNames_success_ordinary_sound namesResult
      cases operatorResult : symbol .colonEqual .yulStatement afterNames with
      | invariant error => simp [operatorResult] at result
      | reject operatorFailure operatorRejected =>
          have operatorRejectedEq := symbol_reject_state_eq .colonEqual
            .yulStatement operatorResult
          subst operatorRejected
          simp only [operatorResult] at result
          cases result
          exact .operatorAbsent namesParsed
            (symbol_reject_tokenKindAbsentAt .colonEqual .yulStatement
              operatorResult)
      | ok operator afterOperator =>
          simp only [operatorResult] at result
          have operatorParsed := symbol_success_exactTokenParses .colonEqual
            .yulStatement operatorResult
          cases valueResult : yulExpression afterOperator with
          | invariant error => simp [valueResult] at result
          | reject valueFailure valueRejected =>
              simp only [valueResult] at result
              cases result
              exact .expressionRejected operator.span namesParsed
                operatorParsed (expressionRejectSound valueResult)
          | ok value afterValue => simp [valueResult, pure] at result

/-- Public inline-Yul expressions instantiate the abstract assignment
rejection bridge with their exact recovery-boundary rejection relation. -/
theorem yulAssignment_public_reject_sound
    {input rejected : State} {failure : Failure}
    (result : yulAssignment input = .reject failure rejected) :
    DeclarativeGrammar.YulAssignmentRejects
      DeclarativeGrammar.YulExpressionRejects input.declarativeRemainder
        rejected.declarativeRemainder :=
  yulAssignment_reject_sound DeclarativeGrammar.YulExpressionRejects
    yulExpression_reject_sound result

/-- A transactional rejection supplies the unary rejection predicate of the
fallback built from any compatible deterministic expression outcomes. -/
theorem yulAssignment_fallback_reject_sound
    (ordinaryExpression cleanExpression :
      DeclarativeGrammar.Remainder → YulExpr →
        DeclarativeGrammar.Remainder → Prop)
    (expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (outcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      ordinaryExpression expressionRejects)
    (cleanToOrdinary : ∀ {input value output},
      cleanExpression input value output →
        ordinaryExpression input value output)
    (expressionRejectSound : ∀ {input rejected : State}
      {failure : Failure},
      yulExpression input = .reject failure rejected →
        expressionRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : yulAssignment input = .reject failure rejected) :
    (DeclarativeGrammar.YulAssignmentFallbackSpec.ofOutcomes
      ordinaryExpression cleanExpression expressionRejects outcomes
        cleanToOrdinary).rejects input.declarativeRemainder :=
  ⟨rejected.declarativeRemainder,
    yulAssignment_reject_sound expressionRejects expressionRejectSound
      result⟩

end Solcore.Syntax.Parser
