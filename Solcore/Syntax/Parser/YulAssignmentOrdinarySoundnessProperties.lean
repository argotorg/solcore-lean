import Solcore.Syntax.DeclarativeYulAssignmentOrdinaryOutcomeProperties
import Solcore.Syntax.Parser.YulAssignmentRejectionSoundnessProperties
import Solcore.Syntax.Parser.YulExpressionPublicFuelSoundnessProperties

/-!
Executable ordinary-success and rejection bridges for public inline-Yul
assignment outcomes.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every executable assignment success follows the exact ordinary public
assignment grammar, without a diagnostic-freedom premise. -/
theorem yulAssignment_success_ordinary_sound
    {input output : State} {statement : YulStmt}
    (result : yulAssignment input = .ok statement output) :
    DeclarativeGrammar.YulAssignmentOrdinaryParses
      input.declarativeRemainder statement output.declarativeRemainder := by
  unfold yulAssignment at result
  cases namesResult : yulNames input with
  | invariant error => simp [bind, namesResult] at result
  | reject namesFailure namesRejected =>
      simp [bind, namesResult] at result
  | ok names afterNames =>
      simp only [bind, namesResult] at result
      cases operatorResult : symbol .colonEqual .yulStatement afterNames with
      | invariant error => simp [operatorResult] at result
      | reject operatorFailure operatorRejected =>
          simp [operatorResult] at result
      | ok operator afterOperator =>
          simp only [operatorResult] at result
          cases valueResult : yulExpression afterOperator with
          | invariant error => simp [valueResult] at result
          | reject valueFailure valueRejected =>
              simp [valueResult] at result
          | ok value afterValue =>
              simp only [valueResult, pure] at result
              cases result
              exact .parsed operator.span
                (yulNames_success_ordinary_sound namesResult)
                (symbol_success_exactTokenParses .colonEqual .yulStatement
                  operatorResult)
                (yulExpression_success_ordinary_sound valueResult)

/-- Every executable assignment rejection follows the rejection half of the
same public deterministic outcome contract. -/
theorem yulAssignment_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : yulAssignment input = .reject failure rejected) :
    DeclarativeGrammar.YulAssignmentRejects
      DeclarativeGrammar.YulExpressionRejects input.declarativeRemainder
        rejected.declarativeRemainder :=
  yulAssignment_public_reject_sound result

/-- Deterministic ordinary outcome contract exposed beside the executable
success and rejection bridges. -/
theorem yulAssignment_publicOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.YulAssignmentOrdinaryParses
      (DeclarativeGrammar.YulAssignmentRejects
        DeclarativeGrammar.YulExpressionRejects) :=
  DeclarativeGrammar.yulAssignmentDeterministicOutcomeSpec

end Solcore.Syntax.Parser
