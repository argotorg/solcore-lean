import Solcore.Syntax.DeclarativeYulNameStatementOutcomeProperties
import Solcore.Syntax.Parser.YulAssignmentOrdinarySoundnessProperties
import Solcore.Syntax.Parser.YulStatementBasicOrdinaryOutcomeSoundnessProperties

/-!
Executable ordinary-success and exact-rejection bridges for the name-start
assignment-or-expression branch of the Yul statement dispatcher.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every successful executable name choice records either assignment success
or exact assignment rejection followed by expression success at the original
input. -/
theorem yulNameStatementChoice_success_ordinary_sound
    {input output : State} {statement : YulStmt}
    (result : orElse yulAssignment yulExpressionStatement input =
      .ok statement output) :
    DeclarativeGrammar.YulNameStatementOrdinaryParses
      input.declarativeRemainder statement output.declarativeRemainder := by
  unfold orElse at result
  cases assignmentResult : yulAssignment input with
  | invariant error => simp [assignmentResult] at result
  | ok assignment afterAssignment =>
      simp only [assignmentResult] at result
      cases result
      exact .primary
        (yulAssignment_success_ordinary_sound assignmentResult)
  | reject assignmentFailure assignmentRejected =>
      simp only [assignmentResult] at result
      exact .fallback
        (yulAssignment_reject_ordinaryOutcome_sound assignmentResult)
        (yulExpressionStatement_success_ordinary_sound result)

/-- Every executable name-choice rejection retains both exact branch
rejections and is nonconsuming because public expression rejection is
nonconsuming. -/
theorem yulNameStatementChoice_reject_sound
    {input rejected : State} {failure : Failure}
    (result : orElse yulAssignment yulExpressionStatement input =
      .reject failure rejected) :
    DeclarativeGrammar.YulNameStatementRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold orElse at result
  cases assignmentResult : yulAssignment input with
  | invariant error => simp [assignmentResult] at result
  | ok assignment afterAssignment => simp [assignmentResult] at result
  | reject assignmentFailure assignmentRejected =>
      simp only [assignmentResult] at result
      have assignmentRejection :=
        yulAssignment_reject_ordinaryOutcome_sound assignmentResult
      have expressionRejection :=
        yulExpressionStatement_reject_ordinaryOutcome_sound result
      cases expressionRejection with
      | expressionRejected rejectedExpression =>
          have outputEq := rejectedExpression.output_eq
          rw [outputEq]
          exact .both assignmentRejection
            (.expressionRejected rejectedExpression)

/-- The concrete name-choice executable exposes its declarative outcome
contract. -/
theorem yulNameStatementChoice_publicOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.YulNameStatementOrdinaryParses
      DeclarativeGrammar.YulNameStatementRejects :=
  DeclarativeGrammar.yulNameStatementDeterministicOutcomeSpec

end Solcore.Syntax.Parser
