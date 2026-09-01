import Solcore.Syntax.DeclarativeYulAssignmentOrdinaryGrammar
import Solcore.Syntax.DeclarativeYulAssignmentOutcomeGrammar
import Solcore.Syntax.DeclarativeYulNameOutcomeProperties

/-!
Functionality, rejection exclusivity, and clean embedding for ordinary public
inline-Yul assignment outcomes.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem exactToken_output_unique {kind : TokenKind}
    {input leftOutput rightOutput : Remainder}
    {leftSpan rightSpan : SourceSpan}
    (leftParsed : ExactTokenParses kind input leftSpan leftOutput)
    (rightParsed : ExactTokenParses kind input rightSpan rightOutput) :
    leftOutput = rightOutput := by
  rw [leftParsed.2, rightParsed.2]

private theorem absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

/-- Ordinary public assignment success has a unique output remainder. -/
theorem YulAssignmentOrdinaryParses.output_unique
    {input : Remainder} {left right : Syntax.YulStmt}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulAssignmentOrdinaryParses input left afterLeft)
    (rightParsed : YulAssignmentOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftOperatorSpan leftNamesParsed leftOperatorParsed
        leftValueParsed =>
      cases rightParsed with
      | parsed rightOperatorSpan rightNamesParsed rightOperatorParsed
            rightValueParsed =>
          have afterNamesEq :=
            leftNamesParsed.output_unique rightNamesParsed
          subst afterNamesEq
          have afterOperatorEq :=
            exactToken_output_unique leftOperatorParsed rightOperatorParsed
          subst afterOperatorEq
          exact
            yulExpressionPublicDeterministicOutcomeSpec.successOutputUnique
              leftValueParsed rightValueParsed

/-- Exact ordinary assignment rejection excludes every ordinary assignment
success. -/
theorem YulAssignmentRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : YulAssignmentRejects YulExpressionRejects input rejected) :
    ¬ ∃ statement output,
      YulAssignmentOrdinaryParses input statement output := by
  rintro ⟨statement, output, successful⟩
  cases successful with
  | parsed successfulOperatorSpan successfulNamesParsed
        successfulOperatorParsed successfulValueParsed =>
      cases rejection with
      | namesRejected namesRejected =>
          exact namesRejected.disjoint
            ⟨_, _, successfulNamesParsed⟩
      | operatorAbsent rejectedNamesParsed operatorAbsent =>
          have afterNamesEq :=
            rejectedNamesParsed.output_unique successfulNamesParsed
          subst afterNamesEq
          exact absent_conflicts_exact operatorAbsent
            successfulOperatorParsed
      | expressionRejected rejectedOperatorSpan rejectedNamesParsed
            rejectedOperatorParsed valueRejected =>
          have afterNamesEq :=
            rejectedNamesParsed.output_unique successfulNamesParsed
          subst afterNamesEq
          have afterOperatorEq := exactToken_output_unique
            rejectedOperatorParsed successfulOperatorParsed
          subst afterOperatorEq
          exact
            yulExpressionPublicDeterministicOutcomeSpec.successRejectDisjoint
              valueRejected ⟨_, _, successfulValueParsed⟩

/-- Public assignment ordinary success and rejection form a deterministic
outcome contract. -/
theorem yulAssignmentDeterministicOutcomeSpec :
    DeterministicOutcomeSpec YulAssignmentOrdinaryParses
      (YulAssignmentRejects YulExpressionRejects) where
  successOutputUnique := YulAssignmentOrdinaryParses.output_unique
  successRejectDisjoint := YulAssignmentRejects.disjointOrdinary

/-- Every clean public assignment success is an ordinary public assignment
success with the same AST, span, name order, and remainder. -/
theorem YulAssignmentParses.toOrdinary
    {input output : Remainder} {statement : Syntax.YulStmt}
    (parsed : YulAssignmentParses YulExpressionParses input statement
      output) :
    YulAssignmentOrdinaryParses input statement output := by
  cases parsed with
  | parsed namesSpan operatorSpan namesParsed operatorParsed valueParsed =>
      exact .parsed operatorSpan namesParsed.toOrdinary operatorParsed
        valueParsed.toOrdinary

end Solcore.Syntax.DeclarativeGrammar
