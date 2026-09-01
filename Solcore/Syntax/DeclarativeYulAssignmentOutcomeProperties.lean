import Solcore.Syntax.DeclarativeYulAssignmentOutcomeGrammar
import Solcore.Syntax.DeclarativeYulNameOutcomeProperties

/-!
Disjointness of exact transactional Yul-assignment rejection and the strict
clean assignment grammar.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem absent_conflicts_exact {input output : Remainder}
    {kind : TokenKind} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

/-- An exact assignment rejection cannot overlap a clean assignment success
when clean expression successes embed into deterministic ordinary outcomes. -/
theorem YulAssignmentRejects.disjointClean
    (ordinaryExpression cleanExpression :
      Remainder → Syntax.YulExpr → Remainder → Prop)
    (expressionRejects : Remainder → Remainder → Prop)
    (outcomes : DeterministicOutcomeSpec ordinaryExpression
      expressionRejects)
    (cleanToOrdinary : ∀ {input value output},
      cleanExpression input value output →
        ordinaryExpression input value output)
    {input rejected : Remainder}
    (rejection : YulAssignmentRejects expressionRejects input rejected) :
    ¬ ∃ statement output,
      YulAssignmentParses cleanExpression input statement output := by
  rintro ⟨statement, output, successful⟩
  cases successful with
  | parsed namesSpan operatorSpan cleanNamesParsed cleanOperatorParsed
        cleanValueParsed =>
      have cleanNamesOrdinary := cleanNamesParsed.toOrdinary
      cases rejection with
      | namesRejected namesRejected =>
          exact namesRejected.disjoint
            ⟨{ span := namesSpan, names := _ }, _, cleanNamesOrdinary⟩
      | operatorAbsent rejectedNamesParsed operatorAbsent =>
          have afterNamesEq :=
            yulNamesDeterministicOutcomeSpec.successOutputUnique
              rejectedNamesParsed cleanNamesOrdinary
          subst afterNamesEq
          exact absent_conflicts_exact operatorAbsent cleanOperatorParsed
      | expressionRejected rejectedOperatorSpan rejectedNamesParsed
            rejectedOperatorParsed valueRejected =>
          have afterNamesEq :=
            yulNamesDeterministicOutcomeSpec.successOutputUnique
              rejectedNamesParsed cleanNamesOrdinary
          subst afterNamesEq
          exact outcomes.successRejectDisjoint valueRejected
            ⟨_, _, by
              simpa [rejectedOperatorParsed.2, cleanOperatorParsed.2] using
                cleanToOrdinary cleanValueParsed⟩

/-- Build the exact committed-assignment fallback from deterministic ordinary
expression outcomes. -/
def YulAssignmentFallbackSpec.ofOutcomes
    (ordinaryExpression cleanExpression :
      Remainder → Syntax.YulExpr → Remainder → Prop)
    (expressionRejects : Remainder → Remainder → Prop)
    (outcomes : DeterministicOutcomeSpec ordinaryExpression
      expressionRejects)
    (cleanToOrdinary : ∀ {input value output},
      cleanExpression input value output →
        ordinaryExpression input value output) :
    YulAssignmentFallbackSpec cleanExpression where
  rejects := YulAssignmentFallbackRejects expressionRejects
  disjoint := by
    intro input rejected
    rcases rejected with ⟨rejectedOutput, rejection⟩
    exact rejection.disjointClean ordinaryExpression cleanExpression
      expressionRejects outcomes cleanToOrdinary

end Solcore.Syntax.DeclarativeGrammar
