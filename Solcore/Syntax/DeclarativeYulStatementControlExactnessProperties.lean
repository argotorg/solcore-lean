import Solcore.Syntax.DeclarativeYulBlockExactnessProperties
import Solcore.Syntax.DeclarativeYulExpressionExactnessProperties
import Solcore.Syntax.DeclarativeYulStatementControlOutcomeProperties

/-! Exact ASTs of recursive inline-Yul conditional and loop statements. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact recursive blocks and public expressions fix an entire Yul if AST. -/
theorem YulIfStatementOrdinaryParses.value_unique
    {statementOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec statementOrdinary statementRejects)
    {input : Remainder} {left right : Syntax.YulStmt}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulIfStatementOrdinaryParses statementOrdinary input left afterLeft)
    (rightParsed : YulIfStatementOrdinaryParses statementOrdinary input right afterRight) :
    left = right := by
  cases leftParsed with
  | parsed leftSpan leftMarker leftCondition leftBody =>
      cases rightParsed with
      | parsed rightSpan rightMarker rightCondition rightBody =>
          rcases leftMarker.result_unique rightMarker with ⟨spanEq, outputEq⟩
          subst spanEq
          subst outputEq
          rcases leftCondition.result_unique rightCondition with ⟨conditionEq, conditionOutputEq⟩
          subst conditionEq
          subst conditionOutputEq
          rcases leftBody.result_unique outcomes rightBody with ⟨bodySpanEq, bodyEq, finalEq⟩
          subst bodySpanEq
          subst bodyEq
          rfl

/-- Exact recursive blocks fix all three source-order loop bodies and its span. -/
theorem YulForStatementOrdinaryParses.value_unique
    {statementOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec statementOrdinary statementRejects)
    {input : Remainder} {left right : Syntax.YulStmt}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulForStatementOrdinaryParses statementOrdinary input left afterLeft)
    (rightParsed : YulForStatementOrdinaryParses statementOrdinary input right afterRight) :
    left = right := by
  cases leftParsed with
  | parsed leftSpan leftMarker leftInitializer leftCondition leftPost leftBody =>
      cases rightParsed with
      | parsed rightSpan rightMarker rightInitializer rightCondition rightPost rightBody =>
          rcases leftMarker.result_unique rightMarker with ⟨spanEq, outputEq⟩
          subst spanEq
          subst outputEq
          rcases leftInitializer.result_unique outcomes rightInitializer with
            ⟨initializerSpanEq, initializerEq, initializerOutputEq⟩
          subst initializerEq
          subst initializerOutputEq
          rcases leftCondition.result_unique rightCondition with ⟨conditionEq, conditionOutputEq⟩
          subst conditionEq
          subst conditionOutputEq
          rcases leftPost.result_unique outcomes rightPost with ⟨postSpanEq, postEq, postOutputEq⟩
          subst postEq
          subst postOutputEq
          rcases leftBody.result_unique outcomes rightBody with ⟨bodySpanEq, bodyEq, finalEq⟩
          subst bodySpanEq
          subst bodyEq
          rfl

end Solcore.Syntax.DeclarativeGrammar
