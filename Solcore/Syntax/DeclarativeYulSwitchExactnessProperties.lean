import Solcore.Syntax.DeclarativeYulBlockExactnessProperties
import Solcore.Syntax.DeclarativeYulExpressionExactnessProperties
import Solcore.Syntax.DeclarativeYulSwitchOutcomeProperties

/-! Exact case order, optional default spans, and complete Yul switch ASTs. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact recursive blocks fix each complete switch case arm and remainder. -/
theorem YulCaseArmParses.result_unique
    {statementOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec statementOrdinary statementRejects)
    {input : Remainder} {left right : Syntax.YulCase}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulCaseArmOrdinaryParses statementOrdinary input left afterLeft)
    (rightParsed : YulCaseArmOrdinaryParses statementOrdinary input right afterRight) :
    left = right ∧ afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftSpan leftBodySpan leftMarker leftLiteral leftBody =>
      cases rightParsed with
      | parsed rightSpan rightBodySpan rightMarker rightLiteral rightBody =>
          rcases leftMarker.result_unique rightMarker with ⟨spanEq, outputEq⟩
          subst spanEq
          subst outputEq
          rcases leftLiteral.result_unique rightLiteral with ⟨literalEq, literalOutputEq⟩
          subst literalEq
          subst literalOutputEq
          rcases leftBody.result_unique outcomes rightBody with ⟨bodySpanEq, bodyEq, finalEq⟩
          subst bodySpanEq
          subst bodyEq
          exact ⟨rfl, finalEq⟩

/-- A maximal case list fixes its full source-order arm list and remainder. -/
theorem YulCaseListParses.result_unique
    {statementOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec statementOrdinary statementRejects)
    {input : Remainder} {left right : List Syntax.YulCase}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulCaseListOrdinaryParses statementOrdinary input left afterLeft)
    (rightParsed : YulCaseListOrdinaryParses statementOrdinary input right afterRight) :
    left = right ∧ afterLeft = afterRight := by
  induction leftParsed generalizing right afterRight with
  | done leftAbsent =>
      cases rightParsed with
      | done => exact ⟨rfl, rfl⟩
      | next rightArm _ _ => exact False.elim (leftAbsent rightArm.startsAt)
  | next leftArm leftProgress leftTail ih =>
      cases rightParsed with
      | done rightAbsent => exact False.elim (rightAbsent leftArm.startsAt)
      | next rightArm _ rightTail =>
          rcases leftArm.result_unique outcomes rightArm with ⟨armEq, outputEq⟩
          subst armEq
          subst outputEq
          rcases ih rightTail with ⟨tailEq, finalEq⟩
          subst tailEq
          exact ⟨rfl, finalEq⟩

/-- Default priority fixes its aligned optional span/body pair and remainder. -/
theorem OptionalYulDefaultParses.result_unique
    {statementOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec statementOrdinary statementRejects)
    {input : Remainder} {leftSpan rightSpan : Option SourceSpan}
    {leftBody rightBody : Option (List Syntax.YulStmt)}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalYulDefaultOrdinaryParses statementOrdinary input
      leftSpan leftBody afterLeft)
    (rightParsed : OptionalYulDefaultOrdinaryParses statementOrdinary input
      rightSpan rightBody afterRight) :
    leftSpan = rightSpan ∧ leftBody = rightBody ∧ afterLeft = afterRight := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent => exact ⟨rfl, rfl, rfl⟩
      | present _ _ rightMarker _ => exact False.elim (leftAbsent ⟨_, rightMarker.1⟩)
  | present leftMarkerSpan leftBodySpan leftMarker leftBody =>
      cases rightParsed with
      | absent rightAbsent => exact False.elim (rightAbsent ⟨_, leftMarker.1⟩)
      | present rightMarkerSpan rightBodySpan rightMarker rightBody =>
          have outputEq := leftMarker.output_unique rightMarker
          subst outputEq
          rcases leftBody.result_unique outcomes rightBody with ⟨spanEq, bodyEq, finalEq⟩
          subst spanEq
          subst bodyEq
          exact ⟨rfl, rfl, finalEq⟩

/-- Ordinary switches fix both normal switch ASTs and diagnosed empty-case ASTs. -/
theorem YulSwitchStatementOrdinaryParses.value_unique
    {statementOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec statementOrdinary statementRejects)
    {input : Remainder} {left right : Syntax.YulStmt}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulSwitchStatementOrdinaryParses statementOrdinary input left afterLeft)
    (rightParsed : YulSwitchStatementOrdinaryParses statementOrdinary input right afterRight) :
    left = right := by
  cases leftParsed <;> cases rightParsed <;>
    grind (ematch := 15) [ExactTokenParses.result_unique,
      YulExpressionOrdinaryParses.result_unique,
      YulCaseListParses.result_unique outcomes,
      OptionalYulDefaultParses.result_unique outcomes]

end Solcore.Syntax.DeclarativeGrammar
