import Solcore.Syntax.DeclarativePrimitiveExactnessProperties
import Solcore.Syntax.DeclarativeYulBlockStatementOutcomeProperties

/-! Exact spans, source-order bodies, and rejection endpoints of Yul blocks. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

/-- Exact statements fix every block-item span, forward body, and remainder. -/
theorem YulBlockItemsParses.result_unique
    {statementOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec statementOrdinary statementRejects)
    {openingSpan : SourceSpan} {input : Remainder}
    {leftSpan rightSpan : SourceSpan} {leftBody rightBody : List Syntax.YulStmt}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulBlockItemsParses statementOrdinary openingSpan input
      leftSpan leftBody afterLeft)
    (rightParsed : YulBlockItemsParses statementOrdinary openingSpan input
      rightSpan rightBody afterRight) :
    leftSpan = rightSpan ∧ leftBody = rightBody ∧ afterLeft = afterRight := by
  induction leftParsed generalizing rightSpan rightBody afterRight with
  | close leftClosing leftToken =>
      cases rightParsed with
      | close rightClosing rightToken =>
          rcases leftToken.result_unique rightToken with ⟨spanEq, outputEq⟩
          subst spanEq
          exact ⟨rfl, rfl, outputEq⟩
      | next _ rightAbsent _ _ _ =>
          exact False.elim (absent_conflicts_exact rightAbsent leftToken)
  | next leftNotAtEnd leftAbsent leftStatement leftProgress leftTail ih =>
      cases rightParsed with
      | close _ rightToken =>
          exact False.elim (absent_conflicts_exact leftAbsent rightToken)
      | next _ _ rightStatement _ rightTail =>
          rcases outcomes.successResultUnique leftStatement rightStatement with
            ⟨statementEq, outputEq⟩
          subst statementEq
          subst outputEq
          rcases ih rightTail with ⟨spanEq, bodyEq, finalEq⟩
          subst bodyEq
          exact ⟨spanEq, rfl, finalEq⟩

/-- A complete Yul block fixes its covering span, forward body, and remainder. -/
theorem YulBlockParses.result_unique
    {statementOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec statementOrdinary statementRejects)
    {input : Remainder} {leftSpan rightSpan : SourceSpan}
    {leftBody rightBody : List Syntax.YulStmt}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulBlockOrdinaryParses statementOrdinary input leftSpan
      leftBody afterLeft)
    (rightParsed : YulBlockOrdinaryParses statementOrdinary input rightSpan
      rightBody afterRight) :
    leftSpan = rightSpan ∧ leftBody = rightBody ∧ afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftOpening leftToken leftItems =>
      cases rightParsed with
      | parsed rightOpening rightToken rightItems =>
          rcases leftToken.result_unique rightToken with ⟨spanEq, outputEq⟩
          subst spanEq
          subst outputEq
          exact leftItems.result_unique outcomes rightItems

/-- Exact statements fix the first rejecting block-item endpoint. -/
theorem YulBlockItemsRejects.output_unique
    {statementOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec statementOrdinary statementRejects)
    {input left right : Remainder}
    (leftRejected : YulBlockItemsRejects statementOrdinary statementRejects input left)
    (rightRejected : YulBlockItemsRejects statementOrdinary statementRejects input right) :
    left = right := by
  induction leftRejected generalizing right with
  | missingClose leftAbsent leftAtEnd =>
      cases rightRejected with
      | missingClose => rfl
      | statementRejected rightNotAtEnd _ _
      | laterRejected rightNotAtEnd _ _ _ _ =>
          exact False.elim ((Nat.not_lt_of_ge leftAtEnd) rightNotAtEnd)
  | statementRejected leftNotAtEnd leftAbsent leftStatementRejected =>
      cases rightRejected with
      | missingClose _ rightAtEnd =>
          exact False.elim ((Nat.not_lt_of_ge rightAtEnd) leftNotAtEnd)
      | statementRejected _ _ rightStatementRejected =>
          exact outcomes.rejectOutputUnique leftStatementRejected rightStatementRejected
      | laterRejected _ _ rightStatement _ _ =>
          exact False.elim
            (outcomes.successRejectDisjoint leftStatementRejected ⟨_, _, rightStatement⟩)
  | laterRejected leftNotAtEnd leftAbsent leftStatement leftProgress leftTail ih =>
      cases rightRejected with
      | missingClose _ rightAtEnd =>
          exact False.elim ((Nat.not_lt_of_ge rightAtEnd) leftNotAtEnd)
      | statementRejected _ _ rightStatementRejected =>
          exact False.elim
            (outcomes.successRejectDisjoint rightStatementRejected ⟨_, _, leftStatement⟩)
      | laterRejected _ _ rightStatement _ rightTail =>
          have outputEq := outcomes.successOutputUnique leftStatement rightStatement
          subst outputEq
          exact ih rightTail

/-- Exact statements fix the rejecting endpoint of a complete Yul block. -/
theorem YulBlockRejects.output_unique
    {statementOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec statementOrdinary statementRejects)
    {input left right : Remainder}
    (leftRejected : YulBlockRejects statementOrdinary statementRejects input left)
    (rightRejected : YulBlockRejects statementOrdinary statementRejects input right) :
    left = right := by
  cases leftRejected with
  | openingMissing leftAbsent =>
      cases rightRejected with
      | openingMissing => rfl
      | itemsRejected _ rightOpening _ =>
          exact False.elim (absent_conflicts_exact leftAbsent rightOpening)
  | itemsRejected _ leftOpening leftItems =>
      cases rightRejected with
      | openingMissing rightAbsent =>
          exact False.elim (absent_conflicts_exact rightAbsent leftOpening)
      | itemsRejected _ rightOpening rightItems =>
          have outputEq := leftOpening.output_unique rightOpening
          subst outputEq
          exact leftItems.output_unique outcomes rightItems

/-- Exact statements lift to fully exact block outcomes. -/
theorem yulBlockExactOutcomeSpec
    {statementOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec statementOrdinary statementRejects) :
    ExactDeterministicOutcomeSpec (YulBlockOutcomeParses statementOrdinary)
      (YulBlockRejects statementOrdinary statementRejects) where
  toDeterministicOutcomeSpec := yulBlockDeterministicOutcomeSpec outcomes.toDeterministicOutcomeSpec
  successValueUnique := by
    intro input left right afterLeft afterRight leftParsed rightParsed
    rcases YulBlockParses.result_unique outcomes leftParsed rightParsed with
      ⟨spanEq, bodyEq, outputEq⟩
    cases left
    cases right
    simp_all
  rejectOutputUnique := YulBlockRejects.output_unique outcomes

/-- Lifting a block to statement position preserves the exact AST. -/
theorem YulBlockStatementOrdinaryParses.value_unique
    {statementOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec statementOrdinary statementRejects)
    {input : Remainder} {left right : Syntax.YulStmt}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulBlockStatementOrdinaryParses statementOrdinary input left afterLeft)
    (rightParsed : YulBlockStatementOrdinaryParses statementOrdinary input right afterRight) :
    left = right := by
  cases leftParsed with
  | parsed leftBlock =>
      cases rightParsed with
      | parsed rightBlock =>
          rcases leftBlock.result_unique outcomes rightBlock with ⟨spanEq, bodyEq, outputEq⟩
          subst spanEq
          subst bodyEq
          rfl

end Solcore.Syntax.DeclarativeGrammar
