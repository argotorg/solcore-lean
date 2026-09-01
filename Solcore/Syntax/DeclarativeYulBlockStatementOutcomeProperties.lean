import Solcore.Syntax.DeclarativeYulBlockOutcomeProperties
import Solcore.Syntax.DeclarativeYulStatementControlGrammar

/-! Ordinary outcomes for lifting one parsed Yul block into statement form. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary block-statement success uses ordinary statements recursively. -/
abbrev YulBlockStatementOrdinaryParses
    (statementOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop) :=
  YulBlockStatementParses statementOrdinary

/-- Block-statement rejection is exactly rejection of its underlying block. -/
abbrev YulBlockStatementRejects
    (statementOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop)
    (statementRejects : Remainder → Remainder → Prop) :=
  YulBlockRejects statementOrdinary statementRejects

/-- Ordinary block-statement success has functional output. -/
theorem YulBlockStatementOrdinaryParses.output_unique
    {statementOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec statementOrdinary statementRejects)
    {input : Remainder} {left right : Syntax.YulStmt}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulBlockStatementOrdinaryParses statementOrdinary input left
      afterLeft)
    (rightParsed : YulBlockStatementOrdinaryParses statementOrdinary input right
      afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftBlock =>
      cases rightParsed with
      | parsed rightBlock => exact leftBlock.output_unique outcomes rightBlock

/-- Underlying block rejection excludes every ordinary block statement. -/
theorem YulBlockStatementRejects.disjointOrdinary
    {statementOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec statementOrdinary statementRejects)
    {input rejected : Remainder}
    (rejection : YulBlockStatementRejects statementOrdinary statementRejects
      input rejected) :
    ¬ ∃ statement output,
      YulBlockStatementOrdinaryParses statementOrdinary input statement
        output := by
  rintro ⟨statement, output, parsed⟩
  cases parsed with
  | parsed blockParsed =>
      apply YulBlockRejects.disjointOrdinary outcomes rejection
      exact ⟨_, _, output, blockParsed⟩

/-- Construct the lifted block-statement outcome contract. -/
theorem yulBlockStatementDeterministicOutcomeSpec
    {statementOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec statementOrdinary statementRejects) :
    DeterministicOutcomeSpec
      (YulBlockStatementOrdinaryParses statementOrdinary)
      (YulBlockStatementRejects statementOrdinary statementRejects) where
  successOutputUnique :=
    YulBlockStatementOrdinaryParses.output_unique outcomes
  successRejectDisjoint :=
    YulBlockStatementRejects.disjointOrdinary outcomes

/-- Clean block statements embed into ordinary block statements unchanged. -/
theorem YulBlockStatementParses.toOrdinary
    {statementClean statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop}
    (cleanToOrdinary : ∀ {input statement output},
      statementClean input statement output →
        statementOrdinary input statement output)
    {input output : Remainder} {statement : Syntax.YulStmt}
    (parsed : YulBlockStatementParses statementClean input statement output) :
    YulBlockStatementOrdinaryParses statementOrdinary input statement
      output := by
  cases parsed with
  | parsed blockParsed => exact .parsed (blockParsed.toOrdinary cleanToOrdinary)

end Solcore.Syntax.DeclarativeGrammar
