import Solcore.Syntax.DeclarativeTransactionalFallbackOutcomeProperties
import Solcore.Syntax.DeclarativeYulAssignmentOrdinaryOutcomeProperties
import Solcore.Syntax.DeclarativeYulAssignmentPublicFallbackProperties
import Solcore.Syntax.DeclarativeYulStatementBasicOutcomeProperties
import Solcore.Syntax.DeclarativeYulStatementCoreGrammar

/-!
Parser-independent ordinary outcomes for the name-start branch of the Yul
statement dispatcher.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary success of the transactional assignment-or-expression choice. -/
abbrev YulNameStatementOrdinaryParses :=
  TransactionalFallbackOrdinaryParses
    YulAssignmentOrdinaryParses
    (YulAssignmentRejects YulExpressionRejects)
    YulExpressionStatementOrdinaryParses

/-- Exact nonconsuming rejection when both name-start alternatives reject. -/
abbrev YulNameStatementRejects :=
  TransactionalFallbackRejects
    (YulAssignmentRejects YulExpressionRejects)
    YulExpressionStatementRejects

/-- Name-start ordinary outcomes inherit determinism from assignment and
expression-statement outcomes. -/
theorem yulNameStatementDeterministicOutcomeSpec :
    DeterministicOutcomeSpec YulNameStatementOrdinaryParses
      YulNameStatementRejects :=
  transactionalFallbackDeterministicOutcomeSpec
    YulAssignmentOrdinaryParses YulExpressionStatementOrdinaryParses
    (YulAssignmentRejects YulExpressionRejects)
    YulExpressionStatementRejects
    yulAssignmentDeterministicOutcomeSpec
    yulExpressionStatementDeterministicOutcomeSpec

/-- The clean name-choice grammar embeds into the public ordinary outcome
without changing the selected AST or remainder. -/
theorem YulNameStatementChoiceParses.toOrdinary
    {input output : Remainder} {statement : Syntax.YulStmt}
    (parsed : YulNameStatementChoiceParses YulExpressionParses
      yulAssignmentPublicFallbackSpec input statement output) :
    YulNameStatementOrdinaryParses input statement output := by
  cases parsed with
  | assignment nameStart assignmentParsed =>
      exact .primary assignmentParsed.toOrdinary
  | rewound nameStart assignmentRejected expressionParsed =>
      rw [yulAssignmentPublicFallbackSpec_rejects_iff]
        at assignmentRejected
      rcases assignmentRejected with ⟨rejected, rejection⟩
      exact .fallback rejection expressionParsed.toOrdinary

end Solcore.Syntax.DeclarativeGrammar
