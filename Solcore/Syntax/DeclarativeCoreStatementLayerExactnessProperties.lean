import Solcore.Syntax.DeclarativeCoreAssemblyStatementExactnessProperties
import Solcore.Syntax.DeclarativeCoreAssignmentStatementExactnessProperties
import Solcore.Syntax.DeclarativeCoreForStatementValueProperties
import Solcore.Syntax.DeclarativeCoreMatchStatementValueProperties
import Solcore.Syntax.DeclarativeCoreStatementBranchValueProperties
import Solcore.Syntax.DeclarativeCoreStatementControlLeafExactnessProperties
import Solcore.Syntax.DeclarativeCoreStatementLayerOutcomeProperties
import Solcore.Syntax.DeclarativeCoreStatementLayerSelectionExactnessProperties
import Solcore.Syntax.DeclarativeCoreStatementSimpleValueProperties

/-! Exact Core statement layers from exact recursive Core-term children. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Every recognized primary stage fixes its exact statement value from the
recursive child outcomes. Core types and inline Yul need no extra premises. -/
theorem StatementLayerPrimaryOrdinaryParses.value_unique
    {statementOrdinary : Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    {patternOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {patternRejects : Remainder → Remainder → Prop}
    (statementOutcomes : ExactDeterministicOutcomeSpec statementOrdinary
      statementRejects)
    (expressionOutcomes : ExactDeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    (patternOutcomes : ExactDeterministicOutcomeSpec patternOrdinary
      patternRejects)
    (stage : StatementLayerStage) (notFallback : stage ≠ .fallback)
    {input : Remainder} {left right : Syntax.Statement}
    {afterLeft afterRight : Remainder}
    (leftParsed : StatementLayerPrimaryOrdinaryParses statementOrdinary
      expressionOrdinary patternOrdinary stage input left afterLeft)
    (rightParsed : StatementLayerPrimaryOrdinaryParses statementOrdinary
      expressionOrdinary patternOrdinary stage input right afterRight) :
    left = right := by
  cases stage with
  | letGuard =>
      exact LetStatementOrdinaryParses.value_unique expressionOutcomes
        leftParsed rightParsed
  | returnGuard =>
      exact ReturnStatementOrdinaryParses.value_unique expressionOutcomes
        leftParsed rightParsed
  | matchGuard =>
      exact MatchStatementOrdinaryParses.value_unique statementOutcomes
        expressionOutcomes patternOutcomes leftParsed rightParsed
  | forGuard =>
      exact ForStatementOrdinaryParses.value_unique statementOutcomes
        expressionOutcomes leftParsed rightParsed
  | whileGuard =>
      exact WhileStatementOrdinaryParses.value_unique expressionOutcomes
        statementOutcomes leftParsed rightParsed
  | ifGuard =>
      exact IfStatementOrdinaryParses.value_unique expressionOutcomes
        statementOutcomes leftParsed rightParsed
  | assemblyGuard =>
      exact assemblyStatementExactOutcomeSpec.successValueUnique
        leftParsed rightParsed
  | blockGuard =>
      exact BlockStatementOrdinaryParses.value_unique statementOutcomes
        leftParsed rightParsed
  | breakGuard =>
      exact TerminatedControlStatementOrdinaryParses.value_unique
        leftParsed rightParsed
  | continueGuard =>
      exact TerminatedControlStatementOrdinaryParses.value_unique
        leftParsed rightParsed
  | fallback => contradiction

/-- Deterministic primaries, their exact successful values, and the exact
assignment fallback fix a complete prioritized statement layer, including
transactionally rewound rejection endpoints. -/
theorem statementLayerExactOutcomeSpec
    {statementOrdinary : Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    {patternOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {patternRejects : Remainder → Remainder → Prop}
    (statementOutcomes : ExactDeterministicOutcomeSpec statementOrdinary
      statementRejects)
    (expressionOutcomes : ExactDeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    (patternOutcomes : ExactDeterministicOutcomeSpec patternOrdinary
      patternRejects) :
    ExactDeterministicOutcomeSpec
      (StatementLayerOrdinaryParses statementOrdinary statementRejects
        expressionOrdinary expressionRejects patternOrdinary patternRejects)
      (StatementLayerRejects statementOrdinary statementRejects
        expressionOrdinary expressionRejects patternOrdinary patternRejects) :=
  statementLayerSelectionExactOutcomeSpecOfSuccess
    (StatementLayerPrimaryOrdinaryParses statementOrdinary expressionOrdinary
      patternOrdinary)
    (StatementLayerPrimaryRejects statementOrdinary statementRejects
      expressionOrdinary expressionRejects patternOrdinary patternRejects)
    (AssignmentOrExpressionStatementOrdinaryParses expressionOrdinary)
    (AssignmentOrExpressionStatementRejects expressionOrdinary
      expressionRejects)
    (statementLayerPrimaryDeterministicOutcomeSpec
      statementOutcomes.toDeterministicOutcomeSpec
      expressionOutcomes.toDeterministicOutcomeSpec
      patternOutcomes.toDeterministicOutcomeSpec)
    (StatementLayerPrimaryOrdinaryParses.value_unique statementOutcomes
      expressionOutcomes patternOutcomes)
    (assignmentOrExpressionStatementExactOutcomeSpec expressionOutcomes)

end Solcore.Syntax.DeclarativeGrammar
