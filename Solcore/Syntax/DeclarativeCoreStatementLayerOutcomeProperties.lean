import Solcore.Syntax.DeclarativeCoreAssemblyStatementOutcomeProperties
import Solcore.Syntax.DeclarativeCoreAssignmentStatementOutcomeProperties
import Solcore.Syntax.DeclarativeCoreForStatementOutcomeProperties
import Solcore.Syntax.DeclarativeCoreMatchStatementOutcomeProperties
import Solcore.Syntax.DeclarativeCoreStatementControlLeafOutcomeProperties
import Solcore.Syntax.DeclarativeCoreStatementIfOutcomeProperties
import Solcore.Syntax.DeclarativeCoreStatementLayerOutcomeGrammar
import Solcore.Syntax.DeclarativeCoreStatementSimpleCompleteOutcomeProperties
import Solcore.Syntax.DeclarativeCoreStatementWhileOutcomeProperties

/-! Deterministic concrete outcomes for one ordered Core statement layer. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Each recognized stage inherits the deterministic contract of its concrete
Core statement parser. -/
theorem statementLayerPrimaryDeterministicOutcomeSpec
    {statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    {patternOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {patternRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects)
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    (patternOutcomes : DeterministicOutcomeSpec patternOrdinary
      patternRejects)
    (stage : StatementLayerStage) (notFallback : stage ≠ .fallback) :
    DeterministicOutcomeSpec
      (StatementLayerPrimaryOrdinaryParses statementOrdinary
        expressionOrdinary patternOrdinary stage)
      (StatementLayerPrimaryRejects statementOrdinary statementRejects
        expressionOrdinary expressionRejects patternOrdinary patternRejects
          stage) := by
  cases stage with
  | letGuard =>
      exact letStatementDeterministicOutcomeSpec expressionOutcomes
        typeExprDeterministicOutcomeSpec
  | returnGuard =>
      exact returnStatementDeterministicOutcomeSpec expressionOutcomes
  | matchGuard =>
      exact matchStatementDeterministicOutcomeSpec statementOutcomes
        expressionOutcomes patternOutcomes
  | forGuard =>
      exact forStatementDeterministicOutcomeSpec statementOutcomes
        expressionOutcomes
  | whileGuard =>
      exact whileStatementDeterministicOutcomeSpec expressionOutcomes
        statementOutcomes
  | ifGuard =>
      exact ifStatementDeterministicOutcomeSpec expressionOutcomes
        statementOutcomes
  | assemblyGuard => exact assemblyStatementDeterministicOutcomeSpec
  | blockGuard =>
      exact blockStatementDeterministicOutcomeSpec statementOutcomes
  | breakGuard =>
      exact terminatedControlStatementDeterministicOutcomeSpec .breakKw
        .breakStmt
  | continueGuard =>
      exact terminatedControlStatementDeterministicOutcomeSpec .continueKw
        .continueStmt
  | fallback => contradiction

/-- Recursive statement, expression, and pattern outcomes lift through the
complete let-prioritized Core statement dispatcher. -/
theorem statementLayerDeterministicOutcomeSpec
    {statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    {patternOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {patternRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects)
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    (patternOutcomes : DeterministicOutcomeSpec patternOrdinary
      patternRejects) :
    DeterministicOutcomeSpec
      (StatementLayerOrdinaryParses statementOrdinary statementRejects
        expressionOrdinary expressionRejects patternOrdinary patternRejects)
      (StatementLayerRejects statementOrdinary statementRejects
        expressionOrdinary expressionRejects patternOrdinary
          patternRejects) :=
  statementLayerSelectionDeterministicOutcomeSpec
    (StatementLayerPrimaryOrdinaryParses statementOrdinary expressionOrdinary
      patternOrdinary)
    (StatementLayerPrimaryRejects statementOrdinary statementRejects
      expressionOrdinary expressionRejects patternOrdinary patternRejects)
    (AssignmentOrExpressionStatementOrdinaryParses expressionOrdinary)
    (AssignmentOrExpressionStatementRejects expressionOrdinary
      expressionRejects)
    (statementLayerPrimaryDeterministicOutcomeSpec statementOutcomes
      expressionOutcomes patternOutcomes)
    (assignmentOrExpressionStatementDeterministicOutcomeSpec
      expressionOutcomes)

end Solcore.Syntax.DeclarativeGrammar
