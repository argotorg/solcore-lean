import Solcore.Syntax.DeclarativeCoreTermLevelOutcomeProperties

/-! Equations for the parser-independent mutually recursive Core fuel levels. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

@[simp] theorem CoreExpressionOrdinaryParsesWithFuel.zero
    {input output : Remainder} {expression : Syntax.Expr} :
    ¬ CoreExpressionOrdinaryParsesWithFuel 0 input expression output := by
  simp [CoreExpressionOrdinaryParsesWithFuel, CoreTermLevel.empty,
    CoreExpressionLevel.empty]

@[simp] theorem CoreExpressionRejectsWithFuel.zero
    {input rejected : Remainder} :
    ¬ CoreExpressionRejectsWithFuel 0 input rejected := by
  simp [CoreExpressionRejectsWithFuel, CoreTermLevel.empty,
    CoreExpressionLevel.empty]

@[simp] theorem CorePatternOrdinaryParsesWithFuel.zero
    {input output : Remainder} {pattern : Syntax.Pattern} :
    ¬ CorePatternOrdinaryParsesWithFuel 0 input pattern output := by
  simp [CorePatternOrdinaryParsesWithFuel, CoreTermLevel.empty,
    CorePatternLevel.empty]

@[simp] theorem CorePatternRejectsWithFuel.zero
    {input rejected : Remainder} :
    ¬ CorePatternRejectsWithFuel 0 input rejected := by
  simp [CorePatternRejectsWithFuel, CoreTermLevel.empty,
    CorePatternLevel.empty]

@[simp] theorem CoreStatementOrdinaryParsesWithFuel.zero
    {input output : Remainder} {statement : Syntax.Statement} :
    ¬ CoreStatementOrdinaryParsesWithFuel 0 input statement output := by
  simp [CoreStatementOrdinaryParsesWithFuel, CoreTermLevel.empty,
    CoreStatementLevel.empty]

@[simp] theorem CoreStatementRejectsWithFuel.zero
    {input rejected : Remainder} :
    ¬ CoreStatementRejectsWithFuel 0 input rejected := by
  simp [CoreStatementRejectsWithFuel, CoreTermLevel.empty,
    CoreStatementLevel.empty]

@[simp] theorem CoreExpressionOrdinaryParsesWithFuel.succ_iff
    {fuel : Nat} {input output : Remainder} {expression : Syntax.Expr} :
    CoreExpressionOrdinaryParsesWithFuel (fuel + 1) input expression output ↔
      CoreExpressionStepOrdinaryParses
        (coreExpressionStepRelationsWithFuel fuel) input expression output := by
  simp only [CoreExpressionOrdinaryParsesWithFuel,
    CoreStatementOrdinaryParsesWithFuel, CoreStatementRejectsWithFuel,
    coreExpressionStepRelationsWithFuel, CoreTermLevel.atFuel,
    CoreTermLevel.next, CoreExpressionLevel.next]

@[simp] theorem CoreExpressionRejectsWithFuel.succ_iff
    {fuel : Nat} {input rejected : Remainder} :
    CoreExpressionRejectsWithFuel (fuel + 1) input rejected ↔
      CoreExpressionStepRejects
        (coreExpressionStepRelationsWithFuel fuel) input rejected := by
  simp only [CoreExpressionRejectsWithFuel,
    CoreStatementOrdinaryParsesWithFuel, CoreStatementRejectsWithFuel,
    coreExpressionStepRelationsWithFuel, CoreTermLevel.atFuel,
    CoreTermLevel.next, CoreExpressionLevel.next]

@[simp] theorem CorePatternOrdinaryParsesWithFuel.succ_iff
    {fuel : Nat} {input output : Remainder} {pattern : Syntax.Pattern} :
    CorePatternOrdinaryParsesWithFuel (fuel + 1) input pattern output ↔
      CorePatternStepOrdinaryParses
        (corePatternStepRelationsWithFuel fuel) input pattern output := by
  simp only [CorePatternOrdinaryParsesWithFuel,
    CoreExpressionOrdinaryParsesWithFuel, CoreExpressionRejectsWithFuel,
    corePatternStepRelationsWithFuel, CoreTermLevel.atFuel,
    CoreTermLevel.next, CorePatternLevel.next]

@[simp] theorem CorePatternRejectsWithFuel.succ_iff
    {fuel : Nat} {input rejected : Remainder} :
    CorePatternRejectsWithFuel (fuel + 1) input rejected ↔
      CorePatternStepRejects
        (corePatternStepRelationsWithFuel fuel) input rejected := by
  simp only [CorePatternRejectsWithFuel,
    CoreExpressionOrdinaryParsesWithFuel, CoreExpressionRejectsWithFuel,
    corePatternStepRelationsWithFuel, CoreTermLevel.atFuel,
    CoreTermLevel.next, CorePatternLevel.next]

@[simp] theorem CoreStatementOrdinaryParsesWithFuel.succ_iff
    {fuel : Nat} {input output : Remainder} {statement : Syntax.Statement} :
    CoreStatementOrdinaryParsesWithFuel (fuel + 1) input statement output ↔
      StatementLayerOrdinaryParses
        (CoreStatementOrdinaryParsesWithFuel fuel)
        (CoreStatementRejectsWithFuel fuel)
        (CoreExpressionOrdinaryParsesWithFuel fuel)
        (CoreExpressionRejectsWithFuel fuel)
        (CorePatternOrdinaryParsesWithFuel fuel)
        (CorePatternRejectsWithFuel fuel) input statement output := by
  simp only [CoreStatementOrdinaryParsesWithFuel,
    CoreStatementRejectsWithFuel, CoreExpressionOrdinaryParsesWithFuel,
    CoreExpressionRejectsWithFuel, CorePatternOrdinaryParsesWithFuel,
    CorePatternRejectsWithFuel, CoreTermLevel.atFuel, CoreTermLevel.next,
    CoreStatementLevel.next]

@[simp] theorem CoreStatementRejectsWithFuel.succ_iff
    {fuel : Nat} {input rejected : Remainder} :
    CoreStatementRejectsWithFuel (fuel + 1) input rejected ↔
      StatementLayerRejects
        (CoreStatementOrdinaryParsesWithFuel fuel)
        (CoreStatementRejectsWithFuel fuel)
        (CoreExpressionOrdinaryParsesWithFuel fuel)
        (CoreExpressionRejectsWithFuel fuel)
        (CorePatternOrdinaryParsesWithFuel fuel)
        (CorePatternRejectsWithFuel fuel) input rejected := by
  simp only [CoreStatementOrdinaryParsesWithFuel,
    CoreStatementRejectsWithFuel, CoreExpressionOrdinaryParsesWithFuel,
    CoreExpressionRejectsWithFuel, CorePatternOrdinaryParsesWithFuel,
    CorePatternRejectsWithFuel, CoreTermLevel.atFuel, CoreTermLevel.next,
    CoreStatementLevel.next]

end Solcore.Syntax.DeclarativeGrammar
