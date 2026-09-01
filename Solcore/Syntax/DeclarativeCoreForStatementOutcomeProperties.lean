import Solcore.Syntax.DeclarativeCoreForStatementRejectionOutcomeProperties

/-! Deterministic ordinary outcomes for complete Core `for` statements. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Lift recursive statement and expression outcomes through Core `for`. -/
theorem forStatementDeterministicOutcomeSpec
    {statementOrdinary : Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects)
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects) :
    DeterministicOutcomeSpec
      (ForStatementOrdinaryParses statementOrdinary expressionOrdinary)
      (ForStatementRejects statementOrdinary statementRejects
        expressionOrdinary expressionRejects) where
  successOutputUnique := ForStatementOrdinaryParses.output_unique
    statementOutcomes expressionOutcomes
  successRejectDisjoint := ForStatementRejects.disjointOrdinary
    statementOutcomes expressionOutcomes

end Solcore.Syntax.DeclarativeGrammar
