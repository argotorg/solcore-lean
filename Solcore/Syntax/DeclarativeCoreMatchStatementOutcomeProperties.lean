import Solcore.Syntax.DeclarativeCoreMatchStatementRejectionProperties

/-! Deterministic diagnostic-inclusive outcomes for complete Core matches. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Lift recursive term outcomes through a complete Core `match`. -/
theorem matchStatementDeterministicOutcomeSpec
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
      (MatchStatementOrdinaryParses statementOrdinary expressionOrdinary
        patternOrdinary)
      (MatchStatementRejects statementOrdinary statementRejects
        expressionOrdinary expressionRejects patternOrdinary
          patternRejects) where
  successOutputUnique := MatchStatementOrdinaryParses.output_unique
    statementOutcomes expressionOutcomes patternOutcomes
  successRejectDisjoint := MatchStatementRejects.disjointOrdinary
    statementOutcomes expressionOutcomes patternOutcomes

end Solcore.Syntax.DeclarativeGrammar
