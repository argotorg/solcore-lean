import Solcore.Syntax.DeclarativeCoreExpressionAtomCoreRejectionProperties

/-! Deterministic outcome contract for the ordered Core atom dispatcher. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Lift deterministic nested expression, lambda-parameter, type, and block
outcomes through all seven ordered Core atom branches and final rejection. -/
theorem expressionAtomCoreDeterministicOutcomeSpec
    {nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    {parameterOrdinary :
      Remainder → Syntax.LambdaParameter → Remainder → Prop}
    {parameterRejects : Remainder → Remainder → Prop}
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    {blockOrdinary : Remainder → Syntax.Block → Remainder → Prop}
    {blockRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : DeterministicOutcomeSpec nestedOrdinary nestedRejects)
    (parameterOutcomes : DeterministicOutcomeSpec parameterOrdinary
      parameterRejects)
    (typeOutcomes : DeterministicOutcomeSpec typeOrdinary typeRejects)
    (blockOutcomes : DeterministicOutcomeSpec blockOrdinary blockRejects) :
    DeterministicOutcomeSpec
      (ExpressionAtomCoreOrdinaryParses nestedOrdinary parameterOrdinary
        typeOrdinary blockOrdinary)
      (ExpressionAtomCoreRejects nestedOrdinary nestedRejects
        parameterOrdinary parameterRejects typeOrdinary typeRejects
          blockRejects) where
  successOutputUnique := ExpressionAtomCoreOrdinaryParses.output_unique
    nestedOutcomes parameterOutcomes typeOutcomes blockOutcomes
  successRejectDisjoint := ExpressionAtomCoreRejects.disjointOrdinary
    nestedOutcomes parameterOutcomes typeOutcomes blockOutcomes

end Solcore.Syntax.DeclarativeGrammar
