import Solcore.Syntax.DeclarativeCoreExpressionConditionalExactnessProperties
import Solcore.Syntax.DeclarativeCoreExpressionLeftAssociativeExactnessProperties
import Solcore.Syntax.DeclarativeCoreExpressionNonAssociativeExactnessProperties

/-! Fully exact outcomes of the complete Core expression operator stack. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact nested and postfix expressions compose through every precedence,
retaining operator spans and the specified associativity. -/
theorem expressionLayerExactOutcomeSpec
    {nestedOrdinary postfixOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects postfixRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : ExactDeterministicOutcomeSpec nestedOrdinary nestedRejects)
    (postfixOutcomes : ExactDeterministicOutcomeSpec postfixOrdinary postfixRejects) :
    ExactDeterministicOutcomeSpec
      (ExpressionLayerOrdinaryParses nestedOrdinary postfixOrdinary)
      (ExpressionLayerRejects nestedOrdinary nestedRejects postfixOrdinary postfixRejects) := by
  let unaryOutcomes := expressionUnaryExactOutcomeSpec postfixOutcomes
  let multiplyOutcomes := leftAssociativeExactOutcomeSpec unaryOutcomes 8
  let addOutcomes := leftAssociativeExactOutcomeSpec multiplyOutcomes 7
  let bitAndOutcomes := leftAssociativeExactOutcomeSpec addOutcomes 6
  let bitXorOutcomes := leftAssociativeExactOutcomeSpec bitAndOutcomes 5
  let bitOrOutcomes := leftAssociativeExactOutcomeSpec bitXorOutcomes 4
  let relationalOutcomes := nonAssociativeExactOutcomeSpec bitOrOutcomes 3
  let equalityOutcomes := nonAssociativeExactOutcomeSpec relationalOutcomes 2
  let logicalAndOutcomes := leftAssociativeExactOutcomeSpec equalityOutcomes 1
  let logicalOrOutcomes := leftAssociativeExactOutcomeSpec logicalAndOutcomes 0
  exact conditionalExactOutcomeSpec nestedOutcomes logicalOrOutcomes

end Solcore.Syntax.DeclarativeGrammar
