import Solcore.Syntax.Parser.ExpressionFuelContractProperties

/-! Fuel-totality for one complete expression precedence layer. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionInternals

/--
Lift a recursive expression contract through postfix, unary, all binary
precedence levels, and the conditional expression layer. The outer layer has
one more unit of fuel than its recursive expression operand.
-/
theorem expressionLayer_fuelTotalityContract
    {statementValid : SourceFile → Statement → Prop}
    (nested : Parser Expr) (block : Parser Block) (nestedFuel : Nat)
    (nestedSyntax : ExpressionContract statementValid nested)
    (postfixSyntax : ExpressionContract statementValid
      (expressionPostfix nested block))
    (nestedTotality : FuelElementTotalityContract nested nestedFuel)
    (postfixTotality : FuelElementTotalityContract
      (expressionPostfix nested block) (nestedFuel + 1)) :
    FuelElementTotalityContract
      (expressionLayer nested block) (nestedFuel + 1) := by
  have unarySyntax := ExpressionContract.unary statementValid nested block
    postfixSyntax
  have unaryTotality := expressionUnary_fuelTotalityContract nested block
    (nestedFuel + 1) postfixSyntax postfixTotality
  have multiplySyntax := ExpressionContract.leftAssociative unarySyntax 8
  have multiplyTotality := leftAssociative_fuelTotalityContract
    (expressionUnary nested block) (nestedFuel + 1) 8 unarySyntax
      unaryTotality
  have addSyntax := ExpressionContract.leftAssociative multiplySyntax 7
  have addTotality := leftAssociative_fuelTotalityContract
    (leftAssociative (expressionUnary nested block) 8) (nestedFuel + 1) 7
      multiplySyntax multiplyTotality
  have bitAndSyntax := ExpressionContract.leftAssociative addSyntax 6
  have bitAndTotality := leftAssociative_fuelTotalityContract
    (leftAssociative
      (leftAssociative (expressionUnary nested block) 8) 7)
      (nestedFuel + 1) 6 addSyntax addTotality
  have bitXorSyntax := ExpressionContract.leftAssociative bitAndSyntax 5
  have bitXorTotality := leftAssociative_fuelTotalityContract _
    (nestedFuel + 1) 5 bitAndSyntax bitAndTotality
  have bitOrSyntax := ExpressionContract.leftAssociative bitXorSyntax 4
  have bitOrTotality := leftAssociative_fuelTotalityContract _
    (nestedFuel + 1) 4 bitXorSyntax bitXorTotality
  have relationalSyntax := ExpressionContract.nonAssociative bitOrSyntax 3
  have relationalTotality := nonAssociative_fuelTotalityContract _
    (nestedFuel + 1) 3 bitOrSyntax bitOrTotality
  have equalitySyntax := ExpressionContract.nonAssociative relationalSyntax 2
  have equalityTotality := nonAssociative_fuelTotalityContract _
    (nestedFuel + 1) 2 relationalSyntax relationalTotality
  have logicalAndSyntax := ExpressionContract.leftAssociative equalitySyntax 1
  have logicalAndTotality := leftAssociative_fuelTotalityContract _
    (nestedFuel + 1) 1 equalitySyntax equalityTotality
  have logicalOrSyntax := ExpressionContract.leftAssociative logicalAndSyntax 0
  have logicalOrTotality := leftAssociative_fuelTotalityContract _
    (nestedFuel + 1) 0 logicalAndSyntax logicalAndTotality
  simpa only [expressionLayer] using
    conditional_fuelTotalityContract nested _ nestedFuel (nestedFuel + 1)
      nestedSyntax logicalOrSyntax nestedTotality logicalOrTotality (by omega)

end Solcore.Syntax.Parser.ExpressionInternals
