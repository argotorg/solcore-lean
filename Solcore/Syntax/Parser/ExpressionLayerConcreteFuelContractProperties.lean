import Solcore.Syntax.Parser.Expression.LambdaTotalityProperties
import Solcore.Syntax.Parser.Expression.PostfixFuelContractProperties
import Solcore.Syntax.Parser.ExpressionLayerFuelContractProperties

/-! Concrete fuel-totality bridge for one complete expression layer. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionInternals

/--
Build the concrete postfix syntax and lambda totality internally, then lift
them through the complete precedence layer with one extra unit of fuel.
-/
theorem expressionLayer_concrete_fuelTotalityContract
    {statementValid : SourceFile → Statement → Prop}
    (nested : Parser Expr) (block : Parser Block) (nestedFuel : Nat)
    (nestedSyntax : ExpressionContract statementValid nested)
    (nestedTotality : FuelElementTotalityContract nested nestedFuel)
    (blockValid : block.ValidFor (Block.ValidFor statementValid))
    (blockWindow : Parser.PreservesTokenWindow block)
    (blockCursor : Parser.CursorMonotoneOnSuccess block)
    (blockStarts : Parser.StartsAtCurrentTokenOnSuccess block (·.span))
    (blockFree : Parser.InvariantFreeOnValid block) :
    FuelElementTotalityContract
      (expressionLayer nested block) (nestedFuel + 1) := by
  let lambdaFree :=
    ExpressionAtomInternals.lambdaExpression_invariantFreeOnValid block
      (blockValid.mono (fun _ _ _ => trivial)) blockFree
  let postfixSyntax := ExpressionContract.concretePostfix statementValid
    nested block nestedSyntax blockValid blockWindow blockCursor blockStarts
  let postfixTotality := expressionPostfix_fuelTotalityContract
    nested block nestedFuel nestedSyntax nestedTotality blockValid blockWindow
      blockCursor blockStarts lambdaFree
  exact expressionLayer_fuelTotalityContract nested block nestedFuel
    nestedSyntax postfixSyntax nestedTotality postfixTotality

end Solcore.Syntax.Parser.ExpressionInternals
