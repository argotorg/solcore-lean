import Solcore.Syntax.Parser.Expression.PostfixTotalityProperties
import Solcore.Syntax.Parser.ExpressionProperties

/-! Compositional fuel-totality contract for postfix expressions. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionInternals

theorem expressionPostfix_fuelTotalityContract
    {statementValid : SourceFile → Statement → Prop}
    (nested : Parser Expr) (block : Parser Block) (nestedFuel : Nat)
    (nestedSyntax : ExpressionContract statementValid nested)
    (nestedTotality : FuelElementTotalityContract nested nestedFuel)
    (blockValid : block.ValidFor (Block.ValidFor statementValid))
    (blockWindow : Parser.PreservesTokenWindow block)
    (blockCursor : Parser.CursorMonotoneOnSuccess block)
    (blockStarts : Parser.StartsAtCurrentTokenOnSuccess block (·.span))
    (lambdaFree : Parser.InvariantFreeOnValid
      (ExpressionAtomInternals.lambdaExpression block)) :
    FuelElementTotalityContract
      (expressionPostfix nested block) (nestedFuel + 1) := by
  let atomSyntax := ExpressionContract.atom statementValid nested block
    nestedSyntax blockValid blockWindow blockCursor blockStarts
  let postfixSyntax := ExpressionContract.concretePostfix statementValid
    nested block nestedSyntax blockValid blockWindow blockCursor blockStarts
  exact {
    validFor := postfixSyntax.validFor.mono (fun _ _ _ => trivial)
    preservesTokenWindow := postfixSyntax.preservesTokenWindow
    cursorLtOnSuccess := postfixSyntax.cursorLtOnSuccess
    ordinary := fun input inputValid adequate =>
      ExpressionAtomInternals.expressionPostfix_ordinary_of_elementFuel
        nested block nestedFuel nestedTotality lambdaFree
          (atomSyntax.validFor.mono (fun _ _ _ => trivial))
            atomSyntax.preservesTokenWindow atomSyntax.cursorLtOnSuccess
              input inputValid adequate
  }

end Solcore.Syntax.Parser.ExpressionInternals
