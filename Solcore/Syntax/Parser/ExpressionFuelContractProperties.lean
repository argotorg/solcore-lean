import Solcore.Syntax.Parser.ExpressionConditionalTotalityProperties
import Solcore.Syntax.Parser.ExpressionLeftAssociativeTotalityProperties
import Solcore.Syntax.Parser.ExpressionNonAssociativeTotalityProperties
import Solcore.Syntax.Parser.ExpressionUnaryLayerTotalityProperties

/-! Compositional fuel-totality lifts for expression parser layers. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionInternals

theorem leftAssociative_fuelTotalityContract
    {statementValid : SourceFile → Statement → Prop}
    (operand : Parser Expr) (fuel precedence : Nat)
    (syntaxContract : ExpressionContract statementValid operand)
    (totality : FuelElementTotalityContract operand fuel) :
    FuelElementTotalityContract (leftAssociative operand precedence) fuel := by
  let layer := ExpressionContract.leftAssociative syntaxContract precedence
  exact {
    validFor := layer.validFor.mono (fun _ _ _ => trivial)
    preservesTokenWindow := layer.preservesTokenWindow
    cursorLtOnSuccess := layer.cursorLtOnSuccess
    ordinary := fun input inputValid adequate =>
      leftAssociative_ordinary_of_elementFuel operand fuel precedence
        totality input inputValid adequate
  }

theorem nonAssociative_fuelTotalityContract
    {statementValid : SourceFile → Statement → Prop}
    (operand : Parser Expr) (fuel precedence : Nat)
    (syntaxContract : ExpressionContract statementValid operand)
    (totality : FuelElementTotalityContract operand fuel) :
    FuelElementTotalityContract (nonAssociative operand precedence) fuel := by
  let layer := ExpressionContract.nonAssociative syntaxContract precedence
  exact {
    validFor := layer.validFor.mono (fun _ _ _ => trivial)
    preservesTokenWindow := layer.preservesTokenWindow
    cursorLtOnSuccess := layer.cursorLtOnSuccess
    ordinary := fun input inputValid adequate =>
      nonAssociative_ordinary_of_elementFuel operand fuel precedence
        totality input inputValid adequate
  }

theorem expressionUnary_fuelTotalityContract
    {statementValid : SourceFile → Statement → Prop}
    (nested : Parser Expr) (block : Parser Block) (fuel : Nat)
    (postfixSyntax : ExpressionContract statementValid
      (expressionPostfix nested block))
    (postfixTotality : FuelElementTotalityContract
      (expressionPostfix nested block) fuel) :
    FuelElementTotalityContract (expressionUnary nested block) fuel := by
  let layer := ExpressionContract.unary statementValid nested block
    postfixSyntax
  exact {
    validFor := layer.validFor.mono (fun _ _ _ => trivial)
    preservesTokenWindow := layer.preservesTokenWindow
    cursorLtOnSuccess := layer.cursorLtOnSuccess
    ordinary := fun input inputValid adequate =>
      expressionUnary_ordinary_of_postfixFuel nested block fuel
        postfixTotality input inputValid adequate
  }

/--
The conditional layer uses the alternative's outer fuel. The supplied bound
ensures that consuming `?` places every recursive expression below its fuel.
-/
theorem conditional_fuelTotalityContract
    {statementValid : SourceFile → Statement → Prop}
    (nested alternative : Parser Expr)
    (nestedFuel outerFuel : Nat)
    (nestedSyntax : ExpressionContract statementValid nested)
    (alternativeSyntax : ExpressionContract statementValid alternative)
    (nestedTotality : FuelElementTotalityContract nested nestedFuel)
    (alternativeTotality :
      FuelElementTotalityContract alternative outerFuel)
    (fuelBound : outerFuel ≤ nestedFuel + 1) :
    FuelElementTotalityContract
      (conditional nested alternative) outerFuel := by
  let layer := ExpressionContract.conditional nestedSyntax alternativeSyntax
  exact {
    validFor := layer.validFor.mono (fun _ _ _ => trivial)
    preservesTokenWindow := layer.preservesTokenWindow
    cursorLtOnSuccess := layer.cursorLtOnSuccess
    ordinary := fun input inputValid adequate =>
      conditional_ordinary_of_elementFuels nested alternative nestedFuel
        outerFuel nestedTotality alternativeTotality input inputValid
          (by omega) adequate
  }

end Solcore.Syntax.Parser.ExpressionInternals
