import Solcore.Syntax.Parser.PatternCoreStrictProperties

/-! A reusable fuel contract for canonical pattern-layer dispatch. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PatternInternals

/-- Existing branchwise syntax validity projects to the weak loop boundary. -/
theorem patternCore_weakValidFor
    (nested : Parser Pattern) (expression : Parser Expr)
    (expressionValid : SourceFile → Expr → Prop)
    (nestedValid : nested.ValidFor (Pattern.ValidFor expressionValid))
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested)
    (expressionValidFor : expression.ValidFor expressionValid)
    (spanValid : ∀ {file : SourceFile} {value : Expr},
      expressionValid file value → value.span.ValidFor file)
    (expressionStarts :
      Parser.StartsAtCurrentTokenOnSuccess expression (·.span)) :
    (patternCore nested expression).ValidFor (fun _ _ => True) :=
  (patternCore_validFor nested expression expressionValid nestedValid
    nestedPreserves expressionValidFor spanValid expressionStarts).mono
      (fun _ _ _ => trivial)

/--
The smaller of the two one-step recursive budgets is the single generic fuel
accepted by `FuelElementTotalityContract`.
-/
theorem patternCore_fuelElementTotalityContract
    (nested : Parser Pattern) (expression : Parser Expr)
    (nestedFuel expressionFuel : Nat)
    (nestedContract : FuelElementTotalityContract nested nestedFuel)
    (expressionContract :
      FuelElementTotalityContract expression expressionFuel)
    (expressionValid : SourceFile → Expr → Prop)
    (nestedValid : nested.ValidFor (Pattern.ValidFor expressionValid))
    (expressionValidFor : expression.ValidFor expressionValid)
    (spanValid : ∀ {file : SourceFile} {value : Expr},
      expressionValid file value → value.span.ValidFor file)
    (expressionStarts :
      Parser.StartsAtCurrentTokenOnSuccess expression (·.span)) :
    FuelElementTotalityContract (patternCore nested expression)
      (Nat.min (nestedFuel + 1) (expressionFuel + 1)) := {
  validFor := patternCore_weakValidFor nested expression expressionValid
    nestedValid nestedContract.preservesTokenWindow.preservesTokensOnSuccess
    expressionValidFor spanValid expressionStarts
  preservesTokenWindow := patternCore_preservesTokenWindow nested expression
    nestedContract.preservesTokenWindow expressionContract.preservesTokenWindow
  cursorLtOnSuccess := patternCore_cursor_lt_onSuccess nested expression
    (fun input value next result =>
      Nat.le_of_lt (nestedContract.cursorLtOnSuccess result))
    (fun input value next result =>
      Nat.le_of_lt (expressionContract.cursorLtOnSuccess result))
  ordinary := by
    intro input inputValid adequate
    apply patternCore_ordinary_of_elementFuel nested expression nestedFuel
      expressionFuel nestedContract expressionContract input inputValid
    · exact Nat.lt_of_lt_of_le adequate
        (Nat.min_le_left (nestedFuel + 1) (expressionFuel + 1))
    · exact Nat.lt_of_lt_of_le adequate
        (Nat.min_le_right (nestedFuel + 1) (expressionFuel + 1))
}

end Solcore.Syntax.Parser.PatternInternals
