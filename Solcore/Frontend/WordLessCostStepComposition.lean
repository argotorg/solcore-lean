import Solcore.Frontend.LocalExpressionCostStepComposition
import Solcore.Core.Derived

/-! Exact ordered paths for existing Core lets and the derived less-than tree.
The weakened right path is an explicit premise, not a general weakening claim. -/

set_option autoImplicit false

namespace Solcore.Frontend.CostStepComposition

open Core

theorem letE {environment : Environment} {initialStore middleStore finalStore : Store}
    {value body : Expr} {boundValue result : Value} {continuation : List Frame}
    {valueCost bodyCost : Nat}
    (valuePath : Steps valueCost
      ⟨.eval value environment, .letBody body environment :: continuation, initialStore⟩
      ⟨.ret boundValue, .letBody body environment :: continuation, middleStore⟩)
    (bodyPath : Steps bodyCost
      ⟨.eval body (boundValue :: environment), continuation, middleStore⟩
      ⟨.ret result, continuation, finalStore⟩) :
    Steps (valueCost + bodyCost + 2)
      ⟨.eval (.letE value body) environment, continuation, initialStore⟩
      ⟨.ret result, continuation, finalStore⟩ := by
  have path := Steps.cons .enterLet (valuePath.trans (.cons .bindLet bodyPath))
  simpa only [Nat.add_assoc] using path

/-- The original left expression runs first. The supplied right path explicitly
uses its weakened Core under the retained left value. The generated comparison
then reads right at zero and left at one without re-evaluating either operand. -/
theorem wordLt {environment : Environment} {initialStore middleStore finalStore : Store}
    {left right : Expr} {leftWord rightWord : Word} {leftCost rightCost : Nat}
    (leftPath : ∀ continuation, Steps leftCost
      ⟨.eval left environment, continuation, initialStore⟩
      ⟨.ret (.word leftWord), continuation, middleStore⟩)
    (rightPath : ∀ continuation, Steps rightCost
      ⟨.eval (right.weakenAt 0) (.word leftWord :: environment), continuation, middleStore⟩
      ⟨.ret (.word rightWord), continuation, finalStore⟩)
    (continuation : List Frame) :
    Steps (leftCost + rightCost + 9)
      ⟨.eval (left.wordLt right) environment, continuation, initialStore⟩
      ⟨.ret (.bool (decide (leftWord < rightWord))), continuation, finalStore⟩ := by
  have compared : Steps 5
      ⟨.eval (.binary .wordGt (.var 0) (.var 1))
        (.word rightWord :: .word leftWord :: environment), continuation, finalStore⟩
      ⟨.ret (.bool (decide (leftWord < rightWord))), continuation, finalStore⟩ :=
    binary (.cons (.var rfl) .refl) (.cons (.var rfl) .refl) rfl
  have inner := letE (rightPath _) compared
  have outer := letE (leftPath _) inner
  simpa only [Expr.wordLt_expansion, Nat.add_assoc] using outer

end Solcore.Frontend.CostStepComposition
