import Solcore.Frontend.WordLessCostStepComposition
import Solcore.Core.LocalFragment

/-! Ordered comparison costs from the two original operand paths. Exact
insertion discharges the weakened-right premise without restricting left
effects, adding runtime typing assumptions, or changing the outer continuation. -/

set_option autoImplicit false

namespace Solcore.Frontend.CostStepComposition

open Core

theorem wordLt_of_local_right
    {environment : Environment} {initialStore middleStore finalStore : Store}
    {left right : Expr} {leftWord rightWord : Word} {leftCost rightCost : Nat}
    (leftPath : ∀ continuation, Steps leftCost
      ⟨.eval left environment, continuation, initialStore⟩
      ⟨.ret (.word leftWord), continuation, middleStore⟩)
    (rightPath : ∀ continuation, Steps rightCost
      ⟨.eval right environment, continuation, middleStore⟩
      ⟨.ret (.word rightWord), continuation, finalStore⟩)
    (rightFragment : right.LocalFragment) (continuation : List Frame) :
    Steps (leftCost + rightCost + 9)
      ⟨.eval (left.wordLt right) environment, continuation, initialStore⟩
      ⟨.ret (.bool (decide (leftWord < rightWord))), continuation, finalStore⟩ :=
  wordLt leftPath
    (fun outer => (rightPath []).weakenAt_zero_localFragment rightFragment (.word leftWord) outer)
    continuation

end Solcore.Frontend.CostStepComposition
