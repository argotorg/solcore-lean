import Solcore.Frontend.StrictWordBinary
import Solcore.Frontend.LocalExpressionCostExecutionProperties

/- Independent source cost for fourteen strict Word meanings. The two child
costs and all three stores are supplied separately; no closed runner, typing,
data-image bridge or whole-environment well-formedness is used. -/
set_option autoImplicit false
namespace Tests.ClosedStrictWordBinaryCost
open Solcore Solcore.Frontend

private def overhead : Syntax.BinaryOp → Nat
  | .notEqual | .lessEqual => 5
  | .less => 9
  | .greaterEqual => 11
  | _ => 3

private theorem costed {names environment initialStore middleStore finalStore}
    {span operatorSpan : Syntax.SourceSpan} {operator : Syntax.BinaryOp}
    {left right : Syntax.Expr} {a b : Core.Word} {value : Core.Value} {kl kr : Nat}
    (meaning : StrictWordBinaryDenotes operator a b value)
    (l : LocalExpressionEvaluatesWithCost names environment initialStore left (.word a) middleStore kl)
    (r : LocalExpressionEvaluatesWithCost names environment middleStore right (.word b) finalStore kr) :
    LocalExpressionEvaluatesWithCost names environment initialStore
      ⟨span,.binary left ⟨operatorSpan,operator⟩ right⟩ value finalStore (kl+kr+overhead operator) := by
  cases meaning with
  | add => exact .add l r
  | subtract => exact .subtract l r
  | multiply => exact .multiply l r
  | divide => exact .divide l r
  | modulo => exact .modulo l r
  | bitAnd => exact .bitAnd l r
  | bitOr => exact .bitOr l r
  | bitXor => exact .bitXor l r
  | greater => exact .greater l r
  | less => exact .less l r
  | equal => exact .equal l r
  | notEqual => exact .notEqual l r
  | lessEqual => exact .lessEqual l r
  | greaterEqual => exact .greaterEqual l r

/-- The direct ten add three transitions, != and <= add five, < adds nine,
and >= adds eleven. These are Core transitions, not source derivation depth.
Original independent costs precede any resolution/lowering or machine path. -/
theorem original_cost_and_machine_steps {names environment initialStore middleStore finalStore}
    {span operatorSpan : Syntax.SourceSpan} {operator : Syntax.BinaryOp}
    {left right : Syntax.Expr} {a b : Core.Word} {value : Core.Value} {kl kr : Nat}
    (meaning : StrictWordBinaryDenotes operator a b value)
    (l : LocalExpressionEvaluatesWithCost names environment initialStore left (.word a) middleStore kl)
    (r : LocalExpressionEvaluatesWithCost names environment middleStore right (.word b) finalStore kr) :
    LocalExpressionEvaluatesWithCost names environment initialStore
      ⟨span,.binary left ⟨operatorSpan,operator⟩ right⟩ value finalStore (kl+kr+overhead operator) ∧
    ∀ {resolved core},
      ResolvesLocalExpression names ⟨span,.binary left ⟨operatorSpan,operator⟩ right⟩ resolved →
      Resolved.Lowers (Resolved.LocalScope.ids environment) resolved core →
      (∀ continuation, Core.Steps (kl+kr+overhead operator)
        ⟨.eval core (Resolved.LocalScope.values environment),continuation,initialStore⟩
        ⟨.ret value,continuation,finalStore⟩) ∧
      ∀ fuel, Core.runStateful fuel
        (Core.State.initial core (Resolved.LocalScope.values environment) initialStore) =
          .done value finalStore ↔ kl+kr+overhead operator ≤ fuel := by
  have original := costed (span:=span) (operatorSpan:=operatorSpan) meaning l r
  refine ⟨original,?_⟩
  intro resolved core resolution lowering
  exact ⟨original.toStepsWithContinuation resolution lowering,
    fun _ => original.runStateful_done_iff resolution lowering⟩

end Tests.ClosedStrictWordBinaryCost
