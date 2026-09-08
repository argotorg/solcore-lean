import Solcore.Frontend.LocalExpressionCost

/-! Source-computable upper bounds on the restricted fragment's Core transition
costs. Numerical bounds neither check expressions nor guarantee evaluation;
unsupported syntax receives zero, and successful cost evidence stays explicit. -/

set_option autoImplicit false

namespace Solcore.Frontend

/-- A conservative, value-independent Core fuel budget. Literal spelling length
and source grouping contribute no Core transitions. The maximum with one pays
for the generated Boolean constant on a short-circuit path, even when the
unselected source expression is unsupported and has bound zero. -/
def localExpressionFuelBound (source : Syntax.Expr) : Nat :=
  match source with
  | ⟨_, .identifier _⟩ => 1
  | ⟨_, .literal _⟩ => 1
  | ⟨_, .group inner⟩ => localExpressionFuelBound inner
  | ⟨_, .unary ⟨_, .logicalNot⟩ operand⟩ => localExpressionFuelBound operand + 2
  | ⟨_, .unary ⟨_, .bitNot⟩ operand⟩ => localExpressionFuelBound operand + 2
  | ⟨_, .binary left ⟨_, .add⟩ right⟩ =>
      localExpressionFuelBound left + localExpressionFuelBound right + 3
  | ⟨_, .binary left ⟨_, .subtract⟩ right⟩ =>
      localExpressionFuelBound left + localExpressionFuelBound right + 3
  | ⟨_, .binary left ⟨_, .multiply⟩ right⟩ =>
      localExpressionFuelBound left + localExpressionFuelBound right + 3
  | ⟨_, .binary left ⟨_, .greater⟩ right⟩ =>
      localExpressionFuelBound left + localExpressionFuelBound right + 3
  | ⟨_, .binary left ⟨_, .less⟩ right⟩ =>
      localExpressionFuelBound left + localExpressionFuelBound right + 9
  | ⟨_, .binary left ⟨_, .equal⟩ right⟩ =>
      localExpressionFuelBound left + localExpressionFuelBound right + 3
  | ⟨_, .binary left ⟨_, .notEqual⟩ right⟩ =>
      localExpressionFuelBound left + localExpressionFuelBound right + 5
  | ⟨_, .binary left ⟨_, .lessEqual⟩ right⟩ =>
      localExpressionFuelBound left + localExpressionFuelBound right + 5
  | ⟨_, .binary left ⟨_, .greaterEqual⟩ right⟩ =>
      localExpressionFuelBound left + localExpressionFuelBound right + 11
  | ⟨_, .binary left ⟨_, .bitAnd⟩ right⟩ =>
      localExpressionFuelBound left + localExpressionFuelBound right + 3
  | ⟨_, .binary left ⟨_, .bitOr⟩ right⟩ =>
      localExpressionFuelBound left + localExpressionFuelBound right + 3
  | ⟨_, .binary left ⟨_, .bitXor⟩ right⟩ =>
      localExpressionFuelBound left + localExpressionFuelBound right + 3
  | ⟨_, .binary left ⟨_, .logicalAnd⟩ right⟩ =>
      localExpressionFuelBound left + max 1 (localExpressionFuelBound right) + 2
  | ⟨_, .binary left ⟨_, .logicalOr⟩ right⟩ =>
      localExpressionFuelBound left + max 1 (localExpressionFuelBound right) + 2
  | ⟨_, .conditional condition _ thenBranch _ elseBranch⟩ =>
      localExpressionFuelBound condition +
        max (localExpressionFuelBound thenBranch) (localExpressionFuelBound elseBranch) + 2
  | _ => 0
termination_by sizeOf source

/-- Every successful independent source cost is bounded, without assumptions
on whole resolution, typing, allocation, or an unselected branch. This is an
upper bound, not an assertion that the same budget is necessary for every value. -/
theorem LocalExpressionEvaluatesWithCost.cost_le_fuelBound
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {source : Syntax.Expr} {value : Core.Value} {cost : Nat}
    (evaluation : LocalExpressionEvaluatesWithCost table environment
      initialStore source value finalStore cost) :
    cost ≤ localExpressionFuelBound source := by
  induction evaluation with
  | identifier named found => simp only [localExpressionFuelBound, Nat.le_refl]
  | wordLiteral meaning => simp only [localExpressionFuelBound, Nat.le_refl]
  | group _ ih => simpa only [localExpressionFuelBound] using ih
  | logicalNot _ ih => simp only [localExpressionFuelBound]; omega
  | bitNot _ ih => simp only [localExpressionFuelBound]; omega
  | add _ _ leftIH rightIH => simp only [localExpressionFuelBound]; omega
  | subtract _ _ leftIH rightIH => simp only [localExpressionFuelBound]; omega
  | multiply _ _ leftIH rightIH => simp only [localExpressionFuelBound]; omega
  | bitAnd _ _ leftIH rightIH => simp only [localExpressionFuelBound]; omega
  | bitOr _ _ leftIH rightIH => simp only [localExpressionFuelBound]; omega
  | bitXor _ _ leftIH rightIH => simp only [localExpressionFuelBound]; omega
  | greater _ _ leftIH rightIH => simp only [localExpressionFuelBound]; omega
  | less _ _ leftIH rightIH => simp only [localExpressionFuelBound]; omega
  | equal _ _ leftIH rightIH => simp only [localExpressionFuelBound]; omega
  | notEqual _ _ leftIH rightIH => simp only [localExpressionFuelBound]; omega
  | lessEqual _ _ leftIH rightIH => simp only [localExpressionFuelBound]; omega
  | greaterEqual _ _ leftIH rightIH => simp only [localExpressionFuelBound]; omega
  | andTrue _ _ leftIH rightIH => simp only [localExpressionFuelBound]; omega
  | andFalse _ ih => simp only [localExpressionFuelBound]; omega
  | orTrue _ ih => simp only [localExpressionFuelBound]; omega
  | orFalse _ _ leftIH rightIH => simp only [localExpressionFuelBound]; omega
  | ifTrue _ _ conditionIH branchIH => simp only [localExpressionFuelBound]; omega
  | ifFalse _ _ conditionIH branchIH => simp only [localExpressionFuelBound]; omega

end Solcore.Frontend
