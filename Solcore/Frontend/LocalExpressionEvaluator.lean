import Solcore.Frontend.LocalReference
import Solcore.Frontend.WordLiteral
import Solcore.Resolved.Eval

/-! Direct execution of the existing raw source fragment, without resolution,
typing, lowering or Core execution. Output costs count existing Core transitions,
not source traversal. A successful selected path does not imply whole checking. -/
set_option autoImplicit false
namespace Solcore.Frontend

/-- Strict Word results and their existing lowering overhead. Short-circuit
operators have no strict Word meaning at this boundary. -/
def evaluateLocalWordBinaryWithCost? (operator : Syntax.BinaryOp) (left right : Core.Word) :
    Option (Core.Value × Nat) :=
  match operator with
  | .add => some (.word (left.add right), 3)
  | .subtract => some (.word (left.sub right), 3)
  | .multiply => some (.word (left.mul right), 3)
  | .divide => some (.word (left.udiv right), 3)
  | .modulo => some (.word (left.umod right), 3)
  | .bitAnd => some (.word (left.bitAnd right), 3)
  | .bitOr => some (.word (left.bitOr right), 3)
  | .bitXor => some (.word (left.bitXor right), 3)
  | .greater => some (.bool (decide (left > right)), 3)
  | .less => some (.bool (decide (left < right)), 9)
  | .equal => some (.bool (left == right), 3)
  | .notEqual => some (.bool (!(left == right)), 5)
  | .lessEqual => some (.bool (!(decide (left > right))), 5)
  | .greaterEqual => some (.bool (!(decide (left < right))), 11)
  | .logicalAnd | .logicalOr => none

/-- First-match actual lookup, strict primitive/binary tuple shapes and selected-only control
flow. No store, type context, alignment, uniqueness or spelling validity is needed.
`none` denotes raw evaluation absence, not source-language invalidity. -/
def evaluateLocalExpressionWithCost? (table : LocalNameTable) (environment : Resolved.Environment)
    (source : Syntax.Expr) : Option (Core.Value × Nat) :=
  match source with
  | ⟨_, .identifier name⟩ => do
      let id ← table.lookup? name.value
      let value ← environment.lookup? id
      return (value, 1)
  | ⟨_, .literal literal⟩ => do
      return (.word (← interpretWordLiteral? literal), 1)
  | ⟨_, .group inner⟩ => evaluateLocalExpressionWithCost? table environment inner
  | ⟨_, .tuple ⟨_, [left, right]⟩⟩ => do
      let (leftValue, leftCost) ← evaluateLocalExpressionWithCost? table environment left
      let (rightValue, rightCost) ← evaluateLocalExpressionWithCost? table environment right
      return (.pair leftValue rightValue, leftCost + rightCost + 3)
  | ⟨_, .unary ⟨_, .logicalNot⟩ operand⟩ => do
      let (.bool value, cost) ← evaluateLocalExpressionWithCost? table environment operand | none
      return (.bool (!value), cost + 2)
  | ⟨_, .unary ⟨_, .bitNot⟩ operand⟩ => do
      let (.word value, cost) ← evaluateLocalExpressionWithCost? table environment operand | none
      return (.word value.bitNot, cost + 2)
  | ⟨_, .binary left ⟨_, .logicalAnd⟩ right⟩ => do
      let (.bool choice, leftCost) ← evaluateLocalExpressionWithCost? table environment left | none
      if choice then
        let (value, rightCost) ← evaluateLocalExpressionWithCost? table environment right
        return (value, leftCost + rightCost + 2)
      else return (.bool false, leftCost + 3)
  | ⟨_, .binary left ⟨_, .logicalOr⟩ right⟩ => do
      let (.bool choice, leftCost) ← evaluateLocalExpressionWithCost? table environment left | none
      if choice then return (.bool true, leftCost + 3)
      else
        let (value, rightCost) ← evaluateLocalExpressionWithCost? table environment right
        return (value, leftCost + rightCost + 2)
  | ⟨_, .binary left ⟨_, operator⟩ right⟩ => do
      let (.word l, leftCost) ← evaluateLocalExpressionWithCost? table environment left | none
      let (.word r, rightCost) ← evaluateLocalExpressionWithCost? table environment right | none
      let (value, overhead) ← evaluateLocalWordBinaryWithCost? operator l r
      return (value, leftCost + rightCost + overhead)
  | ⟨_, .conditional condition _ thenBranch _ elseBranch⟩ => do
      let (.bool choice, conditionCost) ← evaluateLocalExpressionWithCost? table environment condition | none
      let (value, branchCost) ← if choice then evaluateLocalExpressionWithCost? table environment thenBranch
        else evaluateLocalExpressionWithCost? table environment elseBranch
      return (value, conditionCost + branchCost + 2)
  | _ => none
termination_by sizeOf source

end Solcore.Frontend
