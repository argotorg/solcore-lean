import Solcore.Syntax.Operator
import Solcore.Core.Primitive

/- Independent meanings of all fourteen strict source Word binary operators.
Both arguments are actual Words; comparison results are Boolean values.
The two short-circuit operators are excluded. Division and remainder at zero
retain the existing total unsigned Word conventions. -/
set_option autoImplicit false
namespace Solcore.Frontend

inductive StrictWordBinaryDenotes :
    Syntax.BinaryOp → Core.Word → Core.Word → Core.Value → Prop where
  | add {left right : Core.Word} :
      StrictWordBinaryDenotes .add left right (.word (left.add right))
  | subtract {left right : Core.Word} :
      StrictWordBinaryDenotes .subtract left right (.word (left.sub right))
  | multiply {left right : Core.Word} :
      StrictWordBinaryDenotes .multiply left right (.word (left.mul right))
  | divide {left right : Core.Word} :
      StrictWordBinaryDenotes .divide left right (.word (left.udiv right))
  | modulo {left right : Core.Word} :
      StrictWordBinaryDenotes .modulo left right (.word (left.umod right))
  | bitAnd {left right : Core.Word} :
      StrictWordBinaryDenotes .bitAnd left right (.word (left.bitAnd right))
  | bitOr {left right : Core.Word} :
      StrictWordBinaryDenotes .bitOr left right (.word (left.bitOr right))
  | bitXor {left right : Core.Word} :
      StrictWordBinaryDenotes .bitXor left right (.word (left.bitXor right))
  | greater {left right : Core.Word} :
      StrictWordBinaryDenotes .greater left right (.bool (decide (left > right)))
  | less {left right : Core.Word} :
      StrictWordBinaryDenotes .less left right (.bool (decide (left < right)))
  | equal {left right : Core.Word} :
      StrictWordBinaryDenotes .equal left right (.bool (left == right))
  | notEqual {left right : Core.Word} :
      StrictWordBinaryDenotes .notEqual left right (.bool (!(left == right)))
  | lessEqual {left right : Core.Word} :
      StrictWordBinaryDenotes .lessEqual left right (.bool (!(decide (left > right))))
  | greaterEqual {left right : Core.Word} :
      StrictWordBinaryDenotes .greaterEqual left right (.bool (!(decide (left < right))))

def evaluateStrictWordBinary? (operator : Syntax.BinaryOp) (left right : Core.Word) :
    Option Core.Value :=
  match operator with
  | .add => some (.word (left.add right))
  | .subtract => some (.word (left.sub right))
  | .multiply => some (.word (left.mul right))
  | .divide => some (.word (left.udiv right))
  | .modulo => some (.word (left.umod right))
  | .bitAnd => some (.word (left.bitAnd right))
  | .bitOr => some (.word (left.bitOr right))
  | .bitXor => some (.word (left.bitXor right))
  | .greater => some (.bool (decide (left > right)))
  | .less => some (.bool (decide (left < right)))
  | .equal => some (.bool (left == right))
  | .notEqual => some (.bool (!(left == right)))
  | .lessEqual => some (.bool (!(decide (left > right))))
  | .greaterEqual => some (.bool (!(decide (left < right))))
  | .logicalAnd | .logicalOr => none

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.StrictWordBinaryProperties`
-/

/- Exact successful results and operator support of the independent Word relation. -/
set_option autoImplicit false
namespace Solcore.Frontend

theorem evaluateStrictWordBinary?_iff
    {operator : Syntax.BinaryOp} {left right : Core.Word} {value : Core.Value} :
    evaluateStrictWordBinary? operator left right = some value ↔
      StrictWordBinaryDenotes operator left right value := by
  constructor
  · intro accepted
    cases operator <;>
      simp only [evaluateStrictWordBinary?, Option.some.injEq, reduceCtorEq] at accepted
    all_goals subst value; constructor
  · intro meaning
    cases meaning <;> rfl

theorem StrictWordBinaryDenotes.value_unique
    {operator : Syntax.BinaryOp} {left right : Core.Word} {first second : Core.Value}
    (firstMeaning : StrictWordBinaryDenotes operator left right first)
    (secondMeaning : StrictWordBinaryDenotes operator left right second) :
    first = second := by
  cases firstMeaning <;> cases secondMeaning <;> rfl

theorem StrictWordBinaryDenotes.operator_is_strict
    {operator : Syntax.BinaryOp} {left right : Core.Word} {value : Core.Value}
    (meaning : StrictWordBinaryDenotes operator left right value) :
    operator ≠ .logicalAnd ∧ operator ≠ .logicalOr := by
  cases meaning <;> constructor <;> intro impossible <;> cases impossible

theorem evaluateStrictWordBinary?_isSome_iff
    (operator : Syntax.BinaryOp) (left right : Core.Word) :
    (evaluateStrictWordBinary? operator left right).isSome = true ↔
      operator ≠ .logicalAnd ∧ operator ≠ .logicalOr := by
  cases operator <;> simp [evaluateStrictWordBinary?]

end Solcore.Frontend
