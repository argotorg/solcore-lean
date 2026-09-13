import Solcore.Frontend.StrictWordBinary

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
