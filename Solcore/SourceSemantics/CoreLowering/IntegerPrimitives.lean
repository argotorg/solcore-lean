import Solcore.Core.IntegerPrimitives
import Solcore.Core.Eval
import Solcore.SourceSemantics.Dynamic.Primitive

/-! Native mathematical-integer helper definitions implement the independent
source primitive relations, including all signs and the zero-divisor cases. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.IntegerPrimitives

open Solcore.SourceSemantics.Dynamic

theorem divide_source (left right : Int) :
    BinaryPrimitiveApplies .divide (.integer left) (.integer right)
      (.integer (Core.Integer.divide left right)) := by
  by_cases zero : right = 0
  · subst right
    simpa only [Core.Integer.divide_zero] using BinaryPrimitiveApplies.integerDivideZero left
  · simpa only [Core.Integer.divide_nonzero left right zero] using
      BinaryPrimitiveApplies.integerDivide left right zero

theorem modulo_source (left right : Int) :
    BinaryPrimitiveApplies .modulo (.integer left) (.integer right)
      (.integer (Core.Integer.modulo left right)) := by
  by_cases zero : right = 0
  · subst right
    simpa only [Core.Integer.modulo_zero] using BinaryPrimitiveApplies.integerModuloZero left
  · simpa only [Core.Integer.modulo_nonzero left right zero] using
      BinaryPrimitiveApplies.integerModulo left right zero

theorem bitAnd_eq_source (left right : Int) :
    Core.Integer.bitAnd left right = Dynamic.integerBitAnd left right := by
  cases left <;> cases right <;> rfl

theorem bitOr_eq_source (left right : Int) :
    Core.Integer.bitOr left right = Dynamic.integerBitOr left right := by
  cases left <;> cases right <;> rfl

theorem bitXor_eq_source (left right : Int) :
    Core.Integer.bitXor left right = Dynamic.integerBitXor left right := by
  cases left <;> cases right <;> rfl

theorem bitAnd_source (left right : Int) :
    BinaryPrimitiveApplies .bitAnd (.integer left) (.integer right)
      (.integer (Core.Integer.bitAnd left right)) := by
  rw [bitAnd_eq_source]
  exact .integerBitAnd left right

theorem bitOr_source (left right : Int) :
    BinaryPrimitiveApplies .bitOr (.integer left) (.integer right)
      (.integer (Core.Integer.bitOr left right)) := by
  rw [bitOr_eq_source]
  exact .integerBitOr left right

theorem bitXor_source (left right : Int) :
    BinaryPrimitiveApplies .bitXor (.integer left) (.integer right)
      (.integer (Core.Integer.bitXor left right)) := by
  rw [bitXor_eq_source]
  exact .integerBitXor left right

/-- Only mathematical scalar results cross this primitive correspondence. -/
inductive ResultRepresents : Dynamic.Value → Core.Value → Prop where
  | integer (value : Int) : ResultRepresents (.integer value) (.integer value)
  | word (value : Core.Word) : ResultRepresents (.word value) (.word value)
  | bool (value : Bool) : ResultRepresents (.bool value) (.bool value)

inductive BinaryOperation : Core.BinaryOp → Syntax.BinaryOp → Prop where
  | add : BinaryOperation .integerAdd .add
  | subtract : BinaryOperation .integerSub .subtract
  | multiply : BinaryOperation .integerMul .multiply
  | divide : BinaryOperation .integerDiv .divide
  | modulo : BinaryOperation .integerMod .modulo
  | bitAnd : BinaryOperation .integerAnd .bitAnd
  | bitOr : BinaryOperation .integerOr .bitOr
  | bitXor : BinaryOperation .integerXor .bitXor
  | equal : BinaryOperation .integerEq .equal
  | less : BinaryOperation .integerLt .less

private theorem equal_source (left right : Int) :
    BinaryPrimitiveApplies .equal (.integer left) (.integer right)
      (.bool (left == right)) := by
  by_cases same : left = right
  · subst right
    simpa using BinaryPrimitiveApplies.equalTrue
      (ValueEquivalent.refl (ValueComparable.integer left))
  · have different : ¬ ValueEquivalent (.integer left) (.integer right) := by
      intro equivalent
      exact same (Dynamic.Value.integer.inj equivalent.1)
    rw [beq_eq_false_iff_ne.mpr same]
    exact BinaryPrimitiveApplies.equalFalse different

theorem BinaryOperation.preserves {core : Core.BinaryOp} {source : Syntax.BinaryOp}
    (operation : BinaryOperation core source) (left right : Int) :
    ∃ sourceResult coreResult, ResultRepresents sourceResult coreResult ∧
      BinaryPrimitiveApplies source (.integer left) (.integer right) sourceResult ∧
      core.apply (.integer left) (.integer right) = some coreResult := by
  cases operation with
  | add => exact ⟨_, _, .integer _, .integerAdd left right, rfl⟩
  | subtract => exact ⟨_, _, .integer _, .integerSubtract left right, rfl⟩
  | multiply => exact ⟨_, _, .integer _, .integerMultiply left right, rfl⟩
  | divide => exact ⟨_, _, .integer _, divide_source left right, rfl⟩
  | modulo => exact ⟨_, _, .integer _, modulo_source left right, rfl⟩
  | bitAnd => exact ⟨_, _, .integer _, bitAnd_source left right, rfl⟩
  | bitOr => exact ⟨_, _, .integer _, bitOr_source left right, rfl⟩
  | bitXor => exact ⟨_, _, .integer _, bitXor_source left right, rfl⟩
  | equal => exact ⟨_, _, .bool _, equal_source left right, rfl⟩
  | less => exact ⟨_, _, .bool _, .integerLess left right, rfl⟩

/-- Native primitive evaluation preserves the source result while retaining
left-to-right operand effects and the exact final store. -/
theorem BinaryOperation.evaluates {core : Core.BinaryOp} {source : Syntax.BinaryOp}
    (operation : BinaryOperation core source)
    {environment : Core.Environment} {initialStore middleStore finalStore : Core.Store}
    {leftExpr rightExpr : Core.Expr} {left right : Int}
    (leftEvaluated : Core.Evaluates environment initialStore leftExpr (.integer left) middleStore)
    (rightEvaluated : Core.Evaluates environment middleStore rightExpr (.integer right) finalStore) :
    ∃ sourceResult coreResult, ResultRepresents sourceResult coreResult ∧
      BinaryPrimitiveApplies source (.integer left) (.integer right) sourceResult ∧
      Core.Evaluates environment initialStore (.binary core leftExpr rightExpr) coreResult finalStore := by
  obtain ⟨sourceResult, coreResult, represents, meaning, applied⟩ := operation.preserves left right
  exact ⟨sourceResult, coreResult, represents, meaning, .binary leftEvaluated rightEvaluated applied⟩

theorem bitNot_preserves (value : Int) :
    UnaryPrimitiveApplies .bitNot (.integer value) (.integer (~~~value)) ∧
      Core.UnaryOp.integerNot.apply (.integer value) = some (.integer (~~~value)) :=
  ⟨.integerBitNot value, rfl⟩

theorem integerToWord_preserves (value : Int) :
    BuiltinApplies .wordFromInteger [.integer value] (.word (Core.Word.ofIntModulo value)) ∧
      Core.UnaryOp.integerToWord.apply (.integer value) = some (.word (Core.Word.ofIntModulo value)) :=
  ⟨.wordFromInteger value, rfl⟩

theorem wordToInteger_preserves (value : Core.Word) :
    BuiltinApplies .wordToInteger [.word value] (.integer (Int.ofNat value.val)) ∧
      Core.UnaryOp.wordToInteger.apply (.word value) = some (.integer (Int.ofNat value.val)) :=
  ⟨.wordToInteger value, rfl⟩

end Solcore.SourceSemantics.CoreLowering.IntegerPrimitives
