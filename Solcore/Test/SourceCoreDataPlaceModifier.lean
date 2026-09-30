import Solcore.SourceSemantics.CoreLowering.DataPlaceModifier

/-! Typed modifier success and source fault exclusion cover every Word/Integer
assignment spelling. Concrete checks retain zero-divisor behavior, negative
bitwise behavior, and plain assignment's independence from the old snapshot. -/

set_option autoImplicit false
namespace Tests.SourceCoreDataPlaceModifier
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open SourceCoreDataPlaces DataEquality DataPayload DataPlaceModifier

private def catalog : SourceCoreDataCatalog.Catalog := {}
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def functions : GenericHeap.PayloadModel catalog where
  Represents := fun _ _ _ _ _ _ => False
  projection := False.elim
  runtime_hasType := False.elim
  extend := fun impossible _ _ => False.elim impossible

/-- Each source operator has a total initialized primitive result. This covers
Word wrapping, division/modulo by zero and every Integer sign without a runtime
evaluation premise. The store can include arbitrary closure/cell cycles. -/
example (operator : Syntax.ValueAssignOp) (left right : Word) (store : Store) :
    ∃ result value, ValueRep catalog signatures functions [] [] .word result value .word ∧
      Dynamic.AssignmentValueApplies operator (some (.word left)) (.word right) result ∧
      Evaluates [.inRight .unit (.word left), .word right] store
        (modified .word (binaryOperator false operator) false (.var 0) (.var 1) Word.zero)
        (.inRight .word value) store ∧
      ¬ Dynamic.AssignmentOperandsInvalid operator (some (.word left)) (.word right) :=
  initialized_success (.inl rfl) (.word left) (.word right) operator (.var rfl) (.var rfl) store Word.zero

example (operator : Syntax.ValueAssignOp) (left right : Int) (store : Store) :
    ∃ result value, ValueRep catalog signatures functions [] [] .integer result value .integer ∧
      Dynamic.AssignmentValueApplies operator (some (.integer left)) (.integer right) result ∧
      Evaluates [.inRight .unit (.integer left), .integer right] store
        (modified .integer (binaryOperator true operator) false (.var 0) (.var 1) Word.zero)
        (.inRight .word value) store ∧
      ¬ Dynamic.AssignmentOperandsInvalid operator (some (.integer left)) (.integer right) :=
  initialized_success (.inr rfl) (.integer left) (.integer right) operator (.var rfl) (.var rfl) store Word.zero

example (left : Int) (store : Store) :
    ∃ value, ValueRep catalog signatures functions [] [] .integer (.integer 0) value .integer ∧
      Evaluates [.inRight .unit (.integer left), .integer 0] store
        (modified .integer (binaryOperator true .divide) false (.var 0) (.var 1) Word.zero)
        (.inRight .word value) store ∧
      ¬ Dynamic.AssignmentOperandsInvalid .divide (some (.integer left)) (.integer 0) :=
  initialized_preserves (.inr rfl) (.integer left) (.integer 0) (.divide (.integerDivideZero left))
    (.var rfl) (.var rfl) store Word.zero

private def integerCode (operator : Syntax.ValueAssignOp) : Expr :=
  modified .integer (binaryOperator true operator) false (.var 0) (.var 1) Word.zero
example : infer? [.sum .unit .integer, .integer] (integerCode .divide) = some (.sum .word .integer) := by cbv
example : runStateful 30 (.initial (integerCode .divide) [.inRight .unit (.integer (-7)), .integer 0] [.integer 900]) =
    .done (.inRight .word (.integer 0)) [.integer 900] := by cbv
example : runStateful 30 (.initial (integerCode .modulo) [.inRight .unit (.integer (-7)), .integer 0] [.integer 900]) =
    .done (.inRight .word (.integer 0)) [.integer 900] := by cbv
example : runStateful 30 (.initial (integerCode .divide) [.inRight .unit (.integer (-7)), .integer 3] []) =
    .done (.inRight .word (.integer (-3))) [] := by cbv
example : runStateful 30 (.initial (integerCode .modulo) [.inRight .unit (.integer (-7)), .integer 3] []) =
    .done (.inRight .word (.integer 2)) [] := by cbv
example : runStateful 30 (.initial (integerCode .bitXor) [.inRight .unit (.integer (-7)), .integer 3] []) =
    .done (.inRight .word (.integer (-6))) [] := by cbv

/-- Plain assignment can initialize an absent value. Even an unused malformed
snapshot expression is skipped; only the already evaluated RHS is selected. -/
example : Evaluates [.integer 17] []
    (modified .integer none false (.apply .unit .unit) (.var 0) Word.zero) (.inRight .word (.integer 17)) [] :=
  equal_modified (.var rfl) [] Word.zero
example : ¬ Dynamic.AssignmentOperandsInvalid .equal none (.integer 17) :=
  assignment_excludes_invalid (.equal none (.integer 17))

/-- The initialized condition is necessary: compound assignment of an absent
snapshot still returns its language fault and has an independent source fault. -/
example : Dynamic.AssignmentOperandsInvalid .add none (.integer 17) := .uninitialized (by decide)
example : runStateful 30 (.initial (integerCode .add) [.inLeft .integer .unit, .integer 17] []) =
    .done (.inLeft .integer (.word Word.zero)) [] := by cbv

example (value : Word) (store : Store) : Dynamic.BitNotSnapshot (some (.word value)) (.word value.bitNot) ∧
    Evaluates [.inRight .unit (.word value)] store
      (modified .word none true (.var 0) (.apply .unit .unit) Word.zero)
      (.inRight .word (.word value.bitNot)) store ∧
    ¬ Dynamic.UnaryPrimitiveOperandInvalid .bitNot (.word value) :=
  word_bitNot_success value (.var rfl) none store Word.zero

/-- Integer unary behavior is tested as its primitive relation, since the
separate independent bit-not-assignment rule currently accepts only Word. -/
example : Dynamic.UnaryPrimitiveApplies .bitNot (.integer (-7)) (.integer 6) ∧
    Evaluates [.inRight .unit (.integer (-7))] []
      (modified .integer none true (.var 0) .unit Word.zero) (.inRight .word (.integer 6)) [] ∧
    ¬ Dynamic.UnaryPrimitiveOperandInvalid .bitNot (.integer (-7)) :=
  integer_bitNot_primitive (-7) (.var rfl) none [] Word.zero

end Tests.SourceCoreDataPlaceModifier
