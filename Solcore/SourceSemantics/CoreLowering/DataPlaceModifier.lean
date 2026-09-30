import Solcore.SourceSemantics.CoreLowering.DataPayload
import Solcore.SourceSemantics.CoreLowering.IntegerPrimitives
import Solcore.Frontend.SourceCoreDataPlaces
import Solcore.SourceSemantics.Dynamic.Fault

/-! The actual place modifier succeeds on initialized, equally typed numeric
operands. This is the condition needed when Core computes the modifier before
the latest-root traversal: no operand fault can preempt a structural fault.
Uninitialized snapshots remain an explicit separate case. The independent
bit-not-assignment relation currently admits Word only. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPlaceModifier
open Core Frontend Frontend.SourceInference SourceCoreDataPlaces DataEquality GeneralHeap DataPayload

theorem assignment_excludes_invalid {operator : Syntax.ValueAssignOp}
    {snapshot : Option Dynamic.Value} {right result : Dynamic.Value}
    (applied : Dynamic.AssignmentValueApplies operator snapshot right result) :
    ¬ Dynamic.AssignmentOperandsInvalid operator snapshot right := by
  intro invalid
  cases invalid with
  | uninitialized different => cases applied; exact different rfl
  | compound corresponds invalid =>
    cases corresponds <;> cases applied <;>
      exact invalid.excludes_application ⟨_, by assumption⟩

theorem assignment_functional {operator : Syntax.ValueAssignOp}
    {snapshot : Option Dynamic.Value} {right first second : Dynamic.Value}
    (left : Dynamic.AssignmentValueApplies operator snapshot right first)
    (rightApplication : Dynamic.AssignmentValueApplies operator snapshot right second) : first = second := by
  cases left <;> cases rightApplication <;> first
    | rfl
    | exact Dynamic.BinaryPrimitiveApplies.functional (by assumption) (by assumption)

private theorem binary_modified {type : Ty} {operator : Core.BinaryOp}
    {environment : Environment} {snapshot rhs : Expr} {left right result : Value}
    (applied : operator.apply left right = some result)
    (snapshotSelected : Selects environment snapshot (.inRight .unit left))
    (rightSelected : Selects environment rhs right) (store : Store) (invalid : Word) :
    Evaluates environment store (modified type (some operator) false snapshot rhs invalid)
      (.inRight .word result) store :=
  .caseRight (snapshotSelected.evaluates store)
    (.inRight (.binary (.var rfl) ((rightSelected.weaken left).evaluates store) applied))

theorem equal_modified {type : Ty} {environment : Environment} {snapshot rhs : Expr} {right : Value}
    (selected : Selects environment rhs right) (store : Store) (invalid : Word) :
    Evaluates environment store (modified type none false snapshot rhs invalid) (.inRight .word right) store :=
  .inRight (selected.evaluates store)

theorem word_success (operator : Syntax.ValueAssignOp) (left right : Word)
    {environment : Environment} {snapshot rhs : Expr}
    (snapshotSelected : Selects environment snapshot (.inRight .unit (.word left)))
    (rightSelected : Selects environment rhs (.word right)) (store : Store) (invalid : Word) :
    ∃ result : Word, Dynamic.AssignmentValueApplies operator (some (.word left)) (.word right) (.word result) ∧
      Evaluates environment store (modified .word (binaryOperator false operator) false snapshot rhs invalid)
        (.inRight .word (.word result)) store := by
  cases operator with
  | equal => exact ⟨right, .equal _ _, equal_modified rightSelected store invalid⟩
  | add => exact ⟨_, .add (.wordAdd left right), binary_modified rfl snapshotSelected rightSelected store invalid⟩
  | subtract => exact ⟨_, .subtract (.wordSubtract left right), binary_modified rfl snapshotSelected rightSelected store invalid⟩
  | multiply => exact ⟨_, .multiply (.wordMultiply left right), binary_modified rfl snapshotSelected rightSelected store invalid⟩
  | divide => exact ⟨_, .divide (.wordDivide left right), binary_modified rfl snapshotSelected rightSelected store invalid⟩
  | modulo => exact ⟨_, .modulo (.wordModulo left right), binary_modified rfl snapshotSelected rightSelected store invalid⟩
  | bitAnd => exact ⟨_, .bitAnd (.wordBitAnd left right), binary_modified rfl snapshotSelected rightSelected store invalid⟩
  | bitOr => exact ⟨_, .bitOr (.wordBitOr left right), binary_modified rfl snapshotSelected rightSelected store invalid⟩
  | bitXor => exact ⟨_, .bitXor (.wordBitXor left right), binary_modified rfl snapshotSelected rightSelected store invalid⟩

theorem integer_success (operator : Syntax.ValueAssignOp) (left right : Int)
    {environment : Environment} {snapshot rhs : Expr}
    (snapshotSelected : Selects environment snapshot (.inRight .unit (.integer left)))
    (rightSelected : Selects environment rhs (.integer right)) (store : Store) (invalid : Word) :
    ∃ result : Int, Dynamic.AssignmentValueApplies operator (some (.integer left)) (.integer right) (.integer result) ∧
      Evaluates environment store (modified .integer (binaryOperator true operator) false snapshot rhs invalid)
        (.inRight .word (.integer result)) store := by
  cases operator with
  | equal => exact ⟨right, .equal _ _, equal_modified rightSelected store invalid⟩
  | add => exact ⟨_, .add (.integerAdd left right), binary_modified rfl snapshotSelected rightSelected store invalid⟩
  | subtract => exact ⟨_, .subtract (.integerSubtract left right), binary_modified rfl snapshotSelected rightSelected store invalid⟩
  | multiply => exact ⟨_, .multiply (.integerMultiply left right), binary_modified rfl snapshotSelected rightSelected store invalid⟩
  | divide => exact ⟨_, .divide (IntegerPrimitives.divide_source left right), binary_modified rfl snapshotSelected rightSelected store invalid⟩
  | modulo => exact ⟨_, .modulo (IntegerPrimitives.modulo_source left right), binary_modified rfl snapshotSelected rightSelected store invalid⟩
  | bitAnd => exact ⟨_, .bitAnd (IntegerPrimitives.bitAnd_source left right), binary_modified rfl snapshotSelected rightSelected store invalid⟩
  | bitOr => exact ⟨_, .bitOr (IntegerPrimitives.bitOr_source left right), binary_modified rfl snapshotSelected rightSelected store invalid⟩
  | bitXor => exact ⟨_, .bitXor (IntegerPrimitives.bitXor_source left right), binary_modified rfl snapshotSelected rightSelected store invalid⟩

/-- Full authenticated payloads at Word/Integer type expose the matching
primitive values. No source execution or Core modifier evaluation is assumed. -/
theorem initialized_success {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel catalog} {mapping : LocationMap} {world : StoreTyping}
    {sourceType : TypeSystem.Ty} {type : Ty} {left right : Dynamic.Value} {leftCore rightCore : Value}
    (numeric : sourceType = .word ∨ sourceType = .integer)
    (leftRep : ValueRep catalog signatures functions mapping world sourceType left leftCore type)
    (rightRep : ValueRep catalog signatures functions mapping world sourceType right rightCore type)
    (operator : Syntax.ValueAssignOp) {environment : Environment} {snapshot rhs : Expr}
    (snapshotSelected : Selects environment snapshot (.inRight .unit leftCore))
    (rightSelected : Selects environment rhs rightCore) (store : Store) (invalid : Word) :
    ∃ result value, ValueRep catalog signatures functions mapping world sourceType result value type ∧
      Dynamic.AssignmentValueApplies operator (some left) right result ∧
      Evaluates environment store (modified type (binaryOperator (type = .integer) operator) false snapshot rhs invalid)
        (.inRight .word value) store ∧ ¬ Dynamic.AssignmentOperandsInvalid operator (some left) right := by
  rcases numeric with rfl | rfl
  · cases leftRep with
    | word left =>
      cases rightRep with
      | word right =>
        obtain ⟨result, source, core⟩ := word_success operator left right snapshotSelected rightSelected store invalid
        exact ⟨_, _, .word result, source, core, assignment_excludes_invalid source⟩
    | constructed nominal => simp [SourceCoreDataCatalog.nominalParts, TypeSystem.Ty.word] at nominal
  · cases leftRep with
    | integer left =>
      cases rightRep with
      | integer right =>
        obtain ⟨result, source, core⟩ := integer_success operator left right snapshotSelected rightSelected store invalid
        exact ⟨_, _, .integer result, source, core, assignment_excludes_invalid source⟩
    | constructed nominal => simp [SourceCoreDataCatalog.nominalParts, TypeSystem.Ty.integer] at nominal

/-- Preserve an independently chosen source assignment result. Its equality
with the total primitive result follows from the source rules themselves. -/
theorem initialized_preserves {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel catalog} {mapping : LocationMap} {world : StoreTyping}
    {sourceType : TypeSystem.Ty} {type : Ty} {left right result : Dynamic.Value} {leftCore rightCore : Value}
    (numeric : sourceType = .word ∨ sourceType = .integer)
    (leftRep : ValueRep catalog signatures functions mapping world sourceType left leftCore type)
    (rightRep : ValueRep catalog signatures functions mapping world sourceType right rightCore type)
    {operator : Syntax.ValueAssignOp} (source : Dynamic.AssignmentValueApplies operator (some left) right result)
    {environment : Environment} {snapshot rhs : Expr}
    (snapshotSelected : Selects environment snapshot (.inRight .unit leftCore))
    (rightSelected : Selects environment rhs rightCore) (store : Store) (invalid : Word) :
    ∃ value, ValueRep catalog signatures functions mapping world sourceType result value type ∧
      Evaluates environment store (modified type (binaryOperator (type = .integer) operator) false snapshot rhs invalid)
        (.inRight .word value) store ∧ ¬ Dynamic.AssignmentOperandsInvalid operator (some left) right := by
  obtain ⟨result', value, represented, generated, evaluated, valid⟩ :=
    initialized_success numeric leftRep rightRep operator snapshotSelected rightSelected store invalid
  have same := assignment_functional generated source
  subst result'
  exact ⟨value, represented, evaluated, valid⟩

/-- Plain assignment does not inspect its previous snapshot and supports every
authenticated payload, including closures and mappings. -/
theorem equal_success {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel catalog} {mapping : LocationMap} {world : StoreTyping}
    {sourceType : TypeSystem.Ty} {type : Ty} {right : Dynamic.Value} {rightCore : Value}
    (rightRep : ValueRep catalog signatures functions mapping world sourceType right rightCore type)
    (previous : Option Dynamic.Value) {environment : Environment} {snapshot rhs : Expr}
    (rightSelected : Selects environment rhs rightCore) (store : Store) (invalid : Word) :
    ValueRep catalog signatures functions mapping world sourceType right rightCore type ∧
      Dynamic.AssignmentValueApplies .equal previous right right ∧
      Evaluates environment store (modified type (binaryOperator (type = .integer) .equal) false snapshot rhs invalid)
        (.inRight .word rightCore) store ∧ ¬ Dynamic.AssignmentOperandsInvalid .equal previous right :=
  ⟨rightRep, .equal _ _, equal_modified rightSelected store invalid, assignment_excludes_invalid (.equal _ _)⟩

theorem word_bitNot_success (value : Word) {environment : Environment} {snapshot rhs : Expr}
    (snapshotSelected : Selects environment snapshot (.inRight .unit (.word value)))
    (operator : Option Core.BinaryOp) (store : Store) (invalid : Word) :
    Dynamic.BitNotSnapshot (some (.word value)) (.word value.bitNot) ∧
      Evaluates environment store (modified .word operator true snapshot rhs invalid)
        (.inRight .word (.word value.bitNot)) store ∧
      ¬ Dynamic.UnaryPrimitiveOperandInvalid .bitNot (.word value) := by
  refine ⟨.word value, .caseRight (snapshotSelected.evaluates store) (.inRight (.unary (.var rfl) rfl)), ?_⟩
  intro invalid
  exact invalid.excludes_application ⟨_, .wordBitNot value⟩

/-- Integer bit-not agrees with the unary primitive. It is deliberately not
presented as `BitNotSnapshot`, whose independent assignment rule is Word-only. -/
theorem integer_bitNot_primitive (value : Int) {environment : Environment} {snapshot rhs : Expr}
    (snapshotSelected : Selects environment snapshot (.inRight .unit (.integer value)))
    (operator : Option Core.BinaryOp) (store : Store) (invalid : Word) :
    Dynamic.UnaryPrimitiveApplies .bitNot (.integer value) (.integer (~~~value)) ∧
      Evaluates environment store (modified .integer operator true snapshot rhs invalid)
        (.inRight .word (.integer (~~~value))) store ∧
      ¬ Dynamic.UnaryPrimitiveOperandInvalid .bitNot (.integer value) := by
  refine ⟨.integerBitNot value, .caseRight (snapshotSelected.evaluates store) (.inRight (.unary (.var rfl) rfl)), ?_⟩
  intro invalid
  exact invalid.excludes_application ⟨_, .integerBitNot value⟩

/-- Once the initialized numeric premise is established, the modifier cannot
produce a language failure at any completed Core evaluation. -/
theorem no_failure {environment : Environment} {store after : Store} {expression : Expr} {value : Value}
    {type : Ty} {token : Word} (success : Evaluates environment store expression (.inRight .word value) store) :
    ¬ Evaluates environment store expression (.inLeft type (.word token)) after := by
  intro failed
  have impossible := (evaluation_deterministic success failed).1
  cases impossible

end Solcore.SourceSemantics.CoreLowering.DataPlaceModifier
