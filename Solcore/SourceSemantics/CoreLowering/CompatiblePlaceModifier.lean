import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceRhs
import Solcore.SourceSemantics.CoreLowering.DataPlaceModifier

/-! Compatible payloads retain raw source metadata while numeric modifiers
operate on their scalar runtime view. Total initialized primitives justify
computing the modifier before latest-root traversal: it cannot hide a later
structural source fault. This module reuses the existing primitive semantics. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePlaceModifier
open Core Frontend SourceInference GeneralHeap DataEquality CompatiblePayload CompatibleEquality
open SourceCoreCompatibleDataPlaces

variable {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions}
  {functions : FunctionModel checked.catalog ambient} {mapping : LocationMap} {world : StoreTyping}
  {identities : Dynamic.Value → Word → Prop}

theorem word_fields (observations : FunctionObservations checked.catalog functions identities)
    {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {value : Value}
    (related : ValueRep checked registry functions mapping world sourceType source value .word) :
    ∃ word, source = .word word ∧ value = .word word := by
  cases CompatibleEquality.ValueRep.observation observations related with
  | word word => exact ⟨word, rfl, rfl⟩

theorem integer_fields (observations : FunctionObservations checked.catalog functions identities)
    {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {value : Value}
    (related : ValueRep checked registry functions mapping world sourceType source value .integer) :
    ∃ integer, source = .integer integer ∧ value = .integer integer := by
  cases CompatibleEquality.ValueRep.observation observations related with
  | integer integer => exact ⟨integer, rfl, rfl⟩

/-- Plain assignment supports every authenticated payload. Numeric compound
assignment also accepts staged type views, without changing their metadata. -/
theorem initialized_success
    (observations : FunctionObservations checked.catalog functions identities)
    {sourceType : TypeSystem.Ty} {type : Ty} {left right : Dynamic.Value} {leftCore rightCore : Value}
    {operator : Syntax.ValueAssignOp}
    (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType sourceType = .word ∨
      SourceCoreRawMetadata.runtimeType sourceType = .integer)
    (leftRep : ValueRep checked registry functions mapping world sourceType left leftCore type)
    (rightRep : ValueRep checked registry functions mapping world sourceType right rightCore type)
    {environment : Environment} {snapshot rhs : Expr}
    (snapshotSelected : Selects environment snapshot (.inRight .unit leftCore))
    (rightSelected : Selects environment rhs rightCore) (store : Store) (invalid : Word) :
    ∃ result value, ValueRep checked registry functions mapping world sourceType result value type ∧
      Dynamic.AssignmentValueApplies operator (some left) right result ∧
      Evaluates environment store (modified type (binaryOperator (type = .integer) operator) false snapshot rhs invalid)
        (.inRight .word value) store ∧ ¬ Dynamic.AssignmentOperandsInvalid operator (some left) right := by
  rcases profile with rfl | word | integer
  · exact ⟨right, rightCore, rightRep, .equal _ _, .inRight (rightSelected.evaluates store),
      DataPlaceModifier.assignment_excludes_invalid (.equal _ _)⟩
  · have projected : checked.catalog.project sourceType = .ok .word := by
      rw [← checked.catalog.project_runtimeType sourceType, word]; rfl
    have same := Except.ok.inj (leftRep.projection.symm.trans projected)
    subst type
    obtain ⟨left, rfl, rfl⟩ := word_fields observations leftRep
    obtain ⟨right, rfl, rfl⟩ := word_fields observations rightRep
    obtain ⟨result, applied, evaluated⟩ := DataPlaceModifier.word_success operator left right snapshotSelected rightSelected store invalid
    exact ⟨_, _, .compatible (actual := .word) word (.word result), applied, evaluated, DataPlaceModifier.assignment_excludes_invalid applied⟩
  · have projected : checked.catalog.project sourceType = .ok .integer := by
      rw [← checked.catalog.project_runtimeType sourceType, integer]; rfl
    have same := Except.ok.inj (leftRep.projection.symm.trans projected)
    subst type
    obtain ⟨left, rfl, rfl⟩ := integer_fields observations leftRep
    obtain ⟨right, rfl, rfl⟩ := integer_fields observations rightRep
    obtain ⟨result, applied, evaluated⟩ := DataPlaceModifier.integer_success operator left right snapshotSelected rightSelected store invalid
    exact ⟨_, _, .compatible (actual := .integer) integer (.integer result), applied, evaluated, DataPlaceModifier.assignment_excludes_invalid applied⟩

/-- The source operation determines the same result as the actual native
modifier, including division/modulo by zero and unbounded Integer arithmetic. -/
theorem preserves
    (observations : FunctionObservations checked.catalog functions identities)
    {sourceType : TypeSystem.Ty} {type : Ty} {left right result : Dynamic.Value} {leftCore rightCore : Value}
    {operator : Syntax.ValueAssignOp}
    (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType sourceType = .word ∨
      SourceCoreRawMetadata.runtimeType sourceType = .integer)
    (leftRep : ValueRep checked registry functions mapping world sourceType left leftCore type)
    (rightRep : ValueRep checked registry functions mapping world sourceType right rightCore type)
    (applied : Dynamic.AssignmentValueApplies operator (some left) right result)
    {environment : Environment} {snapshot rhs : Expr}
    (snapshotSelected : Selects environment snapshot (.inRight .unit leftCore))
    (rightSelected : Selects environment rhs rightCore) (store : Store) (invalid : Word) :
    ∃ value, ValueRep checked registry functions mapping world sourceType result value type ∧
      Evaluates environment store (modified type (binaryOperator (type = .integer) operator) false snapshot rhs invalid)
        (.inRight .word value) store ∧ ¬ Dynamic.AssignmentOperandsInvalid operator (some left) right := by
  obtain ⟨result', value, related, applied', evaluated, valid⟩ :=
    initialized_success observations profile leftRep rightRep snapshotSelected rightSelected store invalid
  have same := DataPlaceModifier.assignment_functional applied' applied
  subst result'
  exact ⟨value, related, evaluated, valid⟩

end Solcore.SourceSemantics.CoreLowering.CompatiblePlaceModifier
