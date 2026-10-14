import Solcore.SourceSemantics.CoreLowering.CompatibleBareAssignmentCommit

/-! Original Word metadata determines scalar operands without a callable
observation assumption. These facts support the actual bare compound commit. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleBareWordModifier
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap SourceCoreCompatibleDataPlaces DataPlaceExecution CoreProof
open CompatibleBareAssignment

variable {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
  {mapping : LocationMap} {world : StoreTyping}

theorem word_fields {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
    (related : ValueRep checked registry functions mapping world sourceType source value type)
    (view : SourceCoreRawMetadata.runtimeType sourceType = .word) :
    ∃ word, source = .word word ∧ value = .word word ∧ type = .word := by
  revert view
  induction related using ValueRep.rec (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True) (motive_4 := fun _ _ _ _ => True) with
  | word word => intro _; exact ⟨word, rfl, rfl, rfl⟩
  | compatible same _ ih => intro view; exact ih (same.symm.trans view)
  | @constructed metadata id tag sources values types _ _ _ projected _ _ _ =>
      intro view
      have scalar : checked.catalog.project metadata.resultType = .ok .word := by
        rw [← checked.catalog.project_runtimeType, view]
        rfl
      cases Except.ok.inj (projected.symm.trans scalar)
  | unit | bool | integer | product | function | proxy | mappingValue =>
      intro view
      cases view
  | nil | cons | empty | entry | absent | present => trivial

theorem initialized_success
    {sourceType : TypeSystem.Ty} {type : Ty} {left right : Dynamic.Value} {leftCore rightCore : Value}
    {operator : Syntax.ValueAssignOp}
    (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType sourceType = .word)
    (leftRep : ValueRep checked registry functions mapping world sourceType left leftCore type)
    (rightRep : ValueRep checked registry functions mapping world sourceType right rightCore type)
    {environment : Environment} {snapshot rhs : Expr}
    (snapshotSelected : DataEquality.Selects environment snapshot (.inRight .unit leftCore))
    (rightSelected : DataEquality.Selects environment rhs rightCore) (store : Store) (invalid : Word) :
    ∃ result value, ValueRep checked registry functions mapping world sourceType result value type ∧
      Dynamic.AssignmentValueApplies operator (some left) right result ∧
      Evaluates environment store (modified type (binaryOperator (type = .integer) operator) false snapshot rhs invalid)
        (.inRight .word value) store ∧ ¬ Dynamic.AssignmentOperandsInvalid operator (some left) right := by
  rcases profile with rfl | word
  · exact ⟨right, rightCore, rightRep, .equal _ _, .inRight (rightSelected.evaluates store),
      DataPlaceModifier.assignment_excludes_invalid (.equal _ _)⟩
  · obtain ⟨left, rfl, rfl, rfl⟩ := word_fields leftRep word
    obtain ⟨right, rfl, rfl, _⟩ := word_fields rightRep word
    obtain ⟨result, applied, evaluated⟩ := DataPlaceModifier.word_success operator left right
      snapshotSelected rightSelected store invalid
    exact ⟨_, _, .compatible (actual := .word) word (.word result), applied, evaluated,
      DataPlaceModifier.assignment_excludes_invalid applied⟩

/-- The optional pre-RHS snapshot determines whether the actual modifier
fails or produces a replacement. Every outcome keeps the current RHS store. -/
theorem modifier_total {sourceType : TypeSystem.Ty} {type : Ty} {initial : Option Dynamic.Value}
    {snapshot rightCore : Value} {right : Dynamic.Value} {operator : Syntax.ValueAssignOp}
    (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType sourceType = .word)
    (saved : SnapshotRep checked registry functions mapping world sourceType type initial snapshot)
    (rightRep : ValueRep checked registry functions mapping world sourceType right rightCore type)
    {environment : Environment} {snapshotExpression rightExpression : Expr}
    (snapshotSelected : DataEquality.Selects environment snapshotExpression snapshot)
    (rightSelected : DataEquality.Selects environment rightExpression rightCore) (store : Store) (invalid : Word) :
    (Dynamic.AssignmentOperandsInvalid operator initial right ∧
      Evaluates environment store (modified type (binaryOperator (type = .integer) operator) false snapshotExpression rightExpression invalid)
        (.inLeft type (.word invalid)) store) ∨
    ∃ result value, ValueRep checked registry functions mapping world sourceType result value type ∧
      Dynamic.AssignmentValueApplies operator initial right result ∧
      Evaluates environment store (modified type (binaryOperator (type = .integer) operator) false snapshotExpression rightExpression invalid)
        (.inRight .word value) store := by
  cases saved with
  | present related =>
      obtain ⟨result, value, represented, applied, evaluated, _⟩ :=
        initialized_success profile related rightRep snapshotSelected rightSelected store invalid
      exact .inr ⟨result, value, represented, applied, evaluated⟩
  | absent =>
      by_cases equal : operator = .equal
      · subst operator
        exact .inr ⟨right, rightCore, rightRep, .equal _ _, .inRight (rightSelected.evaluates store)⟩
      · refine .inl ⟨.uninitialized equal, ?_⟩
        cases operator <;> first
        | exact (equal rfl).elim
        | (by_cases integer : type = .integer <;>
            simp only [binaryOperator, integer, ite_true, ite_false, modified] <;>
            exact .caseLeft (snapshotSelected.evaluates store) (.inLeft .word))

end Solcore.SourceSemantics.CoreLowering.CompatibleBareWordModifier
