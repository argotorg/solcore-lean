import Solcore.SourceSemantics.CoreLowering.DataPlaceModifier
import Solcore.SourceSemantics.CoreLowering.DataPlaceSnapshot

/-! Completed place modifiers reflect the independently specified source leaf
operation. Plain assignment accepts every full payload; compound Word/Integer
operations are total when initialized. Absence is the only remaining failure,
and is retained for the enclosing latest-root ordering proof. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPlaceModifierReflection
open Core Frontend Frontend.SourceInference GeneralHeap DataPayload DataEquality
open SourceCoreDataPlaces

inductive ResultRep (catalog : SourceCoreDataCatalog.Catalog) (signatures : ProgramSignatures)
    (functions : GenericHeap.PayloadModel catalog) (mapping : LocationMap) (world : StoreTyping)
    (sourceType : TypeSystem.Ty) (type : Ty) (operator : Syntax.ValueAssignOp)
    (snapshot : Option Dynamic.Value) (right : Dynamic.Value) (invalid : Word) : Value → Prop where
  | applied {source : Dynamic.Value} {value : Value}
      (applied : Dynamic.AssignmentValueApplies operator snapshot right source)
      (related : ValueRep catalog signatures functions mapping world sourceType source value type) :
      ResultRep catalog signatures functions mapping world sourceType type operator snapshot right invalid (.inRight .word value)
  | uninitialized (absent : snapshot = none) (notEqual : operator ≠ .equal) :
      ResultRep catalog signatures functions mapping world sourceType type operator snapshot right invalid (.inLeft type (.word invalid))

/-- Total source/Core leaf behavior derived from payloads and the actual
operator spelling. Invalid operands are not conflated with machine faults. -/
theorem evaluates {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel catalog} {mapping : LocationMap} {world : StoreTyping}
    {sourceType : TypeSystem.Ty} {type : Ty} {snapshot : Option Dynamic.Value}
    {right : Dynamic.Value} {snapshotCore rightCore : Value} {operator : Syntax.ValueAssignOp}
    (profile : operator = .equal ∨ sourceType = .word ∨ sourceType = .integer)
    (snapshotRep : DataPlaceSnapshot.OptionalRep catalog signatures functions mapping world sourceType type snapshot snapshotCore)
    (rightRep : ValueRep catalog signatures functions mapping world sourceType right rightCore type)
    {environment : Environment} {snapshotExpression rightExpression : Expr}
    (snapshotSelected : Selects environment snapshotExpression snapshotCore)
    (rightSelected : Selects environment rightExpression rightCore) (store : Store) (invalid : Word) :
    ∃ result, ResultRep catalog signatures functions mapping world sourceType type operator snapshot right invalid result ∧
      Evaluates environment store
        (modified type (binaryOperator (type = .integer) operator) false snapshotExpression rightExpression invalid) result store := by
  by_cases equal : operator = .equal
  · subst operator
    exact ⟨_, .applied (.equal _ _) rightRep, DataPlaceModifier.equal_modified rightSelected store invalid⟩
  · cases snapshotRep with
    | absent =>
      refine ⟨_, .uninitialized rfl equal, ?_⟩
      cases operator <;> try exact (equal rfl).elim
      all_goals exact .caseLeft (snapshotSelected.evaluates store) (.inLeft .word)
    | present related =>
      obtain ⟨source, value, resultRep, sourceApplied, ran, _⟩ :=
        DataPlaceModifier.initialized_success (profile.resolve_left equal) related rightRep operator snapshotSelected rightSelected store invalid
      exact ⟨_, .applied sourceApplied resultRep, ran⟩

theorem reflects {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel catalog} {mapping : LocationMap} {world : StoreTyping}
    {sourceType : TypeSystem.Ty} {type : Ty} {snapshot : Option Dynamic.Value}
    {right : Dynamic.Value} {snapshotCore rightCore : Value} {operator : Syntax.ValueAssignOp}
    (profile : operator = .equal ∨ sourceType = .word ∨ sourceType = .integer)
    (snapshotRep : DataPlaceSnapshot.OptionalRep catalog signatures functions mapping world sourceType type snapshot snapshotCore)
    (rightRep : ValueRep catalog signatures functions mapping world sourceType right rightCore type)
    {environment : Environment} {snapshotExpression rightExpression : Expr}
    (snapshotSelected : Selects environment snapshotExpression snapshotCore)
    (rightSelected : Selects environment rightExpression rightCore)
    {store after : Store} {invalid : Word} {result : Value}
    (completed : Evaluates environment store
      (modified type (binaryOperator (type = .integer) operator) false snapshotExpression rightExpression invalid) result after) :
    after = store ∧ ResultRep catalog signatures functions mapping world sourceType type operator snapshot right invalid result := by
  obtain ⟨actual, represented, ran⟩ := evaluates profile snapshotRep rightRep snapshotSelected rightSelected store invalid
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed ran
  exact ⟨rfl, represented⟩

/-- The absent branch gives the source operand fault, but the enclosing
assignment still must show the latest structural path was traversable first. -/
theorem ResultRep.invalid {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel catalog} {mapping : LocationMap} {world : StoreTyping}
    {sourceType : TypeSystem.Ty} {type : Ty} {snapshot : Option Dynamic.Value} {right : Dynamic.Value}
    {operator : Syntax.ValueAssignOp} {invalid token : Word}
    (related : ResultRep catalog signatures functions mapping world sourceType type operator snapshot right invalid (.inLeft type (.word token))) :
    token = invalid ∧ snapshot = none ∧ Dynamic.AssignmentOperandsInvalid operator snapshot right := by
  cases related with
  | uninitialized absent notEqual => exact ⟨rfl, absent, absent ▸ .uninitialized notEqual⟩

end Solcore.SourceSemantics.CoreLowering.DataPlaceModifierReflection
