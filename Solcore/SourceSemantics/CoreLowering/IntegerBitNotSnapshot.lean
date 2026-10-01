import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceModifier
import Solcore.SourceSemantics.CoreLowering.DataPlaceCommitReflection

/-! Integer bit-not at the retained IR boundary. The declarative snapshot rule
agrees with the already executable unary primitive and ordinary Core modifier.
This does not broaden the source checker's Word-only compound admission. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.IntegerBitNotSnapshot
open Core Frontend SourceInference GeneralHeap DataEquality CompatiblePayload CompatibleEquality
open SourceCoreCompatibleDataPlaces

theorem preserves_type {context : SourceSemantics.Context} {heap : Dynamic.Heap}
    {current : Option Dynamic.Value} {result : Dynamic.Value}
    (typed : Dynamic.OptionalValueHasType context heap current .integer)
    (applies : Dynamic.BitNotSnapshot current result) : Dynamic.ValueHasType context heap result .integer := by
  cases applies with
  | word => cases typed with | some typed => cases typed
  | integer _ => exact .integer _

theorem native_success (value : Int) {environment : Environment} {snapshot rhs : Expr}
    (selected : Selects environment snapshot (.inRight .unit (.integer value)))
    (operator : Option Core.BinaryOp) (store : Store) (invalid : Word) :
    Dynamic.BitNotSnapshot (some (.integer value)) (.integer (~~~value)) ∧
      Evaluates environment store (modified .integer operator true snapshot rhs invalid)
        (.inRight .word (.integer (~~~value))) store ∧
      ¬ Dynamic.UnaryPrimitiveOperandInvalid .bitNot (.integer value) := by
  obtain ⟨_, evaluated, valid⟩ := DataPlaceModifier.integer_bitNot_primitive value selected operator store invalid
  exact ⟨.integer value, evaluated, valid⟩

/-- Every completed generated modifier run returns the independent Integer
snapshot result and keeps the store unchanged. No source runtime is imported. -/
theorem native_reflects (value : Int) {environment : Environment} {snapshot rhs : Expr}
    (selected : Selects environment snapshot (.inRight .unit (.integer value)))
    (operator : Option Core.BinaryOp) {store after : Store} (invalid : Word) {result : Value}
    (completed : Evaluates environment store (modified .integer operator true snapshot rhs invalid) result after) :
    result = .inRight .word (.integer (~~~value)) ∧ after = store ∧
      Dynamic.BitNotSnapshot (some (.integer value)) (.integer (~~~value)) := by
  obtain ⟨applies, evaluated, _⟩ := native_success value selected operator store invalid
  exact ⟨(evaluation_deterministic completed evaluated).1, (evaluation_deterministic completed evaluated).2, applies⟩

theorem compatible_success {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {functions : FunctionModel checked.catalog} {mapping : LocationMap} {world : StoreTyping}
    {identities : Dynamic.Value → Word → Prop}
    (observations : FunctionObservations checked.catalog functions identities)
    {sourceType : TypeSystem.Ty} {type : Ty} {source : Dynamic.Value} {value : Value}
    (profile : SourceCoreRawMetadata.runtimeType sourceType = .integer)
    (represented : ValueRep checked registry functions mapping world sourceType source value type)
    {environment : Environment} {snapshot rhs : Expr}
    (selected : Selects environment snapshot (.inRight .unit value))
    (operator : Option BinaryOp) (store : Store) (invalid : Word) :
    ∃ result native, ValueRep checked registry functions mapping world sourceType result native type ∧
      Dynamic.BitNotSnapshot (some source) result ∧
      Evaluates environment store (modified type operator true snapshot rhs invalid) (.inRight .word native) store ∧
      ¬ Dynamic.UnaryPrimitiveOperandInvalid .bitNot source := by
  have projected : checked.catalog.project sourceType = .ok .integer := by
    rw [← checked.catalog.project_runtimeType sourceType, profile]; rfl
  have same := Except.ok.inj (represented.projection.symm.trans projected)
  subst type
  obtain ⟨integer, rfl, rfl⟩ := CompatiblePlaceModifier.integer_fields observations represented
  obtain ⟨applies, evaluated, valid⟩ := native_success integer selected operator store invalid
  exact ⟨_, _, .compatible (actual := .integer) profile (.integer (~~~integer)), applies, evaluated, valid⟩

/-- The newly admitted dynamic constructor closes an ordinary source snapshot
write. The retained place is Integer typed, without claiming checker admission. -/
theorem source_assignment (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (id : Resolved.LocalId) (value : Int) :
    Dynamic.SourcePlaceSnapshotUpdate program context evidence source Dynamic.BitNotSnapshot
      [(id, ⟨0⟩)] ⟨[⟨.integer, some (.integer value), none⟩]⟩ ⟨id, [], .integer⟩
      (.integer (~~~value)) ⟨[⟨.integer, some (.integer (~~~value)), none⟩]⟩ := by
  apply Dynamic.SourcePlaceSnapshotUpdate.intro
    (selectedHeap := ⟨[⟨.integer, some (.integer value), none⟩]⟩)
    (target := ⟨⟨0⟩, .integer, .integer, [], some (.integer value)⟩)
  · exact Dynamic.SourcePlaceResolves.intro (place := ⟨id, [], .integer⟩)
      (before := ⟨[⟨.integer, some (.integer value), none⟩]⟩)
      (after := ⟨[⟨.integer, some (.integer value), none⟩]⟩)
      .head (.intro .head) .nil (.intro .head) .initialized .nil
  · exact .intro (.intro .head) rfl .initialized (.leaf (.integer value))
      (DataPlaceCommitReflection.source_writes (.intro .head) (.integer (~~~value)))

end Solcore.SourceSemantics.CoreLowering.IntegerBitNotSnapshot
