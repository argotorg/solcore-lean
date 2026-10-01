import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceBitNotModifier
import Solcore.SourceSemantics.CoreLowering.IntegerBitNotSnapshot

/-! Closed Word/Integer snapshot modifier semantics for the retained IR
profile. This extends no source checker or static admission rule. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePlaceNumericBitNotModifier
open Core Frontend GeneralHeap CompatiblePayload CompatibleEquality SourceCoreCompatibleDataPlaces

theorem success {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {mapping : LocationMap} {world : StoreTyping}
    {identities : Dynamic.Value → Word → Prop}
    (observations : FunctionObservations checked.catalog functions identities)
    {sourceType : TypeSystem.Ty} {type : Ty} {source : Dynamic.Value} {value : Value}
    (profile : SourceCoreRawMetadata.runtimeType sourceType = .word ∨ SourceCoreRawMetadata.runtimeType sourceType = .integer)
    (represented : ValueRep checked registry functions mapping world sourceType source value type)
    {environment : Environment} {snapshot rhs : Expr}
    (selected : DataEquality.Selects environment snapshot (.inRight .unit value))
    (operator : Option BinaryOp) (store : Store) (invalid : Word) :
    ∃ result native, ValueRep checked registry functions mapping world sourceType result native type ∧
      Dynamic.BitNotSnapshot (some source) result ∧
      Evaluates environment store (modified type operator true snapshot rhs invalid) (.inRight .word native) store ∧
      ¬ Dynamic.UnaryPrimitiveOperandInvalid .bitNot source := by
  rcases profile with word | integer
  · exact CompatiblePlaceBitNotModifier.word_success observations word represented selected operator store invalid
  · exact IntegerBitNotSnapshot.compatible_success observations integer represented selected operator store invalid

end Solcore.SourceSemantics.CoreLowering.CompatiblePlaceNumericBitNotModifier
