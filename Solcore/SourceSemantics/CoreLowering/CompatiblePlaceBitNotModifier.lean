import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceModifier
import Solcore.SourceSemantics.CoreLowering.DataPlaceUpdateTotality
import Solcore.SourceSemantics.CoreLowering.DataPlaceCommitReflection

/-! Bit-not consumes the saved leaf. The generated Unit RHS is administrative
and has no corresponding source expression. The independent assignment rule
currently has only a Word constructor; Integer primitive agreement is separate. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePlaceBitNotModifier
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality
open SourceCoreCompatibleDataPlaces

variable {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
  {functions : FunctionModel checked.catalog} {mapping : LocationMap} {world : StoreTyping}
  {identities : Dynamic.Value → Word → Prop}

theorem word_success
    (observations : FunctionObservations checked.catalog functions identities)
    {sourceType : TypeSystem.Ty} {type : Ty} {source : Dynamic.Value} {value : Value}
    (profile : SourceCoreRawMetadata.runtimeType sourceType = .word)
    (represented : ValueRep checked registry functions mapping world sourceType source value type)
    {environment : Environment} {snapshot rhs : Expr}
    (selected : DataEquality.Selects environment snapshot (.inRight .unit value))
    (operator : Option BinaryOp) (store : Store) (invalid : Word) :
    ∃ result native, ValueRep checked registry functions mapping world sourceType result native type ∧
      Dynamic.BitNotSnapshot (some source) result ∧
      Evaluates environment store (modified type operator true snapshot rhs invalid) (.inRight .word native) store ∧
      ¬ Dynamic.UnaryPrimitiveOperandInvalid .bitNot source := by
  have projected : checked.catalog.project sourceType = .ok .word := by
    rw [← checked.catalog.project_runtimeType sourceType, profile]; rfl
  have same := Except.ok.inj (represented.projection.symm.trans projected)
  subst type
  obtain ⟨word, rfl, rfl⟩ := CompatiblePlaceModifier.word_fields observations represented
  obtain ⟨applies, evaluated, valid⟩ := DataPlaceModifier.word_bitNot_success word selected operator store invalid
  exact ⟨_, _, .compatible (actual := .word) profile (.word word.bitNot), applies, evaluated, valid⟩

theorem functional {current : Option Dynamic.Value} {left right : Dynamic.Value}
    (first : Dynamic.BitNotSnapshot current left) (second : Dynamic.BitNotSnapshot current right) : left = right := by
  cases first
  cases second
  rfl

/-- A successful independent target supplies all structural facts needed for
a snapshot-only write. No post-RHS source heap exists in this operation. -/
theorem write_exists {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before selected : Dynamic.Heap} {place : PlaceResolution} {target : Dynamic.ResolvedPlace}
    (resolved : Dynamic.SourcePlaceResolves program context evidence source environment before place target selected)
    {replacement : Dynamic.Value} (applies : Dynamic.BitNotSnapshot target.selected replacement) :
    ∃ updated after, Dynamic.ResolvedPlaceWrites (fun _ value => Dynamic.BitNotSnapshot target.selected value)
      selected target updated after := by
  cases resolved with
  | intro lookup initialRead keys currentRead initial read =>
    obtain ⟨updated, changed⟩ := DataPlaceUpdateTotality.read_update read replacement
    exact ⟨updated, _, .intro currentRead rfl initial
      (DataPlaceCommitReflection.update_of_replacement changed (fun _ => applies))
      (DataPlaceCommitReflection.source_writes currentRead updated)⟩

end Solcore.SourceSemantics.CoreLowering.CompatiblePlaceBitNotModifier
