import Solcore.SourceSemantics.CoreLowering.CompatibleEncoding
import Solcore.SourceSemantics.CoreLowering.CompatibleAmbientPayload

/-! Actual data-only encoder receipts transport into a function model under an
extended definition environment. First derive the structural representation in
the empty base function model, then include it in the ambient model. Thus no
fresh function value is justified by the encoder's base native typing receipt.
Raw metadata IDs, ordered entries, and original default types are unchanged. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleAmbientEncoding
open Core Frontend GeneralHeap CompatiblePayload CompatibleEncoding

private def noFunctions (catalog : SourceCoreCompatibleCatalog.Catalog) : FunctionModel catalog where
  Represents := fun _ _ _ _ _ _ _ => False
  projection := False.elim
  runtime_hasType := False.elim
  source_function := False.elim
  extend := fun impossible _ _ _ => False.elim impossible

/-- Successful public encoding supplies the independent source value and its
full payload representation under arbitrary ambient function leaves. -/
theorem encode_represents {fuel : Nat} {context : SourceCoreCompatibleValues.Context}
    {ambient : AmbientDefinitions context.checked.catalog.definitions}
    {functions : FunctionModel context.checked.catalog ambient}
    {expected : TypeSystem.Ty} {carrier : PublicValue}
    {encoded : SourceCoreCompatibleValues.Encoded fuel context expected carrier}
    (accepted : SourceCoreCompatibleValues.encode fuel context expected carrier = .ok encoded)
    (mapping : LocationMap) (world : StoreTyping) :
    ∃ source, Means carrier source ∧
      ValueRep context.checked encoded.context.registry functions mapping world expected source encoded.value encoded.type := by
  obtain ⟨source, meaning, represented⟩ := CompatibleEncoding.encode_represents
    (functions := noFunctions context.checked.catalog) accepted mapping world
  exact ⟨source, meaning, represented.map_functions (initial := noFunctions context.checked.catalog)
    (future := functions) (fun impossible => False.elim impossible)⟩

theorem encode_represents_at {fuel : Nat} {context : SourceCoreCompatibleValues.Context}
    {ambient : AmbientDefinitions context.checked.catalog.definitions}
    {functions : FunctionModel context.checked.catalog ambient}
    {expected : TypeSystem.Ty} {carrier : PublicValue}
    {encoded : SourceCoreCompatibleValues.Encoded fuel context expected carrier} {source : Dynamic.Value}
    (accepted : SourceCoreCompatibleValues.encode fuel context expected carrier = .ok encoded)
    (meaning : Means carrier source) (mapping : LocationMap) (world : StoreTyping) :
    ValueRep context.checked encoded.context.registry functions mapping world expected source encoded.value encoded.type := by
  obtain ⟨actual, actualMeaning, represented⟩ := encode_represents (functions := functions) accepted mapping world
  have same := actualMeaning.functional meaning
  subst actual
  exact represented

/-- Decoded receipts still retain the future registry obtained from their
actual authenticated re-encoding; it is not identified with the input table. -/
theorem decoded_represents_extended {fuel : Nat} {context : SourceCoreCompatibleValues.Context}
    {ambient : AmbientDefinitions context.checked.catalog.definitions}
    {functions : FunctionModel context.checked.catalog ambient}
    {expected : TypeSystem.Ty} {value : Value}
    (decoded : SourceCoreCompatibleValues.Decoded fuel context expected value)
    (mapping : LocationMap) (world : StoreTyping) :
    ∃ registry source, SourceCoreRawMetadata.Extends context.registry registry ∧ Means decoded.source source ∧
      ValueRep context.checked registry functions mapping world expected source value decoded.type := by
  obtain ⟨registry, source, extension, meaning, represented⟩ := CompatibleEncoding.decoded_represents_extended
    (functions := noFunctions context.checked.catalog) decoded mapping world
  exact ⟨registry, source, extension, meaning, represented.map_functions
    (initial := noFunctions context.checked.catalog) (future := functions) (fun impossible => False.elim impossible)⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleAmbientEncoding
