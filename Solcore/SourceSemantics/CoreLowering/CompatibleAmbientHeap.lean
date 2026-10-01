import Solcore.SourceSemantics.CoreLowering.CompatibleAmbientPayload
import Solcore.SourceSemantics.CoreLowering.AmbientHeap
import Solcore.SourceSemantics.CoreLowering.CompatibleHeap

/-! The compatible carrier uses the common heap relation under the actual full
Core definition table. The base source catalog and metadata registry remain
unchanged; administrative definitions receive no fabricated source types. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleAmbientHeap
open Core Frontend GeneralHeap CompatiblePayload CompatibleEquality

def payloadModel (checked : SourceCoreCompatibleCatalog.Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions} (functions : FunctionModel checked.catalog ambient) :
    GenericHeap.PayloadModel (storageCatalog checked.catalog) (CompatibleHeap.projects checked.catalog) ambient.definitions where
  Represents := ValueRep checked registry functions
  projection := ValueRep.projection
  runtime_hasType := ValueRep.runtime_hasType
  extend := fun represented maps worlds => represented.extend (.refl _) maps worlds

abbrev HeapRepresents (checked : SourceCoreCompatibleCatalog.Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions} (functions : FunctionModel checked.catalog ambient) :=
  GenericHeap.HeapRepresents (payloadModel checked registry functions)

theorem model_base {checked : SourceCoreCompatibleCatalog.Checked} {registry : SourceCoreRawMetadata.Registry}
    (functions : FunctionModel checked.catalog) :
    payloadModel checked registry functions = CompatibleHeap.payloadModel checked registry functions := rfl

/-- Existing source values and physical store are preserved when moving to a
larger native definition table and an explicitly including function model. -/
theorem extend_definitions {checked : SourceCoreCompatibleCatalog.Checked} {registry : SourceCoreRawMetadata.Registry}
    {before after : AmbientDefinitions checked.catalog.definitions}
    {initial : FunctionModel checked.catalog before} {future : FunctionModel checked.catalog after}
    (includes : initial.Includes future) (extension : before.definitions.Extends after.definitions)
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    (related : HeapRepresents checked registry initial mapping world heap store) :
    HeapRepresents checked registry future mapping world heap store :=
  GenericHeap.HeapRepresents.extend_definitions
    (fun represented => ValueRep.map_functions includes represented) extension related

end Solcore.SourceSemantics.CoreLowering.CompatibleAmbientHeap
