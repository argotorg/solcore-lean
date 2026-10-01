import Solcore.SourceSemantics.CoreLowering.GenericHeap
import Solcore.SourceSemantics.CoreLowering.AmbientDefinitions

/-! Reindex the common heap/environment relation along an authenticated Core
definition suffix. Source cells and locations are unchanged. Payload semantics
are transferred by a separate model inclusion, not inferred from native typing. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering
open Core Frontend GeneralHeap

namespace DataHeap

theorem EnvRepresents.extend_definitions {catalog : SourceCoreDataCatalog.Catalog}
    {before after : DataEnvironment} (extension : before.Extends after)
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {scope : SourceCoreLocalCell.Scope} {source : Dynamic.Environment} {environment : Environment}
    (related : EnvRepresents catalog mapping world administrative scope source environment before) :
    EnvRepresents catalog mapping world administrative scope source environment after := by
  induction related with
  | nil values => exact .nil (values.extend_definitions extension)
  | cons reference _ ih => exact .cons reference ih
  | internal reference absent _ ih => exact .internal reference absent ih

end DataHeap

namespace GenericHeap

def PayloadModel.Includes {catalog : SourceCoreDataCatalog.Catalog} {projects : Projection}
    {before after : DataEnvironment} (initial : PayloadModel catalog projects before)
    (future : PayloadModel catalog projects after) : Prop :=
  ∀ {mapping world sourceType sourceValue value payload},
    initial.Represents mapping world sourceType sourceValue value payload →
      future.Represents mapping world sourceType sourceValue value payload

theorem CellRepresents.map_model {catalog : SourceCoreDataCatalog.Catalog} {projects : Projection}
    {before after : DataEnvironment} {initial : PayloadModel catalog projects before}
    {future : PayloadModel catalog projects after} (includes : initial.Includes future)
    {mapping : LocationMap} {world : StoreTyping} {cell : Dynamic.Cell} {value : Value} {type : Ty}
    (related : CellRepresents initial mapping world cell value type) :
    CellRepresents future mapping world cell value type := by
  cases related with
  | uninitialized projected => exact .uninitialized projected
  | initialized represented => exact .initialized (includes represented)

theorem HeapRepresents.extend_definitions {catalog : SourceCoreDataCatalog.Catalog} {projects : Projection}
    {before after : DataEnvironment} {initial : PayloadModel catalog projects before}
    {future : PayloadModel catalog projects after} (includes : initial.Includes future)
    (extension : before.Extends after)
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    (related : HeapRepresents initial mapping world heap store) :
    HeapRepresents future mapping world heap store := by
  refine ⟨related.length_eq, related.injective, related.runtime_hasTypes.extend_definitions extension, ?_⟩
  intro source target mapped
  obtain ⟨cell, value, type, sourceRead, typed, read, payload⟩ := related.cells mapped
  exact ⟨cell, value, type, sourceRead, typed, read, payload.map_model includes⟩

end GenericHeap
end Solcore.SourceSemantics.CoreLowering
