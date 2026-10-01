import Solcore.SourceSemantics.CoreLowering.CompatiblePayload

/-! Changing only the ambient Core definition environment preserves the raw
source metadata relation. Function interpretations are transferred explicitly;
a fresh interpretation may authenticate new administrative closure code, while
simple extension transports only the old interpreted values. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePayload
open Core Frontend GeneralHeap

/-- Existing function code and values retain their exact representation when
the definition table grows. This does not add new functions to the relation. -/
def FunctionModel.extend_definitions {catalog : SourceCoreCompatibleCatalog.Catalog}
    {before after : AmbientDefinitions catalog.definitions}
    (functions : FunctionModel catalog before) (extension : before.definitions.Extends after.definitions) :
    FunctionModel catalog after where
  Represents := functions.Represents
  projection := functions.projection
  runtime_hasType := fun represented => (functions.runtime_hasType represented).extend_definitions extension
  source_function := functions.source_function
  extend := functions.extend

/-- A function model may grow to include newly emitted code. Its full typing,
source authenticity and semantic laws remain the new model's responsibility. -/
def FunctionModel.Includes {catalog : SourceCoreCompatibleCatalog.Catalog}
    {before after : AmbientDefinitions catalog.definitions}
    (initial : FunctionModel catalog before) (future : FunctionModel catalog after) : Prop :=
  ∀ {registry mapping world sourceType source value type},
    initial.Represents registry mapping world sourceType source value type →
      future.Represents registry mapping world sourceType source value type

theorem ValueRep.map_functions {checked : SourceCoreCompatibleCatalog.Checked}
    {before after : AmbientDefinitions checked.catalog.definitions}
    {initial : FunctionModel checked.catalog before} {future : FunctionModel checked.catalog after}
    (includes : initial.Includes future)
    {registry : SourceCoreRawMetadata.Registry} {mapping : LocationMap} {world : StoreTyping}
    {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
    (related : ValueRep checked registry initial mapping world sourceType source value type) :
    ValueRep checked registry future mapping world sourceType source value type := by
  induction related using ValueRep.rec
    (motive_2 := fun types sources values coreTypes _ => ValuesRep checked registry future mapping world types sources values coreTypes)
    (motive_3 := fun key value sources entries aType bType _ => EntriesRep checked registry future mapping world key value sources entries aType bType)
    (motive_4 := fun type fallback coreType _ => DefaultRep checked registry future mapping world type fallback coreType) with
  | unit => exact .unit
  | bool => exact .bool _
  | word => exact .word _
  | integer => exact .integer _
  | product _ _ first second => exact .product first second
  | function related => exact .function (includes related)
  | proxy header identity registered => exact .proxy header identity registered
  | constructed header owner selected projected registered _ ih => exact .constructed header owner selected projected registered ih
  | compatible same _ ih => exact .compatible same ih
  | mappingValue header identity key value registered _ _ entries fallback =>
    exact .mappingValue header identity key value registered entries fallback
  | nil => exact .nil
  | cons _ _ head tail => exact .cons head tail
  | empty => exact .empty _ _ _ _
  | entry _ _ _ key value tail => exact .entry key value tail
  | absent missing projected wf => exact .absent missing projected wf
  | present meaning _ ih => exact .present meaning ih

theorem ValueRep.extend_definitions {checked : SourceCoreCompatibleCatalog.Checked}
    {before after : AmbientDefinitions checked.catalog.definitions} (functions : FunctionModel checked.catalog before)
    (extension : before.definitions.Extends after.definitions)
    {registry : SourceCoreRawMetadata.Registry} {mapping : LocationMap} {world : StoreTyping}
    {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
    (related : ValueRep checked registry functions mapping world sourceType source value type) :
    ValueRep checked registry (functions.extend_definitions extension) mapping world sourceType source value type :=
  ValueRep.map_functions (initial := functions) (future := functions.extend_definitions extension) (fun represented => represented) related

end Solcore.SourceSemantics.CoreLowering.CompatiblePayload
