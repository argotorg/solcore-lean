import Solcore.SourceSemantics.CoreLowering.CompatibleMappingEntries

/-! Inversion of a full compatible mapping value. The extracted fields retain
its original key/value types, exact header, ordered entries, and raw default;
the expected source type remains an explicit compatible view. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMapping
open Core Frontend CompatiblePayload CompatibleEquality

structure Fields (checked : SourceCoreCompatibleCatalog.Checked) (registry : Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) (mapping : GeneralHeap.LocationMap) (world : StoreTyping)
    (sourceKey sourceValue : TypeSystem.Ty) (sources : List (Dynamic.Value × Dynamic.Value))
    (header : Word) (layout : Core.OrderedMapping.Layout) (entries : Core.OrderedMapping.Entries) (fallback : Option Value) : Prop where
  metadata : MetadataRep registry (.mapping sourceKey sourceValue) header
  identity : checked.catalog.identity? (.mapping sourceKey sourceValue) = some layout.dataType
  keyProjection : checked.catalog.project sourceKey = .ok layout.keyType
  valueProjection : checked.catalog.project sourceValue = .ok layout.valueType
  registered : layout.Registered checked.catalog.definitions
  stored : EntriesRep checked registry functions mapping world sourceKey sourceValue sources entries layout.keyType layout.valueType
  default : DefaultRep checked registry functions mapping world sourceValue fallback layout.valueType

 theorem Fields.represents {checked : SourceCoreCompatibleCatalog.Checked} {registry : Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {sourceKey sourceValue : TypeSystem.Ty} {sources : List (Dynamic.Value × Dynamic.Value)}
    {header : Word} {layout : Core.OrderedMapping.Layout} {entries : Core.OrderedMapping.Entries} {fallback : Option Value}
    (fields : Fields checked registry functions mapping world sourceKey sourceValue sources header layout entries fallback) :
    ValueRep checked registry functions mapping world (.mapping sourceKey sourceValue) (.mapping sourceKey sourceValue sources)
      (SourceCoreMappingWithDefault.value header fallback layout entries) (SourceCoreMappingWithDefault.type layout) :=
  .mappingValue fields.metadata fields.identity fields.keyProjection fields.valueProjection fields.registered fields.stored fields.default

 theorem mapping_fields {checked : SourceCoreCompatibleCatalog.Checked} {registry : Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {expected : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
    (related : ValueRep checked registry functions mapping world expected source value type) :
    ∀ {sourceKey sourceValue sources}, source = .mapping sourceKey sourceValue sources →
      ∃ header layout entries fallback,
        value = SourceCoreMappingWithDefault.value header fallback layout entries ∧
        type = SourceCoreMappingWithDefault.type layout ∧
        SourceCoreRawMetadata.runtimeType expected = SourceCoreRawMetadata.runtimeType (.mapping sourceKey sourceValue) ∧
        Fields checked registry functions mapping world sourceKey sourceValue sources header layout entries fallback := by
  induction related using ValueRep.rec
    (motive_2 := fun _ _ _ _ _ => True) (motive_3 := fun _ _ _ _ _ _ _ => True) (motive_4 := fun _ _ _ _ => True) with
  | unit | bool | word | integer | product | proxy | constructed => intro _ _ _ impossible; cases impossible
  | function related =>
    intro _ _ _ impossible
    have shape := functions.source_function related
    cases shape <;> cases impossible
  | mappingValue metadata identity key value registered stored fallback _ _ =>
    intro _ _ _ same
    cases same
    exact ⟨_, _, _, _, rfl, rfl, rfl, ⟨metadata, identity, key, value, registered, stored, fallback⟩⟩
  | compatible same related ih =>
    intro _ _ _ source
    obtain ⟨header, layout, entries, fallback, value, type, view, fields⟩ := ih source
    exact ⟨header, layout, entries, fallback, value, type, same.trans view, fields⟩
  | nil | cons | empty | entry | absent | present => trivial

end Solcore.SourceSemantics.CoreLowering.CompatibleMapping
