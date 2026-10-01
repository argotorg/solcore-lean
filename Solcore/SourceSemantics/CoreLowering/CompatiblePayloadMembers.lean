import Solcore.SourceSemantics.CoreLowering.CompatibleMappingView
import Solcore.SourceSemantics.Dynamic.Place

/-! Full compatible constructor payload selection and replacement. Original
constructor metadata and its raw ID remain unchanged, as do every sibling and
nested mapping/default carrier. No evaluation or comparison premise occurs. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePayload
open Core Frontend SourceInference GeneralHeap DataPatternValues
variable {checked : SourceCoreCompatibleCatalog.Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {mapping : LocationMap} {world : StoreTyping}

theorem ValuesRep.at {types : List TypeSystem.Ty} {sources : List Dynamic.Value} {values : List Value} {coreTypes : List Ty}
    (represented : ValuesRep checked registry functions mapping world types sources values coreTypes)
    {index : Nat} {type : TypeSystem.Ty} (lookup : types[index]? = some type) :
    ∃ source value coreType, Dynamic.ValueAt sources index source ∧ values[index]? = some value ∧
      coreTypes[index]? = some coreType ∧ ValueRep checked registry functions mapping world type source value coreType := by
  induction types generalizing sources values coreTypes index with
  | nil => simp at lookup
  | cons head tail ih => cases represented with
    | cons first rest => cases index with
      | zero => cases lookup; exact ⟨_, _, _, .head, rfl, rfl, first⟩
      | succ index =>
        obtain ⟨source, value, type, selected, found, typed, represented⟩ := ih rest lookup
        exact ⟨source, value, type, .tail selected, found, typed, represented⟩

theorem ValuesRep.replace {types : List TypeSystem.Ty} {sources : List Dynamic.Value} {values : List Value} {coreTypes : List Ty}
    (represented : ValuesRep checked registry functions mapping world types sources values coreTypes)
    {index : Nat} {type : TypeSystem.Ty} {coreType : Ty} (lookup : types[index]? = some type)
    (coreLookup : coreTypes[index]? = some coreType)
    {source : Dynamic.Value} {value : Value}
    (replacement : ValueRep checked registry functions mapping world type source value coreType) :
    ValuesRep checked registry functions mapping world types (sources.set index source) (values.set index value) coreTypes := by
  induction types generalizing sources values coreTypes index with
  | nil => simp at lookup
  | cons head tail ih => cases represented with
    | cons first rest => cases index with
      | zero => cases lookup; cases coreLookup; exact .cons replacement rest
      | succ index => exact .cons first (ih rest lookup coreLookup)

theorem ValuesRep.projection {types : List TypeSystem.Ty} {sources : List Dynamic.Value} {values : List Value} {coreTypes : List Ty}
    (represented : ValuesRep checked registry functions mapping world types sources values coreTypes) :
    types.mapM checked.catalog.project = .ok coreTypes := by
  induction types generalizing sources values coreTypes with
  | nil => cases represented; rfl
  | cons head tail ih => cases represented with
    | cons first rest => simp [List.mapM_cons, first.projection, ih rest, bind, Except.bind]

structure ConstructorFields (checked : SourceCoreCompatibleCatalog.Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) (mapping : LocationMap) (world : StoreTyping)
    (expected : TypeSystem.Ty) (metadata : DataConstructorInstantiation) (tag : ConstructorId) (id : Word)
    (sources : List Dynamic.Value) (values : List Value) (types : List Ty) : Prop where
  metadataRep : MetadataRep registry (.constructor metadata) id
  registryOwner : registry.signatures = checked.signatures
  selected : checked.catalog.constructor? metadata = some tag
  projected : checked.catalog.project metadata.resultType = .ok (.namedData tag.owner)
  registered : checked.catalog.definitions.lookupConstructorPayloadType? tag =
    some (.product .word (SourceCoreCompatibleCatalog.packTypes types))
  payloads : ValuesRep checked registry functions mapping world metadata.payloadTypes sources values types
  view : SourceCoreRawMetadata.runtimeType expected = SourceCoreRawMetadata.runtimeType metadata.resultType

theorem ConstructorFields.represents {expected : TypeSystem.Ty} {metadata : DataConstructorInstantiation}
    {tag : ConstructorId} {id : Word} {sources : List Dynamic.Value} {values : List Value} {types : List Ty}
    (fields : ConstructorFields checked registry functions mapping world expected metadata tag id sources values types) :
    ValueRep checked registry functions mapping world expected (.constructed metadata sources)
      (.constructed tag (.pair (.word id) (packValues values))) (.namedData tag.owner) :=
  .compatible fields.view (.constructed fields.metadataRep fields.registryOwner fields.selected fields.projected fields.registered fields.payloads)

theorem ConstructorFields.resolved {expected : TypeSystem.Ty} {metadata : DataConstructorInstantiation}
    {tag : ConstructorId} {id : Word} {sources : List Dynamic.Value} {values : List Value} {types : List Ty}
    (fields : ConstructorFields checked registry functions mapping world expected metadata tag id sources values types) :
    checked.resolveConstructor metadata = .ok tag := by
  have authentic := constructor_authenticated fields.metadataRep fields.registryOwner
  simp [SourceCoreCompatibleCatalog.Checked.resolveConstructor, authentic, fields.selected, fields.payloads.projection, fields.registered, bind, Except.bind, pure, Except.pure]

theorem ConstructorFields.replace {expected : TypeSystem.Ty} {metadata : DataConstructorInstantiation}
    {tag : ConstructorId} {id : Word} {sources : List Dynamic.Value} {values : List Value} {types : List Ty}
    (fields : ConstructorFields checked registry functions mapping world expected metadata tag id sources values types)
    {index : Nat} {sourceType : TypeSystem.Ty} {type : Ty}
    (sourceAt : metadata.payloadTypes[index]? = some sourceType) (typeAt : types[index]? = some type)
    {source : Dynamic.Value} {value : Value}
    (replacement : ValueRep checked registry functions mapping world sourceType source value type) :
    ConstructorFields checked registry functions mapping world expected metadata tag id (sources.set index source) (values.set index value) types :=
  { fields with payloads := fields.payloads.replace sourceAt typeAt replacement }

theorem constructor_fields {expected : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
    (related : ValueRep checked registry functions mapping world expected source value type) :
    ∀ {metadata sources}, source = .constructed metadata sources →
      ∃ tag id values types,
        value = .constructed tag (.pair (.word id) (packValues values)) ∧ type = .namedData tag.owner ∧
        ConstructorFields checked registry functions mapping world expected metadata tag id sources values types := by
  induction related using ValueRep.rec
    (motive_2 := fun _ _ _ _ _ => True) (motive_3 := fun _ _ _ _ _ _ _ => True) (motive_4 := fun _ _ _ _ => True) with
  | unit | bool | word | integer | product | proxy | mappingValue => intro _ _ impossible; cases impossible
  | function related =>
    intro _ _ impossible
    have shape := functions.source_function related
    cases shape <;> cases impossible
  | constructed metadata owner selected projected registered payloads _ =>
    intro _ _ same
    cases same
    exact ⟨_, _, _, _, rfl, rfl, ⟨metadata, owner, selected, projected, registered, payloads, rfl⟩⟩
  | compatible same related ih =>
    intro _ _ source
    obtain ⟨tag, id, values, types, value, type, fields⟩ := ih source
    exact ⟨tag, id, values, types, value, type, { fields with view := same.trans fields.view }⟩
  | nil | cons | empty | entry | absent | present => trivial

end Solcore.SourceSemantics.CoreLowering.CompatiblePayload
