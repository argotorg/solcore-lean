import Solcore.Frontend.SourceCorePublicOutputShapes
import Solcore.SourceSemantics.CoreLowering.CompatibleConstructorMetadata
import Solcore.SourceSemantics.CoreLowering.CompatibleMappings

/-! Independent payload meaning supplies the public codec's structural output
certificate at the same actual metadata registry. Raw defaults and ordered
mapping rows remain exact; no successful codec call is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePublicOutputShapes
open Core Frontend SourceInference GeneralHeap DataPatternValues CompatiblePayload

private theorem pack_eq (values : List Value) : SourceCorePublicOutputShapes.pack values = packValues values := by
  induction values with
  | nil => rfl
  | cons head tail ih => cases tail with
    | nil => rfl
    | cons second rest => exact congrArg (Value.pair head) ih

private theorem layout_at {checked : SourceCoreCompatibleCatalog.Checked}
    {key value : TypeSystem.Ty} {layout : OrderedMapping.Layout}
    (identity : checked.catalog.identity? (.mapping key value) = some layout.dataType)
    (keyProjection : checked.catalog.project key = .ok layout.keyType)
    (valueProjection : checked.catalog.project value = .ok layout.valueType)
    (registered : layout.Registered checked.catalog.definitions) :
    checked.catalog.mappingLayout key value = .ok layout := by
  simp only [SourceCoreCompatibleCatalog.Catalog.mappingLayout, identity, keyProjection, valueProjection,
    pure, Except.pure, bind, Except.bind]
  have same : (⟨layout.keyType, layout.valueType, layout.dataType⟩ : OrderedMapping.Layout) = layout := by cases layout; rfl
  rw [same]
  simp only [registered.lookup, ↓reduceIte]

variable {checked : SourceCoreCompatibleCatalog.Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions}
  {functions : FunctionModel checked.catalog ambient} {mapping : LocationMap} {world : StoreTyping}

private def Meaning (sourceType : TypeSystem.Ty) (source : Dynamic.Value) (native : Value) : Prop :=
  SourceCorePublicOutputShapes.Output checked registry world ambient.definitions sourceType native ∧
  ∀ raw, DefaultData raw source → ∃ data,
    SourceCoreCompatibleValues.defaultFromSource? raw = some data ∧
    SourceCorePublicOutputShapes.DefaultData checked registry sourceType data native

private theorem represents_shape {sourceType : TypeSystem.Ty} {source : Dynamic.Value}
    {native : Value} {type : Ty}
    (related : ValueRep checked registry functions mapping world sourceType source native type) :
    Meaning (checked := checked) (registry := registry) (ambient := ambient) (world := world) sourceType source native := by
  induction related using ValueRep.rec
    (motive_2 := fun types _ natives _ _ => SourceCorePublicOutputShapes.Payloads checked registry world ambient.definitions types natives)
    (motive_3 := fun key value _ entries _ _ _ => SourceCorePublicOutputShapes.Entries checked registry world ambient.definitions key value entries)
    (motive_4 := fun raw fallback nativeType _ =>
      SourceCorePublicOutputShapes.Default checked registry raw nativeType (OrderedMapping.optionValue nativeType fallback)) with
  | unit => exact ⟨.unit, fun _ data => by cases data; exact ⟨_, rfl, .unit⟩⟩
  | bool value => exact ⟨.bool value, fun _ data => by cases data; exact ⟨_, rfl, .bool _⟩⟩
  | word value => exact ⟨.word value, fun _ data => by cases data; exact ⟨_, rfl, .word _⟩⟩
  | integer value => exact ⟨.integer value, fun _ data => by cases data; exact ⟨_, rfl, .integer _⟩⟩
  | product _ _ first second =>
    refine ⟨.product first.1 second.1, ?_⟩
    intro raw data
    cases data with
    | product left right =>
      obtain ⟨a, firstAt, firstShape⟩ := first.2 _ left
      obtain ⟨b, secondAt, secondShape⟩ := second.2 _ right
      exact ⟨.product a b, by simp only [SourceCoreCompatibleValues.defaultFromSource?, firstAt, secondAt, bind, Option.bind, pure],
        .product firstShape secondShape⟩
  | function represented =>
    refine ⟨.function (functions.projection represented) (functions.runtime_hasType represented), ?_⟩
    intro raw data
    have callable := functions.source_function represented
    cases callable <;> cases data
  | proxy metadata identity _ =>
    exact ⟨.proxy metadata.lookup identity, fun _ data => by cases data; exact ⟨_, rfl, .proxy metadata.lookup identity⟩⟩
  | @constructed metadata id tag sources natives types metadataAt owner selected _ registered payloads ih =>
    have authentic := metadataAt.authenticated
    change SourceCoreRawMetadata.constructorAuthentic registry.signatures metadata = true at authentic
    rw [owner] at authentic
    have resolved : checked.resolveConstructor metadata = .ok tag := by
      simp only [SourceCoreCompatibleCatalog.Checked.resolveConstructor, authentic, selected,
        payloads.projection, registered, ↓reduceIte, pure, Except.pure, bind, Except.bind]
    have nominal : ∃ declaration arguments, metadata.resultType = TypeSystem.Ty.nominal declaration arguments := by
      cases CompatibleConstructorMetadata.facts authentic with
      | mk _ _ _ _ _ _ _ _ result => exact ⟨_, _, result⟩
    refine ⟨?_, fun _ data => by cases data⟩
    simpa only [pack_eq] using SourceCorePublicOutputShapes.Output.constructed metadataAt.lookup resolved nominal ih
  | @mappingValue key value id layout sources entries fallback metadata identity keyProjection valueProjection registered stored _ entriesIH defaultIH =>
    have layoutAt := layout_at identity keyProjection valueProjection registered
    refine ⟨.mapping metadata.lookup layoutAt entriesIH defaultIH, ?_⟩
    intro raw data
    cases data
    cases stored
    exact ⟨_, rfl, .mapping metadata.lookup layoutAt defaultIH⟩
  | compatible same _ ih =>
    refine ⟨.compatible same ih.1, ?_⟩
    intro raw data
    obtain ⟨carrier, projected, shaped⟩ := ih.2 raw data
    exact ⟨carrier, projected, .compatible same shaped⟩
  | nil => exact .nil
  | cons _ _ head tail => exact .cons head.1 tail
  | empty key value _ _ => exact .empty key value
  | entry _ _ _ key value tail => exact .entry key.1 value.1 tail
  | @absent raw nativeType missing _ _ =>
    have absent := (CompatiblePayload.defaultValue?_absent_iff (type := raw) (fuel := raw.size + 1) (by omega)).mpr missing
    exact .absent (by simp only [SourceCoreCompatibleValues.defaultValue?, absent, Option.bind_none])
  | @present raw source native nativeType meaning _ ih =>
    obtain ⟨rawValue, computed, data⟩ := CompatiblePayload.defaultValue?_canonical meaning
    obtain ⟨carrier, projected, shaped⟩ := ih.2 rawValue data
    exact .present (by simp only [SourceCoreCompatibleValues.defaultValue?, computed, Option.bind_some, projected]) shaped

/-- The existing independent relation at the actual boundary registry closes
all structural requirements of the public output codec. -/
theorem ValueRep.output {sourceType : TypeSystem.Ty} {source : Dynamic.Value}
    {native : Value} {type : Ty}
    (related : ValueRep checked registry functions mapping world sourceType source native type) :
    SourceCorePublicOutputShapes.Output checked registry world ambient.definitions sourceType native :=
  (represents_shape related).1

end Solcore.SourceSemantics.CoreLowering.CompatiblePublicOutputShapes
