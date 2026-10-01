import Solcore.SourceSemantics.CoreLowering.CompatibleMappings
import Solcore.SourceSemantics.CoreLowering.DataPayloadEncoding
import Solcore.Frontend.SourceCoreCompatibleValues

/-! Static facts extracted from the actual compatible catalog and data codec.
The carrier/source carrier relation is the existing independent structural
relation: it carries no strict-catalog assumption and preserves raw metadata
and ordered entries verbatim. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleEncoding
open Core Frontend Frontend.SourceInference GeneralHeap CompatiblePayload
abbrev PublicValue := SourceCoreDataValues.Value
abbrev Means := DataPayloadEncoding.Means
abbrev Meanings := DataPayloadEncoding.Meanings
abbrev EntryMeanings := DataPayloadEncoding.EntryMeanings
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev Registry := SourceCoreRawMetadata.Registry
abbrev Extended := SourceCoreCompatibleValues.Extended

theorem bind_ok {α β ε : Type} {first : Except ε α} {next : α → Except ε β} {value : β}
    (accepted : first >>= next = .ok value) : ∃ input, first = .ok input ∧ next input = .ok value := by
  cases first <;> simp_all [bind, Except.bind]
theorem mapError_ok {α ε δ : Type} {first : Except ε α} {convert : ε → δ} {value : α}
    (accepted : first.mapError convert = .ok value) : first = .ok value := by
  cases first <;> cases accepted
  rfl

/-- Projecting a pure default's data carrier preserves its independent source
value, including every raw proxy/mapping type. -/
theorem defaultData_project {raw : SourceTypedRuntime.Value} {source : Dynamic.Value}
    (related : DefaultData raw source) :
    ∃ carrier, SourceCoreCompatibleValues.defaultFromSource? raw = some carrier ∧ Means carrier source := by
  induction related with
  | unit => exact ⟨_, rfl, .unit⟩
  | bool => exact ⟨_, rfl, .bool _⟩
  | word => exact ⟨_, rfl, .word _⟩
  | integer => exact ⟨_, rfl, .integer _⟩
  | proxy => exact ⟨_, rfl, .proxy _⟩
  | mapping => exact ⟨_, rfl, .mapping .empty⟩
  | product _ _ first second =>
    obtain ⟨a, aProjected, aRelated⟩ := first
    obtain ⟨b, bProjected, bRelated⟩ := second
    exact ⟨_, by simp [SourceCoreCompatibleValues.defaultFromSource?, aProjected, bProjected], .product aRelated bRelated⟩

theorem default_meaning {fuel : Nat} {type : TypeSystem.Ty} {carrier : PublicValue}
    (found : SourceCoreCompatibleValues.defaultValue? fuel type = some carrier) :
    ∃ source, Dynamic.DefaultValue type source ∧ Means carrier source := by
  unfold SourceCoreCompatibleValues.defaultValue? at found
  cases rawFound : SourceTypedRuntime.defaultValue? fuel type with
  | none => simp [rawFound] at found
  | some raw =>
    simp only [rawFound, Option.bind_some] at found
    obtain ⟨source, meaning, data⟩ := CompatiblePayload.defaultValue?_sound rawFound
    obtain ⟨actual, projected, related⟩ := defaultData_project data
    rw [projected] at found
    cases found
    exact ⟨source, meaning, related⟩

theorem mappingLayout_facts {checked : Checked} {key value : TypeSystem.Ty} {layout : OrderedMapping.Layout}
    (accepted : checked.catalog.mappingLayout key value = .ok layout) :
    checked.catalog.identity? (.mapping key value) = some layout.dataType ∧
    checked.catalog.project key = .ok layout.keyType ∧ checked.catalog.project value = .ok layout.valueType ∧
    layout.Registered checked.catalog.definitions := by
  cases selected : checked.catalog.identity? (.mapping key value) with
  | none => simp [SourceCoreCompatibleCatalog.Catalog.mappingLayout, selected, throw, throwThe, bind, Except.bind] at accepted
  | some identity =>
    cases first : checked.catalog.project key with
    | error => simp [SourceCoreCompatibleCatalog.Catalog.mappingLayout, selected, first, pure, Except.pure, bind, Except.bind] at accepted
    | ok keyType =>
      cases second : checked.catalog.project value with
      | error => simp [SourceCoreCompatibleCatalog.Catalog.mappingLayout, selected, first, second, pure, Except.pure, bind, Except.bind] at accepted
      | ok valueType =>
        by_cases registered : checked.catalog.definitions[identity.index]? =
            some (OrderedMapping.Layout.mk keyType valueType identity).definition
        · simp [SourceCoreCompatibleCatalog.Catalog.mappingLayout, selected, first, second, registered,
            pure, Except.pure, bind, Except.bind] at accepted
          subst layout
          have payload : checked.catalog.definitions.lookupConstructorPayloadType? ⟨identity, 1⟩ =
              some (.product (.product keyType valueType) (.namedData identity)) := by
            simp [DataEnvironment.lookupConstructorPayloadType?, DataEnvironment.lookupDataType?, registered,
              OrderedMapping.Layout.definition, OrderedMapping.Layout.type]
          have wf := checked.definitionsTyped.constructorPayloadType_wellFormed payload
          cases wf with
          | product pair tail => cases pair with
            | product a b => exact ⟨rfl, rfl, rfl, a, b, registered⟩
        · simp [SourceCoreCompatibleCatalog.Catalog.mappingLayout, selected, first, second, registered,
            pure, Except.pure, bind, Except.bind, throw, throwThe] at accepted

theorem mapping_project {catalog : SourceCoreCompatibleCatalog.Catalog} {key value : TypeSystem.Ty} {layout : OrderedMapping.Layout}
    (selected : catalog.identity? (.mapping key value) = some layout.dataType)
    (first : catalog.project key = .ok layout.keyType) (second : catalog.project value = .ok layout.valueType) :
    catalog.project (.mapping key value) = .ok (SourceCoreMappingWithDefault.type layout) := by
  simp [SourceCoreCompatibleCatalog.Catalog.project, selected, first, second, bind, Except.bind, pure, Except.pure]

theorem project_compatible {catalog : SourceCoreCompatibleCatalog.Catalog} {a b : TypeSystem.Ty}
    (same : SourceCoreRawMetadata.runtimeType a = SourceCoreRawMetadata.runtimeType b) :
    catalog.project a = catalog.project b := by
  rw [← catalog.project_runtimeType a, ← catalog.project_runtimeType b, same]

theorem identity_compatible {catalog : SourceCoreCompatibleCatalog.Catalog} {a b : TypeSystem.Ty}
    (same : SourceCoreRawMetadata.runtimeType a = SourceCoreRawMetadata.runtimeType b) :
    catalog.identity? a = catalog.identity? b := by
  simp only [SourceCoreCompatibleCatalog.Catalog.identity?, same]

/-- The real constructor resolver supplies its exact registered native field
layout. Registry authenticity and expected-type compatibility remain separate. -/
theorem resolveConstructor_facts {checked : Checked} {metadata : DataConstructorInstantiation} {tag : ConstructorId}
    (accepted : checked.resolveConstructor metadata = .ok tag) :
    checked.catalog.constructor? metadata = some tag ∧ ∃ types,
      metadata.payloadTypes.mapM checked.catalog.project = .ok types ∧
      checked.catalog.definitions.lookupConstructorPayloadType? tag =
        some (.product .word (SourceCoreCompatibleCatalog.packTypes types)) := by
  by_cases authentic : SourceCoreRawMetadata.constructorAuthentic checked.signatures metadata = true
  · cases selected : checked.catalog.constructor? metadata with
    | none => simp [SourceCoreCompatibleCatalog.Checked.resolveConstructor, authentic, selected, pure, Except.pure, bind, Except.bind, throw, throwThe] at accepted
    | some constructor =>
      cases projected : metadata.payloadTypes.mapM checked.catalog.project with
      | error => simp [SourceCoreCompatibleCatalog.Checked.resolveConstructor, authentic, selected, projected, pure, Except.pure, bind, Except.bind] at accepted
      | ok types =>
        by_cases registered : checked.catalog.definitions.lookupConstructorPayloadType? constructor =
            some (.product .word (SourceCoreCompatibleCatalog.packTypes types))
        · simp [SourceCoreCompatibleCatalog.Checked.resolveConstructor, authentic, selected, projected, registered, pure, Except.pure, bind, Except.bind] at accepted
          subst tag
          exact ⟨rfl, types, rfl, registered⟩
        · simp [SourceCoreCompatibleCatalog.Checked.resolveConstructor, authentic, selected, projected, registered, pure, Except.pure, bind, Except.bind, throw, throwThe] at accepted
  · simp [SourceCoreCompatibleCatalog.Checked.resolveConstructor, authentic, pure, Except.pure, bind, Except.bind, throw, throwThe] at accepted

end Solcore.SourceSemantics.CoreLowering.CompatibleEncoding
