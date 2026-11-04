import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.Payloads
import Solcore.SourceSemantics.CoreLowering.Internal.Data.Payloads
import Solcore.Frontend.SourceCoreCompatibleValues

/-!
# Compatible profile: encoding

The compiler's encoder against the independent payload relation of `Compatible/Payloads`: encoding facts, its induction, leaves and mappings, and the ambient encoding.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleEncodingFacts
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleEncodingInduction
/-! Induction interfaces and list/default steps for the actual compatible
encoder. These steps will be closed by induction on its fuel; they never
substitute a second encoder for the executable implementation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleEncoding
open Core Frontend Frontend.SourceInference GeneralHeap CompatiblePayload DataPatternValues
open SourceCoreCompatibleValues (encodeRaw encodePayloadsRaw encodeEntriesRaw encodeDefaultRaw)

variable (checked : Checked) (functions : FunctionModel checked.catalog) (mapping : LocationMap) (world : StoreTyping)

def RawSound (fuel : Nat) : Prop := ∀ (registry : Registry), registry.signatures = checked.signatures →
  ∀ expected carrier (encoded : Extended registry Value) type,
    encodeRaw fuel checked registry expected carrier = .ok encoded →
    checked.catalog.project expected = .ok type →
    RuntimeValueHasType world encoded.value type checked.catalog.definitions →
    ∃ source, Means carrier source ∧ ValueRep checked encoded.registry functions mapping world expected source encoded.value type

def PayloadSound (fuel : Nat) : Prop := ∀ (registry : Registry), registry.signatures = checked.signatures →
  ∀ types carriers index (encoded : Extended registry Value) coreTypes,
    encodePayloadsRaw fuel checked registry types carriers index = .ok encoded →
    types.mapM checked.catalog.project = .ok coreTypes →
    RuntimeValueHasType world encoded.value (SourceCoreCompatibleCatalog.packTypes coreTypes) checked.catalog.definitions →
    ∃ sources values, Meanings carriers sources ∧ ValuesRep checked encoded.registry functions mapping world types sources values coreTypes ∧
      encoded.value = packValues values

def EntriesSound (fuel : Nat) : Prop := ∀ (registry : Registry), registry.signatures = checked.signatures →
  ∀ keyType valueType layout carriers index (encoded : Extended registry Value),
    encodeEntriesRaw fuel checked registry keyType valueType layout carriers index = .ok encoded →
    checked.catalog.project keyType = .ok layout.keyType → checked.catalog.project valueType = .ok layout.valueType →
    layout.Registered checked.catalog.definitions →
    RuntimeValueHasType world encoded.value layout.type checked.catalog.definitions →
    ∃ sources entries, EntryMeanings carriers sources ∧
      EntriesRep checked encoded.registry functions mapping world keyType valueType sources entries layout.keyType layout.valueType ∧
      encoded.value = OrderedMapping.encode layout entries

variable {checked functions mapping world}

theorem default_sound {fuel : Nat} (induction : RawSound checked functions mapping world fuel)
    {registry : Registry} (owner : registry.signatures = checked.signatures)
    {sourceType : TypeSystem.Ty} {type : Ty} {encoded : Extended registry Value}
    (accepted : encodeDefaultRaw fuel checked registry sourceType type = .ok encoded)
    (projected : checked.catalog.project sourceType = .ok type) (wf : type.WellFormed checked.catalog.definitions)
    (typed : RuntimeValueHasType world encoded.value (.sum .unit type) checked.catalog.definitions) :
    ∃ fallback, encoded.value = OrderedMapping.optionValue type fallback ∧
      DefaultRep checked encoded.registry functions mapping world sourceType fallback type := by
  cases found : SourceCoreCompatibleValues.defaultValue? (sourceType.size + 1) sourceType with
  | none =>
    simp only [encodeDefaultRaw, found, pure, Except.pure] at accepted
    cases accepted
    exact ⟨none, rfl, .absent ((CompatiblePayload.defaultValue?_absent_iff (by omega)).mp
      ((SourceCoreCompatibleValues.defaultValue?_absent_iff _ _).mp found)) projected wf⟩
  | some carrier =>
    simp only [encodeDefaultRaw, found] at accepted
    obtain ⟨inner, generated, accepted⟩ := bind_ok accepted
    cases accepted
    cases typed with
    | inRight typed =>
      obtain ⟨source, means, related⟩ := induction registry owner sourceType carrier inner type generated projected typed
      obtain ⟨actual, meaning, actualMeans⟩ := default_meaning found
      have same := means.functional actualMeans
      subst actual
      exact ⟨some inner.value, rfl, .present meaning related⟩

/-- Child payload representations can be transported across later registry
allocations without changing their source values or native bytes. -/
theorem values_extend {registry future : Registry} {types : List TypeSystem.Ty} {sources : List Dynamic.Value}
    {values : List Value} {coreTypes : List Ty}
    (related : ValuesRep checked registry functions mapping world types sources values coreTypes)
    (extension : SourceCoreRawMetadata.Extends registry future) :
    ValuesRep checked future functions mapping world types sources values coreTypes := by
  induction types generalizing sources values coreTypes with
  | nil => cases related; exact .nil
  | cons type types ih => cases related with
    | cons head tail => exact .cons (head.extend extension ⟨[], by simp⟩ ⟨[], by simp⟩) (ih tail)

theorem payload_zero : PayloadSound checked functions mapping world 0 := by
  intro registry owner types carriers index encoded coreTypes accepted projected typed
  cases types with
  | nil => cases carriers with
    | nil =>
      simp [encodePayloadsRaw] at accepted
      subst encoded
      cases projected
      exact ⟨[], [], .nil, .nil, rfl⟩
    | cons => simp [encodePayloadsRaw, bind, Except.bind, throw, throwThe] at accepted
  | cons head tail =>
    simp only [encodePayloadsRaw] at accepted
    split at accepted <;> simp_all [pure, Except.pure, bind, Except.bind, throw, throwThe]

theorem entries_zero : EntriesSound checked functions mapping world 0 := by
  intro registry owner keyType valueType layout carriers index encoded accepted first second registered typed
  cases carriers with
  | nil => simp only [encodeEntriesRaw, pure, Except.pure] at accepted; cases accepted; exact ⟨[], [], .empty, .empty _ _ _ _, rfl⟩
  | cons => simp [encodeEntriesRaw, throw, throwThe] at accepted

/-- The actual ordered-list encoder consumes keys and values in their stored
order, then extends earlier metadata receipts across the remaining entries. -/
theorem entries_succ {fuel : Nat} (raw : RawSound checked functions mapping world fuel)
    (tail : EntriesSound checked functions mapping world fuel) :
    EntriesSound checked functions mapping world (fuel + 1) := by
  intro registry owner keyType valueType layout carriers index encoded accepted first second registered typed
  cases carriers with
  | nil => simp only [encodeEntriesRaw, pure, Except.pure] at accepted; cases accepted; exact ⟨[], [], .empty, .empty _ _ _ _, rfl⟩
  | cons entry rest =>
    rcases entry with ⟨key, value⟩
    simp only [encodeEntriesRaw] at accepted
    obtain ⟨keyEncoded, keyAccepted, accepted⟩ := bind_ok accepted
    obtain ⟨valueEncoded, valueAccepted, accepted⟩ := bind_ok accepted
    obtain ⟨restEncoded, restAccepted, accepted⟩ := bind_ok accepted
    cases accepted
    cases typed with
    | constructed lookup payloadTyped =>
      have same := Option.some.inj (lookup.symm.trans registered.consLookup)
      subst_vars
      cases payloadTyped with
      | pair entryTyped restTyped => cases entryTyped with
        | pair keyTyped valueTyped =>
          obtain ⟨sourceKey, keyMeans, keyRep⟩ := raw registry owner _ _ _ _ (mapError_ok keyAccepted) first keyTyped
          obtain ⟨sourceValue, valueMeans, valueRep⟩ := raw keyEncoded.registry (keyEncoded.preserves.signatures.trans owner)
            _ _ _ _ (mapError_ok valueAccepted) second valueTyped
          obtain ⟨sources, entries, restMeans, restRep, encoding⟩ := tail valueEncoded.registry
            (valueEncoded.preserves.signatures.trans (keyEncoded.preserves.signatures.trans owner))
            _ _ _ _ _ _ restAccepted first second registered restTyped
          exact ⟨(sourceKey, sourceValue) :: sources, (keyEncoded.value, valueEncoded.value) :: entries,
            .prepend keyMeans valueMeans restMeans,
            .entry (keyRep.extend (valueEncoded.preserves.trans restEncoded.preserves) ⟨[], by simp⟩ ⟨[], by simp⟩)
              (valueRep.extend restEncoded.preserves ⟨[], by simp⟩ ⟨[], by simp⟩) restRep,
            by simp [OrderedMapping.encode, encoding]⟩

theorem project_cons {head : TypeSystem.Ty} {tail : List TypeSystem.Ty} {types : List Ty}
    (projected : (head :: tail).mapM checked.catalog.project = .ok types) :
    ∃ type rest, checked.catalog.project head = .ok type ∧ tail.mapM checked.catalog.project = .ok rest ∧ types = type :: rest := by
  cases first : checked.catalog.project head with
  | error => simp [List.mapM_cons, first, bind, Except.bind] at projected
  | ok type =>
    cases remaining : tail.mapM checked.catalog.project with
    | error => simp [List.mapM_cons, first, remaining, bind, Except.bind] at projected
    | ok rest =>
      simp [List.mapM_cons, first, remaining, bind, Except.bind] at projected
      subst types
      exact ⟨type, rest, rfl, rfl, rfl⟩

theorem payload_succ {fuel : Nat} (raw : RawSound checked functions mapping world fuel)
    (tail : PayloadSound checked functions mapping world fuel) :
    PayloadSound checked functions mapping world (fuel + 1) := by
  intro registry owner types carriers index encoded coreTypes accepted projected typed
  by_cases length : types.length = carriers.length
  · cases types with
    | nil => cases carriers with
      | nil =>
        simp [encodePayloadsRaw] at accepted
        subst encoded
        cases projected
        exact ⟨[], [], .nil, .nil, rfl⟩
      | cons => simp at length
    | cons type types => cases carriers with
      | nil => simp at length
      | cons carrier carriers =>
        obtain ⟨coreType, remainingTypes, firstProjection, remainingProjection, rfl⟩ := project_cons projected
        cases types with
        | nil =>
          have empty : carriers = [] := by simpa using length.symm
          subst carriers
          cases remainingProjection
          simp only [encodePayloadsRaw, length, ↓reduceIte] at accepted
          obtain ⟨source, means, represented⟩ := raw registry owner _ _ _ _ (mapError_ok accepted) firstProjection typed
          exact ⟨[source], [encoded.value], .cons means .nil, .cons represented .nil, rfl⟩
        | cons next types =>
          obtain ⟨nextType, restTypes, nextProjection, restProjection, rfl⟩ := project_cons remainingProjection
          simp only [encodePayloadsRaw, length, ↓reduceIte] at accepted
          obtain ⟨first, firstAccepted, accepted⟩ := bind_ok accepted
          obtain ⟨rest, restAccepted, accepted⟩ := bind_ok accepted
          cases accepted
          cases typed with
          | pair firstTyped restTyped =>
            obtain ⟨source, means, represented⟩ := raw registry owner _ _ _ _ (mapError_ok firstAccepted) firstProjection firstTyped
            obtain ⟨sources, values, meanings, representations, packing⟩ := tail first.registry
              (first.preserves.signatures.trans owner) _ _ _ _ _ restAccepted remainingProjection restTyped
            cases values with
            | nil => cases representations
            | cons head values =>
              exact ⟨source :: sources, first.value :: head :: values, .cons means meanings,
                .cons (represented.extend rest.preserves ⟨[], by simp⟩ ⟨[], by simp⟩) representations,
                by simp only [packValues]; rw [packing]⟩
  · unfold encodePayloadsRaw at accepted
    simp [length, bind, Except.bind, throw, throwThe] at accepted

end Solcore.SourceSemantics.CoreLowering.CompatibleEncoding
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleEncodingLeaves
/-! Scalar, product, proxy and constructor cases of the actual compatible
encoder. Core typing is used only to recover native layout facts; source
metadata authenticity comes from the actual owning registry receipts. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleEncoding
open Core Frontend Frontend.SourceInference GeneralHeap CompatiblePayload DataPatternValues
open SourceCoreCompatibleValues (encodeRaw encodePayloadsRaw encodeEntriesRaw encodeDefaultRaw)
variable {checked : Checked} {functions : FunctionModel checked.catalog} {mapping : LocationMap} {world : StoreTyping}

theorem runtime_view {expected normalized : TypeSystem.Ty}
    (erased : SourceCoreRawMetadata.runtimeType expected = normalized) :
    SourceCoreRawMetadata.runtimeType expected = SourceCoreRawMetadata.runtimeType normalized := by
  rw [← erased, SourceCoreRawMetadata.runtimeType_idempotent]

theorem product_projection {expected left right : TypeSystem.Ty} {type : Ty}
    (erased : SourceCoreRawMetadata.runtimeType expected = .product left right)
    (projected : checked.catalog.project expected = .ok type) :
    ∃ a b, checked.catalog.project left = .ok a ∧ checked.catalog.project right = .ok b ∧ type = .product a b := by
  rw [← checked.catalog.project_runtimeType expected, erased] at projected
  cases first : checked.catalog.project left with
  | error => simp [SourceCoreCompatibleCatalog.Catalog.project, first, bind, Except.bind] at projected
  | ok a => cases second : checked.catalog.project right with
    | error => simp [SourceCoreCompatibleCatalog.Catalog.project, first, second, bind, Except.bind] at projected
    | ok b =>
      simp [SourceCoreCompatibleCatalog.Catalog.project, first, second, bind, Except.bind, pure, Except.pure] at projected
      exact ⟨a, b, rfl, rfl, projected.symm⟩

theorem product_sound {fuel : Nat} (induction : RawSound checked functions mapping world fuel)
    {registry : Registry} (owner : registry.signatures = checked.signatures)
    {expected leftType rightType : TypeSystem.Ty} {left right : PublicValue} {encoded : Extended registry Value} {type : Ty}
    (erased : SourceCoreRawMetadata.runtimeType expected = .product leftType rightType)
    (accepted : encodeRaw (fuel + 1) checked registry expected (.product left right) = .ok encoded)
    (projected : checked.catalog.project expected = .ok type)
    (typed : RuntimeValueHasType world encoded.value type checked.catalog.definitions) :
    ∃ source, Means (.product left right) source ∧ ValueRep checked encoded.registry functions mapping world expected source encoded.value type := by
  unfold encodeRaw at accepted
  rw [erased] at accepted
  obtain ⟨first, firstAccepted, accepted⟩ := bind_ok accepted
  obtain ⟨second, secondAccepted, accepted⟩ := bind_ok accepted
  cases accepted
  obtain ⟨a, b, firstProjection, secondProjection, rfl⟩ := product_projection erased projected
  cases typed with
  | pair firstTyped secondTyped =>
    obtain ⟨aSource, firstMeans, firstRep⟩ := induction registry owner _ _ _ _ (mapError_ok firstAccepted) firstProjection firstTyped
    obtain ⟨bSource, secondMeans, secondRep⟩ := induction first.registry (first.preserves.signatures.trans owner)
      _ _ _ _ (mapError_ok secondAccepted) secondProjection secondTyped
    exact ⟨_, .product firstMeans secondMeans, .compatible (runtime_view erased)
      (.product (firstRep.extend second.preserves ⟨[], by simp⟩ ⟨[], by simp⟩) secondRep)⟩

theorem proxy_sound {fuel : Nat} {registry : Registry}
    {expected inner actual : TypeSystem.Ty} {encoded : Extended registry Value} {type : Ty}
    (erased : SourceCoreRawMetadata.runtimeType expected = .proxy inner)
    (accepted : encodeRaw (fuel + 1) checked registry expected (.proxy actual) = .ok encoded)
    (typed : RuntimeValueHasType world encoded.value type checked.catalog.definitions) :
    ∃ source, Means (.proxy actual) source ∧ ValueRep checked encoded.registry functions mapping world expected source encoded.value type := by
  unfold encodeRaw at accepted
  rw [erased] at accepted
  obtain ⟨registered, registeredAccepted, accepted⟩ := bind_ok accepted
  obtain ⟨identity, identityAccepted, accepted⟩ := bind_ok accepted
  cases accepted
  have selected : checked.catalog.identity? expected = some identity := by
    change (match checked.catalog.identity? expected with | some id => Except.ok id | none => Except.error _) =
      (Except.ok identity : Except SourceCoreCompatibleValues.Error DataTypeId) at identityAccepted
    cases found : checked.catalog.identity? expected <;> simp [found] at identityAccepted
    subst identity
    rfl
  cases typed with
  | constructed payloadLookup payloadTyped =>
    cases payloadTyped
    have actualIdentity : checked.catalog.identity? (.proxy actual) = some identity :=
      (identity_compatible registered.runtime_compatible).symm.trans selected
    exact ⟨_, .proxy _, .compatible registered.runtime_compatible
      (.proxy ⟨registered.reconstruct⟩ actualIdentity payloadLookup)⟩

/-- Constructor encoding uses the exact signature-authenticated metadata,
while compatibility changes only its expected type view. -/
theorem constructed_sound {fuel : Nat} (induction : PayloadSound checked functions mapping world fuel)
    {registry : Registry} (owner : registry.signatures = checked.signatures)
    {expected : TypeSystem.Ty} {metadata : DataConstructorInstantiation} {carriers : List PublicValue}
    {encoded : Extended registry Value} {type : Ty}
    (accepted : encodeRaw (fuel + 1) checked registry expected (.constructed metadata carriers) = .ok encoded)
    (projected : checked.catalog.project expected = .ok type)
    (typed : RuntimeValueHasType world encoded.value type checked.catalog.definitions) :
    ∃ source, Means (.constructed metadata carriers) source ∧ ValueRep checked encoded.registry functions mapping world expected source encoded.value type := by
  have step : ∀ (inserted : SourceCoreRawMetadata.Inserted registry expected (.constructor metadata))
      tag (payloads : Extended inserted.registry Value),
      checked.resolveConstructor metadata = .ok tag →
      encodePayloadsRaw fuel checked inserted.registry metadata.payloadTypes carriers 0 = .ok payloads →
      ∀ type, checked.catalog.project expected = .ok type →
      RuntimeValueHasType world (.constructed tag (.pair (.word inserted.id) payloads.value)) type checked.catalog.definitions →
      ∃ source, Means (.constructed metadata carriers) source ∧
        ValueRep checked payloads.registry functions mapping world expected source
          (.constructed tag (.pair (.word inserted.id) payloads.value)) type := by
    intro inserted tag payloads resolved payloadsAccepted type projected typed
    obtain ⟨selected, types, projections, registered⟩ := resolveConstructor_facts resolved
    cases typed with
    | constructed lookup payloadTyped =>
      have same := Option.some.inj (lookup.symm.trans registered)
      subst_vars
      cases payloadTyped with
      | pair headerTyped fieldsTyped =>
        obtain ⟨sources, values, meanings, related, packed⟩ := induction inserted.registry
          (inserted.preserves.signatures.trans owner) _ _ _ _ _ payloadsAccepted projections fieldsTyped
        have resultProjection : checked.catalog.project metadata.resultType = .ok (.namedData tag.owner) :=
          (project_compatible inserted.runtime_compatible).symm.trans projected
        refine ⟨_, .constructed meanings, .compatible inserted.runtime_compatible ?_⟩
        rw [packed]
        exact .constructed (⟨payloads.preserves.lookup inserted.reconstruct⟩)
          (payloads.preserves.signatures.trans (inserted.preserves.signatures.trans owner)) selected resultProjection registered related
  cases erased : SourceCoreRawMetadata.runtimeType expected <;>
    (unfold encodeRaw at accepted; rw [erased] at accepted)
  case function => cases accepted
  case constructor id =>
    cases id <;> (try (rename_i builtin; cases builtin))
    all_goals
      obtain ⟨inserted, _, accepted⟩ := bind_ok accepted
      obtain ⟨tag, resolved, accepted⟩ := bind_ok accepted
      obtain ⟨payloads, payloadsAccepted, accepted⟩ := bind_ok accepted
      cases accepted
      exact step inserted tag payloads (mapError_ok resolved) payloadsAccepted _ projected typed
  all_goals
    obtain ⟨inserted, _, accepted⟩ := bind_ok accepted
    obtain ⟨tag, resolved, accepted⟩ := bind_ok accepted
    obtain ⟨payloads, payloadsAccepted, accepted⟩ := bind_ok accepted
    cases accepted
    exact step inserted tag payloads (mapError_ok resolved) payloadsAccepted _ projected typed

end Solcore.SourceSemantics.CoreLowering.CompatibleEncoding
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleEncodingMapping
/-! The actual mapping encoder preserves the raw header, every ordered entry,
and the default denoted by the header's original value type. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleEncoding
open Core Frontend GeneralHeap CompatiblePayload
open SourceCoreCompatibleValues (encodeRaw)
variable {checked : Checked} {functions : FunctionModel checked.catalog} {mapping : LocationMap} {world : StoreTyping}

theorem mapping_sound {fuel : Nat} (raw : RawSound checked functions mapping world fuel)
    (entriesSound : EntriesSound checked functions mapping world fuel)
    {registry : Registry} (owner : registry.signatures = checked.signatures)
    {expected keyType valueType actualKey actualValue : TypeSystem.Ty} {carriers : List (PublicValue × PublicValue)}
    {encoded : Extended registry Value} {type : Ty}
    (erased : SourceCoreRawMetadata.runtimeType expected = .mapping keyType valueType)
    (accepted : encodeRaw (fuel + 1) checked registry expected (.mapping actualKey actualValue carriers) = .ok encoded)
    (projected : checked.catalog.project expected = .ok type)
    (typed : RuntimeValueHasType world encoded.value type checked.catalog.definitions) :
    ∃ source, Means (.mapping actualKey actualValue carriers) source ∧
      ValueRep checked encoded.registry functions mapping world expected source encoded.value type := by
  unfold encodeRaw at accepted
  rw [erased] at accepted
  obtain ⟨inserted, _, accepted⟩ := bind_ok accepted
  obtain ⟨layout, layoutAccepted, accepted⟩ := bind_ok accepted
  obtain ⟨entries, entriesAccepted, accepted⟩ := bind_ok accepted
  obtain ⟨fallback, fallbackAccepted, accepted⟩ := bind_ok accepted
  cases accepted
  obtain ⟨selected, first, second, registered⟩ := mappingLayout_facts (mapError_ok layoutAccepted)
  have normalizedProjection := mapping_project selected first second
  have expectedProjection : checked.catalog.project expected = .ok (SourceCoreMappingWithDefault.type layout) := by
    rw [← checked.catalog.project_runtimeType expected, erased]
    exact normalizedProjection
  have typeEq := Except.ok.inj (projected.symm.trans expectedProjection)
  subst type
  have headerCompatible := inserted.runtime_compatible
  have components : keyType = SourceCoreRawMetadata.runtimeType actualKey ∧ valueType = SourceCoreRawMetadata.runtimeType actualValue := by
    rw [erased] at headerCompatible
    exact TypeSystem.Ty.mapping.inj headerCompatible
  have actualFirst : checked.catalog.project actualKey = .ok layout.keyType := by
    rw [← checked.catalog.project_runtimeType actualKey, ← components.1]
    exact first
  have actualSecond : checked.catalog.project actualValue = .ok layout.valueType := by
    rw [← checked.catalog.project_runtimeType actualValue, ← components.2]
    exact second
  have actualSelected : checked.catalog.identity? (.mapping actualKey actualValue) = some layout.dataType :=
    (identity_compatible ((runtime_view erased).symm.trans inserted.runtime_compatible)).symm.trans selected
  cases typed with
  | pair headerTyped restTyped => cases restTyped with
    | pair fallbackTyped entriesTyped =>
      obtain ⟨sources, values, meanings, stored, storedEq⟩ := entriesSound inserted.registry
        (inserted.preserves.signatures.trans owner) _ _ _ _ _ _ entriesAccepted actualFirst actualSecond registered entriesTyped
      obtain ⟨default, defaultEq, defaultRep⟩ := default_sound raw
        (entries.preserves.signatures.trans (inserted.preserves.signatures.trans owner))
        fallbackAccepted actualSecond registered.valueWellFormed fallbackTyped
      refine ⟨_, .mapping meanings, .compatible inserted.runtime_compatible ?_⟩
      rw [storedEq, defaultEq]
      exact .mappingValue ⟨fallback.preserves.lookup (entries.preserves.lookup inserted.reconstruct)⟩
        actualSelected actualFirst actualSecond registered
        (stored.extend fallback.preserves ⟨[], by simp⟩ ⟨[], by simp⟩) defaultRep

end Solcore.SourceSemantics.CoreLowering.CompatibleEncoding
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleEncoding
/-! Successful execution of the actual compatible encoder produces the
independent source/native representation. The induction follows its real
fuel and registry extensions. Public encoding supplies the final native
shape validation; native typing alone never authenticates source metadata. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleEncoding
open Core Frontend Frontend.SourceInference GeneralHeap CompatiblePayload
open SourceCoreCompatibleValues (encodeRaw)
variable {checked : Checked} {functions : FunctionModel checked.catalog} {mapping : LocationMap} {world : StoreTyping}

private theorem unit_sound {fuel : Nat} {registry : Registry} {expected : TypeSystem.Ty}
     {encoded : Extended registry Value} {type : Ty}
    (accepted : encodeRaw (fuel + 1) checked registry expected .unit = .ok encoded)
    (typed : RuntimeValueHasType world encoded.value type checked.catalog.definitions) :
    ∃ source, Means .unit source ∧ ValueRep checked encoded.registry functions mapping world expected source encoded.value type := by
  cases erased : SourceCoreRawMetadata.runtimeType expected <;>
    (unfold encodeRaw at accepted; rw [erased] at accepted)
  all_goals try (solve | cases accepted)
  case constructor id =>
    cases id with
    | declaration => cases accepted
    | builtin builtin =>
      cases builtin <;> try (solve | cases accepted)
      case unit =>
        cases accepted
        cases typed
        exact ⟨_, .unit, .compatible (actual := .unit) erased (.unit)⟩

private theorem bool_sound {fuel : Nat} {registry : Registry} {expected : TypeSystem.Ty}
    (value : Bool) {encoded : Extended registry Value} {type : Ty}
    (accepted : encodeRaw (fuel + 1) checked registry expected (.bool value) = .ok encoded)
    (typed : RuntimeValueHasType world encoded.value type checked.catalog.definitions) :
    ∃ source, Means (.bool value) source ∧ ValueRep checked encoded.registry functions mapping world expected source encoded.value type := by
  cases erased : SourceCoreRawMetadata.runtimeType expected <;>
    (unfold encodeRaw at accepted; rw [erased] at accepted)
  all_goals try (solve | cases accepted)
  case constructor id =>
    cases id with
    | declaration => cases accepted
    | builtin builtin =>
      cases builtin <;> try (solve | cases accepted)
      case bool =>
        cases accepted
        cases typed
        exact ⟨_, .bool value, .compatible (actual := .bool) erased (.bool value)⟩

private theorem word_sound {fuel : Nat} {registry : Registry} {expected : TypeSystem.Ty}
    (value : Word) {encoded : Extended registry Value} {type : Ty}
    (accepted : encodeRaw (fuel + 1) checked registry expected (.word value) = .ok encoded)
    (typed : RuntimeValueHasType world encoded.value type checked.catalog.definitions) :
    ∃ source, Means (.word value) source ∧ ValueRep checked encoded.registry functions mapping world expected source encoded.value type := by
  cases erased : SourceCoreRawMetadata.runtimeType expected <;>
    (unfold encodeRaw at accepted; rw [erased] at accepted)
  all_goals try (solve | cases accepted)
  case constructor id =>
    cases id with
    | declaration => cases accepted
    | builtin builtin =>
      cases builtin <;> try (solve | cases accepted)
      case word =>
        cases accepted
        cases typed
        exact ⟨_, .word value, .compatible (actual := .word) erased (.word value)⟩

private theorem integer_sound {fuel : Nat} {registry : Registry} {expected : TypeSystem.Ty}
    (value : Int) {encoded : Extended registry Value} {type : Ty}
    (accepted : encodeRaw (fuel + 1) checked registry expected (.integer value) = .ok encoded)
    (typed : RuntimeValueHasType world encoded.value type checked.catalog.definitions) :
    ∃ source, Means (.integer value) source ∧ ValueRep checked encoded.registry functions mapping world expected source encoded.value type := by
  cases erased : SourceCoreRawMetadata.runtimeType expected <;>
    (unfold encodeRaw at accepted; rw [erased] at accepted)
  all_goals try (solve | cases accepted)
  case constructor id =>
    cases id with
    | declaration => cases accepted
    | builtin builtin =>
      cases builtin <;> try (solve | cases accepted)
      case integer =>
        cases accepted
        cases typed
        exact ⟨_, .integer value, .compatible (actual := .integer) erased (.integer value)⟩

private theorem raw_succ {fuel : Nat} (raw : RawSound checked functions mapping world fuel)
    (payload : PayloadSound checked functions mapping world fuel) (entries : EntriesSound checked functions mapping world fuel) :
    RawSound checked functions mapping world (fuel + 1) := by
  intro registry owner expected carrier encoded type accepted projected typed
  cases carrier with
  | unit => exact unit_sound accepted typed
  | bool value => exact bool_sound value accepted typed
  | word value => exact word_sound value accepted typed
  | integer value => exact integer_sound value accepted typed
  | constructed metadata carriers => exact constructed_sound payload owner accepted projected typed
  | product left right =>
    cases erased : SourceCoreRawMetadata.runtimeType expected
    case product leftType rightType => exact product_sound raw owner erased accepted projected typed
    all_goals
      unfold encodeRaw at accepted
      rw [erased] at accepted
    all_goals try (solve | cases accepted)
    case constructor id =>
      cases id with
      | declaration => cases accepted
      | builtin builtin => cases builtin <;> cases accepted
  | proxy actual =>
    cases erased : SourceCoreRawMetadata.runtimeType expected
    case proxy inner => exact proxy_sound erased accepted typed
    all_goals
      unfold encodeRaw at accepted
      rw [erased] at accepted
    all_goals try (solve | cases accepted)
    case constructor id =>
      cases id with
      | declaration => cases accepted
      | builtin builtin => cases builtin <;> cases accepted
  | mapping actualKey actualValue carriers =>
    cases erased : SourceCoreRawMetadata.runtimeType expected
    case mapping keyType valueType => exact mapping_sound raw entries owner erased accepted projected typed
    all_goals
      unfold encodeRaw at accepted
      rw [erased] at accepted
    all_goals try (solve | cases accepted)
    case constructor id =>
      cases id with
      | declaration => cases accepted
      | builtin builtin => cases builtin <;> cases accepted

/-- All mutually recursive encoder components are closed by one ordinary
natural-number induction. Children and default execution are derived from the
accepted real encoder computation, never retained as external hypotheses. -/
theorem raw_sound (fuel : Nat) : RawSound checked functions mapping world fuel ∧
    PayloadSound checked functions mapping world fuel ∧ EntriesSound checked functions mapping world fuel := by
  induction fuel with
  | zero =>
    refine ⟨?_, payload_zero, entries_zero⟩
    intro registry owner expected carrier encoded type accepted projected typed
    unfold encodeRaw at accepted
    cases accepted
  | succ fuel ih => exact ⟨raw_succ ih.1 ih.2.1 ih.2.2, payload_succ ih.1 ih.2.1, entries_succ ih.1 ih.2.2⟩

theorem encodeRaw_represents {fuel : Nat} {registry : Registry} (owner : registry.signatures = checked.signatures)
    {expected : TypeSystem.Ty} {carrier : PublicValue} {encoded : Extended registry Value} {type : Ty}
    (accepted : encodeRaw fuel checked registry expected carrier = .ok encoded)
    (projected : checked.catalog.project expected = .ok type)
    (typed : RuntimeValueHasType world encoded.value type checked.catalog.definitions) :
    ∃ source, Means carrier source ∧ ValueRep checked encoded.registry functions mapping world expected source encoded.value type :=
  (raw_sound fuel).1 registry owner expected carrier encoded type accepted projected typed

/-- Public successful encoding supplies the actual native typing receipt and
its original encoder equation. No catalog layout premise is required beyond
the checks actually performed by this public call. -/
theorem encode_represents {fuel : Nat} {context : SourceCoreCompatibleValues.Context}
    {functions : FunctionModel context.checked.catalog} {expected : TypeSystem.Ty} {carrier : PublicValue}
    {encoded : SourceCoreCompatibleValues.Encoded fuel context expected carrier}
    (accepted : SourceCoreCompatibleValues.encode fuel context expected carrier = .ok encoded)
    (mapping : LocationMap) (world : StoreTyping) :
    ∃ source, Means carrier source ∧
      ValueRep context.checked encoded.context.registry functions mapping world expected source encoded.value encoded.type := by
  unfold SourceCoreCompatibleValues.encode at accepted
  obtain ⟨generated, generatedEq, accepted⟩ := bind_ok accepted
  dsimp only at accepted
  split at accepted
  · cases accepted
  · rename_i decoded decodedEq
    split at accepted
    · cases accepted
      exact encodeRaw_represents context.registryOwner generatedEq decoded.projected (decoded.typed world)
    · cases accepted

theorem encode_represents_at {fuel : Nat} {context : SourceCoreCompatibleValues.Context}
    {functions : FunctionModel context.checked.catalog} {expected : TypeSystem.Ty} {carrier : PublicValue}
    {encoded : SourceCoreCompatibleValues.Encoded fuel context expected carrier} {source : Dynamic.Value}
    (accepted : SourceCoreCompatibleValues.encode fuel context expected carrier = .ok encoded)
    (meaning : Means carrier source) (mapping : LocationMap) (world : StoreTyping) :
    ValueRep context.checked encoded.context.registry functions mapping world expected source encoded.value encoded.type := by
  obtain ⟨actual, actualMeaning, represented⟩ := encode_represents (functions := functions) accepted mapping world
  have same := actualMeaning.functional meaning
  subst actual
  exact represented

/-- A standalone decoded receipt exposes an authenticated re-encoding under
an extension of its registry. This statement retains that extension explicitly
and does not identify it with the original registry. -/
theorem decoded_represents_extended {fuel : Nat} {context : SourceCoreCompatibleValues.Context}
    {functions : FunctionModel context.checked.catalog} {expected : TypeSystem.Ty} {value : Value}
    (decoded : SourceCoreCompatibleValues.Decoded fuel context expected value)
    (mapping : LocationMap) (world : StoreTyping) :
    ∃ registry source, SourceCoreRawMetadata.Extends context.registry registry ∧ Means decoded.source source ∧
      ValueRep context.checked registry functions mapping world expected source value decoded.type := by
  obtain ⟨generated, generatedEq, same⟩ := decoded.reencodes
  obtain ⟨source, meaning, represented⟩ := encodeRaw_represents (functions := functions) (mapping := mapping)
    context.registryOwner generatedEq decoded.projected (by rw [same]; exact decoded.typed world)
  exact ⟨generated.registry, source, generated.preserves, meaning, same ▸ represented⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleEncoding
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleAmbientEncoding
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
end
