import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicNestedOutputSelections
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionIndexSource
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicStartMeaning

/-! Recover structural function selections from the real recursive output
encoder. Registry extension is used in its forward direction to authenticate
exact constructor and mapping metadata. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicNestedOutputSelections
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open RecursiveNamedPublicFunctionHistory (Entry)
open SourceCoreIndexedSession

variable {checked : SourceCoreCompatibleCatalog.Checked}
  {ambient : AmbientDefinitions checked.catalog.definitions}
  {functions : FunctionModel checked.catalog ambient}
  {receiving : SourceCoreRawMetadata.Registry} {mapping : LocationMap} {world : StoreTyping}

private theorem source_constructor {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {value : Core.Value} {type : Core.Ty}
    (related : ValueRep checked receiving functions mapping world sourceType source value type) :
    ∀ {owner arguments}, SourceCoreDataCatalog.nominalParts (SourceCoreRawMetadata.runtimeType sourceType) = some (owner, arguments) →
      ∃ metadata payloads, source = .constructed metadata payloads := by
  induction related using ValueRep.rec (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True) (motive_4 := fun _ _ _ _ => True) with
  | unit | bool | word | integer | product | function | proxy | mappingValue => intro _ _ impossible; cases impossible
  | constructed => intro _ _ _; exact ⟨_, _, rfl⟩
  | compatible same _ ih => intro _ _ view; exact ih (by rw [← same]; exact view)
  | nil | cons | empty | entry | absent | present => trivial

private theorem constructed_children {sourceType expected : TypeSystem.Ty} {source : Dynamic.Value}
    {registry : SourceCoreRawMetadata.Registry} {metadata : DataConstructorInstantiation}
    (inserted : SourceCoreRawMetadata.Inserted registry expected (.constructor metadata))
    {tag : ConstructorId} {payload : Core.Value} {type : Core.Ty}
    (represented : ValueRep checked receiving functions mapping world sourceType source
      (.constructed tag (.pair (.word inserted.id) payload)) type)
    (view : SourceCoreRawMetadata.runtimeType sourceType = SourceCoreRawMetadata.runtimeType expected)
    (prior : SourceCoreRawMetadata.Extends receiving registry) :
    ∃ sources values types, source = .constructed metadata sources ∧ type = .namedData tag.owner ∧
      payload = DataPatternValues.packValues values ∧
      ValuesRep checked receiving functions mapping world metadata.payloadTypes sources values types := by
  obtain ⟨signature, constructor, arguments, _, _, _, _, _, resultType⟩ :=
    CompatibleConstructorMetadata.facts inserted.authenticated
  have nominal : SourceCoreDataCatalog.nominalParts (SourceCoreRawMetadata.runtimeType sourceType) =
      some (signature.id, arguments.map SourceCoreRawMetadata.runtimeType) := by
    rw [view, inserted.runtime_compatible]
    change SourceCoreDataCatalog.nominalParts (SourceCoreRawMetadata.runtimeType metadata.resultType) = _
    rw [resultType, CompatibleConstructorMetadata.runtimeType_nominal, DataPatternAuthenticity.nominalParts_nominal]
  obtain ⟨actual, sources, sourceEq⟩ := source_constructor represented nominal
  cases sourceEq
  obtain ⟨actualTag, actualId, values, types, nativeEq, typeEq, fields⟩ := constructor_fields represented rfl
  have parts := Core.Value.constructed.inj nativeEq
  have children := Core.Value.pair.inj parts.2
  have idEq := Core.Value.word.inj children.1
  have original := (prior.trans inserted.preserves).lookup fields.metadataRep.lookup
  rw [← idEq] at original
  have metadataEq := SourceCoreRawMetadata.Metadata.constructor.inj (Option.some.inj (original.symm.trans inserted.reconstruct))
  cases metadataEq
  cases parts.1
  exact ⟨sources, values, types, rfl, typeEq, children.2, fields.payloads⟩

private theorem mapping_children {key value : TypeSystem.Ty} {source : Dynamic.Value}
    {expected : TypeSystem.Ty} {registry : SourceCoreRawMetadata.Registry}
    (inserted : SourceCoreRawMetadata.Inserted registry expected (.mapping key value))
    {layout : OrderedMapping.Layout} {rows fallback : Core.Value}
    (represented : ValueRep checked receiving functions mapping world (.mapping key value) source
      (.pair (.word inserted.id) (.pair fallback rows)) (SourceCoreMappingWithDefault.type layout))
    (registered : layout.Registered checked.catalog.definitions)
    (prior : SourceCoreRawMetadata.Extends receiving registry) :
    ∃ sources values default, source = .mapping key value sources ∧
      rows = OrderedMapping.encode layout values ∧ fallback = OrderedMapping.optionValue layout.valueType default ∧
      EntriesRep checked receiving functions mapping world key value sources values layout.keyType layout.valueType := by
  obtain ⟨actualKey, actualValue, sources, sourceEq⟩ := CompatibleExpressionIndices.source_mapping represented rfl
  cases sourceEq
  obtain ⟨actualId, actualLayout, values, default, nativeEq, typeEq, _, fields⟩ :=
    CompatibleMapping.mapping_fields represented rfl
  have layoutEq := CompatibleMapping.registered_layout_eq fields.registered registered typeEq.symm
  cases layoutEq
  have parts := Core.Value.pair.inj nativeEq
  have idEq := Core.Value.word.inj parts.1
  have original := (prior.trans inserted.preserves).lookup fields.metadata.lookup
  rw [← idEq] at original
  have metadataEq := SourceCoreRawMetadata.Metadata.mapping.inj (Option.some.inj (original.symm.trans inserted.reconstruct))
  cases metadataEq.1
  cases metadataEq.2
  exact ⟨sources, values, default, rfl, (Core.Value.pair.inj parts.2).2,
    (Core.Value.pair.inj parts.2).1, fields.stored⟩

variable {artifact : Artifact} {session : Session artifact}

private def Collects (sourceType : TypeSystem.Ty) (publicValue : SourceCorePublicValues.Value)
    (selection : Selection sourceType publicValue) : Prop :=
  ∀ {source native type},
    ValueRep checked receiving functions mapping world sourceType source native type →
    ∀ {fuel registry expected} {encoded : SourceCoreCompatibleValues.Extended registry Core.Value},
      session.RawEncodedAt fuel registry expected publicValue encoded →
      SourceCoreRawMetadata.runtimeType sourceType = SourceCoreRawMetadata.runtimeType expected →
      encoded.value = native → SourceCoreRawMetadata.Extends receiving registry →
      ∃ entries, Selected checked session selection source native type fuel entries ∧
        entries.map Entry.handle = selection.handles

private def CollectsPayloads (sourceTypes : List TypeSystem.Ty) (publicValues : List SourceCorePublicValues.Value)
    (selection : PayloadSelection sourceTypes publicValues) : Prop :=
  ∀ {sources values types},
    ValuesRep checked receiving functions mapping world sourceTypes sources values types →
    ∀ {fuel registry} {encoded : SourceCoreCompatibleValues.Extended registry Core.Value},
      session.PayloadsEncodedAt fuel registry sourceTypes publicValues encoded →
      encoded.value = DataPatternValues.packValues values → SourceCoreRawMetadata.Extends receiving registry →
      ∃ entries, PayloadSelected checked session selection sources values types fuel entries ∧
        entries.map Entry.handle = selection.handles

private def CollectsEntries (key value : TypeSystem.Ty) (publicRows : List (SourceCorePublicValues.Value × SourceCorePublicValues.Value))
    (selection : EntrySelection key value publicRows) : Prop :=
  ∀ {sources values keyType valueType},
    EntriesRep checked receiving functions mapping world key value sources values keyType valueType →
    ∀ {fuel registry} {layout : OrderedMapping.Layout} {encoded : SourceCoreCompatibleValues.Extended registry Core.Value},
      session.EntriesEncodedAt fuel registry key value layout publicRows encoded →
      encoded.value = OrderedMapping.encode layout values → SourceCoreRawMetadata.Extends receiving registry →
      ∃ entries, EntriesSelected checked session selection sources values keyType valueType fuel entries ∧
        entries.map Entry.handle = selection.handles

/-- Exact current output encoding determines all selected leaves, preserving
constructor packing, mapping duplicates and each leaf's original raw type and
recursive validation fuel. -/
theorem Selection.collect {sourceType publicValue} (selection : Selection sourceType publicValue)
    {recipe : Recipe} (atRecipe : RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact recipe)
    (checkedAt : checked = recipe.compiled.compatible.checked)
    {source native type}
    (represented : ValueRep checked receiving functions mapping world sourceType source native type)
    {fuel registry expected} {encoded : SourceCoreCompatibleValues.Extended registry Core.Value}
    (accepted : session.RawEncodedAt fuel registry expected publicValue encoded)
    (compatible : SourceCoreRawMetadata.runtimeType sourceType = SourceCoreRawMetadata.runtimeType expected)
    (payload : encoded.value = native) (prior : SourceCoreRawMetadata.Extends receiving registry) :
    ∃ entries, Selected checked session selection source native type fuel entries ∧
      entries.map Entry.handle = selection.handles := by
  cases artifact
  rename_i authority actualRecipe
  change actualRecipe = recipe at atRecipe
  subst recipe
  have all : Collects (functions := functions) (receiving := receiving) (mapping := mapping) (world := world)
      (session := session) sourceType publicValue selection := by
    clear represented accepted compatible payload prior
    refine Selection.rec
      (motive_1 := fun type value selection => Collects (functions := functions) (receiving := receiving)
        (mapping := mapping) (world := world) (session := session) type value selection)
      (motive_2 := fun types values selection => CollectsPayloads (functions := functions) (receiving := receiving)
        (mapping := mapping) (world := world) (session := session) types values selection)
      (motive_3 := fun key value rows selection => CollectsEntries (functions := functions) (receiving := receiving)
        (mapping := mapping) (world := world) (session := session) key value rows selection)
      ?skip ?function ?product ?constructed ?mapping ?nil ?cons ?empty ?entry selection
    case skip => intro _ _ _ _ _ _ _ _ _ _ _ _ _ _; exact ⟨[], .skip, rfl⟩
    case function =>
        intro rawType handle
        intro source native type represented fuel registry expected encoded accepted compatible payload prior
        exact ⟨[⟨_, source, _, native, type, fuel⟩], .function (payload ▸ accepted.reimports_function compatible), rfl⟩
    case product =>
        intro a b left right first second firstIH secondIH
        intro source native type represented fuel registry expected encoded accepted compatible payload prior
        obtain ⟨remaining, fuelEq, firstEncoded, secondEncoded, firstAt, secondAt, encodedEq⟩ := accepted.product compatible.symm
        cases encodedEq; cases payload; cases fuelEq
        obtain ⟨x, y, firstType, secondType, sourceEq, typeEq, firstRep, secondRep⟩ := product_rep represented rfl
        cases sourceEq; cases typeEq
        obtain ⟨firstEntries, firstSelected, firstHandles⟩ := firstIH firstRep firstAt
          (SourceCoreRawMetadata.runtimeType_idempotent a).symm rfl prior
        obtain ⟨secondEntries, secondSelected, secondHandles⟩ := secondIH secondRep secondAt
          (SourceCoreRawMetadata.runtimeType_idempotent b).symm rfl (prior.trans firstEncoded.preserves)
        exact ⟨_, .product firstSelected secondSelected, by simp only [List.map_append, firstHandles, secondHandles, handles]⟩
    case constructed =>
        intro rawType metadata publicValues children ih
        intro source native type represented fuel registry expected encoded accepted compatible payload prior
        obtain ⟨remaining, fuelEq, inserted, tag, fields, _, _, fieldsAt, encodedEq⟩ := accepted.constructed
        cases encodedEq; cases payload; cases fuelEq
        obtain ⟨sources, values, types, sourceEq, typeEq, packed, related⟩ :=
          constructed_children inserted represented compatible prior
        cases sourceEq; cases typeEq
        obtain ⟨entries, selected, handles⟩ := ih related fieldsAt packed (prior.trans inserted.preserves)
        exact ⟨entries, packed ▸ .constructed related.projection selected, handles⟩
    case mapping =>
        intro key value rows children ih
        intro source native type represented fuel registry expected encoded accepted compatible payload prior
        obtain ⟨remaining, fuelEq, inserted, layout, rows, fallback, _, layoutAt, rowsAt, _, encodedEq⟩ := accepted.mapping compatible.symm
        cases encodedEq; cases payload; cases fuelEq
        rw [← checkedAt] at layoutAt
        obtain ⟨identity, keyProjection, valueProjection, registered⟩ := CompatibleEncoding.mappingLayout_facts layoutAt
        have projected : checked.catalog.project (.mapping key value) = .ok (SourceCoreMappingWithDefault.type layout) := by
          rw [← checked.catalog.project_runtimeType]
          exact CompatibleEncoding.mapping_project identity keyProjection valueProjection
        have typeEq := Except.ok.inj (represented.projection.symm.trans projected)
        cases typeEq
        obtain ⟨sources, values, default, sourceEq, rowsEq, defaultEq, related⟩ := mapping_children inserted represented registered prior
        cases sourceEq
        obtain ⟨entries, selected, handles⟩ := ih related rowsAt rowsEq (prior.trans inserted.preserves)
        exact ⟨entries, by rw [rowsEq, defaultEq]; exact .mapping registered selected, handles⟩
    case nil =>
        intro sources values types represented fuel registry encoded accepted payload prior
        cases represented
        exact ⟨[], .none, rfl⟩
    case cons =>
        intro sourceType types publicValue publicValues head tail firstIH tailIH
        intro sources values coreTypes represented fuel registry encoded accepted payload prior
        cases represented with
        | cons first rest =>
          cases tail with
          | nil =>
              cases rest
              obtain ⟨remaining, fuelEq, firstAt⟩ := accepted.singleton
              cases fuelEq
              obtain ⟨entries, selected, handles⟩ := firstIH first firstAt rfl payload prior
              exact ⟨entries, .one selected, by simpa [PayloadSelection.handles] using handles⟩
          | cons next remaining =>
              cases rest with
              | cons nextRep remainingRep =>
                obtain ⟨budget, fuelEq, firstEncoded, tailEncoded, firstAt, tailAt, encodedEq⟩ := accepted.cons (by simp)
                cases encodedEq; cases fuelEq
                have parts := Core.Value.pair.inj payload
                obtain ⟨firstEntries, firstSelected, firstHandles⟩ := firstIH first firstAt rfl parts.1 prior
                obtain ⟨restEntries, restSelected, restHandles⟩ := tailIH (.cons nextRep remainingRep) tailAt parts.2 (prior.trans firstEncoded.preserves)
                exact ⟨_, .more firstSelected restSelected, by simp only [List.map_append, firstHandles, restHandles, PayloadSelection.handles]⟩
    case empty =>
        intro key value
        intro sources values keyType valueType represented fuel registry layout encoded accepted payload prior
        have actual := accepted.nil
        cases actual
        cases represented with
        | empty => exact ⟨[], .empty, rfl⟩
        | entry => cases payload
    case entry =>
        intro key value a b rows first second tail firstIH secondIH tailIH
        intro sources values keyType valueType represented fuel registry layout encoded accepted payload prior
        obtain ⟨remaining, fuelEq, keyEncoded, valueEncoded, tailEncoded, keyAt, valueAt, tailAt, encodedEq⟩ := accepted.cons
        cases encodedEq; cases fuelEq
        cases represented with
        | empty => cases payload
        | entry keyRep valueRep restRep =>
          have rowEq := (Core.Value.constructed.inj payload).2
          have parts := Core.Value.pair.inj rowEq
          have items := Core.Value.pair.inj parts.1
          obtain ⟨keys, keysSelected, keysHandles⟩ := firstIH keyRep keyAt rfl items.1 prior
          obtain ⟨values, valuesSelected, valuesHandles⟩ := secondIH valueRep valueAt rfl items.2 (prior.trans keyEncoded.preserves)
          obtain ⟨rest, restSelected, restHandles⟩ := tailIH restRep tailAt parts.2 (prior.trans (keyEncoded.preserves.trans valueEncoded.preserves))
          exact ⟨_, .entry keysSelected valuesSelected restSelected,
            by simp only [List.map_append, keysHandles, valuesHandles, restHandles, EntrySelection.handles]⟩
  exact all represented accepted compatible payload prior

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicNestedOutputSelections
