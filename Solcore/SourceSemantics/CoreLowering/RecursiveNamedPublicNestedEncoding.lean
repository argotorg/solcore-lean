import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicNestedEncodingContainers

/-! Structural induction connects nested public inputs to their original
encoded bytes. Every function leaf is discharged by the issued callable
producer. Payload packing, metadata extension and mapping order follow the
actual encoder receipts; no child representation is supplied by the caller. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicNestedEncoding
open Core Frontend SourceInference GeneralHeap CompatiblePayload DataPatternValues
open SourceCoreIndexedSession RecursiveNamedPublicNestedInputs RecursiveNamedPublicNestedEncodingContext
open CallableIndexedOwnedPreparedFiniteNamedInventories (Inventory)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled)}
  {rows : Inventory inputs} {artifact : Artifact} {session : Session artifact}
  {context : SourceSemantics.Context}
  {recipe : Recipe}
  {ambient : AmbientDefinitions recipe.compiled.compatible.checked.catalog.definitions}
  {functions : FunctionModel recipe.compiled.compatible.checked.catalog ambient}
  {receiving : SourceCoreRawMetadata.Registry} {mapping : LocationMap} {world : StoreTyping}

theorem Input.represents {sourceType : TypeSystem.Ty} {value : SourceCorePublicValues.Value}
    {source : Dynamic.Value} (receipt : Input rows session context sourceType value source)
    (atRecipe : RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact recipe)
    (leaves : ∀ {type value source},
      RecursiveNamedPublicMixedArgumentReceipts.Input rows session context type value source →
      RawMeaning session functions receiving mapping world type value source) :
    RawMeaning session functions receiving mapping world sourceType value source := by
  induction receipt using Input.rec
    (motive_2 := fun types values sources _ => PayloadMeaning session functions receiving mapping world types values sources)
    (motive_3 := fun key value entries sources _ => EntriesMeaning session functions receiving mapping world key value entries sources) with
  | leaf receipt => exact leaves receipt
  | product _ _ first second =>
      intro fuel registry expected encoded type owner compatible accepted projected typed metadata
      have view := compatible
      simp only [SourceCoreRawMetadata.runtimeType] at view
      obtain ⟨remaining, _fuel, left, right, leftAt, rightAt, shape⟩ := accepted.product view
      cases shape
      obtain ⟨a, b, leftProjected, rightProjected, rfl⟩ := CompatibleEncoding.product_projection view projected
      cases typed with
      | pair leftTyped rightTyped =>
          exact .product
            (first owner (SourceCoreRawMetadata.runtimeType_idempotent _) leftAt leftProjected leftTyped
              (right.preserves.trans metadata))
            (second (left.preserves.signatures.trans owner)
              (SourceCoreRawMetadata.runtimeType_idempotent _) rightAt rightProjected rightTyped metadata)
  | constructed _ _ payloads =>
      intro fuel registry expected encoded type owner compatible accepted projected typed metadata
      exact .compatible compatible.symm
        (RecursiveNamedPublicNestedEncodingContainers.constructed atRecipe payloads owner accepted projected typed metadata)
  | mapping _ entries =>
      intro fuel registry expected encoded type owner compatible accepted projected typed metadata
      exact .compatible compatible.symm
        (RecursiveNamedPublicNestedEncodingContainers.mapping_value atRecipe entries owner compatible accepted projected typed metadata)
  | @comptime sourceType _ _ _ child =>
      intro fuel registry expected encoded type owner compatible accepted projected typed metadata
      exact .compatible (actual := sourceType) rfl (child owner compatible accepted projected typed metadata)
  | nil =>
      intro fuel registry encoded coreTypes owner accepted projected typed metadata
      have shape := accepted.nil
      cases shape
      cases projected
      exact ⟨[], .nil, rfl⟩
  | @cons type types value values source sources head tail first rest =>
      intro fuel registry encoded coreTypes owner accepted projected typed metadata
      obtain ⟨coreType, remainingTypes, firstProjection, remainingProjection, rfl⟩ :=
        CompatibleEncoding.project_cons projected
      cases types with
      | nil =>
          cases tail
          cases remainingProjection
          obtain ⟨remaining, _fuel, actual⟩ := accepted.singleton
          exact ⟨[encoded.value], .cons (first owner rfl actual firstProjection typed metadata) .nil, rfl⟩
      | cons next types =>
          obtain ⟨nextType, restTypes, nextProjection, restProjection, rfl⟩ :=
            CompatibleEncoding.project_cons remainingProjection
          obtain ⟨remaining, _fuel, headEncoded, tailEncoded, headAt, tailAt, shape⟩ :=
            accepted.cons (by simp)
          cases shape
          cases typed with
          | pair headTyped tailTyped =>
              obtain ⟨native, related, packing⟩ := rest (headEncoded.preserves.signatures.trans owner)
                tailAt remainingProjection tailTyped metadata
              cases native with
              | nil => cases related
              | cons next native =>
                  exact ⟨headEncoded.value :: next :: native,
                    .cons (first owner rfl headAt firstProjection headTyped
                      (tailEncoded.preserves.trans metadata)) related,
                    by simp only [packValues]; rw [packing]⟩
  | empty key value =>
      intro fuel registry layout encoded owner accepted keyProjection valueProjection registered typed metadata
      have shape := accepted.nil
      cases shape
      exact ⟨[], .empty _ _ _ _, rfl⟩
  | entry _ _ _ key value rest =>
      intro fuel registry layout encoded owner accepted keyProjection valueProjection registered typed metadata
      obtain ⟨remaining, _fuel, keyEncoded, valueEncoded, tailEncoded, keyAt, valueAt, tailAt, shape⟩ :=
        accepted.cons
      cases shape
      cases typed with
      | constructed lookup payloadTyped =>
          have same := Option.some.inj (lookup.symm.trans (ambient.basePrefix.constructor_lookup registered.consLookup))
          cases same
          cases payloadTyped with
          | pair pairTyped restTyped => cases pairTyped with
            | pair keyTyped valueTyped =>
                obtain ⟨native, represented, packing⟩ := rest
                  (valueEncoded.preserves.signatures.trans (keyEncoded.preserves.signatures.trans owner))
                  tailAt keyProjection valueProjection registered restTyped metadata
                exact ⟨(keyEncoded.value, valueEncoded.value) :: native,
                  .entry
                    (key owner rfl keyAt keyProjection keyTyped
                      (valueEncoded.preserves.trans (tailEncoded.preserves.trans metadata)))
                    (value (keyEncoded.preserves.signatures.trans owner) rfl valueAt valueProjection valueTyped
                      (tailEncoded.preserves.trans metadata)) represented,
                  by simp only [OrderedMapping.encode]; rw [packing]⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicNestedEncoding
