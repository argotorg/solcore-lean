import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicReturnedInputs
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicNestedEncodingContainers
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicRuntimeMeaning

/-! A returned callable can occur repeatedly inside subsequent public inputs.
Its original value representation supplies each function occurrence; the real
codec selects exactly that payload. Data and all containers use their actual
encoding receipts in one fixed receiving metadata registry. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicReturnedEncoding
open Core Frontend SourceInference GeneralHeap CompatiblePayload DataPatternValues
open SourceCoreIndexedSession RecursiveNamedPublicReturnedInputs RecursiveNamedPublicNestedEncodingContext

variable {artifact : Artifact} {session : Session artifact} {recipe : Recipe}
  {ambient : AmbientDefinitions recipe.compiled.compatible.checked.catalog.definitions}
  {functions : FunctionModel recipe.compiled.compatible.checked.catalog ambient}
  {receiving : SourceCoreRawMetadata.Registry} {mapping : LocationMap} {world : StoreTyping}
  {context : SourceSemantics.Context}

private theorem data_meaning
    (atRecipe : RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact recipe)
    {sourceType : TypeSystem.Ty} {value : SourceCorePublicValues.Value} {source : Dynamic.Value}
    (inputTyped : RecursiveNamedPublicDataArgumentReceipts.PublicDataTyped context value sourceType)
    (meaning : RecursiveNamedPublicDataInputs.Means value source) :
    RawMeaning session functions receiving mapping world sourceType value source := by
  cases artifact
  rename_i authority actualRecipe
  change actualRecipe = recipe at atRecipe
  subst actualRecipe
  intro fuel before expected encoded type owner compatible accepted projected typed metadata
  obtain ⟨carrier, image, _typed⟩ := inputTyped
  have encodedAt := accepted.data owner ⟨carrier, image⟩
  obtain ⟨interpreted, interpretedAt, represented⟩ :=
    RecursiveNamedPublicDataInputs.EncodedDataInput.represents functions mapping world
      encodedAt projected ambient.basePrefix typed
  have same := RecursiveNamedPublicRuntimeMeaning.means_functional interpretedAt meaning
  subst interpreted
  exact .compatible compatible.symm (represented.extend metadata (.refl _) (.refl _))

variable {returnedType : TypeSystem.Ty} {returnedValue : SourceCorePublicValues.Value}
  {returnedSource : Dynamic.Value} {returnedNative : Core.Value} {returnedNativeType : Core.Ty}
  {returnedFuel : Nat} {handle : SourceCorePublicValues.Handle}

private theorem represents
    {sourceType : TypeSystem.Ty} {value : SourceCorePublicValues.Value} {source : Dynamic.Value}
    (receipt : Input returnedType returnedValue returnedSource context sourceType value source)
    (atRecipe : RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact recipe)
    (imported : session.EncodesAt returnedFuel returnedType returnedValue returnedNative)
    (handleValue : returnedValue = .function handle)
    (represented : ValueRep recipe.compiled.compatible.checked receiving functions mapping world
      returnedType returnedSource returnedNative returnedNativeType) :
    RawMeaning session functions receiving mapping world sourceType value source := by
  induction receipt using Input.rec
    (motive_2 := fun types values sources _ => PayloadMeaning session functions receiving mapping world types values sources)
    (motive_3 := fun key value entries sources _ => EntriesMeaning session functions receiving mapping world key value entries sources) with
  | returned =>
      intro fuel before expected encoded type owner compatible accepted projected typed metadata
      rw [handleValue] at accepted
      have actualImport := imported
      rw [handleValue] at actualImport
      have sameValue := accepted.function_eq actualImport
      have actualProjection := (CompatibleEncoding.project_compatible compatible).symm.trans projected
      have sameType := Except.ok.inj (represented.projection.symm.trans actualProjection)
      rw [sameValue]
      exact sameType ▸ represented
  | data inputTyped meaning => exact data_meaning atRecipe inputTyped meaning
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

/-- The single preceding result supplies the only function leaf. All other
positions are discharged from independent data input certificates, and every
container preserves its full ordered native payload. -/
theorem Input.meaning
    {sourceType : TypeSystem.Ty} {value : SourceCorePublicValues.Value} {source : Dynamic.Value}
    (receipt : Input returnedType returnedValue returnedSource context sourceType value source)
    (atRecipe : RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact recipe)
    (imported : session.EncodesAt returnedFuel returnedType returnedValue returnedNative)
    (handleValue : returnedValue = .function handle)
    (represented : ValueRep recipe.compiled.compatible.checked receiving functions mapping world
      returnedType returnedSource returnedNative returnedNativeType)
    {heap : Dynamic.Heap}
    (returnedTyped : Dynamic.ValueHasType context heap returnedSource returnedType) :
    RawMeaning session functions receiving mapping world sourceType value source ∧
      Dynamic.ValueHasType context heap source sourceType :=
  ⟨represents receipt atRecipe imported handleValue represented, receipt.source_hasType returnedTyped⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicReturnedEncoding
