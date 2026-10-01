import Solcore.SourceSemantics.CoreLowering.CompatibleEncodingLeaves

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
