import Solcore.SourceSemantics.CoreLowering.CompatibleEncodingInduction

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
