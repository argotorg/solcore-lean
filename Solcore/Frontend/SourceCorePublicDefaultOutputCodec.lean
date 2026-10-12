import Solcore.Frontend.SourceCorePublicOutputShapes

/-! The actual data codec terminates and recovers each structurally represented
pure default. Existing metadata is reused; decoding and re-encoding keep the
same raw registry, including nested mapping defaults. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCorePublicOutputShapes
open TypeSystem SourceInference
namespace Codec
abbrev Context := SourceCoreCompatibleValues.Context
open SourceCoreCompatibleValues (decodeRaw encodeRaw decodeDefaultRaw encodeDefaultRaw defaultValue?)

theorem identity_eq {catalog : SourceCoreCompatibleCatalog.Catalog} {expected actual : Ty}
    (same : SourceCoreRawMetadata.runtimeType expected = SourceCoreRawMetadata.runtimeType actual) : catalog.identity? expected = catalog.identity? actual := by
  simp only [SourceCoreCompatibleCatalog.Catalog.identity?, same]

theorem mapping_layout_runtime {catalog : SourceCoreCompatibleCatalog.Catalog}
    {key value : Ty} {layout : Core.OrderedMapping.Layout}
    (accepted : catalog.mappingLayout key value = .ok layout) :
    catalog.mappingLayout (SourceCoreRawMetadata.runtimeType key) (SourceCoreRawMetadata.runtimeType value) = .ok layout := by
  have identity : catalog.identity? (.mapping (SourceCoreRawMetadata.runtimeType key) (SourceCoreRawMetadata.runtimeType value)) =
      catalog.identity? (.mapping key value) := by
    simp only [SourceCoreCompatibleCatalog.Catalog.identity?, SourceCoreRawMetadata.runtimeType,
      SourceCoreRawMetadata.runtimeType_idempotent]
    rfl
  unfold SourceCoreCompatibleCatalog.Catalog.mappingLayout at accepted ⊢
  rw [identity, catalog.project_runtimeType, catalog.project_runtimeType]
  cases selected : catalog.identity? (.mapping key value) with
  | none => simp [selected, throw, throwThe, bind, Except.bind] at accepted
  | some owner =>
    simp only [selected, pure, Except.pure, bind, Except.bind] at accepted ⊢
    cases first : catalog.project key with
    | error error => simp [first] at accepted
    | ok a =>
      cases second : catalog.project value with
      | error error => simp [first, second] at accepted
      | ok b =>
        simp only [first, second] at accepted ⊢
        split at accepted
        · rename_i registered
          simpa only [if_pos registered] using accepted
        · cases accepted

private def DataComplete (context : Context) (raw : Ty) (data : DataValue) (native : Core.Value) : Prop :=
  ∃ bound, ∀ fuel, bound ≤ fuel → ∀ expected, SourceCoreRawMetadata.runtimeType expected = SourceCoreRawMetadata.runtimeType raw →
    decodeRaw fuel context expected native = .ok data ∧
    encodeRaw fuel context.checked context.registry expected data = .ok (.pure context.registry native)

private def DefaultComplete (context : Context) (raw : Ty) (type : Core.Ty) (native : Core.Value) : Prop :=
  ∃ bound, ∀ fuel, bound ≤ fuel →
    decodeDefaultRaw fuel context raw type native = .ok (defaultValue? (raw.size + 1) raw) ∧
    encodeDefaultRaw fuel context.checked context.registry raw type = .ok (.pure context.registry native)

theorem data_complete (context : Context) {raw : Ty} {data : DataValue} {native : Core.Value}
    (shape : DefaultData context.checked context.registry raw data native) :
    DataComplete context raw data native := by
  induction shape using DefaultData.rec
    (motive_2 := fun raw type native _ => DefaultComplete context raw type native) with
  | unit =>
    refine ⟨1, ?_⟩
    intro fuel enough expected same
    cases fuel with
    | zero => omega
    | succ fuel =>
      unfold decodeRaw encodeRaw
      rw [same]
      exact ⟨rfl, rfl⟩
  | bool value =>
    refine ⟨1, ?_⟩
    intro fuel enough expected same
    cases fuel with
    | zero => omega
    | succ fuel =>
      unfold decodeRaw encodeRaw
      rw [same]
      exact ⟨rfl, rfl⟩
  | word value =>
    refine ⟨1, ?_⟩
    intro fuel enough expected same
    cases fuel with
    | zero => omega
    | succ fuel =>
      unfold decodeRaw encodeRaw
      rw [same]
      exact ⟨rfl, rfl⟩
  | integer value =>
    refine ⟨1, ?_⟩
    intro fuel enough expected same
    cases fuel with
    | zero => omega
    | succ fuel =>
      unfold decodeRaw encodeRaw
      rw [same]
      exact ⟨rfl, rfl⟩
  | @product leftType rightType left right a b first second leftIH rightIH =>
    obtain ⟨leftBound, leftComplete⟩ := leftIH
    obtain ⟨rightBound, rightComplete⟩ := rightIH
    refine ⟨max leftBound rightBound + 1, ?_⟩
    intro fuel enough expected same
    cases fuel with
    | zero => omega
    | succ fuel =>
      obtain ⟨leftDecoded, leftEncoded⟩ := leftComplete fuel (by omega) (SourceCoreRawMetadata.runtimeType leftType)
        (SourceCoreRawMetadata.runtimeType_idempotent leftType)
      obtain ⟨rightDecoded, rightEncoded⟩ := rightComplete fuel (by omega) (SourceCoreRawMetadata.runtimeType rightType)
        (SourceCoreRawMetadata.runtimeType_idempotent rightType)
      constructor
      · unfold decodeRaw
        rw [same]
        simp only [SourceCoreRawMetadata.runtimeType, leftDecoded, rightDecoded, Except.mapError,
          bind, Except.bind, pure, Except.pure]
      · unfold encodeRaw
        rw [same]
        simp only [SourceCoreRawMetadata.runtimeType, leftEncoded, rightEncoded, SourceCoreCompatibleValues.Extended.pure, Except.mapError,
          bind, Except.bind, pure, Except.pure]
  | @proxy inner owner id metadata identity =>
    refine ⟨1, ?_⟩
    intro fuel enough expected same
    cases fuel with
    | zero => omega
    | succ fuel =>
      have expectedIdentity := (identity_eq same).trans identity
      exact ⟨SourceCoreCompatibleValues.decode_proxy_at context metadata same expectedIdentity fuel,
        SourceCoreCompatibleValues.encode_proxy_at context.checked metadata same expectedIdentity fuel⟩
  | @mapping key value id layout fallback metadata layoutAt defaultValue defaultIH =>
    obtain ⟨bound, complete⟩ := defaultIH
    refine ⟨bound + 2, ?_⟩
    intro fuel enough expected same
    cases fuel with
    | zero => omega
    | succ fuel =>
      obtain ⟨defaultDecoded, defaultEncoded⟩ := complete fuel (by omega)
      have rowsDecoded : SourceCoreCompatibleValues.decodeEntriesRaw fuel context key value layout
          (Core.OrderedMapping.encode layout []) 0 = .ok [] := by
        cases fuel with
        | zero => omega
        | succ fuel => simp [SourceCoreCompatibleValues.decodeEntriesRaw, Core.OrderedMapping.encode]
      exact ⟨SourceCoreCompatibleValues.decode_mapping_at context metadata same layoutAt rowsDecoded defaultDecoded,
        SourceCoreCompatibleValues.encode_mapping_at context.checked metadata same (mapping_layout_runtime layoutAt)
          (by simp [SourceCoreCompatibleValues.encodeEntriesRaw]) defaultEncoded⟩
  | compatible same shape ih =>
    obtain ⟨bound, complete⟩ := ih
    exact ⟨bound, fun fuel enough expected matched => complete fuel enough expected (matched.trans same)⟩
  | absent missing =>
    exact ⟨0, fun _ _ => ⟨by simp [decodeDefaultRaw, missing], by simp [encodeDefaultRaw, missing]⟩⟩
  | @present raw type data native computed shape ih =>
    obtain ⟨bound, complete⟩ := ih
    refine ⟨bound, ?_⟩
    intro fuel enough
    obtain ⟨decoded, encoded⟩ := complete fuel enough raw rfl
    constructor
    · simp [decodeDefaultRaw, computed, decoded]
      rfl
    · simp [encodeDefaultRaw, computed, encoded]
      rfl

theorem default_complete (context : Context) {raw : Ty} {type : Core.Ty} {native : Core.Value}
    (shape : Default context.checked context.registry raw type native) :
    DefaultComplete context raw type native := by
  cases shape with
  | absent missing =>
    exact ⟨0, fun _ _ => ⟨by simp [decodeDefaultRaw, missing], by simp [encodeDefaultRaw, missing]⟩⟩
  | present computed shape =>
    obtain ⟨bound, complete⟩ := data_complete context shape
    refine ⟨bound, ?_⟩
    intro fuel enough
    obtain ⟨decoded, encoded⟩ := complete fuel enough raw rfl
    constructor
    · simp [decodeDefaultRaw, computed, decoded]
      rfl
    · simp [encodeDefaultRaw, computed, encoded]
      rfl

end Codec
end Solcore.Frontend.SourceCorePublicOutputShapes
