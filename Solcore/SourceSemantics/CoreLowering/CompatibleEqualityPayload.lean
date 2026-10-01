import Solcore.SourceSemantics.CoreLowering.CompatibleEqualityValues
import Solcore.SourceSemantics.CoreLowering.DataEqualityGeneration

/-! Equality observations automatically extracted from independent full
compatible payloads. Function models must separately authenticate callable
identities/code shape; data-only models discharge that boundary vacuously. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleEquality
open Core Frontend SourceInference CompatiblePayload DataPatternValues DataEqualityGeneration

 theorem identity_entry {catalog : Catalog} {type : TypeSystem.Ty} {id : DataTypeId}
    (selected : catalog.identity? type = some id) :
    ∃ entry, catalog.entries[id.index]? = some entry ∧ entry.sourceType = SourceCoreRawMetadata.runtimeType type := by
  unfold SourceCoreCompatibleCatalog.Catalog.identity? at selected
  cases found : catalog.entries.zipIdx.find? (fun item => decide (item.1.sourceType = SourceCoreRawMetadata.runtimeType type)) with
  | none => simp [found] at selected
  | some item =>
    have member := List.mk_mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some found)
    have same : item.1.sourceType = SourceCoreRawMetadata.runtimeType type := by simpa using List.find?_some found
    simp only [found, Option.map_some, Option.some.injEq] at selected
    subst id
    exact ⟨item.1, member, same⟩

 theorem constructor_identity {catalog : Catalog} {metadata : DataConstructorInstantiation} {tag : ConstructorId}
    (selected : catalog.constructor? metadata = some tag) : catalog.identity? metadata.resultType = some tag.owner := by
  unfold SourceCoreCompatibleCatalog.Catalog.constructor? at selected
  cases identity : catalog.identity? metadata.resultType with
  | none => simp [identity] at selected
  | some id =>
    cases row : catalog.entries[id.index]? with
    | none => simp [identity, row] at selected
    | some entry =>
      cases ctor : entry.constructors.zipIdx.find? (fun item => decide (item.1 = metadata.constructor)) with
      | none => simp [identity, row, ctor] at selected
      | some item =>
        simp only [identity, row, ctor, bind, Option.bind, pure, Option.some.injEq] at selected
        subst tag
        rfl

private theorem native_beq_self (type : Ty) : (type == type) = true := by
  induction type <;> simp_all [BEq.beq, Core.instBEqTy.beq, Core.instBEqDataTypeId.beq]

theorem mapping_recognized {catalog : Catalog} {key value : TypeSystem.Ty} {layout : OrderedMapping.Layout}
    (identity : catalog.identity? (.mapping key value) = some layout.dataType)
    (keyProjection : catalog.project key = .ok layout.keyType)
    (valueProjection : catalog.project value = .ok layout.valueType) :
    SourceCoreCompatibleDataEquality.isMappingCarrier catalog (SourceCoreMappingWithDefault.type layout) = true := by
  obtain ⟨entry, selected, sourceType⟩ := identity_entry identity
  have projection : catalog.project (.mapping key value) = .ok (SourceCoreMappingWithDefault.type layout) := by
    simp only [SourceCoreCompatibleCatalog.Catalog.project, identity, keyProjection, valueProjection,
      bind, Except.bind, pure, Except.pure]
  have entryProjection : catalog.project entry.sourceType = .ok (SourceCoreMappingWithDefault.type layout) := by
    rw [sourceType, SourceCoreCompatibleCatalog.Catalog.project_runtimeType]
    exact projection
  have sourceKind : entry.sourceType = .mapping (SourceCoreRawMetadata.runtimeType key) (SourceCoreRawMetadata.runtimeType value) := sourceType
  change (match catalog.entries[layout.dataType.index]? with
    | some entry => match entry.sourceType with
      | .mapping _ _ => match catalog.project entry.sourceType with
        | .ok projected => projected == SourceCoreMappingWithDefault.type layout
        | .error _ => false
      | _ => false
    | none => false) = true
  rw [selected]
  simp only [sourceKind] at entryProjection ⊢
  rw [entryProjection]
  exact native_beq_self _

theorem named_project_not_mapping {catalog : Catalog} {source : TypeSystem.Ty} {id : DataTypeId}
    (projected : catalog.project source = .ok (.namedData id)) : ∀ key value, source ≠ .mapping key value := by
  intro key value same
  subst source
  unfold SourceCoreCompatibleCatalog.Catalog.project at projected
  cases identity : catalog.identity? (.mapping key value) <;>
    simp only [identity, bind, Except.bind, pure, Except.pure] at projected
  · cases projected
  · cases keyProjection : catalog.project key <;> simp only [keyProjection] at projected
    · cases projected
    · cases valueProjection : catalog.project value <;> simp only [valueProjection] at projected
      all_goals cases projected

/-- Static function leaf obligations, independent of runtime comparisons. -/
def FunctionObservations (catalog : Catalog) (functions : FunctionModel catalog)
    (identities : Dynamic.Value → Word → Prop) : Prop :=
  ∀ {registry mapping world sourceType source value type},
    functions.Represents registry mapping world sourceType source value type →
      Observation catalog registry identities type source value

theorem ValueRep.observation {checked : SourceCoreCompatibleCatalog.Checked} {registry : Registry}
    {functions : FunctionModel checked.catalog} {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {identities : Dynamic.Value → Word → Prop} (functionLeaves : FunctionObservations checked.catalog functions identities)
    {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
    (related : ValueRep checked registry functions mapping world sourceType source value type) :
    Observation checked.catalog registry identities type source value := by
  induction related using ValueRep.rec
    (motive_2 := fun _ sources values types _ => ∃ packed, Dynamic.ValuesPack sources packed ∧
      Observation checked.catalog registry identities (SourceCoreCompatibleCatalog.packTypes types) packed (packValues values))
    (motive_3 := fun _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ => True) with
  | unit => exact .unit
  | bool value => exact .bool value
  | word value => exact .word value
  | integer value => exact .integer value
  | product _ _ first second => exact .product first second
  | function related => exact functionLeaves related
  | @proxy inner owner id metadata identity registered =>
    obtain ⟨entry, selected, sourceType⟩ := identity_entry identity
    apply Observation.data selected (fun key value impossible => by rw [sourceType] at impossible; cases impossible)
      registered (.proxy metadata identity) (.word id)
  | @constructed metadata id tag sources values types metadataRep owner selected projected registered payloads ih =>
    obtain ⟨packed, packing, observed⟩ := ih
    obtain ⟨entry, found, sourceType⟩ := identity_entry (constructor_identity selected)
    have projectedEntry : checked.catalog.project entry.sourceType = .ok (.namedData tag.owner) := by
      rw [sourceType, SourceCoreCompatibleCatalog.Catalog.project_runtimeType]
      exact projected
    exact Observation.data found (named_project_not_mapping projectedEntry) registered
      (.constructed metadataRep selected payloads.length.1.symm packing) (.product (.word id) observed)
  | @mappingValue keyType valueType id layout sources entries fallback metadata identity keyProjection valueProjection registered stored defaultValue _ _ =>
    exact .mapping layout.dataType layout.valueType (mapping_recognized identity keyProjection valueProjection)
      keyType valueType sources _
  | compatible _ _ ih => exact ih
  | nil => exact ⟨.unit, .nil, .unit⟩
  | @cons sourceType source value type sourceTypes sources values types head tail first rest =>
    obtain ⟨packed, packing, observed⟩ := rest
    cases tail with
    | nil => exact ⟨source, .singleton source, first⟩
    | cons second remaining => exact ⟨.product source packed, .cons packing, .product first observed⟩
  | empty | entry | absent | present => trivial

end Solcore.SourceSemantics.CoreLowering.CompatibleEquality
