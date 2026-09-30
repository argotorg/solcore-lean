import Solcore.SourceSemantics.CoreLowering.DataPayloadMapping

/-! Structural field and ordered-entry facts for complete payloads. These
lemmas retain siblings and captured code while selecting/replacing one field;
no runtime expression evaluation appears in the assumptions. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPayload
open Core Frontend Frontend.SourceInference GeneralHeap DataPatternValues
variable {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
  {functions : GenericHeap.PayloadModel catalog} {mapping : LocationMap} {world : StoreTyping}

theorem ValuesRep.at {types : List TypeSystem.Ty} {sources : List Dynamic.Value} {values : List Value} {coreTypes : List Ty}
    (represented : ValuesRep catalog signatures functions mapping world types sources values coreTypes)
    {index : Nat} {type : TypeSystem.Ty} (lookup : types[index]? = some type) :
    ∃ source value coreType, Dynamic.ValueAt sources index source ∧ values[index]? = some value ∧
      coreTypes[index]? = some coreType ∧ ValueRep catalog signatures functions mapping world type source value coreType := by
  induction types generalizing sources values coreTypes index with
  | nil => simp at lookup
  | cons head tail ih => cases represented with
    | cons first rest => cases index with
      | zero => cases lookup; exact ⟨_, _, _, .head, rfl, rfl, first⟩
      | succ index =>
        obtain ⟨source, value, type, selected, found, typed, represented⟩ := ih rest lookup
        exact ⟨source, value, type, .tail selected, found, typed, represented⟩

theorem ValuesRep.replace {types : List TypeSystem.Ty} {sources : List Dynamic.Value} {values : List Value} {coreTypes : List Ty}
    (represented : ValuesRep catalog signatures functions mapping world types sources values coreTypes)
    {index : Nat} {type : TypeSystem.Ty} {coreType : Ty} (lookup : types[index]? = some type)
    (coreLookup : coreTypes[index]? = some coreType)
    {source : Dynamic.Value} {value : Value}
    (replacement : ValueRep catalog signatures functions mapping world type source value coreType) :
    ValuesRep catalog signatures functions mapping world types (sources.set index source) (values.set index value) coreTypes := by
  induction types generalizing sources values coreTypes index with
  | nil => simp at lookup
  | cons head tail ih => cases represented with
    | cons first rest => cases index with
      | zero => cases lookup; cases coreLookup; exact .cons replacement rest
      | succ index => exact .cons first (ih rest lookup coreLookup)

theorem ValueRep.nominal_parts {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
    {declaration : Resolved.DeclarationId} {arguments : List TypeSystem.Ty}
    (nominal : SourceCoreDataCatalog.nominalParts sourceType = some (declaration, arguments))
    (represented : ValueRep catalog signatures functions mapping world sourceType source value type) :
    ∃ metadata tag sources values types,
      source = .constructed metadata sources ∧ value = .constructed tag (packValues values) ∧ type = .namedData tag.owner ∧
      metadata.resultType = sourceType ∧ catalog.resolveConstructor signatures metadata = .ok tag ∧
      catalog.definitions.lookupConstructorPayloadType? tag = some (SourceCoreDataMatches.bundleType types) ∧
      ValuesRep catalog signatures functions mapping world metadata.payloadTypes sources values types := by
  cases represented with
  | constructed nominal result authenticated projection registered payloads => exact ⟨_, _, _, _, _, rfl, rfl, rfl, result, authenticated, registered, payloads⟩
  | _ => simp [SourceCoreDataCatalog.nominalParts, TypeSystem.Ty.unit, TypeSystem.Ty.bool, TypeSystem.Ty.word, TypeSystem.Ty.integer] at nominal

theorem ValueRep.mapping_parts {keyType valueType : TypeSystem.Ty} {source : Dynamic.Value} {value : Value}
    (layout : Core.OrderedMapping.Layout)
    (keyProjected : catalog.project keyType = .ok layout.keyType)
    (valueProjected : catalog.project valueType = .ok layout.valueType)
    (represented : ValueRep catalog signatures functions mapping world (.mapping keyType valueType) source value layout.type) :
    ∃ sources entries, source = .mapping keyType valueType sources ∧ value = Core.OrderedMapping.encode layout entries ∧
      catalog.identity? (.mapping keyType valueType) = some layout.dataType ∧ layout.Registered catalog.definitions ∧
      EntriesRep catalog signatures functions mapping world keyType valueType layout.keyType layout.valueType sources entries := by
  generalize typeEq : layout.type = type at represented
  cases represented with
  | @mapping sourceKeyType sourceValueType actual sources entries identity keyProjection valueProjection registered contents =>
    have sameKey := Except.ok.inj (keyProjection.symm.trans keyProjected)
    have sameValue := Except.ok.inj (valueProjection.symm.trans valueProjected)
    have sameLayout : actual = layout := by
      cases actual; cases layout
      simp_all [Core.OrderedMapping.Layout.type]
    subst actual
    exact ⟨_, _, rfl, rfl, identity, registered, contents⟩
  | constructed nominal => simp [SourceCoreDataCatalog.nominalParts] at nominal

end Solcore.SourceSemantics.CoreLowering.DataPayload
