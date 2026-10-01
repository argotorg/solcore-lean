import Solcore.SourceSemantics.CoreLowering.CompatiblePayloadMembers
import Solcore.SourceSemantics.CoreLowering.DataPatternAuthenticity

/-! Runtime-compatible constructor metadata remains authenticated by its raw
signature reconstruction. These static facts compare normalized payload types
without equating original constructor metadata or raw registry IDs. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleConstructorMetadata
open Core Frontend SourceInference TypeSystem CompatiblePayload

/-- A lookup retains the exact source constructor at the returned index. -/
theorem constructor_lookup {catalog : SourceCoreCompatibleCatalog.Catalog}
    {metadata : DataConstructorInstantiation} {tag : ConstructorId}
    (selected : catalog.constructor? metadata = some tag) :
    ∃ entry, catalog.entries[tag.owner.index]? = some entry ∧
      entry.constructors[tag.index]? = some metadata.constructor := by
  unfold SourceCoreCompatibleCatalog.Catalog.constructor? at selected
  cases identityEq : catalog.identity? metadata.resultType with
  | none => simp [identityEq] at selected
  | some identity =>
    cases entryLookup : catalog.entries[identity.index]? with
    | none => simp [identityEq, entryLookup] at selected
    | some entry =>
      cases constructorLookup : entry.constructors.zipIdx.find? (fun item => decide (item.1 = metadata.constructor)) with
      | none => simp [identityEq, entryLookup, constructorLookup] at selected
      | some item =>
        have found := List.mem_of_find?_eq_some constructorLookup
        have same : item.1 = metadata.constructor := by simpa using List.find?_some constructorLookup
        have found := List.mk_mem_zipIdx_iff_getElem?.mp found
        simp only [identityEq, entryLookup, constructorLookup, bind, Option.bind, pure, Option.some.injEq] at selected
        subst tag
        refine ⟨entry, entryLookup, ?_⟩
        simpa [same] using found

theorem constructor_identity {catalog : SourceCoreCompatibleCatalog.Catalog}
    {metadata : DataConstructorInstantiation} {tag : ConstructorId}
    (selected : catalog.constructor? metadata = some tag) :
    catalog.identity? metadata.resultType = some tag.owner := by
  unfold SourceCoreCompatibleCatalog.Catalog.constructor? at selected
  cases identityEq : catalog.identity? metadata.resultType with
  | none => simp [identityEq] at selected
  | some identity =>
    cases entryLookup : catalog.entries[identity.index]? with
    | none => simp [identityEq, entryLookup] at selected
    | some entry =>
      cases constructorLookup : entry.constructors.zipIdx.find? (fun item => decide (item.1 = metadata.constructor)) with
      | none => simp [identityEq, entryLookup, constructorLookup] at selected
      | some item =>
        simp only [identityEq, entryLookup, constructorLookup, bind, Option.bind, pure, Option.some.injEq] at selected
        subst tag
        rfl

theorem constructor_eq_of_same_tag {catalog : SourceCoreCompatibleCatalog.Catalog}
    {left right : DataConstructorInstantiation} {tag : ConstructorId}
    (leftSelected : catalog.constructor? left = some tag)
    (rightSelected : catalog.constructor? right = some tag) : left.constructor = right.constructor := by
  obtain ⟨leftEntry, leftLookup, leftConstructor⟩ := constructor_lookup leftSelected
  obtain ⟨rightEntry, rightLookup, rightConstructor⟩ := constructor_lookup rightSelected
  have entries := leftLookup.symm.trans rightLookup
  cases entries
  exact Option.some.inj (leftConstructor.symm.trans rightConstructor)

theorem constructor_lookup_congr (catalog : SourceCoreCompatibleCatalog.Catalog)
    {left right : DataConstructorInstantiation}
    (constructor : left.constructor = right.constructor)
    (result : SourceCoreRawMetadata.runtimeType left.resultType = SourceCoreRawMetadata.runtimeType right.resultType) :
    catalog.constructor? left = catalog.constructor? right := by
  simp only [SourceCoreCompatibleCatalog.Catalog.constructor?, SourceCoreCompatibleCatalog.Catalog.identity?, constructor, result]

inductive Facts (signatures : ProgramSignatures) (metadata : DataConstructorInstantiation) : Prop where
  | mk (signature : ProgramDataSignature) (constructor : ProgramDataConstructorSignature) (arguments : List TypeSystem.Ty)
      (signatureSelected : signatures.dataTypes.filter (fun item => decide (item.id = metadata.constructor.dataType)) = [signature])
      (constructorSelected : signature.constructors.filter (fun item => decide (item.id = metadata.constructor)) = [constructor])
      (parameters : metadata.parameterSubstitution.map Prod.fst = signature.parameters)
      (argumentsSelected : signature.parameters.mapM metadata.parameterSubstitution.lookup? = some arguments)
      (payloads : metadata.payloadTypes = constructor.payloadTypes.map metadata.parameterSubstitution.apply)
      (result : metadata.resultType = TypeSystem.Ty.nominal signature.id arguments) : Facts signatures metadata

 theorem facts {signatures : ProgramSignatures} {metadata : DataConstructorInstantiation}
    (authentic : SourceCoreRawMetadata.constructorAuthentic signatures metadata = true) : Facts signatures metadata := by
  unfold SourceCoreRawMetadata.constructorAuthentic at authentic
  split at authentic <;> try cases authentic
  rename_i signature signatureLookup
  have signatureSelected : signatures.dataTypes.filter (fun item => decide (item.id = metadata.constructor.dataType)) = [signature] := by
    change (match signatures.dataTypes.filter (fun item => decide (item.id = metadata.constructor.dataType)) with
      | [one] => some one | _ => none) = some signature at signatureLookup
    split at signatureLookup <;> try cases signatureLookup
    next one selected => exact selected
  split at authentic <;> try cases authentic
  rename_i constructor constructorLookup
  have constructorSelected : signature.constructors.filter (fun item => decide (item.id = metadata.constructor)) = [constructor] := by
    change (match signature.constructors.filter (fun item => decide (item.id = metadata.constructor)) with
      | [one] => some one | _ => none) = some constructor at constructorLookup
    split at constructorLookup <;> try cases constructorLookup
    next one selected => exact selected
  split at authentic <;> try cases authentic
  rename_i parameters
  have parameters : metadata.parameterSubstitution.map Prod.fst = signature.parameters := by simpa using parameters
  split at authentic <;> try cases authentic
  rename_i arguments argumentsSelected
  simp only [Bool.and_eq_true, decide_eq_true_eq] at authentic
  exact .mk signature constructor arguments signatureSelected constructorSelected parameters argumentsSelected authentic.1 authentic.2

 theorem runtimeType_applyMany (head : TypeSystem.Ty) (arguments : List TypeSystem.Ty) :
    SourceCoreRawMetadata.runtimeType (TypeSystem.Ty.applyMany head arguments) =
      TypeSystem.Ty.applyMany (SourceCoreRawMetadata.runtimeType head) (arguments.map SourceCoreRawMetadata.runtimeType) := by
  induction arguments generalizing head with
  | nil => rfl
  | cons first rest ih => simpa only [TypeSystem.Ty.applyMany, List.foldl_cons, List.map_cons, SourceCoreRawMetadata.runtimeType] using ih (.application head first)

 theorem runtimeType_nominal (declaration : Resolved.DeclarationId) (arguments : List TypeSystem.Ty) :
    SourceCoreRawMetadata.runtimeType (TypeSystem.Ty.nominal declaration arguments) =
      TypeSystem.Ty.nominal declaration (arguments.map SourceCoreRawMetadata.runtimeType) := runtimeType_applyMany _ _

private theorem lookup_none (substitution : ParameterSubstitution) (parameter : TypeParameterId)
    (missing : parameter ∉ substitution.map Prod.fst) : substitution.lookup? parameter = none := by
  induction substitution with
  | nil => rfl
  | cons head tail ih =>
    obtain ⟨other, type⟩ := head
    simp only [List.map_cons, List.mem_cons, not_or] at missing
    simp only [ParameterSubstitution.lookup?, if_neg (Ne.symm missing.1)]
    exact ih missing.2

private theorem mapped_lookup_congr (left right : ParameterSubstitution)
    {parameters : List TypeParameterId} {a b : List TypeSystem.Ty}
    (first : parameters.mapM left.lookup? = some a) (second : parameters.mapM right.lookup? = some b)
    (same : a.map SourceCoreRawMetadata.runtimeType = b.map SourceCoreRawMetadata.runtimeType) :
    ∀ parameter ∈ parameters, (left.lookup? parameter).map SourceCoreRawMetadata.runtimeType =
      (right.lookup? parameter).map SourceCoreRawMetadata.runtimeType := by
  induction parameters generalizing a b with
  | nil => simp
  | cons head tail ih =>
    rw [List.mapM_cons] at first second
    obtain ⟨leftType, leftFound, first⟩ := Option.bind_eq_some_iff.mp first
    obtain ⟨leftTypes, leftTail, first⟩ := Option.bind_eq_some_iff.mp first
    obtain ⟨rightType, rightFound, second⟩ := Option.bind_eq_some_iff.mp second
    obtain ⟨rightTypes, rightTail, second⟩ := Option.bind_eq_some_iff.mp second
    cases first
    cases second
    simp only [List.map_cons, List.cons.injEq] at same
    intro parameter member
    rcases List.mem_cons.mp member with rfl | member
    · simpa only [leftFound, rightFound, Option.map_some] using congrArg some same.1
    · exact ih leftTail rightTail same.2 parameter member

 theorem substitution_apply_congr (left right : ParameterSubstitution)
    (lookups : ∀ parameter, (left.lookup? parameter).map SourceCoreRawMetadata.runtimeType =
      (right.lookup? parameter).map SourceCoreRawMetadata.runtimeType) (type : TypeSystem.Ty) :
    SourceCoreRawMetadata.runtimeType (left.apply type) = SourceCoreRawMetadata.runtimeType (right.apply type) := by
  induction type with
  | parameter parameter =>
    have same := lookups parameter
    cases first : left.lookup? parameter <;> cases second : right.lookup? parameter <;>
      simp_all [ParameterSubstitution.apply, SourceCoreRawMetadata.runtimeType]
  | _ => simp_all [ParameterSubstitution.apply, SourceCoreRawMetadata.runtimeType]

 theorem payloads_runtimeType {signatures : ProgramSignatures} {left right : DataConstructorInstantiation}
    (first : SourceCoreRawMetadata.constructorAuthentic signatures left = true)
    (second : SourceCoreRawMetadata.constructorAuthentic signatures right = true)
    (constructor : left.constructor = right.constructor)
    (result : SourceCoreRawMetadata.runtimeType left.resultType = SourceCoreRawMetadata.runtimeType right.resultType) :
    left.payloadTypes.map SourceCoreRawMetadata.runtimeType = right.payloadTypes.map SourceCoreRawMetadata.runtimeType := by
  obtain ⟨leftSignature, leftConstructor, leftArguments, leftData, leftCtor, leftKeys, leftMapped, leftPayloads, leftResult⟩ := facts first
  obtain ⟨rightSignature, rightConstructor, rightArguments, rightData, rightCtor, rightKeys, rightMapped, rightPayloads, rightResult⟩ := facts second
  rw [constructor] at leftData leftCtor
  have sameSignature := (List.cons.inj (leftData.symm.trans rightData)).1
  subst rightSignature
  have sameConstructor := (List.cons.inj (leftCtor.symm.trans rightCtor)).1
  subst rightConstructor
  rw [leftResult, rightResult, runtimeType_nominal, runtimeType_nominal] at result
  have sameArguments : leftArguments.map SourceCoreRawMetadata.runtimeType = rightArguments.map SourceCoreRawMetadata.runtimeType := by
    have same := congrArg SourceCoreDataCatalog.nominalParts result
    simpa only [DataPatternAuthenticity.nominalParts_nominal, Option.some.injEq, Prod.mk.injEq, true_and] using same
  have lookups : ∀ parameter, (left.parameterSubstitution.lookup? parameter).map SourceCoreRawMetadata.runtimeType =
      (right.parameterSubstitution.lookup? parameter).map SourceCoreRawMetadata.runtimeType := by
    intro parameter
    by_cases member : parameter ∈ leftSignature.parameters
    · exact mapped_lookup_congr _ _ leftMapped rightMapped sameArguments parameter member
    · rw [lookup_none _ _ (by simpa only [leftKeys] using member), lookup_none _ _ (by simpa only [rightKeys] using member)]
  rw [leftPayloads, rightPayloads, List.map_map, List.map_map]
  apply List.map_congr_left
  intro type _
  exact substitution_apply_congr _ _ lookups type

/-- Native projection erases staging; the authenticated raw metadata does not. -/
theorem projectList_runtimeType (catalog : SourceCoreCompatibleCatalog.Catalog) (types : List TypeSystem.Ty) :
    (types.map SourceCoreRawMetadata.runtimeType).mapM catalog.project = types.mapM catalog.project := by
  induction types with
  | nil => rfl
  | cons head tail ih => simp only [List.map_cons, List.mapM_cons, catalog.project_runtimeType, ih]

theorem resolved_facts {checked : SourceCoreCompatibleCatalog.Checked}
    {metadata : DataConstructorInstantiation} {tag : ConstructorId}
    (accepted : checked.resolveConstructor metadata = .ok tag) :
    SourceCoreRawMetadata.constructorAuthentic checked.signatures metadata = true ∧
      checked.catalog.constructor? metadata = some tag := by
  by_cases authentic : SourceCoreRawMetadata.constructorAuthentic checked.signatures metadata = true
  · simp only [SourceCoreCompatibleCatalog.Checked.resolveConstructor, authentic, ↓reduceIte,
      bind, Except.bind, pure, Except.pure] at accepted
    cases selected : checked.catalog.constructor? metadata with
    | none => simp [selected, throw] at accepted
    | some selectedTag =>
      simp only [selected] at accepted
      cases payloads : metadata.payloadTypes.mapM checked.catalog.project with
      | error error => simp [payloads] at accepted
      | ok payloadTypes =>
        simp only [payloads] at accepted
        split at accepted
        · cases accepted; exact ⟨authentic, rfl⟩
        · cases accepted
  · simp [SourceCoreCompatibleCatalog.Checked.resolveConstructor, authentic, throw, bind, Except.bind] at accepted

/-- Equal normalized result types and equal authenticated tags determine the
projected payload list, while retaining distinct raw IDs and source metadata. -/
theorem resolved_payloads_project {checked : SourceCoreCompatibleCatalog.Checked}
    {left right : DataConstructorInstantiation} {tag : ConstructorId}
    (first : checked.resolveConstructor left = .ok tag)
    (second : checked.resolveConstructor right = .ok tag)
    (result : SourceCoreRawMetadata.runtimeType left.resultType = SourceCoreRawMetadata.runtimeType right.resultType) :
    left.payloadTypes.mapM checked.catalog.project = right.payloadTypes.mapM checked.catalog.project := by
  obtain ⟨leftAuthentic, leftSelected⟩ := resolved_facts first
  obtain ⟨rightAuthentic, rightSelected⟩ := resolved_facts second
  have same := payloads_runtimeType leftAuthentic rightAuthentic
    (constructor_eq_of_same_tag leftSelected rightSelected) result
  calc
    _ = (left.payloadTypes.map SourceCoreRawMetadata.runtimeType).mapM checked.catalog.project := (projectList_runtimeType _ _).symm
    _ = (right.payloadTypes.map SourceCoreRawMetadata.runtimeType).mapM checked.catalog.project := congrArg (List.mapM checked.catalog.project) same
    _ = _ := projectList_runtimeType _ _

end Solcore.SourceSemantics.CoreLowering.CompatibleConstructorMetadata
