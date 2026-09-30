import Solcore.SourceSemantics.CoreLowering.DataPatternTypedValues

/-! Source metadata facts from the actual catalog authenticator. Equality of a
Core tag alone is insufficient; both source instantiations must be accepted. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPatternAuthenticity
open Core Frontend Frontend.SourceInference

private theorem bind_ok {α β ε : Type} {first : Except ε α} {next : α → Except ε β} {value : β}
    (accepted : first >>= next = .ok value) : ∃ input, first = .ok input ∧ next input = .ok value := by
  cases first <;> simp_all [bind, Except.bind]

/-- A lookup retains the exact source constructor at the returned index. -/
theorem constructor_lookup {catalog : SourceCoreDataCatalog.Catalog}
    {metadata : DataConstructorInstantiation} {tag : ConstructorId}
    (selected : catalog.constructor? metadata = some tag) :
    ∃ entry, catalog.entries[tag.owner.index]? = some entry ∧
      entry.constructors[tag.index]? = some metadata.constructor := by
  unfold SourceCoreDataCatalog.Catalog.constructor? at selected
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

theorem constructor_identity {catalog : SourceCoreDataCatalog.Catalog}
    {metadata : DataConstructorInstantiation} {tag : ConstructorId}
    (selected : catalog.constructor? metadata = some tag) :
    catalog.identity? metadata.resultType = some tag.owner := by
  unfold SourceCoreDataCatalog.Catalog.constructor? at selected
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

theorem constructor_eq_of_same_tag {catalog : SourceCoreDataCatalog.Catalog}
    {left right : DataConstructorInstantiation} {tag : ConstructorId}
    (leftSelected : catalog.constructor? left = some tag)
    (rightSelected : catalog.constructor? right = some tag) : left.constructor = right.constructor := by
  obtain ⟨leftEntry, leftLookup, leftConstructor⟩ := constructor_lookup leftSelected
  obtain ⟨rightEntry, rightLookup, rightConstructor⟩ := constructor_lookup rightSelected
  have entries := leftLookup.symm.trans rightLookup
  cases entries
  exact Option.some.inj (leftConstructor.symm.trans rightConstructor)

inductive MetadataFacts (signatures : ProgramSignatures) (metadata : DataConstructorInstantiation) : Prop where
  | mk (signature : ProgramDataSignature) (constructor : ProgramDataConstructorSignature)
    (signatureSelected : signatures.dataTypes.filter (fun item => decide (item.id = metadata.constructor.dataType)) = [signature])
    (constructorSelected : signature.constructors.filter (fun item => decide (item.id = metadata.constructor)) = [constructor])
    (parameters : metadata.parameterSubstitution.map Prod.fst = signature.parameters)
    (result : metadata.resultType = TypeSystem.Ty.nominal signature.id (metadata.parameterSubstitution.map Prod.snd))
    (payloads : metadata.payloadTypes = constructor.payloadTypes.map metadata.parameterSubstitution.apply) :
    MetadataFacts signatures metadata

theorem metadataFacts {catalog : SourceCoreDataCatalog.Catalog}
    {signatures : ProgramSignatures} {metadata : DataConstructorInstantiation} {tag : ConstructorId}
    (accepted : catalog.resolveConstructor signatures metadata = .ok tag) : MetadataFacts signatures metadata := by
  unfold SourceCoreDataCatalog.Catalog.resolveConstructor at accepted
  obtain ⟨signature, selected, accepted⟩ := bind_ok accepted
  change (match signatures.dataTypes.filter (fun item => decide (item.id = metadata.constructor.dataType)) with
    | [] => Except.error (SourceCoreDataCatalog.Error.missingData metadata.constructor.dataType)
    | [item] => .ok item
    | _ => .error (SourceCoreDataCatalog.Error.ambiguousData metadata.constructor.dataType)) = .ok signature at selected
  split at selected
  · cases selected
  · rename_i singleton
    cases selected
    simp only [pure, Except.pure, bind, Except.bind, throw] at accepted
    split at accepted
    · rename_i constructor constructorSelected
      split at accepted
      · rename_i parameters
        split at accepted
        · split at accepted
          · rename_i result
            split at accepted
            · rename_i payloads
              exact ⟨_, constructor, singleton, constructorSelected, parameters, result, payloads⟩
            · cases accepted
          · cases accepted
        · cases accepted
      · cases accepted
    · cases accepted
  · cases selected


private theorem nominalParts_applyMany (head : TypeSystem.Ty) (arguments : List TypeSystem.Ty)
    (declaration : Resolved.DeclarationId) (previous : List TypeSystem.Ty)
    (parts : SourceCoreDataCatalog.nominalParts head = some (declaration, previous)) :
    SourceCoreDataCatalog.nominalParts (TypeSystem.Ty.applyMany head arguments) = some (declaration, previous ++ arguments) := by
  unfold TypeSystem.Ty.applyMany
  induction arguments generalizing head previous with
  | nil => simpa using parts
  | cons argument arguments ih =>
    simp only [List.foldl_cons]
    have next : SourceCoreDataCatalog.nominalParts (.application head argument) = some (declaration, previous ++ [argument]) := by
      simp [SourceCoreDataCatalog.nominalParts, parts]
    simpa [List.append_assoc] using ih _ _ next

theorem nominalParts_nominal (declaration : Resolved.DeclarationId) (arguments : List TypeSystem.Ty) :
    SourceCoreDataCatalog.nominalParts (TypeSystem.Ty.nominal declaration arguments) = some (declaration, arguments) := by
  simpa [TypeSystem.Ty.nominal] using nominalParts_applyMany (.constructor (.declaration declaration)) arguments declaration [] rfl

/-- Within one source result type, the same authenticated Core tag denotes the
same source constructor and instantiated payload list. No catalog-wide
injectivity or source typing is inferred from a Core runtime type alone. -/
theorem resolveConstructor_agree {catalog : SourceCoreDataCatalog.Catalog}
    {signatures : ProgramSignatures} {left right : DataConstructorInstantiation} {tag : ConstructorId}
    (leftAccepted : catalog.resolveConstructor signatures left = .ok tag)
    (rightAccepted : catalog.resolveConstructor signatures right = .ok tag)
    (sameResult : left.resultType = right.resultType) :
    Dynamic.ConstructorInstantiationsAgree left right := by
  have constructors := constructor_eq_of_same_tag
    (SourceCoreDataValues.resolveConstructor_lookup leftAccepted)
    (SourceCoreDataValues.resolveConstructor_lookup rightAccepted)
  obtain ⟨leftSignature, leftConstructor, leftSignatureSelected, leftConstructorSelected, leftParameters, leftResult, leftPayloads⟩ := metadataFacts leftAccepted
  obtain ⟨rightSignature, rightConstructor, rightSignatureSelected, rightConstructorSelected, rightParameters, rightResult, rightPayloads⟩ := metadataFacts rightAccepted
  rw [constructors] at leftSignatureSelected leftConstructorSelected
  have signatureSame : leftSignature = rightSignature := (List.singleton_inj.mp (leftSignatureSelected.symm.trans rightSignatureSelected))
  subst rightSignature
  have constructorSame : leftConstructor = rightConstructor := List.singleton_inj.mp (leftConstructorSelected.symm.trans rightConstructorSelected)
  subst rightConstructor
  have arguments : left.parameterSubstitution.map Prod.snd = right.parameterSubstitution.map Prod.snd := by
    have equal := congrArg SourceCoreDataCatalog.nominalParts (leftResult.symm.trans (sameResult.trans rightResult))
    simpa [nominalParts_nominal] using equal
  have substitution : left.parameterSubstitution = right.parameterSubstitution := by
    have first := List.zip_of_prod leftParameters (rfl : left.parameterSubstitution.map Prod.snd = _)
    have second := List.zip_of_prod rightParameters (rfl : right.parameterSubstitution.map Prod.snd = _)
    rw [arguments] at first
    exact first.trans second.symm
  exact ⟨constructors, leftPayloads.trans (by rw [substitution]; exact rightPayloads.symm), sameResult⟩

end Solcore.SourceSemantics.CoreLowering.DataPatternAuthenticity
