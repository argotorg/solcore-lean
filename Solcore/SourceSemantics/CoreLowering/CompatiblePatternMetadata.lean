import Solcore.SourceSemantics.CoreLowering.CompatibleConstructorMetadata

/-! The actual raw constructor guard agrees with independent source matching.
Authentic declarations have a unique parameter domain; the ordered argument
lookup therefore recovers every retained substitution entry. Constructor tags
or native type equality alone do not justify this exact metadata identity. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePatternMetadata
open Core Frontend SourceInference TypeSystem CompatiblePayload CompatibleConstructorMetadata

private theorem lookup_cons (parameters : List TypeParameterId) (candidate : TypeParameterId)
    (value : TypeSystem.Ty) (tail : ParameterSubstitution) (missing : candidate ∉ parameters) :
    parameters.mapM (ParameterSubstitution.lookup? ((candidate, value) :: tail)) = parameters.mapM tail.lookup? := by
  induction parameters with
  | nil => rfl
  | cons parameter rest ih =>
    simp only [List.mem_cons, not_or] at missing
    rw [List.mapM_cons, List.mapM_cons]
    rw [show ParameterSubstitution.lookup? ((candidate, value) :: tail) parameter = tail.lookup? parameter by
      simp only [ParameterSubstitution.lookup?, if_neg missing.1]]
    rw [ih missing.2]

private theorem ordered_lookup (substitution : ParameterSubstitution) (unique : (substitution.map Prod.fst).Nodup) :
    (substitution.map Prod.fst).mapM substitution.lookup? = some (substitution.map Prod.snd) := by
  induction substitution with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨parameter, value⟩ := entry
    simp only [List.map_cons, List.nodup_cons] at unique
    rw [List.map_cons, List.mapM_cons]
    rw [show ParameterSubstitution.lookup? ((parameter, value) :: rest) parameter = some value by
      simp [ParameterSubstitution.lookup?]]
    rw [lookup_cons _ _ _ _ unique.1, ih unique.2]
    rfl

theorem metadata_eq {signatures : ProgramSignatures} {left right : DataConstructorInstantiation}
    (valid : SignatureCatalogWellFormed signatures)
    (first : SourceCoreRawMetadata.constructorAuthentic signatures left = true)
    (second : SourceCoreRawMetadata.constructorAuthentic signatures right = true)
    (agrees : Dynamic.ConstructorInstantiationsAgree left right) : left = right := by
  obtain ⟨leftSignature, leftConstructor, leftArguments, leftData, leftCtor, leftKeys, leftMapped, leftPayloads, leftResult⟩ := facts first
  obtain ⟨rightSignature, rightConstructor, rightArguments, rightData, rightCtor, rightKeys, rightMapped, rightPayloads, rightResult⟩ := facts second
  have constructor := agrees.constructor_eq
  rw [constructor] at leftData
  have sameSignature := (List.cons.inj (leftData.symm.trans rightData)).1
  subst rightSignature
  have member : leftSignature ∈ signatures.dataTypes :=
    (List.mem_filter.mp (leftData ▸ (show leftSignature ∈ [leftSignature] by simp))).1
  have unique := (valid.data_parameters leftSignature member).1
  have arguments : leftArguments = rightArguments := by
    have same := congrArg SourceCoreDataCatalog.nominalParts (leftResult.symm.trans (agrees.result_type_eq.trans rightResult))
    simpa only [DataPatternAuthenticity.nominalParts_nominal, Option.some.injEq, Prod.mk.injEq, true_and] using same
  have leftValues := ordered_lookup left.parameterSubstitution (leftKeys.symm ▸ unique)
  have rightValues := ordered_lookup right.parameterSubstitution (rightKeys.symm ▸ unique)
  rw [leftKeys] at leftValues
  rw [rightKeys] at rightValues
  have leftValues := Option.some.inj (leftValues.symm.trans leftMapped)
  have rightValues := Option.some.inj (rightValues.symm.trans rightMapped)
  have firstZip := List.zip_of_prod leftKeys leftValues
  have secondZip := List.zip_of_prod rightKeys rightValues
  rw [arguments] at firstZip
  have substitution := firstZip.trans secondZip.symm
  cases left
  cases right
  cases constructor
  cases substitution
  cases agrees.payload_types_eq
  cases agrees.result_type_eq
  rfl

theorem raw_guard_iff {checked : SourceCoreCompatibleCatalog.Checked}
    {registry : SourceCoreRawMetadata.Registry} {actual expected : DataConstructorInstantiation} {left right : Word}
    (valid : SignatureCatalogWellFormed checked.signatures)
    (owner : registry.signatures = checked.signatures)
    (first : MetadataRep registry (.constructor actual) left)
    (second : MetadataRep registry (.constructor expected) right) :
    left = right ↔ Dynamic.ConstructorInstantiationsAgree actual expected := by
  constructor
  · intro same
    have exactMetadata := (first.ids_equal_iff second).mp same
    cases exactMetadata
    exact .refl _
  · intro agree
    have same := metadata_eq valid (constructor_authenticated first owner) (constructor_authenticated second owner) agree
    exact (first.ids_equal_iff second).mpr (congrArg SourceCoreRawMetadata.Metadata.constructor same)

end Solcore.SourceSemantics.CoreLowering.CompatiblePatternMetadata
