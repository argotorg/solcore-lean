import Solcore.SourceSemantics.SourceCompiledBodySelection

/-! Static formation and normalized inference come from the selected body's
actual catalog origin. The shared carrier introduces no typing assumption. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledMethodFinalization SourceInferenceRequirementFormation
open SourceInferenceNormalizedCoercionFormation

namespace BodySelection
variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
  {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}

theorem header (selected : BodySelection compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program) :
    CheckedBodyHeaderWellFormed compiled.program.signatures selected.signature selected.original := by
  apply selected.of_origins
  · intro ordinary
    obtain ⟨signature, member, formed⟩ :=
      checkedFunctionHeaderWellFormed_ofCheckProgram checked ordinary.originalMember
    have same := eq_of_mem_of_nodup_map
      (SignatureCatalogWellFormed.ofCheckProgram checked).function_ids member ordinary.signatureMember
      (formed.declaration_eq.symm.trans (checkFunctionBody_success_declaration ordinary.body.accepted))
    subst signature
    exact formed
  · intro retained receipt _ _
    exact receipt.header checked

theorem canonical (selected : BodySelection compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program) :
    SignatureParametersWellFormed selected.signature.id selected.signature.scheme.parameters := by
  apply selected.of_origins
  · intro ordinary
    exact (Frontend.checkProgram_success_signature_parameters_wellFormed checked).functions
      ordinary.signature ordinary.signatureMember
  · intro retained receipt _ _
    exact receipt.canonical checked

theorem predicates_fixed (selected : BodySelection compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program) (substitution : Substitution) :
    selected.signature.scheme.predicates.map (TypedTraitResolution.applySubstitution substitution) =
      selected.signature.scheme.predicates := by
  apply selected.of_origins
  · intro ordinary
    exact ((Frontend.checkProgram_success_signature_formation checked).functions
      ordinary.signature ordinary.signatureMember).2.2.apply_eq_self substitution
  · intro retained receipt _ _
    exact receipt.predicates_fixed checked substitution

theorem returns_closed (selected : BodySelection compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program) :
    (Ty.productMany selected.signature.returnTypes).VariablesBelow 0 := by
  apply Ty.variablesBelow_productMany
  intro type member metavariable occurs
  rw [StructuralSubstitution.TypeWellFormed.freeVariables_eq_nil
    ((selected.header checked).return_types type member)] at occurs
  cases occurs

theorem inferenceProgress (selected : BodySelection compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program) :
    BodyInferenceProgress selected.body := by
  apply selected.of_origins
  · intro ordinary
    exact ordinary.inferenceProgress checked
  · intro retained receipt _ _
    exact receipt.inferenceProgress checked

def normalizedContext (selected : BodySelection compiled row fuel) : SourceSemantics.Context :=
  declarationContext compiled.program.signatures selected.signature.id
    selected.signature.scheme.parameters selected.signature.scheme.predicates
    selected.body.finalized.solvedRequirements

theorem normalizedFormationContext (selected : BodySelection compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {semantic : SourceSemantics.Context}
    (signatures : semantic.signatures = compiled.program.signatures)
    (parameters : semantic.typeParameters = selected.signature.scheme.parameters)
    (owner : semantic.currentDeclaration = some selected.signature.id)
    (residual : semantic.residualTypeVariables = true) :
    InferenceFormationContext semantic
      (context compiled.program.environment compiled.program.signatures selected.signature selected.body.declaration)
      selected.body.finalized.substitution := by
  revert parameters owner
  apply selected.of_origins
  · intro ordinary parameters owner
    exact ordinary.normalizedFormationContext checked signatures parameters owner residual
  · intro retained receipt _ _ parameters owner
    exact receipt.normalizedFormationContext checked signatures parameters owner residual

theorem normalizedBodyFormation (selected : BodySelection compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {semantic : SourceSemantics.Context}
    (signatures : semantic.signatures = compiled.program.signatures)
    (parameters : semantic.typeParameters = selected.signature.scheme.parameters)
    (owner : semantic.currentDeclaration = some selected.signature.id)
    (residual : semantic.residualTypeVariables = true) :
    TypeAdmissible semantic (selected.body.finalized.substitution.apply selected.body.body.type) ∧
      NormalizedStateFormation semantic selected.body.finalized.substitution selected.body.body.state := by
  revert parameters owner
  apply selected.of_origins
  · intro ordinary parameters owner
    exact ordinary.normalizedBodyFormation checked signatures parameters owner residual
  · intro retained receipt _ _ parameters owner
    exact receipt.normalizedBodyFormation checked signatures parameters owner residual

theorem normalizedLedger (selected : BodySelection compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program) :
    ∀ requirement ∈ selected.body.body.state.requirements,
      PredicateAdmissible selected.normalizedContext
        (TypedTraitResolution.applySubstitution selected.body.finalized.substitution requirement.predicate) :=
  (selected.normalizedBodyFormation checked rfl rfl rfl rfl).2.requirements

end BodySelection
end Solcore.SourceSemantics.SourceCompiledLocalFinalization
