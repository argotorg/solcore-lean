import Solcore.SourceSemantics.SourceInferenceNormalizedInference
import Solcore.SourceSemantics.SourceCompiledSelectedInferenceProgress

/-! The same selected original check supplies every terminal input to the
normalized inference traversal. Its complete raw ledger therefore has formed
predicates after the actual final substitution, before semantic body typing. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceInferenceRequirementFormation SourceInferenceNormalizedCoercionFormation

namespace Selected
variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
  {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}

def normalizedContext (selected : Selected compiled row fuel) : SourceSemantics.Context :=
  declarationContext compiled.program.signatures selected.signature.id
    selected.signature.scheme.parameters selected.signature.scheme.predicates
    selected.body.finalized.solvedRequirements

theorem normalizedFormationContext (selected : Selected compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {semantic : SourceSemantics.Context}
    (signatures : semantic.signatures = compiled.program.signatures)
    (parameters : semantic.typeParameters = selected.signature.scheme.parameters)
    (owner : semantic.currentDeclaration = some selected.signature.id)
    (residual : semantic.residualTypeVariables = true) :
    InferenceFormationContext semantic
      (context compiled.program.environment compiled.program.signatures selected.signature selected.body.declaration)
      selected.body.finalized.substitution := by
  have catalog : SignatureCatalogWellFormed semantic.signatures :=
    signatures.symm ▸ SignatureCatalogWellFormed.ofCheckProgram checked
  have canonical := (Frontend.checkProgram_success_signature_parameters_wellFormed checked).functions
    selected.signature selected.signatureMember
  have declarationEq := (ProgramEnvironment.declaration?_sound selected.body.declared).2
  have binders : TypeParameterBindersWellFormed semantic :=
    StructuralSubstitution.TypeParameterBindersWellFormed.transportContext parameters owner
      (SourceSemantics.SignatureParametersWellFormed.declarationContextBinders
        (signatures := compiled.program.signatures) canonical selected.signature.scheme.predicates [])
  have scope : ProducerScope
      (context compiled.program.environment compiled.program.signatures selected.signature selected.body.declaration)
      semantic := {
    binders, signatures, parameters, residual, catalog
    owner := by simpa only [context, ProgramTypeScope.ofDeclaration, declarationEq] using owner }
  have formation := CoercionFormationContext.of_function signatures catalog
    (signatures.symm ▸ selected.signatureMember) parameters owner residual
    (context := context compiled.program.environment compiled.program.signatures selected.signature selected.body.declaration) rfl
  refine { formation with
    range := selected.body.resources.producerRange scope
    scope
    canonical := ?_
    validated := Frontend.checkProgram_success_signature_formation checked
    functionShapes := ?_ }
  · simpa only [context, ProgramTypeScope.ofDeclaration, declarationEq] using canonical
  · intro candidate member
    exact (Frontend.checkProgram_success_function_signature_shape checked member).2

/-- The finalizer itself discharges continuation and capture inventories.
Only static context fields are supplied to permit lexical initializer scopes. -/
theorem normalizedBodyFormation (selected : Selected compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {semantic : SourceSemantics.Context}
    (signatures : semantic.signatures = compiled.program.signatures)
    (parameters : semantic.typeParameters = selected.signature.scheme.parameters)
    (owner : semantic.currentDeclaration = some selected.signature.id)
    (residual : semantic.residualTypeVariables = true) :
    TypeAdmissible semantic (selected.body.finalized.substitution.apply selected.body.body.type) ∧
      NormalizedStateFormation semantic selected.body.finalized.substitution selected.body.body.state := by
  have formation := selected.normalizedFormationContext checked signatures parameters owner residual
  have progress := selected.inferenceProgress checked
  have entry := function_entry_normalized_formation formation.toFormationContext
    (signatures.symm ▸ selected.signatureMember) parameters owner selected.body.declaration.id
  have returns : ∀ type ∈ selected.signature.returnTypes,
      TypeAdmissible semantic (selected.body.finalized.substitution.apply type) := by
    intro type member
    have formed := (formation.catalog.functions_semantic selected.signature
      (signatures.symm ▸ selected.signatureMember)).return_types type member
    apply type_applySubstitution_residual residual formation.range
    exact TypeAdmissible.ofWellFormed (StructuralSubstitution.TypeWellFormed.transportContext
      (source := signatureContext semantic.signatures selected.signature.id
        selected.signature.scheme.parameters selected.signature.scheme.predicates)
      rfl parameters owner formed)
  have capture : NoCaptureNodes selected.body.finalized.substitution selected.body.body.state.nodes := by
    rw [← selected.body.returned_nodes]
    exact NoCaptureNodes.of_finalizer selected.body.resources
  exact inferStatementsFuel_normalized_formation semantic selected.body.finalized.substitution
    fuel _ _ _ _ progress.initialReady (State.initial_nodesBelowNextOccurrence _ _ _)
    entry formation progress.returnBelow (normalized_productMany formation.scope.binders returns)
    _ selected.body.inferred progress.final_substitution capture

theorem normalizedLedger (selected : Selected compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program) :
    ∀ requirement ∈ selected.body.body.state.requirements,
      PredicateAdmissible selected.normalizedContext
        (TypedTraitResolution.applySubstitution selected.body.finalized.substitution requirement.predicate) :=
  (selected.normalizedBodyFormation checked rfl rfl rfl rfl).2.requirements

end Selected

/-- Successful selected compilation now supplies whole-body ledger formation
without any issuance, initializer typing or monomorphism premise. -/
theorem compile_normalized_ledger {raw : Workspace.RawWorkspace}
    {seeds : List SourceCoreCompiler.Seed} {options : SourceCoreCompiler.Options}
    {compiled : SourceCoreCompiler.Compiled}
    (accepted : SourceCoreCompiler.compile raw seeds options = .ok compiled)
    {row : SourceSpecialization.SpecializedFunction} (member : row ∈ compiled.plan.specializations) :
    ∃ selected : Selected compiled row options.checkingFuel,
      ∀ requirement ∈ selected.body.body.state.requirements,
        PredicateAdmissible selected.normalizedContext
          (TypedTraitResolution.applySubstitution selected.body.finalized.substitution requirement.predicate) := by
  obtain ⟨selected⟩ := of_compile accepted member
  exact ⟨selected, selected.normalizedLedger (SourceCoreCompiler.compile_checked_source accepted)⟩

end Solcore.SourceSemantics.SourceCompiledLocalFinalization
