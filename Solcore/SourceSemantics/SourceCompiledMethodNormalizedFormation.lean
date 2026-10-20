import Solcore.SourceSemantics.SourceCompiledCachedMethodReceipt

/-! The real implementation signature and finalizer supply normalized body
and ledger formation before any semantic body-typing judgment is available. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledMethodFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceInferenceRequirementFormation
open SourceInferenceNormalizedCoercionFormation

private theorem predicate_transport {source target : SourceSemantics.Context}
    {predicate : ProgramPredicate}
    (signatures : target.signatures = source.signatures)
    (parameters : target.typeParameters = source.typeParameters)
    (owner : target.currentDeclaration = source.currentDeclaration)
    (formed : PredicateWellFormed source predicate) : PredicateWellFormed target predicate := by
  refine ⟨StructuralSubstitution.TypeWellFormed.transportContext
    (source := source) signatures parameters owner formed.subject,
    fun argument present => StructuralSubstitution.TypeWellFormed.transportContext
      (source := source) signatures parameters owner (formed.arguments argument present), ?_⟩
  cases choice : predicate.trait <;> simpa only [choice, signatures] using formed.trait

namespace MethodBodyReceipt
variable {program : CheckedProgram} {retained : CheckedImplementationMethod} {fuel : Nat}

/-- Method assumptions use the implementation's rigid scope, including the
trait predicates instantiated at its actual head. -/
theorem predicates_formed {raw : Workspace.RawWorkspace}
    (receipt : MethodBodyReceipt program retained fuel)
    (checked : Frontend.checkProgram raw fuel = .ok program) :
    PredicatesWellFormed (signatureContext program.signatures receipt.signature.id
      receipt.signature.scheme.parameters receipt.signature.scheme.predicates)
      receipt.signature.scheme.predicates := by
  let catalog := SignatureCatalogWellFormed.ofCheckProgram checked
  have implementation := catalog.implementations_semantic receipt.implementation receipt.implementationMember
  have method := implementation.methods receipt.method receipt.methodMember
  obtain ⟨trait, traitMember, head, _exact, _range, inherited⟩ := implementation.trait_catalog
  have actual := receipt.trait_origin checked
  have idEq : trait.id = receipt.trait.id := by
    have same := head.symm.trans actual.2
    injection same
  have same := Frontend.trait_signature_eq_of_mem_of_id_eq catalog.trait_ids traitMember actual.1 idEq
  subst trait
  intro predicate member
  change predicate ∈ receipt.implementation.methodAssumptions receipt.trait receipt.method at member
  simp only [ProgramImplementationSignature.methodAssumptions, List.mem_append] at member
  rcases member with (inheritedMember | implementationMember) | methodMember
  · have formed := implementation.predicates predicate (inherited predicate inheritedMember)
    exact predicate_transport (source := signatureContext program.signatures receipt.implementation.id receipt.implementation.parameters receipt.implementation.wherePredicates) rfl rfl rfl formed
  · have formed := implementation.predicates predicate implementationMember
    exact predicate_transport (source := signatureContext program.signatures receipt.implementation.id receipt.implementation.parameters receipt.implementation.wherePredicates) rfl rfl rfl formed
  · have formed := method.predicates predicate methodMember
    exact predicate_transport (source := signatureContext program.signatures receipt.implementation.id receipt.implementation.parameters (receipt.implementation.wherePredicates ++ receipt.method.wherePredicates)) rfl rfl rfl formed

theorem inferenceProgress {raw : Workspace.RawWorkspace}
    (receipt : MethodBodyReceipt program retained fuel)
    (checked : Frontend.checkProgram raw fuel = .ok program) :
    BodyInferenceProgress receipt.body := by
  have formation := Frontend.checkProgram_success_signature_formation checked
  have functions : ∀ candidate ∈ program.signatures.functions,
      candidate.scheme.body = .function (Ty.productMany candidate.parameterTypes)
        (Ty.productMany candidate.returnTypes) := by
    intro candidate member
    exact (Frontend.checkProgram_success_function_signature_shape checked member).2
  have ready : (initial receipt.signature receipt.body.declaration).InferenceReady :=
    State.InferenceReady.initial _ _ _
  have returns : (Ty.productMany receipt.signature.returnTypes).VariablesBelow
      (initial receipt.signature receipt.body.declaration).inference.next := by
    apply Ty.variablesBelow_productMany
    intro type member metavariable occurs
    rw [StructuralSubstitution.TypeWellFormed.freeVariables_eq_nil
      ((receipt.header checked).return_types type member)] at occurs
    cases occurs
  have body := Detail.inferStatementsFuel_inferenceProperties ready formation functions returns receipt.body.inferred
  have returnBound := returns.weaken body.1.next_le
  have unified := Detail.unify_inferenceProgress body.2.1.solved body.2.2 returnBound receipt.body.unified
  have returned := Detail.unify_preserves_inferenceReady body.2.1 body.2.2 returnBound receipt.body.unified
  exact ⟨ready, returns, body.1, body.2.1, body.2.2, unified, returned,
    receipt.body.resources.progress_of_ready returned⟩

def normalizedContext (receipt : MethodBodyReceipt program retained fuel) : SourceSemantics.Context :=
  declarationContext program.signatures receipt.signature.id receipt.signature.scheme.parameters
    receipt.signature.scheme.predicates receipt.body.finalized.solvedRequirements

theorem normalizedFormationContext {raw : Workspace.RawWorkspace}
    (receipt : MethodBodyReceipt program retained fuel)
    (checked : Frontend.checkProgram raw fuel = .ok program)
    {semantic : SourceSemantics.Context}
    (signatures : semantic.signatures = program.signatures)
    (parameters : semantic.typeParameters = receipt.signature.scheme.parameters)
    (owner : semantic.currentDeclaration = some receipt.signature.id)
    (residual : semantic.residualTypeVariables = true) :
    InferenceFormationContext semantic
      (context program.environment program.signatures receipt.signature receipt.body.declaration)
      receipt.body.finalized.substitution := by
  have catalog : SignatureCatalogWellFormed semantic.signatures :=
    signatures.symm ▸ SignatureCatalogWellFormed.ofCheckProgram checked
  have canonical := receipt.canonical checked
  have declarationEq := (ProgramEnvironment.declaration?_sound receipt.body.declared).2
  have binders : TypeParameterBindersWellFormed semantic :=
    StructuralSubstitution.TypeParameterBindersWellFormed.transportContext parameters owner
      (SourceSemantics.SignatureParametersWellFormed.declarationContextBinders
        (signatures := program.signatures) canonical receipt.signature.scheme.predicates [])
  have scope : ProducerScope
      (context program.environment program.signatures receipt.signature receipt.body.declaration)
      semantic := {
    binders, signatures, parameters, residual, catalog
    owner := by simpa only [signature, context, ProgramTypeScope.ofDeclaration, declarationEq] using owner }
  have assumptions : ∀ predicate ∈ receipt.signature.scheme.predicates,
      PredicateWellFormed semantic predicate := by
    intro predicate member
    have formed := receipt.predicates_formed checked predicate member
    exact predicate_transport (source := signatureContext program.signatures receipt.signature.id
      receipt.signature.scheme.parameters receipt.signature.scheme.predicates) signatures parameters owner formed
  refine {
    signatures := signatures
    catalog := catalog
    residual := residual
    assumptions := assumptions
    range := receipt.body.resources.producerRange scope
    scope := scope
    canonical := ?_
    validated := Frontend.checkProgram_success_signature_formation checked
    functionShapes := ?_ }
  · simpa only [signature, context, ProgramTypeScope.ofDeclaration, declarationEq] using canonical
  · intro candidate member
    exact (Frontend.checkProgram_success_function_signature_shape checked member).2

theorem normalizedBodyFormation {raw : Workspace.RawWorkspace}
    (receipt : MethodBodyReceipt program retained fuel)
    (checked : Frontend.checkProgram raw fuel = .ok program)
    {semantic : SourceSemantics.Context}
    (signatures : semantic.signatures = program.signatures)
    (parameters : semantic.typeParameters = receipt.signature.scheme.parameters)
    (owner : semantic.currentDeclaration = some receipt.signature.id)
    (residual : semantic.residualTypeVariables = true) :
    TypeAdmissible semantic (receipt.body.finalized.substitution.apply receipt.body.body.type) ∧
      NormalizedStateFormation semantic receipt.body.finalized.substitution receipt.body.body.state := by
  have formation := receipt.normalizedFormationContext checked signatures parameters owner residual
  have progress := receipt.inferenceProgress checked
  have entry : NormalizedStateFormation semantic receipt.body.finalized.substitution
      (initial receipt.signature receipt.body.declaration) := by
    apply NormalizedStateFormation.initial
    · intro entry member
      obtain ⟨parameter, _, rfl⟩ := List.mem_map.mp member
      rfl
    · intro entry member
      obtain ⟨parameter, present, rfl⟩ := List.mem_map.mp member
      have formed := (receipt.header checked).parameter_types parameter.2 (List.of_mem_zip present).2
      apply type_applySubstitution_residual residual formation.range
      exact TypeAdmissible.ofWellFormed
        (StructuralSubstitution.TypeWellFormed.transportContext
          (source := checkedBodyContext program.signatures receipt.signature retained.checked)
          signatures parameters owner formed)
  have returns : ∀ type ∈ receipt.signature.returnTypes,
      TypeAdmissible semantic (receipt.body.finalized.substitution.apply type) := by
    intro type member
    apply type_applySubstitution_residual residual formation.range
    exact TypeAdmissible.ofWellFormed (StructuralSubstitution.TypeWellFormed.transportContext
      (source := checkedBodyContext program.signatures receipt.signature retained.checked)
      signatures parameters owner ((receipt.header checked).return_types type member))
  have capture : NoCaptureNodes receipt.body.finalized.substitution receipt.body.body.state.nodes := by
    rw [← receipt.body.returned_nodes]
    exact NoCaptureNodes.of_finalizer receipt.body.resources
  exact inferStatementsFuel_normalized_formation semantic receipt.body.finalized.substitution
    fuel _ _ _ _ progress.initialReady (State.initial_nodesBelowNextOccurrence _ _ _)
    entry formation progress.returnBelow (normalized_productMany formation.scope.binders returns)
    _ receipt.body.inferred progress.final_substitution capture

theorem normalizedLedger {raw : Workspace.RawWorkspace}
    (receipt : MethodBodyReceipt program retained fuel)
    (checked : Frontend.checkProgram raw fuel = .ok program) :
    ∀ requirement ∈ receipt.body.body.state.requirements,
      PredicateAdmissible receipt.normalizedContext
        (TypedTraitResolution.applySubstitution receipt.body.finalized.substitution requirement.predicate) :=
  (receipt.normalizedBodyFormation checked rfl rfl rfl rfl).2.requirements

end MethodBodyReceipt
end Solcore.SourceSemantics.SourceCompiledMethodFinalization
