import Solcore.SourceSemantics.SourceInferenceSoundness

/-! Formation of obligations from their actual signature and operand producers. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.SourceInferenceRequirementFormation

open Frontend SourceInference TypeSystem
open SourceInferenceSoundness

/-- A closed signature predicate remains meaningful when its rigid parameters
are replaced by admissible occurrence types, including residual variables. -/
theorem predicate_applyParameters_admissible
    {source target : SourceSemantics.Context} {predicate : ProgramPredicate}
    (substitution : TypeSystem.ParameterSubstitution)
    (exact : SourceSemantics.ParameterSubstitution.Exact substitution
      source.typeParameters)
    (range : SourceSemantics.ParameterSubstitution.RangeAdmissible target substitution)
    (signatures : target.signatures = source.signatures)
    (binders : TypeParameterBindersWellFormed target)
    (formed : PredicateWellFormed source predicate) :
    PredicateAdmissible target (predicate.applyParameters substitution) := by
  constructor
  · exact StructuralSubstitution.TypeWellScoped.applyParametersAdmissibleTo
      substitution exact range signatures binders formed.subject.typeWellScoped
  · intro argument member
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    exact StructuralSubstitution.TypeWellScoped.applyParametersAdmissibleTo
      substitution exact range signatures binders
      (formed.arguments original originalMember).typeWellScoped
  · cases traitEq : predicate.trait with
    | builtin builtin =>
        cases builtin
        have valid := formed.trait
        rw [traitEq] at valid
        simpa [ProgramPredicate.applyParameters, traitEq] using valid
    | declaration id =>
        have valid := formed.trait
        rw [traitEq] at valid
        obtain ⟨signature, member, idEq, arity⟩ := valid
        simp only [ProgramPredicate.applyParameters, traitEq]
        exact ⟨signature, by simpa [signatures] using member, idEq,
          by simpa [ProgramPredicate.applyParameters, traitEq] using arity⟩

/-- The catalog and exact fresh instantiation establish every declaration
predicate before its requirement identities are allocated. -/
theorem instantiated_function_predicates
    {context : SourceSemantics.Context}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (binders : TypeParameterBindersWellFormed context)
    (residual : context.residualTypeVariables = true)
    {signature : ProgramFunctionSignature}
    (member : signature ∈ context.signatures.functions) (next : Nat) :
    ∀ predicate ∈ (signature.scheme.instantiate next).predicates,
      PredicateAdmissible context predicate := by
  rw [ConstrainedDeclarationScheme.instantiate_predicates]
  intro predicate predicateMember
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp predicateMember
  exact predicate_applyParameters_admissible
    (source := signatureContext context.signatures signature.id
      signature.scheme.parameters signature.scheme.predicates)
    (signature.scheme.instantiate next).parameterSubstitution
    (DeclarationInstantiation.instantiate_parameterSubstitution_exact
      signature.scheme next (catalog.function_parameters signature member).1)
    (DeclarationInstantiation.instantiate_parameterSubstitution_rangeAdmissible
      binders residual signature.scheme next) rfl binders
    ((catalog.functions_semantic signature member).predicates original originalMember)

/-- Recover the exact declaration predicate batch and its ledger allocation
from the accepted candidate, with formation for every predicate in that batch. -/
theorem candidate_signature_issuance
    {inferenceContext : Frontend.SourceInference.Context}
    {arguments : List InferredExpression}
    {integerOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected : Option Ty} {state : State}
    {signature : ProgramFunctionSignature} {result : Detail.CandidateAttemptResult}
    {context : SourceSemantics.Context}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (binders : TypeParameterBindersWellFormed context)
    (residual : context.residualTypeVariables = true)
    (member : signature ∈ context.signatures.functions)
    (success : Detail.tryFunctionCandidate inferenceContext arguments integerOrigins
      call expected state signature = .ok (some result)) :
    RequirementPredicatesCorrespond result.state.requirements
      (signature.scheme.instantiate state.inference.next).predicates
      result.signatureRequirements ∧
    (∀ predicate ∈ (signature.scheme.instantiate state.inference.next).predicates,
      PredicateAdmissible context predicate) := by
  obtain ⟨fittedArguments, fittedResult, _, _, _, _, _, _, idsEq, stateEq⟩ :=
    Detail.tryFunctionCandidate_some_resultFitAllocationWitness
      (catalog.functions_semantic signature member).scheme_body success
  constructor
  · rw [idsEq, stateEq]
    exact State.addRequirementsWithIds_correspond fittedResult.state _
  · exact instantiated_function_predicates catalog binders residual member _

/-- The builtin integer obligation is formed by the type of its operand. -/
theorem builtin_integer_predicate {context : SourceSemantics.Context} {type : Ty}
    (formed : TypeAdmissible context type) :
    PredicateAdmissible context (ProgramSignatures.builtinIntPredicate type) := by
  exact ⟨formed, by simp [ProgramSignatures.builtinIntPredicate], rfl⟩

/-- An operator profile supplies the real trait member, exact singleton rigid
substitution, and cataloged method predicates. Its operand supplies the range. -/
theorem operator_profile_predicates
    {context : SourceSemantics.Context} {traitName methodName : String}
    {operand : Ty} {parameters returns : List Ty} {predicates : List ProgramPredicate}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (binders : TypeParameterBindersWellFormed context)
    (operandFormed : TypeAdmissible context operand)
    (profile : OperatorProfileInstantiates context traitName methodName operand
      parameters returns predicates) :
    ∀ predicate ∈ predicates, PredicateAdmissible context predicate := by
  cases profile with
  | @intro signature method parameter signatureMember _ parametersEq methodUnique _ _ =>
      have signatureFormed := catalog.traits_semantic signature signatureMember
      have methodMember : method ∈ signature.methods := by
        have filtered : method ∈ signature.methods.filter
            (fun candidate => candidate.name == methodName) := by
          rw [methodUnique]
          simp
        exact (List.mem_filter.mp filtered).1
      have exactSubstitution : SourceSemantics.ParameterSubstitution.Exact
          [(parameter, operand)] signature.parameters := by
        rw [parametersEq]
        exact SourceSemantics.ParameterSubstitution.exact_singleton _ _
      have range : SourceSemantics.ParameterSubstitution.RangeAdmissible context
          [(parameter, operand)] := by
        intro candidate replacement member
        simp only [List.mem_singleton] at member
        cases member
        exact operandFormed
      intro predicate member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨operandFormed, by simp,
          signature, signatureMember, rfl, by simp [parametersEq]⟩
      · obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
        exact predicate_applyParameters_admissible
          (source := signatureContext context.signatures signature.id signature.parameters
            (signature.wherePredicates ++ method.wherePredicates))
          [(parameter, operand)] exactSubstitution range rfl binders
          ((signatureFormed.methods method methodMember).predicates original originalMember)

/-- Successful operator-profile construction therefore issues formed
predicates. No evidence-entailment premise is used to establish formation. -/
theorem operator_issuance
    {inferenceContext : Frontend.SourceInference.Context}
    {context : SourceSemantics.Context} {trait : Resolved.DeclarationId}
    {traitName methodName : String} {operand : Ty}
    {parameters returns : List Ty} {predicates : List ProgramPredicate}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (binders : TypeParameterBindersWellFormed context)
    (signatures : context.signatures = inferenceContext.signatures)
    (traitNameEq : (inferenceContext.signatures.trait? trait).map (·.name) = some traitName)
    (operandFormed : TypeAdmissible context operand)
    (success : Detail.operatorTraitPredicates inferenceContext trait methodName operand
      parameters returns = .ok predicates) :
    ∀ predicate ∈ predicates, PredicateAdmissible context predicate :=
  operator_profile_predicates catalog binders operandFormed
    (operatorTraitPredicates_instantiates signatures traitNameEq success)

/-- Every issued identity selects one of the producer's exact predicates.
Ledger extension preserves this statement without assuming arbitrary row formation. -/
theorem issued_identity_formed
    {context : SourceSemantics.Context} {requirements : List Requirement}
    {predicates : List ProgramPredicate} {ids : List RequirementId}
    (correspondence : RequirementPredicatesCorrespond requirements predicates ids)
    (formed : ∀ predicate ∈ predicates, PredicateAdmissible context predicate)
    {id : RequirementId} (member : id ∈ ids) :
    ∃ predicate, ({ id, predicate } : Requirement) ∈ requirements ∧
      PredicateAdmissible context predicate := by
  induction correspondence with
  | nil => simp at member
  | @cons predicate head predicates ids headMember _ induction =>
      rcases List.mem_cons.mp member with rfl | tailMember
      · exact ⟨predicate, headMember, formed predicate (by simp)⟩
      · exact induction (fun predicate member => formed predicate (by simp [member])) tailMember

end Solcore.SourceSemantics.SourceInferenceRequirementFormation
