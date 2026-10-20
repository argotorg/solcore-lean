import Solcore.SourceSemantics.SourceInferenceRequirementSubstitution
import Solcore.SourceSemantics.SourceInferenceUnannotatedLetCertificate

/-! Actual issuance and finalizer continuation for retained qualified requirements. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.SourceInferenceRequirementFormation

open Frontend SourceInference TypeSystem
open SourceInferenceSoundness

private theorem row_eq_of_unique_ids
    {rows : List Requirement}
    (unique : (rows.map (fun row => row.id.index)).Nodup)
    {left right : Requirement} (leftMember : left ∈ rows)
    (rightMember : right ∈ rows) (same : left.id = right.id) : left = right := by
  induction rows generalizing left right with
  | nil => simp at leftMember
  | cons head tail induction =>
      simp only [List.map_cons, List.nodup_cons] at unique
      simp only [List.mem_cons] at leftMember rightMember
      rcases leftMember with rfl | leftMember
      · rcases rightMember with rfl | rightMember
        · rfl
        · exact False.elim (unique.1 (List.mem_map.mpr
            ⟨right, rightMember, congrArg RequirementId.index same.symm⟩))
      · rcases rightMember with rfl | rightMember
        · exact False.elim (unique.1 (List.mem_map.mpr
            ⟨left, leftMember, congrArg RequirementId.index same⟩))
        · exact induction unique.2 leftMember rightMember same

/-- A retained identity selects the producer's exact row because the actual
ledger has unique allocation identities. Merely sharing an ID without this
ledger invariant would not establish predicate formation. -/
theorem retained_issued_row_formed
    {context : SourceSemantics.Context} {state : State}
    {predicates : List ProgramPredicate} {ids : List RequirementId}
    (wellFormed : state.RequirementsWellFormed)
    (correspondence : RequirementPredicatesCorrespond state.requirements predicates ids)
    (formed : ∀ predicate ∈ predicates, PredicateAdmissible context predicate)
    {row : Requirement} (member : row ∈ state.requirements) (selected : row.id ∈ ids) :
    PredicateAdmissible context row.predicate := by
  obtain ⟨predicate, issuedMember, predicateFormed⟩ :=
    issued_identity_formed correspondence formed selected
  have unique : (state.requirements.map (fun row => row.id.index)).Nodup := by
    rw [show state.requirements.map (fun row => row.id.index) =
      List.range state.nextRequirement from wellFormed]
    exact List.nodup_range
  have same := row_eq_of_unique_ids unique member issuedMember rfl
  have predicateEq := congrArg Requirement.predicate same
  exact predicateEq.symm ▸ predicateFormed

/-- Candidate allocation, actual ledger retention and unique IDs establish
formation of every retained row owned by that candidate's signature batch. -/
theorem retained_candidate_row_formed
    {inferenceContext : Frontend.SourceInference.Context}
    {arguments : List InferredExpression} {integerOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected : Option Ty} {initial retained : State}
    {signature : ProgramFunctionSignature} {result : Detail.CandidateAttemptResult}
    {context : SourceSemantics.Context}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (binders : TypeParameterBindersWellFormed context)
    (residual : context.residualTypeVariables = true)
    (signatureMember : signature ∈ context.signatures.functions)
    (success : Detail.tryFunctionCandidate inferenceContext arguments integerOrigins
      call expected initial signature = .ok (some result))
    (included : result.state.requirements ⊆ retained.requirements)
    (wellFormed : retained.RequirementsWellFormed)
    {row : Requirement} (member : row ∈ retained.requirements)
    (selected : row.id ∈ result.signatureRequirements) :
    PredicateAdmissible context row.predicate := by
  have issuance := candidate_signature_issuance catalog binders residual signatureMember success
  exact retained_issued_row_formed wellFormed (issuance.1.mono included)
    issuance.2 member selected

/-- The actual outer substitution absorbs ready-state normalization. The
finalizer's no-capture fact removes the quantifier restriction, while the
separate semantic-extension premise records the genuine inference continuation. -/
theorem retained_predicate_normalization
    {ready : State} {outer : Substitution} {binder : TypedBinder}
    (continuation : outer.SemanticallyExtends ready.inference.substitution)
    (noCapture : Detail.LocalBinderInstantiationNoCapture outer binder)
    (predicate : ProgramPredicate) :
    TypedTraitResolution.applySubstitution (outer.without binder.scheme.quantified)
        (Detail.applyPredicate ready predicate) =
      TypedTraitResolution.applySubstitution outer predicate := by
  rw [FlexibleSubstitution.Substitution.without_eq_self_of_disjoint_domain
    outer binder.scheme.quantified noCapture.quantified_fresh]
  cases predicate with
  | mk trait subject arguments =>
      simp only [Detail.applyPredicate,
        TypedTraitResolution.applySubstitution, List.map_map]
      congr 1
      · exact continuation subject
      · apply List.map_congr_left
        intro argument _
        exact continuation argument

/-- Finalizer range formation closes one authentic retained issuance. This
requires the real ready-to-final substitution continuation, not a backwards
inference from the final requirement ledger. -/
theorem retained_predicate_formed
    {inferenceContext : Frontend.SourceInference.Context}
    {type : Ty} {state ready : State} {roots : List NodeId}
    {result : Frontend.SourceInference.Result}
    (resources : FinalInferenceResources inferenceContext type state roots result)
    {context : SourceSemantics.Context} {binder : TypedBinder} {predicate : ProgramPredicate}
    (binders : TypeParameterBindersWellFormed context)
    (signatures : context.signatures = inferenceContext.signatures)
    (parameters : context.typeParameters = inferenceContext.typeParameters)
    (owner : context.currentDeclaration = some inferenceContext.scope.genericOwner)
    (residual : context.residualTypeVariables = true)
    (continuation : result.substitution.SemanticallyExtends ready.inference.substitution)
    (noCapture : Detail.LocalBinderInstantiationNoCapture result.substitution binder)
    (formed : PredicateAdmissible context predicate) :
    PredicateAdmissible context
      (TypedTraitResolution.applySubstitution (result.substitution.without binder.scheme.quantified)
        (Detail.applyPredicate ready predicate)) := by
  rw [retained_predicate_normalization continuation noCapture]
  simpa only [Substitution.without, List.foldl_nil] using
    finalizer_predicate_formation resources binders signatures parameters owner residual formed []

/-- Assemble the existing generalized-initializer interface from the exact
selected raw issuances, actual finalization and actual substitution continuation.
The producer premise is restricted to this binder's retained template IDs. -/
theorem retained_formation_of_issuances
    {inferenceContext : Frontend.SourceInference.Context}
    {type : Ty} {state ready : State} {roots : List NodeId}
    {result : Frontend.SourceInference.Result}
    (resources : FinalInferenceResources inferenceContext type state roots result)
    {target : SourceSemantics.Context} {binder : TypedBinder}
    (binders : TypeParameterBindersWellFormed
      (localSchemeInitializerContext target (binder.applySubstitution result.substitution)))
    (signatures : target.signatures = inferenceContext.signatures)
    (parameters : target.typeParameters = inferenceContext.typeParameters)
    (owner : target.currentDeclaration = some inferenceContext.scope.genericOwner)
    (residual : target.residualTypeVariables = true)
    (continuation : result.substitution.SemanticallyExtends ready.inference.substitution)
    (noCapture : Detail.LocalBinderInstantiationNoCapture result.substitution binder)
    (issued : ∀ row ∈ ready.requirements, row.id ∈ localSchemeTemplateIds binder →
      PredicateAdmissible
        (localSchemeInitializerContext target (binder.applySubstitution result.substitution))
        row.predicate) :
    RetainedRequirementPredicateFormationAt ready binder result.substitution target := by
  intro row member selected
  exact retained_predicate_formed resources binders signatures parameters owner residual
    continuation noCapture (issued row member selected)

end Solcore.SourceSemantics.SourceInferenceRequirementFormation
