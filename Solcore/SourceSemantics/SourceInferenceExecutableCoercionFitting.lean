import Solcore.Frontend.SourceInference.SelectedCoercionPlanTrait
import Solcore.SourceSemantics.SourceInferenceExecutableCoercionRetention

/-! Actual expected-type fitting consumes executable interfaces only at its
retained coercion sites. Empty fitting paths require no Coerce declaration.
All method type equations still come from the original inference plan. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

private theorem committed_member_has_planned_correspondence_in_active
    {requirements : List Requirement}
    {plan : List Detail.PlannedCoercionStep}
    {steps : List CoercionStep}
    (corresponds : Detail.CoercionPlanCommitCorresponds requirements
      plan steps)
    {committed : CoercionStep}
    (member : committed ∈ steps) :
    ∃ planned, planned ∈ plan ∧
      Detail.PlannedCoercionStep.CommitCorresponds requirements
        planned committed := by
  induction corresponds with
  | nil => simp at member
  | @cons planned committed plan steps head tail induction =>
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact ⟨planned, by simp, head⟩
      · obtain ⟨candidate, candidateMember, candidateCorresponds⟩ :=
          induction member
        exact ⟨candidate, by simp [candidateMember], candidateCorresponds⟩

private theorem solved_row_of_requirement_mem
    {inferenceContext : Frontend.SourceInference.Context}
    {state : Frontend.SourceInference.State}
    {requirements : List Requirement}
    {solved : List SolvedRequirement}
    (corresponds : Forall₂ (fun requirement row =>
      row.id = requirement.id ∧
        row.predicate = Detail.applyPredicate state requirement.predicate ∧
        Detail.solveRequirementEvidence inferenceContext state requirement =
          .ok row.evidence) requirements solved)
    {requirement : Requirement}
    (member : requirement ∈ requirements) :
    ∃ row, row ∈ solved ∧
      row.id = requirement.id ∧
      row.predicate = Detail.applyPredicate state requirement.predicate := by
  induction corresponds with
  | nil => simp at member
  | @cons head row tail rows headCorresponds tailCorresponds induction =>
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact ⟨row, by simp, headCorresponds.1, headCorresponds.2.1⟩
      · obtain ⟨found, foundMember, idEq, predicateEq⟩ := induction member
        exact ⟨found, by simp [foundMember], idEq, predicateEq⟩

theorem coercionPlan?_some_committedPathValid_from_interfaces
    {inferenceContext : Frontend.SourceInference.Context}
    {solverContext : Frontend.SourceInference.Context}
    {state later : State} {source target : Ty}
    {plan : List Detail.PlannedCoercionStep}
    {solved : List SolvedRequirement}
    {base active : SourceSemantics.Context}
    {ledgerSource : TypedSource} {occurrence : NodeId}
    (planSuccess :
      Detail.coercionPlan? inferenceContext state source target =
        .ok (some plan))
    (interfaces : ExecutableCoercionInterfaces.SourceInterfaces
      inferenceContext.signatures solved ledgerSource)
    (present : CoercionPrimariesPresent ledgerSource (Detail.commitCoercionPlan state plan).1)
    (requirementsSubset :
      (Detail.commitCoercionPlan state plan).2.requirements ⊆
        later.requirements)
    (catalog : SignatureCatalogWellFormed active.signatures)
    (signaturesEq : active.signatures = inferenceContext.signatures)
    (solveSuccess : Detail.solveRequirements solverContext later
      later.requirements = .ok solved)
    (solvedEq : base.solvedRequirements = solved)
    (ledger : ScopedRequirementLedgerWellFormed base ledgerSource)
    (ownership : RequirementOwnership base ledgerSource)
    (activeSignaturesEq : active.signatures = base.signatures)
    (activeRequirementsEq :
      active.solvedRequirements = base.solvedRequirements)
    (assumptionsMono : base.assumptions ⊆ active.assumptions)
    (covered : TemplateScopeCovered ledgerSource active occurrence)
    (occurs : ∀ id,
      id ∈ coercionRequirementIds
        (Detail.commitCoercionPlan state plan).1 →
      PrimaryRequirementOccursAt ledgerSource occurrence id) :
    CoercionPathValid active
      (later.inference.substitution.apply source)
      (later.inference.substitution.apply target)
      ((Detail.commitCoercionPlan state plan).1.map
        (CoercionStep.applySubstitution
          later.inference.substitution)) := by
  have corresponds : Detail.CoercionPlanCommitCorresponds later.requirements
      plan (Detail.commitCoercionPlan state plan).1 :=
    (Detail.commitCoercionPlan_corresponds state plan).mono requirementsSubset
  by_cases empty : (Detail.commitCoercionPlan state plan).1 = []
  · have structural := corresponds.isValid (Detail.coercionPlan?_some_isValid planSuccess)
    have normalized := Frontend.SourceInference.CoercionPath.isValid_applySubstitution
      later.inference.substitution structural
    apply CoercionPathValid.of_isValid normalized
    intro step member
    simp only [empty, List.map_nil, List.not_mem_nil] at member
  · obtain ⟨committed, committedMember⟩ := List.exists_mem_of_ne_nil _ empty
    obtain ⟨planned, plannedMember, correspondence⟩ :=
      committed_member_has_planned_correspondence_in_active corresponds committedMember
    obtain ⟨trait, traitSuccess, traitEq⟩ :=
      Detail.SelectedCoercionPlanTrait.trait_of_accepted planSuccess plannedMember
    obtain ⟨row, rowMember, rowId, predicateEq⟩ :=
      solved_row_of_requirement_mem (solveRequirements_corresponds solveSuccess) correspondence.primary_mem
    obtain ⟨node, nodeMember, finalStep, finalSite, finalId⟩ := present committed committedMember
    have interface := interfaces.interface_at nodeMember finalSite rowMember (rowId.trans finalId.symm)
    have rowTrait : row.predicate.trait = .declaration trait := by
      rw [predicateEq]
      exact traitEq
    rw [rowTrait] at interface
    obtain ⟨profile, profileSuccess⟩ := interface.profile rfl
    exact coercionPlan?_some_committedPathValid_at_scoped_in_active
      traitSuccess profileSuccess planSuccess requirementsSubset catalog signaturesEq
      interface.traitName solveSuccess solvedEq ledger ownership activeSignaturesEq
      activeRequirementsEq assumptionsMono covered occurs

theorem withExpected_success_coercionPathValid_from_interfaces
    {inferenceContext : Frontend.SourceInference.Context}
    {solverContext : Frontend.SourceInference.Context}
    {state later : State} {actual : InferredExpression}
    {expected : Option Ty} {result : Detail.ExpectationResult}
    {solved : List SolvedRequirement}
    {base active : SourceSemantics.Context}
    {ledgerSource : TypedSource} {occurrence : NodeId}
    (success : Detail.withExpected inferenceContext state actual expected =
      .ok result)
    (interfaces : ExecutableCoercionInterfaces.SourceInterfaces
      inferenceContext.signatures solved ledgerSource)
    (present : CoercionPrimariesPresent ledgerSource result.coercions)
    (requirementsSubset : result.state.requirements ⊆ later.requirements)
    (catalog : SignatureCatalogWellFormed active.signatures)
    (signaturesEq : active.signatures = inferenceContext.signatures)
    (solveSuccess : Detail.solveRequirements solverContext later
      later.requirements = .ok solved)
    (solvedEq : base.solvedRequirements = solved)
    (ledger : ScopedRequirementLedgerWellFormed base ledgerSource)
    (ownership : RequirementOwnership base ledgerSource)
    (activeSignaturesEq : active.signatures = base.signatures)
    (activeRequirementsEq :
      active.solvedRequirements = base.solvedRequirements)
    (assumptionsMono : base.assumptions ⊆ active.assumptions)
    (covered : TemplateScopeCovered ledgerSource active occurrence)
    (occurs : ∀ id, id ∈ coercionRequirementIds result.coercions →
      PrimaryRequirementOccursAt ledgerSource occurrence id) :
    CoercionPathValid active
      (later.inference.substitution.apply
        (result.state.resolve actual.type))
      (later.inference.substitution.apply result.expression.type)
      (result.coercions.map
        (CoercionStep.applySubstitution
          later.inference.substitution)) := by
  rcases Detail.withExpected_success_cases success with
    ⟨coercionsEq, _, typeEq⟩ |
      ⟨expectedType, plan, _, planSuccess, resultEq⟩
  · rw [coercionsEq]
    simp only [List.map_nil]
    rw [typeEq]
    exact .nil _
  · subst expected
    subst result
    change CoercionPathValid active
      (later.inference.substitution.apply
        ((Detail.commitCoercionPlan state plan).2.resolve actual.type))
      (later.inference.substitution.apply (state.resolve expectedType))
      ((Detail.commitCoercionPlan state plan).1.map
        (CoercionStep.applySubstitution later.inference.substitution))
    rw [Detail.commitCoercionPlan_resolve]
    exact coercionPlan?_some_committedPathValid_from_interfaces
      planSuccess interfaces present requirementsSubset catalog
      signaturesEq solveSuccess solvedEq ledger ownership
      activeSignaturesEq activeRequirementsEq assumptionsMono covered occurs

theorem
    recordExpressionWithExpected_success_ordinaryExpressionTypingBase_from_interfaces
    {inferenceContext : Frontend.SourceInference.Context}
    {solverContext : Frontend.SourceInference.Context}
    {source : Syntax.Expr} {id : ExpressionId}
    {rawType : Ty} {form : ExpressionForm}
    {owned : List RequirementId} {expected : Option Ty}
    {state later : State}
    {localSchemeInstantiationStart : Option Nat}
    {result : InferredExpression × State}
    {roots : List NodeId}
    {solved : List SolvedRequirement}
    {base active : SourceSemantics.Context}
    {semanticSource evidenceSource : TypedSource}
    (success : Detail.recordExpressionWithExpected inferenceContext source id
      rawType form owned expected state localSchemeInstantiationStart =
        .ok result)
    (substitutionExtends :
      later.inference.substitution.SemanticallyExtends
        result.2.inference.substitution)
    (requirementsSubset : result.2.requirements ⊆ later.requirements)
    (retained : ExpressionRequirementsRetainedAt
      (result.2.toTypedSource roots) evidenceSource result.1.id)
    (formType : ExpressionFormHasRawType semanticSource active
      (form.applySubstitution later.inference.substitution)
      (later.inference.substitution.apply rawType) (.ordinary owned))
    (rawAdmissible : TypeAdmissible active
      (later.inference.substitution.apply rawType))
    (interfaces : ExecutableCoercionInterfaces.SourceInterfaces
      inferenceContext.signatures solved evidenceSource)
    (coercionsRetained : ExpressionCoercionPrimariesRetainedAt
      (result.2.toTypedSource roots) evidenceSource result.1.id)
    (catalog : SignatureCatalogWellFormed active.signatures)
    (signaturesEq : active.signatures = inferenceContext.signatures)
    (solveSuccess : Detail.solveRequirements solverContext later
      later.requirements = .ok solved)
    (solvedEq : base.solvedRequirements = solved)
    (ledger : ScopedRequirementLedgerWellFormed base evidenceSource)
    (ownership : RequirementOwnership base evidenceSource)
    (activeSignaturesEq : active.signatures = base.signatures)
    (activeRequirementsEq :
      active.solvedRequirements = base.solvedRequirements)
    (assumptionsMono : base.assumptions ⊆ active.assumptions)
    (covered : TemplateScopeCovered evidenceSource active
      (.expression result.1.id)) :
    ExpressionTypingBase (result.2.toTypedSource roots) semanticSource active
      later.inference.substitution result.1 := by
  obtain ⟨fitted, fittedSuccess, resultExpressionEq, resultStateEq⟩ :=
    Detail.recordExpressionWithExpected_success_record success
  have recordedContains : ContainsExpression
      (result.2.toTypedSource roots) result.1.id {
        id := result.1.id
        span := source.span
        type := result.1.type
        form
        requirements := owned ++
          Detail.coercionRequirements fitted.coercions
        coercions := fitted.coercions
        localSchemeInstantiationStart
      } := by
    rw [resultExpressionEq, resultStateEq]
    exact recordNode_containsExpression fitted.state _ roots
  have fittedRequirementsSubset :
      fitted.state.requirements ⊆ later.requirements := by
    intro requirement member
    apply requirementsSubset
    rw [resultStateEq]
    exact member
  have fittedSubstitutionExtends :
      later.inference.substitution.SemanticallyExtends
        fitted.state.inference.substitution := by
    simpa [resultStateEq, State.recordNode] using substitutionExtends
  have occursOwned : ∀ requirement, requirement ∈ owned →
      PrimaryRequirementOccursAt evidenceSource
        (.expression result.1.id) requirement := by
    intro requirement member
    apply retained recordedContains
    simp [member]
  have occursCoercion : ∀ requirement,
      requirement ∈ coercionRequirementIds fitted.coercions →
        PrimaryRequirementOccursAt evidenceSource
          (.expression result.1.id) requirement := by
    intro requirement member
    apply retained recordedContains
    change requirement ∈
      owned ++ Detail.coercionRequirements fitted.coercions
    apply List.mem_append_right owned
    simpa [Detail.coercionRequirements, coercionRequirementIds] using member
  have ownedValid : RequirementIdsValid active owned :=
    ledger.requirementIdsValidAt ownership activeSignaturesEq
      activeRequirementsEq assumptionsMono covered occursOwned
  have present : CoercionPrimariesPresent evidenceSource fitted.coercions := by
    intro step member
    exact coercionsRetained.present recordedContains step (List.mem_append_left _ member)
  have path :=
    withExpected_success_coercionPathValid_from_interfaces
      fittedSuccess interfaces present fittedRequirementsSubset
      catalog signaturesEq solveSuccess solvedEq ledger ownership
      activeSignaturesEq activeRequirementsEq assumptionsMono covered
      occursCoercion
  have rawEndpointEq :
      later.inference.substitution.apply (fitted.state.resolve rawType) =
        later.inference.substitution.apply rawType :=
    TypeSystem.InferState.apply_resolve_eq_apply fittedSubstitutionExtends
      rawType
  have finalPath : CoercionPathValid active
      (later.inference.substitution.apply rawType)
      (later.inference.substitution.apply result.1.type)
      (fitted.coercions.map
        (CoercionStep.applySubstitution
          later.inference.substitution)) := by
    rw [resultExpressionEq, ← rawEndpointEq]
    exact path
  have requirementsEq :
      owned ++ Detail.coercionRequirements fitted.coercions =
      owned ++ coercionRequirementIds
        (fitted.coercions.map
          (CoercionStep.applySubstitution
            later.inference.substitution)) := by
    rw [FlexibleSubstitution.coercionRequirementIds_applySubstitution]
    rfl
  refine ExpressionTypingBase.intro (plan := .ordinary owned)
    recordedContains (by rfl) ?_ rawAdmissible ?_
  · simpa [ExpressionNode.applySubstitution] using formType
  · exact ExpressionRequirementPlan.Valid.ordinary ownedValid finalPath
      requirementsEq

end Solcore.SourceSemantics.SourceInferenceSoundness
