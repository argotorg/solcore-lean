import Solcore.Frontend.SourceInference.ProgramProperties
import Solcore.SourceSemantics.TraitSubstitutionProperties
import Solcore.SourceSemantics.TraitResolutionSoundness

/-! Conditional bridge from executable finalization to declarative typing. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.SourceInferenceSoundness

open Frontend SourceInference

private theorem requirementId_beq_iff_eq
    (left right : RequirementId) :
    (left == right) = true ↔ left = right := by
  rw [show (left == right) = (left.index == right.index) by rfl]
  rw [beq_iff_eq]
  constructor
  · intro indices_eq
    cases left
    cases right
    cases indices_eq
    rfl
  · intro same
    exact congrArg RequirementId.index same

private theorem requirementId_contains_iff_mem
    (id : RequirementId) (ids : List RequirementId) :
    ids.contains id = true ↔ id ∈ ids := by
  induction ids with
  | nil => simp
  | cons head tail induction =>
      rw [List.contains_cons, List.mem_cons]
      rw [Bool.or_eq_true, requirementId_beq_iff_eq, induction]

/-- Successful normalized predicate solving retains declaratively valid
evidence.  The available assumptions are normalized exactly once by the same
inference substitution used by the executable solver. -/
theorem solveNormalizedPredicate_sound
    {context : Frontend.SourceInference.Context}
    {state : Frontend.SourceInference.State}
    {goal : ProgramPredicate}
    {retained : PredicateEvidence}
    (success : Detail.solveNormalizedPredicate context state goal =
      .ok retained) :
    RetainedEvidenceValid
      (context.assumptions.map (Detail.applyPredicate state))
      context.signatures.resolutionRules goal retained := by
  unfold Detail.solveNormalizedPredicate at success
  cases assumed : Detail.requirementAssumption? context state goal with
  | true =>
      simp only [assumed, ↓reduceIte, Except.ok.injEq] at success
      subst retained
      apply RetainedEvidenceValid.intro (.assumption goal)
      apply EvidenceValid.assumption
      unfold Detail.requirementAssumption? at assumed
      obtain ⟨assumption, member, equal⟩ := List.any_eq_true.mp assumed
      apply List.mem_map.mpr
      exact ⟨assumption, member, of_decide_eq_true equal⟩
  | false =>
      cases resolved : TypedTraitResolution.resolve
          context.signatures.resolutionRules context.traitDepth goal with
      | mk outcome statistics =>
          cases outcome with
          | noSolution =>
              simp [assumed, resolved] at success
          | inconclusive reason =>
              simp [assumed, resolved] at success
          | success evidence =>
              simp [assumed, resolved] at success
              subst retained
              apply RetainedEvidenceValid.weakenAssumptions
                (smaller := [])
              · simp
              · exact
                  TraitResolutionSoundness.resolve_success_retainedEvidenceValid
                    (rules := context.signatures.resolutionRules)
                    (maxDepth := context.traitDepth)
                    (goal := goal)
                    (retained := evidence)
                    (by simp [resolved])

/-- `solvePredicate` first normalizes its source predicate and then delegates
to `solveNormalizedPredicate`, so its successful result has the same retained
evidence guarantee at the normalized goal. -/
theorem solvePredicate_sound
    {context : Frontend.SourceInference.Context}
    {state : Frontend.SourceInference.State}
    {source : ProgramPredicate}
    {retained : PredicateEvidence}
    (success : Detail.solvePredicate context state source = .ok retained) :
    RetainedEvidenceValid
      (context.assumptions.map (Detail.applyPredicate state))
      context.signatures.resolutionRules
      (Detail.applyPredicate state source) retained := by
  exact solveNormalizedPredicate_sound success

/-- An ordinary solved ledger row inherits the predicate solver's evidence
validity once the executable and declarative contexts agree on the catalog and
on the normalized declaration assumptions. -/
theorem solveRequirementEvidence_ordinary_sound
    {inferenceContext : Frontend.SourceInference.Context}
    {state : Frontend.SourceInference.State}
    {requirement : Requirement}
    {retained : PredicateEvidence}
    {semanticContext : SourceSemantics.Context}
    (ordinary : requirement.id ∉ state.localSchemeAssumptions)
    (signatures_eq : semanticContext.signatures = inferenceContext.signatures)
    (assumptions_eq : semanticContext.assumptions =
      inferenceContext.assumptions.map (Detail.applyPredicate state))
    (success : Detail.solveRequirementEvidence inferenceContext state
      requirement = .ok retained) :
    SolvedRequirementValid semanticContext {
      id := requirement.id
      predicate := Detail.applyPredicate state requirement.predicate
      evidence := retained
    } := by
  have ordinaryContains :
      state.localSchemeAssumptions.contains requirement.id = false := by
    cases containsEq : state.localSchemeAssumptions.contains requirement.id with
    | false => rfl
    | true =>
        exact False.elim
          (ordinary ((requirementId_contains_iff_mem _ _).mp containsEq))
  have normalizedSuccess :
      Detail.solveNormalizedPredicate inferenceContext state
          (Detail.applyPredicate state requirement.predicate) = .ok retained := by
    unfold Detail.solveRequirementEvidence at success
    rw [ordinaryContains] at success
    simpa using success
  apply SolvedRequirementValid.intro
  rw [signatures_eq, assumptions_eq]
  exact solveNormalizedPredicate_sound normalizedSuccess

/-- Qualified-local template rows bypass trait search and retain exactly an
assumption for their normalized predicate. -/
theorem solveRequirementEvidence_template_eq
    {context : Frontend.SourceInference.Context}
    {state : Frontend.SourceInference.State}
    {requirement : Requirement}
    {retained : PredicateEvidence}
    (template : requirement.id ∈ state.localSchemeAssumptions)
    (success : Detail.solveRequirementEvidence context state requirement =
      .ok retained) :
    retained = .assumption
      (Detail.applyPredicate state requirement.predicate) := by
  have templateContains :
      state.localSchemeAssumptions.contains requirement.id = true := by
    exact (requirementId_contains_iff_mem _ _).mpr template
  have retainedEq :
      (.assumption (Detail.applyPredicate state requirement.predicate) :
        PredicateEvidence) = retained := by
    unfold Detail.solveRequirementEvidence at success
    rw [templateContains] at success
    change Except.ok (.assumption
      (Detail.applyPredicate state requirement.predicate)) =
        Except.ok retained at success
    exact Except.ok.inj success
  exact retainedEq.symm

end Solcore.SourceSemantics.SourceInferenceSoundness

namespace Solcore.SourceSemantics.FlexibleSubstitution

open Frontend SourceInference TypeSystem

/-- Once the inference pass has supplied a semantically valid closing
substitution, successful finalization transports the corresponding declarative
body derivation to the emitted typed source and result type. -/
theorem finalize_bodyHasType
    {inferenceContext : Frontend.SourceInference.Context}
    {type : Ty} {state : State} {roots : List NodeId} {result : Result}
    {sourceContext targetContext : SourceSemantics.Context}
    {closedVariables : List TypeVarId} {facts : BodyFacts}
    (success : Detail.finalize inferenceContext type state roots = .ok result)
    (catalog : SignatureCatalogWellFormed sourceContext.signatures)
    (contextValid : ContextSubstitutionValid result.substitution
      closedVariables sourceContext targetContext)
    (typing : BodyHasType (state.toTypedSource roots) sourceContext type facts) :
    BodyHasType result.typedSource targetContext result.type
      (applyBodyFacts result.substitution facts) := by
  rw [Detail.finalize_typedSource success, Detail.finalize_type success]
  exact BodyHasType.applySubstitution catalog contextValid typing

end Solcore.SourceSemantics.FlexibleSubstitution
