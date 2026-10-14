import Solcore.SourceSemantics.SourceInferenceExecutableOperatorRetention

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem
open ExecutableCoercionInterfaces

/-- Exact executable names for the ordinary requirement prefix issued at one
operator occurrence. The list is independent of later output coercions. -/
def OperatorNamesAt (signatures : ProgramSignatures) (solved : List SolvedRequirement)
    (requirements : List RequirementId) (dispatch : String → Prop) : Prop :=
  ∀ primary companions name, requirements = primary :: companions → dispatch name →
    ∃ actual trait,
      solved.filter (fun row => decide (row.id = primary)) = [actual] ∧
      actual.predicate.trait = .declaration trait ∧
      (signatures.trait? trait).map (·.name) = some name

theorem OperatorNamesAt.of_retained
    {signatures : ProgramSignatures} {solved : List SolvedRequirement}
    {before after : TypedSource} {id : ExpressionId} {node : ExpressionNode}
    {requirements : List RequirementId} {dispatch : String → Prop}
    (retained : ExpressionOperatorSiteRetainedAt before after id)
    (interfaces : SourceInterfaces signatures solved after)
    (found : ContainsExpression before id node)
    (layout : node.requirements = requirements ++ node.coercions.flatMap CoercionStep.requirements)
    (dispatchAt : ∀ name, dispatch name → operatorDispatch node name) :
    OperatorNamesAt signatures solved requirements dispatch := by
  intro primary companions name headEq selected
  obtain ⟨finalNode, finalFound, finalLayout, finalDispatch⟩ :=
    retained found primary companions name (by simpa only [headEq] using layout) (dispatchAt name selected)
  exact interfaces.operators finalNode finalFound.1 primary companions name finalLayout finalDispatch

theorem operatorTraitPredicates_primary
    {context : Frontend.SourceInference.Context} {trait : Resolved.DeclarationId}
    {method : String} {operand : Ty} {parameters returns : List Ty}
    {predicates : List ProgramPredicate}
    (accepted : Detail.operatorTraitPredicates context trait method operand parameters returns = .ok predicates) :
    ∃ companions, predicates = {trait := .declaration trait, subject := operand, arguments := []} :: companions := by
  unfold Detail.operatorTraitPredicates at accepted
  cases selected : Detail.exactOperatorTraitMethod context trait method with
  | error error => simp [selected, bind, Except.bind] at accepted
  | ok pair =>
    simp only [selected, bind, Except.bind] at accepted
    split at accepted
    · split at accepted
      · cases accepted
        exact ⟨_, rfl⟩
      · cases accepted
    · cases accepted

theorem RequirementPredicatesCorrespond.first
    {requirements : List Requirement} {predicate : ProgramPredicate}
    {predicates : List ProgramPredicate} {ids : List RequirementId}
    (corresponds : RequirementPredicatesCorrespond requirements (predicate :: predicates) ids) :
    ∃ primary companions, ids = primary :: companions ∧
      ({id := primary, predicate := predicate} : Requirement) ∈ requirements := by
  cases corresponds with
  | cons member _ => exact ⟨_, _, rfl, member⟩

private theorem selectedSolvedRow
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

theorem OperatorNamesAt.traitName
    {context : Frontend.SourceInference.Context} {state : State}
    {signatures : ProgramSignatures} {solved : List SolvedRequirement}
    {ids : List RequirementId} {dispatch : String → Prop}
    (names : OperatorNamesAt signatures solved ids dispatch)
    (accepted : Detail.solveRequirements context state state.requirements = .ok solved)
    {trait : Resolved.DeclarationId} {operand : Ty} {companions : List ProgramPredicate}
    (corresponds : RequirementPredicatesCorrespond state.requirements
      ({trait := .declaration trait, subject := operand, arguments := []} :: companions) ids)
    {name : String} (selected : dispatch name) :
    (signatures.trait? trait).map (·.name) = some name := by
  obtain ⟨primary, companions, headEq, member⟩ := RequirementPredicatesCorrespond.first corresponds
  obtain ⟨row, present, identity, predicate⟩ :=
    selectedSolvedRow (solveRequirements_corresponds accepted) member
  obtain ⟨actual, actualTrait, unique, actualSelected, actualName⟩ :=
    names primary companions name headEq selected
  have inFilter : row ∈ solved.filter (fun row => decide (row.id = primary)) :=
    List.mem_filter.mpr ⟨present, by simp only [identity, decide_true]⟩
  rw [unique] at inFilter
  have same : row = actual := List.mem_singleton.mp inFilter
  subst actual
  have original : row.predicate.trait = .declaration trait := by
    rw [predicate]
    rfl
  have sameTrait : trait = actualTrait := by
    simpa only [original, ProgramTraitId.declaration.injEq] using actualSelected
  simpa only [sameTrait] using actualName

end Solcore.SourceSemantics.SourceInferenceSoundness
