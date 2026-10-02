import Solcore.SourceSemantics.CoreLowering.CallableNamedMetadata
import Solcore.SourceSemantics.TraitResolutionSoundness
import Solcore.SourceSemantics.Dynamic.Evidence

/-! Exact ordered evidence metadata and independent semantic dictionaries.
Lookup uses the first matching goal, including when later goals repeat. Resolver
success supplies validity through the existing independent soundness bridge. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableEvidenceEnvironment
open Frontend SourceInference Solcore.SourceSemantics.Dynamic
open CallableNamedMetadata (evidence environment evidence_represents)

@[simp] theorem evidence_goal (retained : TypedTraitResolution.Evidence) :
    (evidence retained).goal = SourceCompilationPlan.runtimeEvidenceGoal retained := by
  cases retained; simp [evidence, TraitEvidence.goal, SourceCompilationPlan.runtimeEvidenceGoal]

/-- The raw executable list is kept in full; equal goals do not identify trees. -/
theorem lookup_of_find {available : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    {goal : ProgramPredicate} {retained : TypedTraitResolution.Evidence}
    (found : available.find? (fun item => decide (SourceCompilationPlan.runtimeEvidenceGoal item = goal)) = some retained) :
    (environment available).LooksUp goal (evidence retained) := by
  induction available with
  | nil => cases found
  | cons head tail ih =>
    by_cases same : SourceCompilationPlan.runtimeEvidenceGoal head = goal
    · simp only [List.find?_cons, same, decide_true, Option.some.injEq] at found
      subst retained
      change EvidenceEnvironment.LooksUp ((_, _) :: _) _ _
      rw [same]
      exact .head
    · simp only [List.find?_cons, same, decide_false] at found
      exact .tail same (ih found)

/-- Every semantic first-match lookup comes from the same raw list entry. -/
theorem find_of_lookup {available : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    {goal : ProgramPredicate} {selected : TraitEvidence}
    (found : (environment available).LooksUp goal selected) :
    ∃ retained, available.find? (fun item => decide (SourceCompilationPlan.runtimeEvidenceGoal item = goal)) = some retained ∧
      selected = evidence retained := by
  induction available with
  | nil => cases found
  | cons head tail ih =>
    cases found with
    | head => exact ⟨head, by simp, rfl⟩
    | tail different found =>
      obtain ⟨retained, chosen, same⟩ := ih found
      exact ⟨retained, by simp [different, chosen], same⟩

/-- Closed implementation trees contain no assumption leaves to replace. -/
theorem closes_self (caller : EvidenceEnvironment) (retained : TypedTraitResolution.Evidence) :
    EvidenceCloses caller (evidence retained) (evidence retained) := by
  induction retained using TraitResolution.Evidence.rec
    (motive_2 := fun entries => Forall₂ (EvidenceCloses caller) (entries.map evidence) (entries.map evidence)) with
  | byImpl goal implementation premises ih => simpa only [evidence] using (EvidenceCloses.implementation (goal := goal) (implementation := implementation) ih)
  | nil => exact .nil
  | cons head rest headIH restIH => exact .cons headIH restIH

mutual
  theorem closes_functional {caller : EvidenceEnvironment} {openTree first second : TraitEvidence}
      (left : EvidenceCloses caller openTree first) (right : EvidenceCloses caller openTree second) : first = second := by
    cases left with
    | assumption first => cases right with | assumption second => exact first.functional second
    | implementation premises =>
      cases right with
      | implementation others => exact congrArg (TraitEvidence.implementation _ _) (closes_spine_functional premises others)

  theorem closes_spine_functional {caller : EvidenceEnvironment} {openTrees first second : List TraitEvidence}
      (left : Forall₂ (EvidenceCloses caller) openTrees first) (right : Forall₂ (EvidenceCloses caller) openTrees second) : first = second := by
    cases left with
    | nil => cases right; rfl
    | cons head tail =>
      cases right with
      | cons otherHead otherTail => rw [closes_functional head otherHead, closes_spine_functional tail otherTail]
end

def predicateEvidence : PredicateEvidence → TraitEvidence
  | .assumption goal => .assumption goal
  | .implementation retained => evidence retained

theorem predicate_represents (retained : PredicateEvidence) :
    PredicateEvidenceRepresents retained (predicateEvidence retained) := by
  cases retained with
  | assumption goal => exact .assumption goal
  | implementation retained => exact .implementation (evidence_represents retained)

theorem retained_valid {context : Context} {solved : SolvedRequirement}
    (valid : SolvedRequirementValid context solved) :
    EvidenceValid context.assumptions context.signatures.resolutionRules solved.predicate (predicateEvidence solved.evidence) := by
  cases valid with
  | intro retained =>
    cases retained with
    | intro represents valid =>
      rw [← represents.functional (predicate_represents _)]
      exact valid

/-- Actual resolver output is valid as the complete semantic tree, not merely
as a list of goals. No caller validity premise is required here. -/
theorem resolved_valid {program : CheckedProgram} {key : SourceCompilationPlan.Key}
    {predicates : List ProgramPredicate} {available : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    (resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program key predicates = .ok available) :
    (environment available).Valid program.signatures.resolutionRules ∧
      (environment available).map Prod.fst = predicates := by
  induction predicates generalizing available with
  | nil =>
    cases resolved
    refine ⟨?_, rfl⟩
    intro goal selected found
    cases found
  | cons predicate predicates ih =>
    simp only [SourceCompilationPlan.resolveRuntimeEvidenceEnvironment] at resolved
    split at resolved
    · cases resolved
    · cases resolved
    · rename_i chosen resolution
      have valid := TraitResolutionSoundness.resolve_success_evidenceValid resolution
      obtain ⟨semantic, represents, nativeValid⟩ := valid
      have nativeValid : EvidenceValid [] program.signatures.resolutionRules predicate (evidence chosen) := by
        rwa [represents.functional (evidence_represents _)] at nativeValid
      have goalEq := nativeValid.evidence_goal_eq
      cases chosen with
      | byImpl goal implementation premises =>
        simp only at resolved
        split at resolved
        · cases resolved
        · cases tail : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program key predicates with
          | error error => simp [tail, bind, Except.bind] at resolved
          | ok remaining =>
            simp only [tail, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at resolved
            subst available
            obtain ⟨tailValid, tailGoals⟩ := ih tail
            have same : goal = predicate := by simpa [evidence, TraitEvidence.goal] using goalEq
            refine ⟨?_, ?_⟩
            · intro selected output found
              cases found with
              | head => simpa only [← same, SourceCompilationPlan.runtimeEvidenceGoal] using nativeValid
              | tail _ found => exact tailValid _ _ found
            · change goal :: (environment remaining).map Prod.fst = _
              rw [same, tailGoals]

theorem resolved_covers {program : CheckedProgram} {key : SourceCompilationPlan.Key}
    {context : Context} {available : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    (signatures : context.signatures = program.signatures)
    (resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program key context.assumptions = .ok available) :
    (environment available).Covers context := by
  obtain ⟨valid, keys⟩ := resolved_valid resolved
  refine ⟨by simpa only [signatures] using valid, ?_⟩
  intro predicate member
  exact EvidenceEnvironment.LooksUp.exists_of_key_mem (keys ▸ member)

end Solcore.SourceSemantics.CoreLowering.CallableEvidenceEnvironment
