import Solcore.SourceSemantics.CoreLowering.CallableEvidenceEnvironment

/-! The real call-dictionary materializer produces the independent ordered
requirement judgment. Retained-ledger validity and exact caller evidence remain
explicit; a successful goal check alone cannot establish either condition.
Coercion ledger slicing and method dictionary assembly are separate boundaries. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableCallEvidence
open Frontend SourceInference Solcore.SourceSemantics.Dynamic
open CallableNamedMetadata (evidence environment)
open CallableEvidenceEnvironment

abbrev Selected (caller : SourceSpecialization.SpecializedFunction) (id : RequirementId)
    (solved : SolvedRequirement) : Prop :=
  caller.function.solvedRequirements.filter (fun row => decide (row.id = id)) = [solved]

theorem Selected.contains {caller : SourceSpecialization.SpecializedFunction} {id : RequirementId}
    {solved : SolvedRequirement} (selected : Selected caller id solved)
    {context : Context} (ledger : context.solvedRequirements = caller.function.solvedRequirements) :
    ContainsRequirement context id solved := by
  have member : solved ∈ caller.function.solvedRequirements.filter (fun row => decide (row.id = id)) := by
    rw [selected]; simp
  have matched := List.mem_filter.mp member
  exact ⟨ledger ▸ matched.1, of_decide_eq_true matched.2⟩

theorem Selected.unique {caller : SourceSpecialization.SpecializedFunction} {id : RequirementId}
    {solved other : SolvedRequirement} (selected : Selected caller id solved)
    {context : Context} (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (contains : ContainsRequirement context id other) : other = solved := by
  have member : other ∈ caller.function.solvedRequirements.filter (fun row => decide (row.id = id)) :=
    List.mem_filter.mpr ⟨ledger ▸ contains.1, by simp [contains.2]⟩
  rw [selected] at member
  exact List.mem_singleton.mp member

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {result : β}
    (accepted : action >>= next = .ok result) : ∃ value, action = .ok value ∧ next value = .ok result := by
  cases action with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem map_ok {α β ε : Type} {action : Except ε α} {f : α → β} {result : β}
    (accepted : f <$> action = .ok result) : ∃ value, action = .ok value ∧ result = f value := by
  cases action with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, (Except.ok.inj accepted).symm⟩

/-- One successful step retains its actual singleton ledger selection and the
complete evidence closure. This also records the exact remaining ordered call. -/
theorem cons_accepted {caller : SourceSpecialization.SpecializedFunction} {occurrence : ExpressionId}
    {available result : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    {id : RequirementId} {ids : List RequirementId} {predicate : ProgramPredicate} {predicates : List ProgramPredicate}
    (accepted : SourceCompilationPlan.materializeCallEvidence caller occurrence available
      (id :: ids) (predicate :: predicates) = .ok result) :
    ∃ solved head tail, Selected caller id solved ∧ solved.predicate = predicate ∧
      EvidenceCloses (environment available) (predicateEvidence solved.evidence) (evidence head) ∧
      SourceCompilationPlan.runtimeEvidenceGoal head = predicate ∧
      SourceCompilationPlan.materializeCallEvidence caller occurrence available ids predicates = .ok tail ∧
      result = head :: tail := by
  simp only [SourceCompilationPlan.materializeCallEvidence] at accepted
  obtain ⟨solved, picked, accepted⟩ := bind_ok accepted
  have selected : Selected caller id solved := by
    change (match caller.function.solvedRequirements.filter (fun row => decide (row.id = id)) with
      | [] => .error (.missingSolvedRequirement caller.key occurrence id)
      | [row] => .ok row
      | rows => .error (.duplicateSolvedRequirements caller.key occurrence id rows.length) : Except SourceTypedRuntime.RuntimeError SolvedRequirement) = .ok solved at picked
    cases filtered : caller.function.solvedRequirements.filter (fun row => decide (row.id = id)) with
    | nil => simp [filtered] at picked
    | cons row rest =>
      cases rest with
      | nil => simp only [filtered, Except.ok.injEq] at picked; subst solved; exact filtered
      | cons other rest => simp [filtered] at picked
  rcases solved with ⟨solvedId, solvedPredicate, retained⟩
  split at accepted
  · cases accepted
  · rename_i equalPredicate
    have matchedPredicate : solvedPredicate = predicate := by simpa using equalPredicate
    split at accepted
    · cases accepted
    · rename_i equalGoal
      have matchedGoal : retained.goal = solvedPredicate := by simpa using equalGoal
      cases retained with
      | implementation raw =>
        change (List.cons raw <$> SourceCompilationPlan.materializeCallEvidence caller occurrence available ids predicates) = .ok result at accepted
        obtain ⟨tail, remaining, same⟩ := map_ok accepted
        refine ⟨_, raw, tail, selected, matchedPredicate, closes_self _ raw, ?_, remaining, same⟩
        cases raw
        exact matchedGoal.trans matchedPredicate
      | assumption goal =>
        change (match available.find? (fun item => decide (SourceCompilationPlan.runtimeEvidenceGoal item = goal)) with
          | some raw => List.cons raw <$> SourceCompilationPlan.materializeCallEvidence caller occurrence available ids predicates
          | none => .error (.missingRuntimeAssumptionEvidence caller.key occurrence id goal)) = .ok result at accepted
        cases found : available.find? (fun item => decide (SourceCompilationPlan.runtimeEvidenceGoal item = goal)) with
        | none => simp [found] at accepted
        | some raw =>
          rw [found] at accepted
          obtain ⟨tail, remaining, same⟩ := map_ok accepted
          refine ⟨_, raw, tail, selected, matchedPredicate, .assumption (lookup_of_find found), ?_, remaining, same⟩
          have rawGoal := List.find?_some found
          have rawSame : SourceCompilationPlan.runtimeEvidenceGoal raw = goal := of_decide_eq_true rawGoal
          exact rawSame.trans (matchedGoal.trans matchedPredicate)

/-- Compiler success becomes the independent requirement-production judgment
when the same retained ledger and caller dictionary have source validity. -/
theorem produces {caller : SourceSpecialization.SpecializedFunction} {occurrence : ExpressionId}
    {available result : SourceTypedRuntime.RuntimeEvidenceEnvironment} {ids : List RequirementId}
    {predicates : List ProgramPredicate} {context : Context}
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (retained : SolvedRequirementsValid context caller.function.solvedRequirements)
    (valid : (environment available).Valid context.signatures.resolutionRules)
    (accepted : SourceCompilationPlan.materializeCallEvidence caller occurrence available ids predicates = .ok result) :
    RequirementsProduceEnvironment context (environment available) ids predicates (environment result) := by
  induction ids generalizing predicates result with
  | nil =>
    cases predicates with
    | nil => cases accepted; exact .nil
    | cons predicate predicates => cases accepted
  | cons id ids ih =>
    cases predicates with
    | nil => cases accepted
    | cons predicate predicates =>
      obtain ⟨solved, head, tail, selected, samePredicate, closed, goal, remaining, rfl⟩ := cons_accepted accepted
      have contains := selected.contains ledger
      have rowValid := retained solved (ledger ▸ contains.1)
      have closedValid := EvidenceCloses.preserves_valid valid closed (retained_valid rowValid)
      have headProduces : RequirementProducesEvidence context (environment available) id predicate (evidence head) :=
        .intro contains samePredicate (predicate_represents _) rowValid closed (samePredicate ▸ closedValid)
      change RequirementsProduceEnvironment context (environment available) (id :: ids) (predicate :: predicates)
        ((SourceCompilationPlan.runtimeEvidenceGoal head, evidence head) :: environment tail)
      rw [goal]
      exact .cons headProduces (ih remaining)

/-- A resolver-created caller dictionary discharges the caller-validity
premise. The retained source ledger remains independently checked. -/
theorem produces_of_resolved {program : CheckedProgram} {caller : SourceSpecialization.SpecializedFunction}
    {occurrence : ExpressionId} {available result : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    {ids : List RequirementId} {predicates : List ProgramPredicate} {context : Context}
    (signatures : context.signatures = program.signatures)
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (retained : SolvedRequirementsValid context caller.function.solvedRequirements)
    (resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions = .ok available)
    (accepted : SourceCompilationPlan.materializeCallEvidence caller occurrence available ids predicates = .ok result) :
    RequirementsProduceEnvironment context (environment available) ids predicates (environment result) :=
  produces ledger retained (by simpa only [signatures] using (resolved_valid resolved).1) accepted

/-- Exact singleton selection is sufficient for agreement at reached IDs;
no global uniqueness assumption is imposed on unrelated ledger entries. -/
theorem agrees {caller : SourceSpecialization.SpecializedFunction} {occurrence : ExpressionId}
    {available result : SourceTypedRuntime.RuntimeEvidenceEnvironment} {ids : List RequirementId}
    {predicates : List ProgramPredicate} {context : Context} {semantic : EvidenceEnvironment}
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (accepted : SourceCompilationPlan.materializeCallEvidence caller occurrence available ids predicates = .ok result)
    (independent : RequirementsProduceEnvironment context (environment available) ids predicates semantic) :
    semantic = environment result := by
  induction independent generalizing result with
  | nil => cases accepted; rfl
  | @cons id ids predicate predicates selected rest head tail ih =>
    obtain ⟨solved, raw, remaining, singleton, samePredicate, closed, goal, acceptedTail, rfl⟩ := cons_accepted accepted
    cases head with
    | intro contains _ represents _ closes _ =>
      have sameRow := singleton.unique ledger contains
      cases sameRow
      have sameOpen := represents.functional (predicate_represents _)
      rw [sameOpen] at closes
      have sameEvidence := closes_functional closes closed
      change (predicate, selected) :: rest = (SourceCompilationPlan.runtimeEvidenceGoal raw, evidence raw) :: environment remaining
      rw [sameEvidence, goal, ih acceptedTail]

end Solcore.SourceSemantics.CoreLowering.CallableCallEvidence
