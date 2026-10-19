import Solcore.Frontend.SourceInference.LocalReadRequirementOrigins

/-! Inference may mark newly issued declaration-call requirements. It cannot
change the classification of an earlier operational requirement. -/

set_option autoImplicit false
set_option Elab.async false

namespace Solcore.Frontend.SourceInference
open TypeSystem
/-- The ledger-only relation makes updates to unrelated inference fields
transparent to the recursive traversal. -/
structure RequirementLedgerProgress
    (beforeRows : List Requirement) (beforeNext : Nat) (beforeDirect : List RequirementId)
    (afterRows : List Requirement) (afterNext : Nat) (afterDirect : List RequirementId) : Prop where
  included : beforeRows ⊆ afterRows
  wellFormed : beforeRows.map (fun requirement => requirement.id.index) = List.range beforeNext →
    afterRows.map (fun requirement => requirement.id.index) = List.range afterNext
  allocated : beforeRows.map (fun requirement => requirement.id.index) = List.range beforeNext →
    beforeDirect ⊆ beforeRows.map Requirement.id → afterDirect ⊆ afterRows.map Requirement.id
  existing : beforeRows.map (fun requirement => requirement.id.index) = List.range beforeNext →
    ∀ id ∈ beforeRows.map Requirement.id, id ∈ afterDirect ↔ id ∈ beforeDirect

namespace State

abbrev DirectRequirementsProgress (before after : State) : Prop :=
  RequirementLedgerProgress before.requirements before.nextRequirement before.directCallRequirements
    after.requirements after.nextRequirement after.directCallRequirements

namespace DirectRequirementsProgress

theorem refl (state : State) : DirectRequirementsProgress state state :=
  ⟨fun _ member => member, id, fun _ allocated => allocated, fun _ _ _ => Iff.rfl⟩

theorem trans {first second third : State}
    (left : DirectRequirementsProgress first second)
    (right : DirectRequirementsProgress second third) : DirectRequirementsProgress first third := by
  refine ⟨left.included.trans right.included,
    fun wf => right.wellFormed (left.wellFormed wf),
    fun wf allocated => right.allocated (left.wellFormed wf) (left.allocated wf allocated), ?_⟩
  intro wf id member
  have secondMember : id ∈ second.requirements.map Requirement.id := by
    obtain ⟨requirement, present, same⟩ := List.mem_map.mp member
    exact List.mem_map.mpr ⟨requirement, left.included present, same⟩
  exact (right.existing (left.wellFormed wf) id secondMember).trans
    (left.existing wf id member)

theorem of_direct_eq {before after : State}
    (included : before.requirements ⊆ after.requirements)
    (wellFormed : before.RequirementsWellFormed → after.RequirementsWellFormed)
    (same : after.directCallRequirements = before.directCallRequirements) :
    DirectRequirementsProgress before after := by
  refine ⟨included, wellFormed, ?_, ?_⟩
  · intro _ allocated id present
    rw [same] at present
    obtain ⟨requirement, member, eq⟩ := List.mem_map.mp (allocated present)
    exact List.mem_map.mpr ⟨requirement, included member, eq⟩
  · intro _ _ _
    rw [same]

theorem of_fields_eq {before after : State}
    (requirements : after.requirements = before.requirements)
    (next : after.nextRequirement = before.nextRequirement)
    (direct : after.directCallRequirements = before.directCallRequirements) :
    DirectRequirementsProgress before after := by
  apply of_direct_eq (by rw [requirements]; exact fun _ member => member) ?_ direct
  simp only [RequirementsWellFormed, requirements, next, imp_self]

theorem inference (state : State) (inference : InferState) :
    DirectRequirementsProgress state {state with inference} := of_fields_eq rfl rfl rfl

theorem addRequirementWithId (state : State) (predicate : ProgramPredicate) :
    DirectRequirementsProgress state (state.addRequirementWithId predicate).2 :=
  of_direct_eq (State.addRequirementWithId_requirements_subset state predicate)
    (State.addRequirementWithId_preserves_requirementsWellFormed state predicate) rfl

theorem addRequirementsWithIds (state : State) (predicates : List ProgramPredicate) :
    DirectRequirementsProgress state (state.addRequirementsWithIds predicates).2 :=
  of_direct_eq (State.addRequirementsWithIds_requirements_subset state predicates)
    (State.addRequirementsWithIds_preserves_requirementsWellFormed state predicates)
    (State.addRequirementsWithIds_direct_eq state predicates)

private theorem correspondence_ids {requirements : List Requirement}
    {predicates : List ProgramPredicate} {ids : List RequirementId}
    (rows : RequirementPredicatesCorrespond requirements predicates ids) :
    ids ⊆ requirements.map Requirement.id := by
  induction rows with
  | nil => simp
  | @cons predicate id predicates ids present tail ih =>
    intro selected member
    rcases List.mem_cons.mp member with same | later
    · subst selected
      exact List.mem_map.mpr ⟨_, present, rfl⟩
    · exact ih later

theorem addRequirementsWithIds_mark (state : State) (predicates : List ProgramPredicate) :
    DirectRequirementsProgress state
      ((state.addRequirementsWithIds predicates).2.markDirectCallRequirements
        (state.addRequirementsWithIds predicates).1) := by
  refine ⟨State.addRequirementsWithIds_requirements_subset state predicates,
    State.addRequirementsWithIds_preserves_requirementsWellFormed state predicates, ?_, ?_⟩
  · intro wf allocated id member
    rcases List.mem_append.mp member with prior | issued
    · exact (addRequirementsWithIds state predicates).allocated wf allocated prior
    · exact correspondence_ids (State.addRequirementsWithIds_correspond state predicates) issued
  · exact fun wf id member => State.addRequirementsWithIds_mark_existing state predicates wf member

end DirectRequirementsProgress
end State

namespace Detail
open State (DirectRequirementsProgress)

theorem withExpected_direct_progress
    {context : Context} {state : State} {actual : InferredExpression}
    {expected : Option Ty} {result : ExpectationResult}
    (accepted : withExpected context state actual expected = .ok result) :
    DirectRequirementsProgress state result.state :=
  .of_direct_eq (withExpected_requirements_subset accepted)
    (withExpected_preserves_requirementsWellFormed accepted) (withExpected_direct_eq accepted)

theorem candidateWithExpected_direct_progress
    {context : Context} {state : State} {actual : InferredExpression}
    {expected : Option Ty} {result : ExpectationResult}
    (accepted : candidateWithExpected context state actual expected = .ok (some result)) :
    DirectRequirementsProgress state result.state := by
  unfold candidateWithExpected at accepted
  cases fitted : withExpected context state actual expected with
  | ok value =>
    simp only [fitted, Except.ok.injEq, Option.some.injEq] at accepted
    subst result
    exact withExpected_direct_progress fitted
  | error error =>
    cases error <;> simp_all
    rename_i error
    cases error <;> simp_all

theorem fitArguments_direct_progress
    {context : Context} {state : State} {arguments : List InferredExpression}
    {parameters : List Ty} {result : ArgumentFitResult}
    (accepted : fitArguments context state arguments parameters = .ok (some result)) :
    DirectRequirementsProgress state result.state := by
  induction arguments generalizing state parameters result with
  | nil =>
    cases parameters <;> simp_all [fitArguments]
    subst result
    exact .refl _
  | cons argument arguments ih =>
    cases parameters with
    | nil => simp [fitArguments] at accepted
    | cons parameter parameters =>
      unfold fitArguments at accepted
      cases fitted : candidateWithExpected context state argument (some parameter) with
      | error error => simp [fitted, bind, Except.bind] at accepted
      | ok value =>
        cases value with
        | none => simp [fitted, bind, Except.bind] at accepted
        | some fit =>
          simp only [fitted, bind, Except.bind] at accepted
          cases remaining : fitArguments context fit.state arguments parameters with
          | error error => simp [remaining] at accepted
          | ok value =>
            cases value with
            | none => simp [remaining] at accepted
            | some tail =>
              simp only [remaining, pure, Except.pure, Except.ok.injEq, Option.some.injEq] at accepted
              subst result
              exact (candidateWithExpected_direct_progress fitted).trans (ih (result := tail) remaining)

/-- The sole inference operation that marks direct-call rows allocates its
signature predicates after argument/result fitting, then marks exactly them. -/
theorem tryFunctionCandidate_direct_progress
    {context : Context} {arguments : List InferredExpression}
    {integerLiteralOrigins : List IntegerLiteralOrigin} {call : ExpressionId}
    {expected : Option Ty} {state : State}
    {signature : ProgramFunctionSignature} {result : CandidateAttemptResult}
    (accepted : tryFunctionCandidate context arguments integerLiteralOrigins
      call expected state signature = .ok (some result)) :
    DirectRequirementsProgress state result.state := by
  unfold tryFunctionCandidate at accepted
  simp_all [bind, Except.bind]
  repeat' first | split at accepted
  all_goals try cases accepted
  all_goals have argumentsProgress := fitArguments_direct_progress (by assumption)
  all_goals have resultProgress := candidateWithExpected_direct_progress (by assumption)
  all_goals
    exact (DirectRequirementsProgress.inference state _).trans
      (argumentsProgress.trans (resultProgress.trans
        (DirectRequirementsProgress.addRequirementsWithIds_mark _ _)))

end Detail
end Solcore.Frontend.SourceInference
