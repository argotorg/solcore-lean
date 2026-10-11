import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicSpecializationMeaning

/-!
Ordinary requests keep their actual catalog provenance when the real worklist
extends a plan. The general extension theorem separates unchanged rows and the
supplied detached root from rows resolved by ordinary requests. Its ordinary
corollary obtains catalog membership from accepted request and worklist actions.
No detached method is asserted to be an ordinary catalog function.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.CallablePreparedOrdinaryRequestOrigins

open Frontend SourceInference TypeSystem SourceSpecializationWorklist

private theorem bind_ok {α β ε : Type} {action : Except ε α}
    {next : α → Except ε β} {result : β}
    (accepted : action >>= next = .ok result) :
    ∃ value, action = .ok value ∧ next value = .ok result := by
  cases action with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem next_resolved {program : CheckedProgram}
    {seen : List SourceSpecialization.SpecializationKey}
    {queue rest : List Request} {request : Request}
    {specialized : SourceSpecialization.SpecializedFunction}
    (accepted : nextUnseen program seen queue =
      .ok (some (request, specialized, rest))) :
    resolveRequest program request = .ok specialized := by
  induction queue with
  | nil => cases accepted
  | cons head tail ih =>
      unfold nextUnseen at accepted
      obtain ⟨value, resolved, accepted⟩ := bind_ok accepted
      split at accepted
      · exact ih accepted
      · cases accepted
        exact resolved

private theorem runAux_origin_cases {program : CheckedProgram}
    {seedKeys seen : List SourceSpecialization.SpecializationKey}
    {queue : List Request}
    {entries : List SourceSpecialization.SpecializedFunction}
    {calls : List CallEdge} {references : List ReferenceEdge}
    {budget : Nat} {outcome : Outcome}
    (accepted : runAux program seedKeys queue seen entries calls references
      budget = .ok outcome) :
    ∀ row ∈ outcome.plan.specializations,
      row ∈ entries ∨ RecursiveNamedPublicSpecializationMeaning.Origin program row := by
  induction budget generalizing queue seen entries calls references outcome with
  | zero =>
      unfold runAux at accepted
      obtain ⟨next, _, accepted⟩ := bind_ok accepted
      cases next with
      | none => cases accepted; exact fun row member => Or.inl member
      | some item =>
          rcases item with ⟨request, selected, rest⟩
          cases accepted
          exact fun row member => Or.inl member
  | succ budget ih =>
      unfold runAux at accepted
      obtain ⟨next, found, accepted⟩ := bind_ok accepted
      cases next with
      | none => cases accepted; exact fun row member => Or.inl member
      | some item =>
          rcases item with ⟨request, selected, rest⟩
          obtain ⟨⟨requests, newCalls, newReferences⟩, _, accepted⟩ := bind_ok accepted
          intro row member
          rcases ih (accepted := accepted) row member with previous | origin
          · rcases List.mem_append.mp previous with old | added
            · exact Or.inl old
            · have same : row = selected := by simpa using added
              subst row
              exact Or.inr (RecursiveNamedPublicSpecializationMeaning.resolve_origin
                (next_resolved found))
          · exact Or.inr origin

/-- New retained rows have genuine ordinary request origins. Previously stored
rows and the actual supplied detached root remain separately identified. -/
theorem extend_origin_cases {program : CheckedProgram} {before : Plan}
    {root : SourceSpecialization.SpecializedFunction} {edge : CallEdge}
    {budget : Nat} {outcome : Outcome}
    (accepted : extendCompletePlan program before root edge budget = .ok outcome) :
    ∀ row ∈ outcome.plan.specializations,
      row ∈ before.specializations ∨ row = root ∨
        RecursiveNamedPublicSpecializationMeaning.Origin program row := by
  unfold extendCompletePlan at accepted
  obtain ⟨checked, _, accepted⟩ := bind_ok accepted
  cases checked
  split at accepted <;> try contradiction
  dsimp only at accepted
  split at accepted
  · simp only [pure, Except.pure, bind, Except.bind] at accepted
    obtain ⟨⟨requests, calls, references⟩, _, accepted⟩ := bind_ok accepted
    intro row member
    rcases runAux_origin_cases accepted row member with previous | origin
    · rcases List.mem_append.mp previous with old | added
      · exact Or.inl old
      · have same : row = root := by simpa using added
        exact Or.inr (Or.inl same)
    · exact Or.inr (Or.inr origin)
  · split at accepted <;> try contradiction
    simp only [pure, Except.pure, bind, Except.bind] at accepted
    obtain ⟨⟨requests, calls, references⟩, _, accepted⟩ := bind_ok accepted
    intro row member
    rcases runAux_origin_cases accepted row member with previous | origin
    · exact Or.inl previous
    · exact Or.inr (Or.inr origin)

/-- A genuine ordinary seed run and an actually resolved ordinary root suffice
for catalog provenance of every row retained by their accepted extension. -/
theorem extend_from_worklist_request_origins {program : CheckedProgram}
    {requests : List Request} {initialBudget : Nat} {initial : Outcome}
    {request : Request} {root : SourceSpecialization.SpecializedFunction}
    {edge : CallEdge} {budget : Nat} {outcome : Outcome}
    (initialAccepted : run program requests initialBudget = .ok initial)
    (rootAccepted : resolveRequest program request = .ok root)
    (extended : extendCompletePlan program initial.plan root edge budget = .ok outcome) :
    ∀ row ∈ outcome.plan.specializations,
      RecursiveNamedPublicSpecializationMeaning.Origin program row := by
  intro row member
  rcases extend_origin_cases extended row member with previous | same | origin
  · exact RecursiveNamedPublicSpecializationMeaning.worklist_origins
      initialAccepted row previous
  · subst row
    exact RecursiveNamedPublicSpecializationMeaning.resolve_origin rootAccepted
  · exact origin

/-- Canonical input validation actually replays ordinary requests and compares
all plan fields. Its retained rows therefore keep complete catalog origins. -/
theorem canonical_input_origins {program : CheckedProgram} {plan : Plan}
    (accepted : SourceCompilationPlan.validateCanonicalInputPlan program plan = .ok ()) :
    ∀ row ∈ plan.specializations,
      RecursiveNamedPublicSpecializationMeaning.Origin program row := by
  unfold SourceCompilationPlan.validateCanonicalInputPlan at accepted
  obtain ⟨seeds, _, accepted⟩ := bind_ok accepted
  obtain ⟨outcome, executed, accepted⟩ := bind_ok accepted
  have executed : run program seeds plan.specializations.length = .ok outcome := by
    cases action : run program seeds plan.specializations.length with
    | error error => rw [action] at executed; cases executed
    | ok actual =>
        simp only [action, Except.mapError, Except.ok.injEq] at executed
        cases executed
        rfl
  cases outcome with
  | budgetExhausted previous next pending => cases accepted
  | complete expected =>
      by_cases same : (expected == plan) = true
      · have rows : expected.specializations = plan.specializations := by
          have fields : ((expected.seedKeys == plan.seedKeys) &&
              ((expected.specializations == plan.specializations) &&
                ((expected.callEdges == plan.callEdges) &&
                  (expected.referenceEdges == plan.referenceEdges)))) = true := by
            exact same
          simp only [Bool.and_eq_true] at fields
          exact LawfulBEq.eq_of_beq fields.2.1
        intro row member
        exact RecursiveNamedPublicSpecializationMeaning.worklist_origins executed
          row (by simpa only [Outcome.plan_complete, rows] using member)
      · simp only [same, throw, throwThe, MonadExceptOf.throw] at accepted
        cases accepted

/-- Successful public evidence preparation authenticates the original input
rows by canonical replay. Detached rows subsequently inserted by scanning are
not included in this conclusion. -/
theorem initial_origins_of_preparation {program : CheckedProgram}
    {before after : Plan} {fuel budget : Nat}
    (accepted : SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget
      program before fuel budget = .ok after) :
    ∀ row ∈ before.specializations,
      RecursiveNamedPublicSpecializationMeaning.Origin program row := by
  obtain ⟨prepared, _, accepted⟩ := bind_ok accepted
  obtain ⟨checked, canonical, returned⟩ := bind_ok accepted
  cases checked
  cases returned
  exact canonical_input_origins canonical

end Solcore.SourceSemantics.CoreLowering.CallablePreparedOrdinaryRequestOrigins
