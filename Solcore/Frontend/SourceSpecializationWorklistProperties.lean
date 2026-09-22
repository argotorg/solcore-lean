import Solcore.Frontend.SourceSpecializationWorklist

/-! Small checked laws for finite specialization-worklist boundaries. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceSpecializationWorklist

/-- Recover the accumulated plan from either finite worklist outcome. -/
def Outcome.plan : Outcome → Plan
  | .complete plan => plan
  | .budgetExhausted plan _ _ => plan

@[simp] theorem Outcome.plan_complete (plan : Plan) :
    (Outcome.complete plan).plan = plan := rfl

@[simp] theorem Outcome.plan_budgetExhausted (plan : Plan)
    (next : SourceSpecialization.SpecializationKey) (pending : List Request) :
    (Outcome.budgetExhausted plan next pending).plan = plan := rfl

private theorem except_bind_ok {Error Value Result : Type}
    (source : Except Error Value) (continuation : Value → Except Error Result)
    (result : Result)
    (success : (do
      let value ← source
      continuation value) = .ok result) :
    ∃ value, source = .ok value ∧ continuation value = .ok result := by
  cases source with
  | error error => simp [bind, Except.bind] at success
  | ok value =>
      exact ⟨value, rfl, by simpa [bind, Except.bind] using success⟩

@[simp] theorem run_empty (program : CheckedProgram) (budget : Nat) :
    run program [] budget = .ok (.complete {
      seedKeys := []
      specializations := []
      callEdges := []
    }) := by
  cases budget <;> rfl

theorem run_zero_single (program : CheckedProgram) (request : Request)
    (specialized : SourceSpecialization.SpecializedFunction)
    (resolved : resolveRequest program request = .ok specialized) :
    run program [request] 0 = .ok (.budgetExhausted {
      seedKeys := [specialized.key]
      specializations := []
      callEdges := []
    } specialized.key [request]) := by
  simp [run, canonicalSeedKeys, runAux, nextUnseen, resolved]
  rfl

theorem runAux_preserves_seedKeys (program : CheckedProgram)
    (seedKeys : List SourceSpecialization.SpecializationKey)
    (queue : List Request)
    (seen : List SourceSpecialization.SpecializationKey)
    (specializations : List SourceSpecialization.SpecializedFunction)
    (callEdges : List CallEdge) (referenceEdges : List ReferenceEdge)
    (budget : Nat) (outcome : Outcome)
    (result : runAux program seedKeys queue seen specializations callEdges
      referenceEdges budget = .ok outcome) :
    outcome.plan.seedKeys = seedKeys := by
  induction budget generalizing queue seen specializations callEdges
      referenceEdges outcome with
  | zero =>
      simp only [runAux] at result
      obtain ⟨next, _, continuation⟩ := except_bind_ok _ _ _ result
      cases next with
      | none =>
          have shape : Outcome.complete {
              seedKeys, specializations, callEdges, referenceEdges } = outcome := by
            simpa [pure, Pure.pure, Except.pure] using continuation
          rw [← shape]
          rfl
      | some entry =>
          rcases entry with ⟨request, specialized, rest⟩
          have shape : Outcome.budgetExhausted {
              seedKeys, specializations, callEdges, referenceEdges }
              specialized.key (request :: rest) = outcome := by
            simpa [pure, Pure.pure, Except.pure] using continuation
          rw [← shape]
          rfl
  | succ budget ih =>
      simp only [runAux] at result
      obtain ⟨next, _, continuation⟩ := except_bind_ok _ _ _ result
      cases next with
      | none =>
          have shape : Outcome.complete {
              seedKeys, specializations, callEdges, referenceEdges } = outcome := by
            simpa [pure, Pure.pure, Except.pure] using continuation
          rw [← shape]
          rfl
      | some entry =>
          rcases entry with ⟨request, specialized, rest⟩
          obtain ⟨found, _, recursive⟩ :=
            except_bind_ok _ _ _ continuation
          rcases found with ⟨requests, edges, references⟩
          exact ih _ _ _ _ _ _ recursive

theorem runAux_specializations_length_le (program : CheckedProgram)
    (seedKeys : List SourceSpecialization.SpecializationKey)
    (queue : List Request)
    (seen : List SourceSpecialization.SpecializationKey)
    (specializations : List SourceSpecialization.SpecializedFunction)
    (callEdges : List CallEdge) (referenceEdges : List ReferenceEdge)
    (budget : Nat) (outcome : Outcome)
    (result : runAux program seedKeys queue seen specializations callEdges
      referenceEdges budget = .ok outcome) :
    outcome.plan.specializations.length ≤ specializations.length + budget := by
  induction budget generalizing queue seen specializations callEdges
      referenceEdges outcome with
  | zero =>
      simp only [runAux] at result
      obtain ⟨next, _, continuation⟩ := except_bind_ok _ _ _ result
      cases next with
      | none =>
          have shape : Outcome.complete {
              seedKeys, specializations, callEdges, referenceEdges } = outcome := by
            simpa [pure, Pure.pure, Except.pure] using continuation
          rw [← shape]
          simp
      | some entry =>
          rcases entry with ⟨request, specialized, rest⟩
          have shape : Outcome.budgetExhausted {
              seedKeys, specializations, callEdges, referenceEdges }
              specialized.key (request :: rest) = outcome := by
            simpa [pure, Pure.pure, Except.pure] using continuation
          rw [← shape]
          simp
  | succ budget ih =>
      simp only [runAux] at result
      obtain ⟨next, _, continuation⟩ := except_bind_ok _ _ _ result
      cases next with
      | none =>
          have shape : Outcome.complete {
              seedKeys, specializations, callEdges, referenceEdges } = outcome := by
            simpa [pure, Pure.pure, Except.pure] using continuation
          rw [← shape]
          simp only [Outcome.plan_complete]
          omega
      | some entry =>
          rcases entry with ⟨request, specialized, rest⟩
          obtain ⟨found, _, recursive⟩ :=
            except_bind_ok _ _ _ continuation
          rcases found with ⟨requests, edges, references⟩
          have bound := ih _ _ _ _ _ _ recursive
          simp only [List.length_append, List.length_singleton] at bound
          omega

theorem run_preserves_seedKeys (program : CheckedProgram)
    (seeds : List Request) (budget : Nat) (outcome : Outcome)
    (seedKeys : List SourceSpecialization.SpecializationKey)
    (canonical : canonicalSeedKeys program seeds = .ok seedKeys)
    (result : run program seeds budget = .ok outcome) :
    outcome.plan.seedKeys = seedKeys := by
  simp only [run, canonical] at result
  exact runAux_preserves_seedKeys program seedKeys seeds [] [] [] [] budget
    outcome result

/-- A successful public run records exactly the eagerly canonicalized seeds. -/
theorem run_seedKeys_eq_canonical (program : CheckedProgram)
    (seeds : List Request) (budget : Nat) (outcome : Outcome)
    (result : run program seeds budget = .ok outcome) :
    canonicalSeedKeys program seeds = .ok outcome.plan.seedKeys := by
  simp only [run] at result
  obtain ⟨seedKeys, canonical, recursive⟩ := except_bind_ok _ _ _ result
  have preserved := runAux_preserves_seedKeys program seedKeys seeds [] [] [] []
    budget outcome recursive
  simpa [preserved] using canonical

/-- Every ordinary worklist outcome respects the distinct-specialization
budget, independently of whether the frontier closes. -/
theorem run_specializations_length_le (program : CheckedProgram)
    (seeds : List Request) (budget : Nat) (outcome : Outcome)
    (result : run program seeds budget = .ok outcome) :
    outcome.plan.specializations.length ≤ budget := by
  simp only [run] at result
  obtain ⟨seedKeys, _, recursive⟩ := except_bind_ok _ _ _ result
  simpa using
    runAux_specializations_length_le program seedKeys seeds [] [] [] []
      budget outcome recursive

theorem run_complete_specializations_length_le (program : CheckedProgram)
    (seeds : List Request) (budget : Nat) (plan : Plan)
    (result : run program seeds budget = .ok (.complete plan)) :
    plan.specializations.length ≤ budget := by
  simpa using run_specializations_length_le program seeds budget
    (.complete plan) result

theorem run_budgetExhausted_specializations_length_le
    (program : CheckedProgram) (seeds : List Request) (budget : Nat)
    (plan : Plan) (next : SourceSpecialization.SpecializationKey)
    (pending : List Request)
    (result : run program seeds budget =
      .ok (.budgetExhausted plan next pending)) :
    plan.specializations.length ≤ budget := by
  simpa using run_specializations_length_le program seeds budget
    (.budgetExhausted plan next pending) result

end Solcore.Frontend.SourceSpecializationWorklist
