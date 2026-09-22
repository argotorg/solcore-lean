import Solcore.Frontend.SourceSpecializationWorklist

/-! Small checked laws for finite specialization-worklist boundaries. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceSpecializationWorklist

/-- Canonical specialization identities retained by a worklist plan. -/
def Plan.specializationKeys (plan : Plan) :
    List SourceSpecialization.SpecializationKey :=
  plan.specializations.map (·.key)

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

private def RequestResolvesTo (program : CheckedProgram) (request : Request)
    (key : SourceSpecialization.SpecializationKey) : Prop :=
  ∃ specialized, resolveRequest program request = .ok specialized ∧
    specialized.key = key

private def CoveredKey (program : CheckedProgram)
    (seen : List SourceSpecialization.SpecializationKey)
    (queue : List Request) (key : SourceSpecialization.SpecializationKey) : Prop :=
  key ∈ seen ∨ ∃ request ∈ queue, RequestResolvesTo program request key

private theorem any_key_eq_true_iff
    (seen : List SourceSpecialization.SpecializationKey)
    (key : SourceSpecialization.SpecializationKey) :
    (seen.any fun candidate => decide (candidate = key)) = true ↔
      key ∈ seen := by
  simp [List.any_eq_true]

private theorem nodup_reverse {α : Type} (values : List α)
    (unique : values.Nodup) : values.reverse.Nodup := by
  change List.Pairwise (fun left right : α => left ≠ right) values.reverse
  rw [List.pairwise_reverse]
  exact unique.imp fun notEqual equal => notEqual equal.symm

private theorem nextUnseen_some_key_not_mem (program : CheckedProgram)
    (seen : List SourceSpecialization.SpecializationKey) (queue : List Request)
    (request : Request) (specialized : SourceSpecialization.SpecializedFunction)
    (rest : List Request)
    (result : nextUnseen program seen queue =
      .ok (some (request, specialized, rest))) :
    specialized.key ∉ seen := by
  induction queue generalizing request specialized with
  | nil =>
      simp [nextUnseen, pure, Pure.pure, Except.pure] at result
  | cons current tail ih =>
      simp only [nextUnseen] at result
      cases resolved : resolveRequest program current with
      | error error =>
          simp [resolved, bind, Except.bind] at result
      | ok currentSpecialized =>
          by_cases present : currentSpecialized.key ∈ seen
          · have selected :
                (seen.any fun key => decide (key = currentSpecialized.key)) =
                  true :=
              (any_key_eq_true_iff seen currentSpecialized.key).2 present
            simp [resolved, selected, bind, Except.bind] at result
            exact ih (request := request) (specialized := specialized) result
          · have selected :
                (seen.any fun key => decide (key = currentSpecialized.key)) =
                  false := by
              cases choice :
                  (seen.any fun key => decide (key = currentSpecialized.key)) with
              | false => rfl
              | true =>
                  exact False.elim (present
                    ((any_key_eq_true_iff seen currentSpecialized.key).1 choice))
            simp [resolved, selected, bind, Except.bind] at result
            cases result
            exact present

private theorem nextUnseen_none_resolved_mem (program : CheckedProgram)
    (seen : List SourceSpecialization.SpecializationKey) (queue : List Request)
    (result : nextUnseen program seen queue = .ok none)
    (request : Request) (requestMember : request ∈ queue)
    (specialized : SourceSpecialization.SpecializedFunction)
    (resolvedRequest : resolveRequest program request = .ok specialized) :
    specialized.key ∈ seen := by
  induction queue generalizing request specialized with
  | nil => simp at requestMember
  | cons current tail ih =>
      simp only [nextUnseen] at result
      cases resolved : resolveRequest program current with
      | error error =>
          simp [resolved, bind, Except.bind] at result
      | ok currentSpecialized =>
          by_cases present : currentSpecialized.key ∈ seen
          · have selected :
                (seen.any fun key => decide (key = currentSpecialized.key)) =
                  true :=
              (any_key_eq_true_iff seen currentSpecialized.key).2 present
            simp [resolved, selected, bind, Except.bind] at result
            simp only [List.mem_cons] at requestMember
            rcases requestMember with rfl | requestMember
            · rw [resolved] at resolvedRequest
              cases resolvedRequest
              exact present
            · exact ih (request := request) (specialized := specialized) result
                requestMember resolvedRequest
          · have selected :
                (seen.any fun key => decide (key = currentSpecialized.key)) =
                  false := by
              cases choice :
                  (seen.any fun key => decide (key = currentSpecialized.key)) with
              | false => rfl
              | true =>
                  exact False.elim (present
                    ((any_key_eq_true_iff seen currentSpecialized.key).1 choice))
            simp [resolved, selected, bind, Except.bind, pure, Pure.pure,
              Except.pure] at result

private theorem nextUnseen_none_covers (program : CheckedProgram)
    (seen : List SourceSpecialization.SpecializationKey) (queue : List Request)
    (result : nextUnseen program seen queue = .ok none)
    (key : SourceSpecialization.SpecializationKey)
    (covered : CoveredKey program seen queue key) :
    key ∈ seen := by
  rcases covered with seenMember | ⟨request, requestMember, specialized,
      resolved, rfl⟩
  · exact seenMember
  · exact nextUnseen_none_resolved_mem program seen queue result request
      requestMember specialized resolved

private theorem nextUnseen_some_resolved_covered (program : CheckedProgram)
    (seen : List SourceSpecialization.SpecializationKey) (queue : List Request)
    (selectedRequest : Request)
    (selected : SourceSpecialization.SpecializedFunction) (rest : List Request)
    (result : nextUnseen program seen queue =
      .ok (some (selectedRequest, selected, rest)))
    (request : Request) (requestMember : request ∈ queue)
    (specialized : SourceSpecialization.SpecializedFunction)
    (resolvedRequest : resolveRequest program request = .ok specialized) :
    CoveredKey program (selected.key :: seen) rest specialized.key := by
  induction queue generalizing request specialized with
  | nil => simp at requestMember
  | cons current tail ih =>
      simp only [nextUnseen] at result
      cases resolved : resolveRequest program current with
      | error error =>
          simp [resolved, bind, Except.bind] at result
      | ok currentSpecialized =>
          by_cases present : currentSpecialized.key ∈ seen
          · have chosen :
                (seen.any fun key => decide (key = currentSpecialized.key)) =
                  true :=
              (any_key_eq_true_iff seen currentSpecialized.key).2 present
            simp [resolved, chosen, bind, Except.bind] at result
            simp only [List.mem_cons] at requestMember
            rcases requestMember with rfl | requestMember
            · rw [resolved] at resolvedRequest
              cases resolvedRequest
              exact .inl (.tail _ present)
            · exact ih (request := request) (specialized := specialized) result
                requestMember resolvedRequest
          · have chosen :
                (seen.any fun key => decide (key = currentSpecialized.key)) =
                  false := by
              cases choice :
                  (seen.any fun key => decide (key = currentSpecialized.key)) with
              | false => rfl
              | true =>
                  exact False.elim (present
                    ((any_key_eq_true_iff seen currentSpecialized.key).1 choice))
            simp [resolved, chosen, bind, Except.bind] at result
            cases result
            simp only [List.mem_cons] at requestMember
            rcases requestMember with rfl | requestMember
            · rw [resolved] at resolvedRequest
              cases resolvedRequest
              exact .inl (.head _)
            · exact .inr ⟨request, requestMember, specialized,
                resolvedRequest, rfl⟩

private theorem nextUnseen_some_preserves_covered (program : CheckedProgram)
    (seen : List SourceSpecialization.SpecializationKey) (queue : List Request)
    (request : Request) (specialized : SourceSpecialization.SpecializedFunction)
    (rest : List Request)
    (result : nextUnseen program seen queue =
      .ok (some (request, specialized, rest)))
    (key : SourceSpecialization.SpecializationKey)
    (covered : CoveredKey program seen queue key) :
    CoveredKey program (specialized.key :: seen) rest key := by
  rcases covered with seenMember | ⟨queued, queuedMember, resolved,
      resolvedOk, rfl⟩
  · exact .inl (.tail _ seenMember)
  · exact nextUnseen_some_resolved_covered program seen queue request
      specialized rest result queued queuedMember resolved resolvedOk

private theorem coveredKey_append_queue (program : CheckedProgram)
    (seen : List SourceSpecialization.SpecializationKey)
    (left right : List Request) (key : SourceSpecialization.SpecializationKey)
    (covered : CoveredKey program seen left key) :
    CoveredKey program seen (left ++ right) key := by
  rcases covered with seenMember | ⟨request, member, resolved⟩
  · exact .inl seenMember
  · exact .inr ⟨request, List.mem_append_left right member, resolved⟩

private theorem canonicalSeedKeys_cover (program : CheckedProgram)
    (seeds : List Request)
    (seedKeys : List SourceSpecialization.SpecializationKey)
    (result : canonicalSeedKeys program seeds = .ok seedKeys) :
    ∀ key ∈ seedKeys, CoveredKey program [] seeds key := by
  induction seeds generalizing seedKeys with
  | nil =>
      simp [canonicalSeedKeys, pure, Pure.pure, Except.pure] at result
      subst seedKeys
      simp
  | cons request rest ih =>
      simp only [canonicalSeedKeys] at result
      obtain ⟨specialized, resolved, continuation⟩ :=
        except_bind_ok _ _ _ result
      obtain ⟨restKeys, recursive, shape⟩ :=
        except_bind_ok _ _ _ continuation
      have seedShape : specialized.key :: restKeys = seedKeys := by
        simpa [pure, Pure.pure, Except.pure] using shape
      subst seedKeys
      intro key member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact .inr ⟨request, .head _, specialized, resolved, rfl⟩
      · have covered := ih restKeys recursive key member
        rcases covered with seenMember | ⟨queued, queuedMember, resolved⟩
        · simp at seenMember
        · exact .inr ⟨queued, .tail _ queuedMember, resolved⟩

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

theorem runAux_specializationKeys_nodup (program : CheckedProgram)
    (seedKeys : List SourceSpecialization.SpecializationKey)
    (queue : List Request)
    (seen : List SourceSpecialization.SpecializationKey)
    (specializations : List SourceSpecialization.SpecializedFunction)
    (callEdges : List CallEdge) (referenceEdges : List ReferenceEdge)
    (budget : Nat) (outcome : Outcome)
    (aligned : specializations.map (·.key) = seen.reverse)
    (unique : seen.Nodup)
    (result : runAux program seedKeys queue seen specializations callEdges
      referenceEdges budget = .ok outcome) :
    outcome.plan.specializationKeys.Nodup := by
  induction budget generalizing queue seen specializations callEdges
      referenceEdges outcome with
  | zero =>
      simp only [runAux] at result
      obtain ⟨next, _, continuation⟩ := except_bind_ok _ _ _ result
      have currentUnique : (specializations.map (·.key)).Nodup := by
        rw [aligned]
        exact nodup_reverse seen unique
      cases next with
      | none =>
          have shape : Outcome.complete {
              seedKeys, specializations, callEdges, referenceEdges } = outcome := by
            simpa [pure, Pure.pure, Except.pure] using continuation
          rw [← shape]
          exact currentUnique
      | some entry =>
          rcases entry with ⟨request, specialized, rest⟩
          have shape : Outcome.budgetExhausted {
              seedKeys, specializations, callEdges, referenceEdges }
              specialized.key (request :: rest) = outcome := by
            simpa [pure, Pure.pure, Except.pure] using continuation
          rw [← shape]
          exact currentUnique
  | succ budget ih =>
      simp only [runAux] at result
      obtain ⟨next, nextResult, continuation⟩ :=
        except_bind_ok _ _ _ result
      cases next with
      | none =>
          have shape : Outcome.complete {
              seedKeys, specializations, callEdges, referenceEdges } = outcome := by
            simpa [pure, Pure.pure, Except.pure] using continuation
          rw [← shape]
          change (specializations.map (·.key)).Nodup
          rw [aligned]
          exact nodup_reverse seen unique
      | some entry =>
          rcases entry with ⟨request, specialized, rest⟩
          have fresh : specialized.key ∉ seen :=
            nextUnseen_some_key_not_mem program seen queue request specialized
              rest nextResult
          obtain ⟨found, _, recursive⟩ :=
            except_bind_ok _ _ _ continuation
          rcases found with ⟨requests, edges, references⟩
          have nextAligned :
              (specializations ++ [specialized]).map (·.key) =
                (specialized.key :: seen).reverse := by
            simp [aligned]
          have nextUnique : (specialized.key :: seen).Nodup :=
            List.nodup_cons.mpr ⟨fresh, unique⟩
          exact ih _ _ _ _ _ _ nextAligned nextUnique recursive

private theorem runAux_complete_seedKeys_mem (program : CheckedProgram)
    (seedKeys : List SourceSpecialization.SpecializationKey)
    (queue : List Request)
    (seen : List SourceSpecialization.SpecializationKey)
    (specializations : List SourceSpecialization.SpecializedFunction)
    (callEdges : List CallEdge) (referenceEdges : List ReferenceEdge)
    (budget : Nat) (plan : Plan)
    (aligned : specializations.map (·.key) = seen.reverse)
    (covered : ∀ key ∈ seedKeys, CoveredKey program seen queue key)
    (result : runAux program seedKeys queue seen specializations callEdges
      referenceEdges budget = .ok (.complete plan)) :
    ∀ key ∈ seedKeys, key ∈ plan.specializationKeys := by
  induction budget generalizing queue seen specializations callEdges
      referenceEdges plan with
  | zero =>
      simp only [runAux] at result
      obtain ⟨next, nextResult, continuation⟩ :=
        except_bind_ok _ _ _ result
      cases next with
      | none =>
          have shape : {
              seedKeys, specializations, callEdges, referenceEdges } = plan := by
            simpa [pure, Pure.pure, Except.pure] using continuation
          subst plan
          intro key member
          change key ∈ specializations.map (·.key)
          rw [aligned]
          simpa using nextUnseen_none_covers program seen queue nextResult key
            (covered key member)
      | some entry =>
          rcases entry with ⟨request, specialized, rest⟩
          simp [pure, Pure.pure, Except.pure] at continuation
  | succ budget ih =>
      simp only [runAux] at result
      obtain ⟨next, nextResult, continuation⟩ :=
        except_bind_ok _ _ _ result
      cases next with
      | none =>
          have shape : {
              seedKeys, specializations, callEdges, referenceEdges } = plan := by
            simpa [pure, Pure.pure, Except.pure] using continuation
          subst plan
          intro key member
          change key ∈ specializations.map (·.key)
          rw [aligned]
          simpa using nextUnseen_none_covers program seen queue nextResult key
            (covered key member)
      | some entry =>
          rcases entry with ⟨request, specialized, rest⟩
          obtain ⟨found, _, recursive⟩ :=
            except_bind_ok _ _ _ continuation
          rcases found with ⟨requests, edges, references⟩
          have nextAligned :
              (specializations ++ [specialized]).map (·.key) =
                (specialized.key :: seen).reverse := by
            simp [aligned]
          have nextCovered : ∀ key ∈ seedKeys,
              CoveredKey program (specialized.key :: seen)
                (rest ++ requests) key := by
            intro key member
            exact coveredKey_append_queue program (specialized.key :: seen)
              rest requests key
              (nextUnseen_some_preserves_covered program seen queue request
                specialized rest nextResult key (covered key member))
          exact ih _ _ _ _ _ _ nextAligned nextCovered recursive

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

/-- Successful worklist execution admits each canonical specialization key at
most once, independently of whether the finite frontier closes. -/
theorem run_specializationKeys_nodup (program : CheckedProgram)
    (seeds : List Request) (budget : Nat) (outcome : Outcome)
    (result : run program seeds budget = .ok outcome) :
    outcome.plan.specializationKeys.Nodup := by
  simp only [run] at result
  obtain ⟨seedKeys, _, recursive⟩ := except_bind_ok _ _ _ result
  exact runAux_specializationKeys_nodup program seedKeys seeds [] [] [] []
    budget outcome (by simp) (by simp) recursive

theorem run_complete_specializationKeys_nodup (program : CheckedProgram)
    (seeds : List Request) (budget : Nat) (plan : Plan)
    (result : run program seeds budget = .ok (.complete plan)) :
    plan.specializationKeys.Nodup := by
  simpa using run_specializationKeys_nodup program seeds budget
    (.complete plan) result

theorem run_budgetExhausted_specializationKeys_nodup
    (program : CheckedProgram) (seeds : List Request) (budget : Nat)
    (plan : Plan) (next : SourceSpecialization.SpecializationKey)
    (pending : List Request)
    (result : run program seeds budget =
      .ok (.budgetExhausted plan next pending)) :
    plan.specializationKeys.Nodup := by
  simpa using run_specializationKeys_nodup program seeds budget
    (.budgetExhausted plan next pending) result

/-- A closed worklist plan contains every eagerly canonicalized seed key.  Seed
order and duplicates remain in `seedKeys`; admission itself is unique. -/
theorem run_complete_seedKeys_mem (program : CheckedProgram)
    (seeds : List Request) (budget : Nat) (plan : Plan)
    (result : run program seeds budget = .ok (.complete plan)) :
    ∀ key ∈ plan.seedKeys, key ∈ plan.specializationKeys := by
  simp only [run] at result
  obtain ⟨seedKeys, canonical, recursive⟩ := except_bind_ok _ _ _ result
  have preserved := runAux_preserves_seedKeys program seedKeys seeds [] [] [] []
    budget (.complete plan) recursive
  have included := runAux_complete_seedKeys_mem program seedKeys seeds [] [] [] []
    budget plan (by simp) (canonicalSeedKeys_cover program seeds seedKeys canonical)
    recursive
  simp only [Outcome.plan_complete] at preserved
  rw [preserved]
  exact included

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
