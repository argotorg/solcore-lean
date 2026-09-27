import Solcore.Frontend.TraitResolution

/-!
Soundness of the generic tabled trait-resolution kernel.

The certificate below records only equations exposed by the caller-supplied
head matcher.  Typed head-matching soundness and source-level semantic
instantiation remain separate bridges.
-/

set_option autoImplicit false

namespace Solcore.Frontend.TraitResolution

universe u v w

variable {Trait : Type u} {Ty : Type v} {ImplId : Type w}

mutual

/-- Executable evidence is justified by catalog membership, one successful
head-matcher equation, and evidence for every returned premise. -/
inductive ResolutionEvidenceValid
    (program : Program Trait Ty ImplId) :
    Predicate Trait Ty → Evidence Trait Ty ImplId → Prop where
  | byImpl
      {rule : ImplRule Trait Ty ImplId}
      {goal : Predicate Trait Ty}
      {implId : ImplId}
      {premiseGoals : List (Predicate Trait Ty)}
      {premiseEvidence : List (Evidence Trait Ty ImplId)}
      (rule_mem : rule ∈ program.rules)
      (id_eq : rule.id = implId)
      (matched : program.matchHead rule goal = some premiseGoals)
      (premises : ResolutionPremisesValid program
        premiseGoals premiseEvidence) :
      ResolutionEvidenceValid program goal
        (.byImpl goal implId premiseEvidence)

/-- Pointwise validity of a premise goal/evidence spine. -/
inductive ResolutionPremisesValid
    (program : Program Trait Ty ImplId) :
    List (Predicate Trait Ty) → List (Evidence Trait Ty ImplId) → Prop where
  | nil : ResolutionPremisesValid program [] []
  | cons
      {goal : Predicate Trait Ty}
      {goals : List (Predicate Trait Ty)}
      {evidence : Evidence Trait Ty ImplId}
      {evidences : List (Evidence Trait Ty ImplId)}
      (head : ResolutionEvidenceValid program goal evidence)
      (tail : ResolutionPremisesValid program goals evidences) :
      ResolutionPremisesValid program (goal :: goals) (evidence :: evidences)

end

/-- A candidate retains enough data to recover one catalog rule and its exact
head-matcher result. -/
def CandidateOriginates
    (program : Program Trait Ty ImplId)
    (goal : Predicate Trait Ty)
    (candidate : Candidate Trait Ty ImplId) : Prop :=
  ∃ rule,
    rule ∈ program.rules ∧
    rule.id = candidate.implId ∧
    program.matchHead rule goal = some candidate.premises

namespace Program

/-- Every enumerated candidate originates in a catalog rule whose matcher
returned the candidate's premise spine. -/
theorem candidate_originates
    {program : Program Trait Ty ImplId}
    {goal : Predicate Trait Ty}
    {candidate : Candidate Trait Ty ImplId}
    (member : candidate ∈ program.candidates goal) :
    CandidateOriginates program goal candidate := by
  simp only [candidates, List.mem_filterMap] at member
  obtain ⟨rule, rule_mem, matched⟩ := member
  cases result : program.matchHead rule goal with
  | none => simp [result] at matched
  | some premises =>
      simp only [result, Option.map_some, Option.some.injEq] at matched
      subst candidate
      exact ⟨rule, rule_mem, rfl, result⟩

/-- Filtering the complete candidate list into either priority tier preserves
catalog origin. -/
theorem ordinaryCandidate_originates
    {program : Program Trait Ty ImplId}
    {goal : Predicate Trait Ty}
    {candidate : Candidate Trait Ty ImplId}
    (member : candidate ∈ program.ordinaryCandidates goal) :
    CandidateOriginates program goal candidate := by
  exact candidate_originates (List.mem_filter.mp member).1

theorem defaultCandidate_originates
    {program : Program Trait Ty ImplId}
    {goal : Predicate Trait Ty}
    {candidate : Candidate Trait Ty ImplId}
    (member : candidate ∈ program.defaultCandidates goal) :
    CandidateOriginates program goal candidate := by
  exact candidate_originates (List.mem_filter.mp member).1

end Program

namespace Detail

/-- Only successful outcomes carry a proof obligation. -/
def OutcomeValid (program : Program Trait Ty ImplId)
    (goal : Predicate Trait Ty) : Outcome Trait Ty ImplId → Prop
  | .success evidence => ResolutionEvidenceValid program goal evidence
  | .noSolution
  | .inconclusive _ => True

/-- Only a successful premise traversal carries a pointwise proof obligation. -/
def PremiseOutcomeValid (program : Program Trait Ty ImplId)
    (goals : List (Predicate Trait Ty)) :
    PremiseOutcome Trait Ty ImplId → Prop
  | .success evidence => ResolutionPremisesValid program goals evidence
  | .noSolution
  | .inconclusive _ => True

/-- Every successful result stored in the completed-goal table is valid for
its cache key. -/
def MemoValid (program : Program Trait Ty ImplId)
    (memo : Memo Trait Ty ImplId) : Prop :=
  ∀ goal outcome, (goal, outcome) ∈ memo → OutcomeValid program goal outcome

def SearchStateValid (program : Program Trait Ty ImplId)
    (state : SearchState Trait Ty ImplId) : Prop :=
  MemoValid program state.memo

/-- The optional first success retained while scanning sibling candidates is
valid whenever it is present. -/
def FirstSuccessValid (program : Program Trait Ty ImplId)
    (goal : Predicate Trait Ty) :
    Option (ImplId × Evidence Trait Ty ImplId) → Prop
  | none => True
  | some (_, evidence) => ResolutionEvidenceValid program goal evidence

/-- Every candidate in the current search suffix comes from the program. -/
def CandidatesOriginate (program : Program Trait Ty ImplId)
    (goal : Predicate Trait Ty)
    (candidates : List (Candidate Trait Ty ImplId)) : Prop :=
  ∀ candidate, candidate ∈ candidates →
    CandidateOriginates program goal candidate

theorem candidatesOriginate_tail
    {program : Program Trait Ty ImplId}
    {goal : Predicate Trait Ty}
    {candidate : Candidate Trait Ty ImplId}
    {candidates : List (Candidate Trait Ty ImplId)}
    (originate : CandidatesOriginate program goal (candidate :: candidates)) :
    CandidatesOriginate program goal candidates := by
  intro current member
  exact originate current (List.mem_cons_of_mem candidate member)

theorem lookupMemo?_sound [DecidableEq Trait] [DecidableEq Ty]
    {program : Program Trait Ty ImplId}
    {memo : Memo Trait Ty ImplId}
    {goal : Predicate Trait Ty}
    {outcome : Outcome Trait Ty ImplId}
    (valid : MemoValid program memo)
    (found : lookupMemo? goal memo = some outcome) :
    OutcomeValid program goal outcome := by
  induction memo with
  | nil => simp [lookupMemo?] at found
  | cons entry rest induction =>
      rcases entry with ⟨cached, cachedOutcome⟩
      by_cases same : cached = goal
      · subst cached
        have outcome_eq : cachedOutcome = outcome := by
          simpa [lookupMemo?] using found
        have cached_valid := valid goal cachedOutcome (by simp)
        simpa [outcome_eq] using cached_valid
      · simp only [lookupMemo?, if_neg same] at found
        apply induction
        · intro otherGoal otherOutcome member
          exact valid otherGoal otherOutcome (by simp [member])
        · exact found

theorem cacheConclusive_valid [DecidableEq Trait] [DecidableEq Ty]
    {program : Program Trait Ty ImplId}
    {goal : Predicate Trait Ty}
    {outcome : Outcome Trait Ty ImplId}
    {state : SearchState Trait Ty ImplId}
    (state_valid : SearchStateValid program state)
    (outcome_valid : OutcomeValid program goal outcome) :
    SearchStateValid program (cacheConclusive goal outcome state) := by
  cases outcome with
  | success evidence =>
      intro otherGoal otherOutcome member
      simp only [List.mem_cons] at member
      rcases member with same | member
      · cases same
        exact outcome_valid
      · exact state_valid otherGoal otherOutcome member
  | noSolution =>
      intro otherGoal otherOutcome member
      simp only [List.mem_cons] at member
      rcases member with same | member
      · cases same
        trivial
      · exact state_valid otherGoal otherOutcome member
  | inconclusive reason => exact state_valid

/-- Successful child resolution and memo validity are sufficient to justify
the complete left-to-right premise traversal. -/
theorem resolvePremises_sound
    {program : Program Trait Ty ImplId}
    (resolveChild : SearchState Trait Ty ImplId → Predicate Trait Ty →
      Outcome Trait Ty ImplId × SearchState Trait Ty ImplId)
    (child_sound : ∀ state goal,
      SearchStateValid program state →
      OutcomeValid program goal (resolveChild state goal).1 ∧
        SearchStateValid program (resolveChild state goal).2) :
    ∀ state goals,
      SearchStateValid program state →
      PremiseOutcomeValid program goals
          (resolvePremises resolveChild state goals).1 ∧
        SearchStateValid program
          (resolvePremises resolveChild state goals).2 := by
  intro state goals state_valid
  induction goals generalizing state with
  | nil => exact ⟨ResolutionPremisesValid.nil, state_valid⟩
  | cons goal goals induction =>
      cases childResult : resolveChild state goal with
      | mk headOutcome afterHead =>
          have headSound := child_sound state goal state_valid
          rw [childResult] at headSound
          cases headOutcome with
          | noSolution =>
              simpa [resolvePremises, childResult, PremiseOutcomeValid] using
                And.intro True.intro headSound.2
          | success headEvidence =>
              have tailSound := induction afterHead headSound.2
              cases tailResult : resolvePremises resolveChild afterHead goals with
              | mk tailOutcome afterTail =>
                  rw [tailResult] at tailSound
                  cases tailOutcome with
                  | success tailEvidence =>
                      simpa [resolvePremises, childResult, tailResult,
                          PremiseOutcomeValid] using
                        And.intro
                          (ResolutionPremisesValid.cons headSound.1 tailSound.1)
                          tailSound.2
                  | noSolution =>
                      simpa [resolvePremises, childResult, tailResult,
                          PremiseOutcomeValid] using
                        And.intro True.intro tailSound.2
                  | inconclusive reason =>
                      simpa [resolvePremises, childResult, tailResult,
                          PremiseOutcomeValid] using
                        And.intro True.intro tailSound.2
          | inconclusive headReason =>
              have tailSound := induction afterHead headSound.2
              cases tailResult : resolvePremises resolveChild afterHead goals with
              | mk tailOutcome afterTail =>
                  rw [tailResult] at tailSound
                  cases tailOutcome <;>
                    simpa [resolvePremises, childResult, tailResult,
                      PremiseOutcomeValid] using
                      And.intro True.intro tailSound.2

/-- Candidate scanning preserves memo validity, and any unique successful
candidate yields a valid evidence node. -/
theorem resolveCandidates_sound
    {program : Program Trait Ty ImplId}
    (resolveChild : SearchState Trait Ty ImplId → Predicate Trait Ty →
      Outcome Trait Ty ImplId × SearchState Trait Ty ImplId)
    (child_sound : ∀ state goal,
      SearchStateValid program state →
      OutcomeValid program goal (resolveChild state goal).1 ∧
        SearchStateValid program (resolveChild state goal).2) :
    ∀ goal state candidates firstSuccess firstUnknown,
      SearchStateValid program state →
      CandidatesOriginate program goal candidates →
      FirstSuccessValid program goal firstSuccess →
      OutcomeValid program goal
          (resolveCandidates resolveChild goal state candidates firstSuccess
            firstUnknown).1 ∧
        SearchStateValid program
          (resolveCandidates resolveChild goal state candidates firstSuccess
            firstUnknown).2 := by
  intro goal state candidates
  induction candidates generalizing state with
  | nil =>
      intro firstSuccess firstUnknown state_valid _ first_valid
      cases firstSuccess with
      | none => cases firstUnknown <;> exact ⟨trivial, state_valid⟩
      | some first =>
          cases firstUnknown with
          | none => exact ⟨first_valid, state_valid⟩
          | some reason => exact ⟨trivial, state_valid⟩
  | cons candidate candidates induction =>
      intro firstSuccess firstUnknown state_valid origins first_valid
      have premiseSound := resolvePremises_sound resolveChild child_sound
        state candidate.premises state_valid
      cases premiseResult : resolvePremises resolveChild state candidate.premises with
      | mk premiseOutcome afterCandidate =>
          rw [premiseResult] at premiseSound
          have tailOrigins := candidatesOriginate_tail origins
          cases premiseOutcome with
          | noSolution =>
              have tailSound := induction afterCandidate firstSuccess
                firstUnknown premiseSound.2 tailOrigins first_valid
              simpa [resolveCandidates, premiseResult] using tailSound
          | inconclusive reason =>
              have tailSound := induction afterCandidate firstSuccess
                (firstUnknown.orElse fun _ => some reason) premiseSound.2
                tailOrigins first_valid
              simpa [resolveCandidates, premiseResult] using tailSound
          | success premiseEvidence =>
              have origin := origins candidate (by simp)
              rcases origin with ⟨rule, rule_mem, id_eq, matched⟩
              have evidenceValid : ResolutionEvidenceValid program goal
                  (.byImpl goal candidate.implId premiseEvidence) :=
                .byImpl rule_mem id_eq matched premiseSound.1
              cases firstSuccess with
              | none =>
                  have tailSound := induction afterCandidate
                    (some (candidate.implId,
                      Evidence.byImpl goal candidate.implId premiseEvidence))
                    firstUnknown premiseSound.2 tailOrigins evidenceValid
                  simpa [resolveCandidates, premiseResult] using tailSound
              | some previous =>
                  simpa [resolveCandidates, premiseResult, OutcomeValid] using
                    And.intro True.intro premiseSound.2

theorem ordinaryCandidates_originate
    {program : Program Trait Ty ImplId}
    (goal : Predicate Trait Ty) :
    CandidatesOriginate program goal (program.ordinaryCandidates goal) := by
  intro candidate member
  exact program.ordinaryCandidate_originates member

theorem defaultCandidates_originate
    {program : Program Trait Ty ImplId}
    (goal : Predicate Trait Ty) :
    CandidatesOriginate program goal (program.defaultCandidates goal) := by
  intro candidate member
  exact program.defaultCandidate_originates member

/-- Every successful result of the fuel-bounded, tabled search is justified by
the program's matcher equations; every success cached during the search has
the same property. -/
theorem resolveAux_sound [DecidableEq Trait] [DecidableEq Ty]
    (program : Program Trait Ty ImplId) :
    ∀ fuel active state goal,
      SearchStateValid program state →
      OutcomeValid program goal
          (resolveAux program fuel active state goal).1 ∧
        SearchStateValid program
          (resolveAux program fuel active state goal).2 := by
  intro fuel
  induction fuel with
  | zero =>
      intro active state goal state_valid
      cases memoResult : lookupMemo? goal state.memo with
      | some outcome =>
          rw [resolveAux, memoResult]
          exact ⟨lookupMemo?_sound state_valid memoResult, state_valid⟩
      | none =>
          by_cases activeGoal : isActive goal active = true
          · rw [resolveAux, memoResult, if_pos activeGoal]
            exact ⟨True.intro, state_valid⟩
          · rw [resolveAux, memoResult, if_neg activeGoal]
            exact ⟨True.intro, state_valid⟩
  | succ remaining induction =>
      intro active state goal state_valid
      cases memoResult : lookupMemo? goal state.memo with
      | some outcome =>
          rw [resolveAux, memoResult]
          exact ⟨lookupMemo?_sound state_valid memoResult, state_valid⟩
      | none =>
          by_cases activeGoal : isActive goal active = true
          · rw [resolveAux, memoResult, if_pos activeGoal]
            exact ⟨True.intro, state_valid⟩
          · let expanded : SearchState Trait Ty ImplId :=
              { state with
                statistics.expandedGoals := state.statistics.expandedGoals + 1 }
            let resolveChild nextState child :=
              resolveAux program remaining (goal :: active) nextState child
            have expanded_valid : SearchStateValid program expanded := state_valid
            have child_sound : ∀ nextState child,
                SearchStateValid program nextState →
                OutcomeValid program child (resolveChild nextState child).1 ∧
                  SearchStateValid program (resolveChild nextState child).2 := by
              intro nextState child next_valid
              exact induction (goal :: active) nextState child next_valid
            have ordinarySound := resolveCandidates_sound resolveChild child_sound
              goal expanded (program.ordinaryCandidates goal) none none
              expanded_valid (ordinaryCandidates_originate goal) trivial
            cases ordinaryResult : resolveCandidates resolveChild goal expanded
                (program.ordinaryCandidates goal) none none with
            | mk ordinaryOutcome afterOrdinary =>
                rw [ordinaryResult] at ordinarySound
                cases ordinaryOutcome with
                | success evidence =>
                    have cached := cacheConclusive_valid ordinarySound.2
                      ordinarySound.1
                    rw [resolveAux, memoResult, if_neg activeGoal]
                    simpa [expanded, resolveChild, ordinaryResult] using
                      And.intro ordinarySound.1 cached
                | inconclusive reason =>
                    have cached := cacheConclusive_valid ordinarySound.2
                      ordinarySound.1
                    rw [resolveAux, memoResult, if_neg activeGoal]
                    simpa [expanded, resolveChild, ordinaryResult] using
                      And.intro ordinarySound.1 cached
                | noSolution =>
                    have defaultSound := resolveCandidates_sound resolveChild
                      child_sound goal afterOrdinary
                      (program.defaultCandidates goal) none none ordinarySound.2
                      (defaultCandidates_originate goal) trivial
                    cases defaultResult : resolveCandidates resolveChild goal
                        afterOrdinary (program.defaultCandidates goal) none none with
                    | mk defaultOutcome finished =>
                        rw [defaultResult] at defaultSound
                        have cached := cacheConclusive_valid defaultSound.2
                          defaultSound.1
                        rw [resolveAux, memoResult, if_neg activeGoal]
                        simpa [expanded, resolveChild, ordinaryResult,
                          defaultResult] using
                          And.intro defaultSound.1 cached

end Detail

/-- Public resolver success is backed by a complete matcher-equation
certificate, independently of fuel, memoization, and priority-tier behavior. -/
theorem resolve_success_sound [DecidableEq Trait] [DecidableEq Ty]
    {program : Program Trait Ty ImplId}
    {maxDepth : Nat}
    {goal : Predicate Trait Ty}
    {evidence : Evidence Trait Ty ImplId}
    (success : (resolve program maxDepth goal).outcome = .success evidence) :
    ResolutionEvidenceValid program goal evidence := by
  cases result : Detail.resolveAux program maxDepth [] {} goal with
  | mk outcome state =>
      have sound := Detail.resolveAux_sound program maxDepth [] {} goal (by
        intro cachedGoal cachedOutcome member
        simp at member)
      rw [result] at sound
      simp only [result] at success
      cases success
      exact sound.1

end Solcore.Frontend.TraitResolution
