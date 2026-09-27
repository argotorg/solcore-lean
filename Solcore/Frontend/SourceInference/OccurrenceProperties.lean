import Solcore.Frontend.SourceInference.Expression
import Solcore.Frontend.SourceInference.StateProperties

/-!
Occurrence-allocation preservation for source inference.

This layer retains the monotone declaration-local occurrence bound and the
fact that every recorded node lies below it.  Exact node preservation is kept
separate because selected-call argument fitting may refine freshly recorded
expression roots with committed coercions.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Solcore.Frontend.SourceInference.Detail

open TypeSystem

@[simp] private theorem except_pure_eq_ok {epsilon alpha : Type}
    (value result : alpha) :
    ((pure value : Except epsilon alpha) = .ok result) ↔ value = result := by
  change (Except.ok value = Except.ok result) ↔ value = result
  simp

/-- Successful unification leaves source nodes and occurrence allocation exact. -/
theorem unify_occurrenceState_eq
    {state next : State} {left right : Ty}
    (success : unify state left right = .ok next) :
    next.nodes = state.nodes ∧
      next.nextOccurrence = state.nextOccurrence := by
  unfold unify at success
  cases inferenceResult : liftUnification (state.inference.unify left right) with
  | error error => simp [inferenceResult, bind, Except.bind] at success
  | ok inference =>
      simp only [inferenceResult, bind, Except.bind] at success
      change Except.ok { state with inference } = Except.ok next at success
      injection success with nextEq
      subst next
      exact ⟨rfl, rfl⟩

/-- Successful unification changes no occurrence allocation state. -/
theorem unify_occurrenceBoundExtends
    {state next : State} {left right : Ty}
    (success : unify state left right = .ok next) :
    state.OccurrenceBoundExtends next := by
  have exactState := unify_occurrenceState_eq success
  exact .of_nodes_eq_nextOccurrence_eq exactState.1 exactState.2

/-- Committing a coercion plan allocates requirements but no occurrences. -/
theorem commitCoercionPlan_occurrenceBoundExtends
    (state : State) (plan : List PlannedCoercionStep) :
    state.OccurrenceBoundExtends (commitCoercionPlan state plan).2 := by
  induction plan generalizing state with
  | nil => exact .refl state
  | cons step rest induction =>
      simp only [commitCoercionPlan]
      exact
        (State.OccurrenceBoundExtends.addRequirementWithId
          state step.predicate).trans
        ((State.OccurrenceBoundExtends.addRequirementsWithIds
          (state.addRequirementWithId step.predicate).2
          step.methodPredicates).trans
        (induction
          ((state.addRequirementWithId step.predicate).2
            |>.addRequirementsWithIds step.methodPredicates).2))

@[simp] theorem commitCoercionPlan_nodes
    (state : State) (plan : List PlannedCoercionStep) :
    (commitCoercionPlan state plan).2.nodes = state.nodes := by
  induction plan generalizing state with
  | nil => rfl
  | cons step rest induction =>
      simp only [commitCoercionPlan]
      rw [induction]
      simp [State.addRequirementWithId]

@[simp] theorem commitCoercionPlan_nextOccurrence
    (state : State) (plan : List PlannedCoercionStep) :
    (commitCoercionPlan state plan).2.nextOccurrence =
      state.nextOccurrence := by
  induction plan generalizing state with
  | nil => rfl
  | cons step rest induction =>
      simp only [commitCoercionPlan]
      rw [induction]
      simp [State.addRequirementWithId]

/-- Expected-type fitting preserves the occurrence bound in both the direct
unification and planned-coercion branches. -/
theorem withExpected_occurrenceBoundExtends
    {context : Context} {state : State} {actual : InferredExpression}
    {expected : Option Ty} {result : ExpectationResult}
    (success : withExpected context state actual expected = .ok result) :
    state.OccurrenceBoundExtends result.state := by
  cases expected with
  | none =>
      simp only [withExpected] at success
      injection success with resultEq
      subst result
      exact .refl _
  | some expected =>
      cases unification : state.inference.unify actual.type expected with
      | ok inference =>
          simp only [withExpected, unification] at success
          injection success with resultEq
          subst result
          exact .of_nodes_eq_nextOccurrence_eq rfl rfl
      | error error =>
          cases error with
          | occursCheck metavariable type =>
              simp [withExpected, unification] at success
          | exhausted =>
              simp [withExpected, unification] at success
          | mismatch left right =>
              simp only [withExpected, unification] at success
              cases planResult : coercionPlan? context state
                  (state.resolve actual.type) (state.resolve expected) with
              | error error =>
                  simp [planResult, bind, Except.bind] at success
              | ok plan? =>
                  cases plan? with
                  | none =>
                      simp [planResult, bind, Except.bind] at success
                  | some plan =>
                      simp only [planResult, bind, Except.bind] at success
                      change Except.ok _ = Except.ok result at success
                      injection success with resultEq
                      subst result
                      exact commitCoercionPlan_occurrenceBoundExtends state plan

/-- Expected-type fitting never changes the source occurrence identity. -/
theorem withExpected_success_expression_id
    {context : Context} {state : State} {actual : InferredExpression}
    {expected : Option Ty} {result : ExpectationResult}
    (success : withExpected context state actual expected = .ok result) :
    result.expression.id = actual.id := by
  cases expected with
  | none =>
      simp only [withExpected] at success
      injection success with resultEq
      subst result
      rfl
  | some expected =>
      cases unification : state.inference.unify actual.type expected with
      | ok inference =>
          simp only [withExpected, unification] at success
          injection success with resultEq
          subst result
          rfl
      | error error =>
          cases error with
          | occursCheck metavariable type =>
              simp [withExpected, unification] at success
          | exhausted =>
              simp [withExpected, unification] at success
          | mismatch left right =>
              simp only [withExpected, unification] at success
              cases planResult : coercionPlan? context state
                  (state.resolve actual.type) (state.resolve expected) with
              | error error =>
                  simp [planResult, bind, Except.bind] at success
              | ok plan? =>
                  cases plan? with
                  | none =>
                      simp [planResult, bind, Except.bind] at success
                  | some plan =>
                      simp only [planResult, bind, Except.bind] at success
                      change Except.ok _ = Except.ok result at success
                      injection success with resultEq
                      subst result
                      rfl

/-- Expected-type fitting allocates neither occurrence identities nor source
nodes. -/
theorem withExpected_occurrenceState_eq
    {context : Context} {state : State} {actual : InferredExpression}
    {expected : Option Ty} {result : ExpectationResult}
    (success : withExpected context state actual expected = .ok result) :
    result.state.nodes = state.nodes ∧
      result.state.nextOccurrence = state.nextOccurrence := by
  cases expected with
  | none =>
      simp only [withExpected] at success
      injection success with resultEq
      subst result
      exact ⟨rfl, rfl⟩
  | some expected =>
      cases unification : state.inference.unify actual.type expected with
      | ok inference =>
          simp only [withExpected, unification] at success
          injection success with resultEq
          subst result
          exact ⟨rfl, rfl⟩
      | error error =>
          cases error with
          | occursCheck metavariable type =>
              simp [withExpected, unification] at success
          | exhausted =>
              simp [withExpected, unification] at success
          | mismatch left right =>
              simp only [withExpected, unification] at success
              cases planResult : coercionPlan? context state
                  (state.resolve actual.type) (state.resolve expected) with
              | error error =>
                  simp [planResult, bind, Except.bind] at success
              | ok plan? =>
                  cases plan? with
                  | none =>
                      simp [planResult, bind, Except.bind] at success
                  | some plan =>
                      simp only [planResult, bind, Except.bind] at success
                      change Except.ok _ = Except.ok result at success
                      injection success with resultEq
                      subst result
                      exact ⟨commitCoercionPlan_nodes state plan,
                        commitCoercionPlan_nextOccurrence state plan⟩

/-- Retaining one expected-type candidate preserves the occurrence bound. -/
theorem candidateWithExpected_some_occurrenceBoundExtends
    {context : Context} {state : State} {actual : InferredExpression}
    {expected : Option Ty} {result : ExpectationResult}
    (success : candidateWithExpected context state actual expected =
      .ok (some result)) :
    state.OccurrenceBoundExtends result.state := by
  unfold candidateWithExpected at success
  cases fittedResult : withExpected context state actual expected with
  | error error =>
      cases error <;> simp [fittedResult] at success
      all_goals cases ‹Unification.Error› <;> simp_all
  | ok fitted =>
      simp only [fittedResult] at success
      injection success with resultEq
      have fittedEq : fitted = result := Option.some.inj resultEq
      subst result
      exact withExpected_occurrenceBoundExtends fittedResult

/-- Retaining an expected-type candidate leaves nodes and the occurrence
counter exact. -/
theorem candidateWithExpected_some_occurrenceState_eq
    {context : Context} {state : State} {actual : InferredExpression}
    {expected : Option Ty} {result : ExpectationResult}
    (success : candidateWithExpected context state actual expected =
      .ok (some result)) :
    result.state.nodes = state.nodes ∧
      result.state.nextOccurrence = state.nextOccurrence := by
  unfold candidateWithExpected at success
  cases fittedResult : withExpected context state actual expected with
  | error error =>
      cases error <;> simp [fittedResult] at success
      all_goals cases ‹Unification.Error› <;> simp_all
  | ok fitted =>
      simp only [fittedResult] at success
      injection success with resultEq
      have fittedEq : fitted = result := Option.some.inj resultEq
      subst result
      exact withExpected_occurrenceState_eq fittedResult

/-- Candidate filtering does not alter the fitted expression occurrence. -/
theorem candidateWithExpected_some_expression_id
    {context : Context} {state : State} {actual : InferredExpression}
    {expected : Option Ty} {result : ExpectationResult}
    (success : candidateWithExpected context state actual expected =
      .ok (some result)) :
    result.expression.id = actual.id := by
  unfold candidateWithExpected at success
  cases fittedResult : withExpected context state actual expected with
  | error error =>
      cases error <;> simp [fittedResult] at success
      all_goals cases ‹Unification.Error› <;> simp_all
  | ok fitted =>
      simp only [fittedResult] at success
      injection success with resultEq
      have fittedEq : fitted = result := Option.some.inj resultEq
      subst result
      exact withExpected_success_expression_id fittedResult

/-- Fitting an argument spine preserves the occurrence bound from the shared
input state to the state returned by the final fitted argument. -/
theorem fitArguments_some_occurrenceBoundExtends
    {context : Context} {state : State}
    {arguments : List InferredExpression} {parameters : List Ty}
    {result : ArgumentFitResult}
    (success : fitArguments context state arguments parameters =
      .ok (some result)) :
    state.OccurrenceBoundExtends result.state := by
  induction arguments generalizing parameters state result with
  | nil =>
      cases parameters <;> simp [fitArguments] at success
      subst result
      exact .refl state
  | cons argument arguments induction =>
      cases parameters with
      | nil => simp [fitArguments] at success
      | cons parameter parameters =>
          simp only [fitArguments] at success
          cases fittedResult :
              candidateWithExpected context state argument (some parameter) with
          | error error =>
              simp [fittedResult, bind, Except.bind] at success
          | ok fitted? =>
              cases fitted? with
              | none =>
                  simp only [fittedResult, bind, Except.bind] at success
                  change Except.ok (none : Option ArgumentFitResult) =
                    Except.ok (some result) at success
                  simp at success
              | some fitted =>
                  simp only [fittedResult, bind, Except.bind] at success
                  cases tailResult : fitArguments context fitted.state arguments
                      parameters with
                  | error error => simp [tailResult] at success
                  | ok tail? =>
                      cases tail? with
                      | none =>
                          simp only [tailResult] at success
                          change Except.ok (none : Option ArgumentFitResult) =
                            Except.ok (some result) at success
                          simp at success
                      | some tail =>
                          simp only [tailResult] at success
                          change Except.ok (some {
                            state := tail.state
                            cost := fitted.coercions.length + tail.cost
                            coercions := {
                              expression := argument.id
                              coercions := fitted.coercions
                            } :: tail.coercions
                          }) = Except.ok (some result) at success
                          injection success with resultEq
                          have resultEq : _ = result :=
                            Option.some.inj resultEq
                          subst result
                          exact
                            (candidateWithExpected_some_occurrenceBoundExtends
                              fittedResult).trans
                            (induction (result := tail) tailResult)

/-- Fitting arguments changes only types and requirements, leaving occurrence
nodes and their allocator exact. -/
theorem fitArguments_some_occurrenceState_eq
    {context : Context} {state : State}
    {arguments : List InferredExpression} {parameters : List Ty}
    {result : ArgumentFitResult}
    (success : fitArguments context state arguments parameters =
      .ok (some result)) :
    result.state.nodes = state.nodes ∧
      result.state.nextOccurrence = state.nextOccurrence := by
  induction arguments generalizing parameters state result with
  | nil =>
      cases parameters <;> simp [fitArguments] at success
      subst result
      exact ⟨rfl, rfl⟩
  | cons argument arguments induction =>
      cases parameters with
      | nil => simp [fitArguments] at success
      | cons parameter parameters =>
          simp only [fitArguments] at success
          cases fittedResult :
              candidateWithExpected context state argument (some parameter) with
          | error error =>
              simp [fittedResult, bind, Except.bind] at success
          | ok fitted? =>
              cases fitted? with
              | none =>
                  simp only [fittedResult, bind, Except.bind] at success
                  change Except.ok (none : Option ArgumentFitResult) =
                    Except.ok (some result) at success
                  simp at success
              | some fitted =>
                  simp only [fittedResult, bind, Except.bind] at success
                  cases tailResult : fitArguments context fitted.state arguments
                      parameters with
                  | error error => simp [tailResult] at success
                  | ok tail? =>
                      cases tail? with
                      | none =>
                          simp only [tailResult] at success
                          change Except.ok (none : Option ArgumentFitResult) =
                            Except.ok (some result) at success
                          simp at success
                      | some tail =>
                          simp only [tailResult] at success
                          change Except.ok (some {
                            state := tail.state
                            cost := fitted.coercions.length + tail.cost
                            coercions := {
                              expression := argument.id
                              coercions := fitted.coercions
                            } :: tail.coercions
                          }) = Except.ok (some result) at success
                          injection success with resultEq
                          have resultEq : _ = result :=
                            Option.some.inj resultEq
                          subst result
                          have fittedEq :=
                            candidateWithExpected_some_occurrenceState_eq
                              fittedResult
                          have tailEq := induction (result := tail) tailResult
                          exact ⟨tailEq.1.trans fittedEq.1,
                            tailEq.2.trans fittedEq.2⟩

/-- Trying one overload candidate allocates no source occurrences. -/
theorem tryFunctionCandidate_some_occurrenceState_eq
    {context : Context} {arguments : List InferredExpression}
    {integerLiteralOrigins : List IntegerLiteralOrigin} {call : ExpressionId}
    {expected : Option Ty} {state : State}
    {signature : ProgramFunctionSignature} {result : CandidateAttemptResult}
    (success : tryFunctionCandidate context arguments integerLiteralOrigins
      call expected state signature = .ok (some result)) :
    result.state.nodes = state.nodes ∧
      result.state.nextOccurrence = state.nextOccurrence := by
  unfold tryFunctionCandidate at success
  simp_all [bind, Except.bind]
  repeat' first | split at success
  all_goals try cases success
  all_goals try
    have fittedArgumentsEq :=
      fitArguments_some_occurrenceState_eq (by assumption)
  all_goals try
    have fittedResultEq :=
      candidateWithExpected_some_occurrenceState_eq (by assumption)
  all_goals
    constructor
    · simpa [State.markDirectCallRequirements] using
        fittedResultEq.1.trans fittedArgumentsEq.1
    · simpa [State.markDirectCallRequirements] using
        fittedResultEq.2.trans fittedArgumentsEq.2

/-- Trying one retained overload candidate preserves the occurrence bound. -/
theorem tryFunctionCandidate_some_occurrenceBoundExtends
    {context : Context} {arguments : List InferredExpression}
    {integerLiteralOrigins : List IntegerLiteralOrigin} {call : ExpressionId}
    {expected : Option Ty} {state : State}
    {signature : ProgramFunctionSignature} {result : CandidateAttemptResult}
    (success : tryFunctionCandidate context arguments integerLiteralOrigins
      call expected state signature = .ok (some result)) :
    state.OccurrenceBoundExtends result.state := by
  have exactState := tryFunctionCandidate_some_occurrenceState_eq success
  exact .of_nodes_eq_nextOccurrence_eq exactState.1 exactState.2

/-- A retained overload attempt keeps the caller-provided call occurrence as
its result occurrence. -/
theorem tryFunctionCandidate_some_result_id
    {context : Context} {arguments : List InferredExpression}
    {integerLiteralOrigins : List IntegerLiteralOrigin} {call : ExpressionId}
    {expected : Option Ty} {state : State}
    {signature : ProgramFunctionSignature} {result : CandidateAttemptResult}
    (success : tryFunctionCandidate context arguments integerLiteralOrigins
      call expected state signature = .ok (some result)) :
    result.result.id = call := by
  unfold tryFunctionCandidate at success
  simp_all [bind, Except.bind]
  repeat' first | split at success
  all_goals try cases success
  all_goals try have fittedId :=
    candidateWithExpected_some_expression_id (by assumption)
  all_goals simp_all

private theorem collectCandidateAttempts_success_occurrenceState_eq
    {attempt : ProgramFunctionSignature →
      Except Error (Option CandidateAttemptResult)}
    {state : State}
    (attemptEq : ∀ signature result,
      attempt signature = .ok (some result) →
        result.state.nodes = state.nodes ∧
          result.state.nextOccurrence = state.nextOccurrence) :
    ∀ candidates success,
      success ∈ (collectCandidateAttempts attempt candidates).successes →
        success.attempt.state.nodes = state.nodes ∧
          success.attempt.state.nextOccurrence = state.nextOccurrence := by
  intro candidates
  induction candidates with
  | nil => simp [collectCandidateAttempts]
  | cons signature candidates induction =>
      intro selected member
      simp only [collectCandidateAttempts] at member
      cases attemptResult : attempt signature with
      | error error =>
          simp only [attemptResult] at member
          exact induction selected member
      | ok result? =>
          cases result? with
          | none =>
              simp only [attemptResult] at member
              exact induction selected member
          | some result =>
              simp only [attemptResult, List.mem_cons] at member
              cases member with
              | inl selectedEq =>
                  subst selected
                  exact attemptEq signature result attemptResult
              | inr member => exact induction selected member

private theorem collectCandidateAttempts_success_result_id
    {attempt : ProgramFunctionSignature →
      Except Error (Option CandidateAttemptResult)}
    {call : ExpressionId}
    (attemptId : ∀ signature result,
      attempt signature = .ok (some result) → result.result.id = call) :
    ∀ candidates selected,
      selected ∈ (collectCandidateAttempts attempt candidates).successes →
        selected.attempt.result.id = call := by
  intro candidates
  induction candidates with
  | nil => simp [collectCandidateAttempts]
  | cons signature candidates induction =>
      intro selected member
      simp only [collectCandidateAttempts] at member
      cases attemptResult : attempt signature with
      | error error =>
          simp only [attemptResult] at member
          exact induction selected member
      | ok result? =>
          cases result? with
          | none =>
              simp only [attemptResult] at member
              exact induction selected member
          | some result =>
              simp only [attemptResult, List.mem_cons] at member
              cases member with
              | inl selectedEq =>
                  subst selected
                  exact attemptId signature result attemptResult
              | inr member => exact induction selected member

private theorem bestCandidateSuccesses_occurrence_subset
    (successes : List CandidateSuccess) :
    bestCandidateSuccesses successes ⊆ successes := by
  intro success member
  unfold bestCandidateSuccesses at member
  dsimp only at member
  split at member
  · contradiction
  · have preferredMember := (List.mem_filter.mp member).1
    by_cases empty :
        (successes.filter fun success =>
          !success.attempt.hasDeferredIntegerLiterals).isEmpty
    · simpa [empty] using preferredMember
    · have groundMember :
          success ∈ successes.filter fun success =>
            !success.attempt.hasDeferredIntegerLiterals := by
        simpa [empty] using preferredMember
      exact (List.mem_filter.mp groundMember).1

/-- Explicit-candidate overload selection returns a state with the exact input
occurrence table and allocator. -/
theorem selectFunctionCandidateFrom_occurrenceState_eq
    {context : Context} {name : String}
    {candidates : List ProgramFunctionSignature}
    {arguments : List InferredExpression}
    {integerLiteralOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected : Option Ty} {state : State}
    {result : CandidateAttemptResult}
    (success : selectFunctionCandidateFrom context name candidates arguments
      integerLiteralOrigins call expected state = .ok result) :
    result.state.nodes = state.nodes ∧
      result.state.nextOccurrence = state.nextOccurrence := by
  unfold selectFunctionCandidateFrom at success
  let attempt := tryFunctionCandidate context arguments integerLiteralOrigins
    call expected state
  let search := collectCandidateAttempts attempt candidates
  change selectCandidateSearch name candidates search = .ok result at success
  unfold selectCandidateSearch at success
  cases selected : bestCandidateSuccesses search.successes with
  | nil =>
      simp only [selected] at success
      repeat' first | split at success
      all_goals contradiction
  | cons candidate rest =>
      cases rest with
      | cons second tail => simp [selected] at success
      | nil =>
          simp only [selected] at success
          split at success
          · contradiction
          · injection success with resultEq
            subst result
            have member : candidate ∈ search.successes :=
              bestCandidateSuccesses_occurrence_subset search.successes
                (by simp [selected])
            exact collectCandidateAttempts_success_occurrenceState_eq
              (state := state)
              (fun signature attemptResult attemptSuccess =>
                tryFunctionCandidate_some_occurrenceState_eq attemptSuccess)
              candidates candidate member

/-- Explicit overload selection cannot replace the caller-provided call
occurrence retained by the selected attempt. -/
theorem selectFunctionCandidateFrom_result_id
    {context : Context} {name : String}
    {candidates : List ProgramFunctionSignature}
    {arguments : List InferredExpression}
    {integerLiteralOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected : Option Ty} {state : State}
    {result : CandidateAttemptResult}
    (success : selectFunctionCandidateFrom context name candidates arguments
      integerLiteralOrigins call expected state = .ok result) :
    result.result.id = call := by
  unfold selectFunctionCandidateFrom at success
  let attempt := tryFunctionCandidate context arguments integerLiteralOrigins
    call expected state
  let search := collectCandidateAttempts attempt candidates
  change selectCandidateSearch name candidates search = .ok result at success
  unfold selectCandidateSearch at success
  cases selected : bestCandidateSuccesses search.successes with
  | nil =>
      simp only [selected] at success
      repeat' first | split at success
      all_goals contradiction
  | cons candidate rest =>
      cases rest with
      | cons second tail => simp [selected] at success
      | nil =>
          simp only [selected] at success
          split at success
          · contradiction
          · injection success with resultEq
            subst result
            have member : candidate ∈ search.successes :=
              bestCandidateSuccesses_occurrence_subset search.successes
                (by simp [selected])
            exact collectCandidateAttempts_success_result_id
              (call := call)
              (fun signature attemptResult attemptSuccess =>
                tryFunctionCandidate_some_result_id attemptSuccess)
              candidates candidate member

/-- Visible overload lookup itself is read-only, so ordinary selection retains
the explicit selector's exact occurrence state. -/
theorem selectFunctionCandidate_occurrenceState_eq
    {context : Context} {name : String}
    {arguments : List InferredExpression}
    {integerLiteralOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected : Option Ty} {state : State}
    {result : CandidateAttemptResult}
    (success : selectFunctionCandidate context name arguments
      integerLiteralOrigins call expected state = .ok result) :
    result.state.nodes = state.nodes ∧
      result.state.nextOccurrence = state.nextOccurrence := by
  unfold selectFunctionCandidate at success
  cases candidatesResult : functionsNamed context name with
  | error error =>
      simp [candidatesResult, bind, Except.bind] at success
  | ok candidates =>
      simp only [candidatesResult, bind, Except.bind] at success
      exact selectFunctionCandidateFrom_occurrenceState_eq success

/-- Visible overload lookup inherits the explicit selector's result identity. -/
theorem selectFunctionCandidate_result_id
    {context : Context} {name : String}
    {arguments : List InferredExpression}
    {integerLiteralOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected : Option Ty} {state : State}
    {result : CandidateAttemptResult}
    (success : selectFunctionCandidate context name arguments
      integerLiteralOrigins call expected state = .ok result) :
    result.result.id = call := by
  unfold selectFunctionCandidate at success
  cases candidatesResult : functionsNamed context name with
  | error error =>
      simp [candidatesResult, bind, Except.bind] at success
  | ok candidates =>
      simp only [candidatesResult, bind, Except.bind] at success
      exact selectFunctionCandidateFrom_result_id success

/-- Explicit-candidate overload selection preserves the occurrence bound. -/
theorem selectFunctionCandidateFrom_occurrenceBoundExtends
    {context : Context} {name : String}
    {candidates : List ProgramFunctionSignature}
    {arguments : List InferredExpression}
    {integerLiteralOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected : Option Ty} {state : State}
    {result : CandidateAttemptResult}
    (success : selectFunctionCandidateFrom context name candidates arguments
      integerLiteralOrigins call expected state = .ok result) :
    state.OccurrenceBoundExtends result.state := by
  have exactState := selectFunctionCandidateFrom_occurrenceState_eq success
  exact .of_nodes_eq_nextOccurrence_eq exactState.1 exactState.2

/-- Applying an indirect function type changes no source occurrence state. -/
theorem applyFunctionType_occurrenceState_eq
    {context : Context} {call : ExpressionId} {calleeType : Ty}
    {arguments : List InferredExpression} {expected : Option Ty}
    {state : State} {result : IndirectApplicationResult}
    (success : applyFunctionType context call calleeType arguments expected
      state = .ok result) :
    result.state.nodes = state.nodes ∧
      result.state.nextOccurrence = state.nextOccurrence := by
  unfold applyFunctionType at success
  cases partsResult : functionParts? (state.resolve calleeType) with
  | some parts =>
      rcases parts with ⟨parameter, returnType⟩
      simp only [partsResult] at success
      cases argumentResult : withExpected context state
          { id := call, type := Ty.productMany (arguments.map (fun x => x.type)) }
          (some parameter) with
      | error error =>
          simp [argumentResult, bind, Except.bind] at success
      | ok fittedArgument =>
          simp only [argumentResult, bind, Except.bind] at success
          cases resultResult : withExpected context fittedArgument.state
              { id := call, type := returnType } expected with
          | error error =>
              simp [resultResult, bind, Except.bind] at success
          | ok fittedResult =>
              simp only [resultResult, bind, Except.bind] at success
              change Except.ok {
                result := fittedResult.expression
                argumentCoercions := fittedArgument.coercions
                callCoercions := fittedResult.coercions
                state := fittedResult.state
              } = Except.ok result at success
              injection success with resultEq
              subst result
              have argumentEq := withExpected_occurrenceState_eq argumentResult
              have resultEq := withExpected_occurrenceState_eq resultResult
              exact ⟨resultEq.1.trans argumentEq.1,
                resultEq.2.trans argumentEq.2⟩
  | none =>
      simp only [partsResult] at success
      generalize freshResultEq : state.fresh = freshResult at success
      rcases freshResult with ⟨resultType, freshState⟩
      cases unifyResult : unify freshState calleeType
          (.function (Ty.productMany (arguments.map fun x => x.type))
            resultType) with
      | error error =>
          simp [unifyResult, bind, Except.bind] at success
      | ok unifiedState =>
          simp only [unifyResult, bind, Except.bind] at success
          cases resultResult : withExpected context unifiedState
              { id := call, type := resultType } expected with
          | error error =>
              simp [resultResult, bind, Except.bind] at success
          | ok fittedResult =>
              simp only [resultResult, bind, Except.bind] at success
              change Except.ok {
                result := fittedResult.expression
                argumentCoercions := []
                callCoercions := fittedResult.coercions
                state := fittedResult.state
              } = Except.ok result at success
              injection success with resultEq
              subst result
              have freshNodes : freshState.nodes = state.nodes := by
                exact (congrArg (fun result => result.2.nodes)
                  freshResultEq).symm
              have freshNext :
                  freshState.nextOccurrence = state.nextOccurrence := by
                exact (congrArg (fun result => result.2.nextOccurrence)
                  freshResultEq).symm
              have unifiedEq := unify_occurrenceState_eq unifyResult
              have resultEq := withExpected_occurrenceState_eq resultResult
              exact ⟨resultEq.1.trans (unifiedEq.1.trans freshNodes),
                resultEq.2.trans (unifiedEq.2.trans freshNext)⟩

/-- Indirect application preserves the occurrence bound. -/
theorem applyFunctionType_occurrenceBoundExtends
    {context : Context} {call : ExpressionId} {calleeType : Ty}
    {arguments : List InferredExpression} {expected : Option Ty}
    {state : State} {result : IndirectApplicationResult}
    (success : applyFunctionType context call calleeType arguments expected
      state = .ok result) :
    state.OccurrenceBoundExtends result.state := by
  have exactState := applyFunctionType_occurrenceState_eq success
  exact .of_nodes_eq_nextOccurrence_eq exactState.1 exactState.2

/-- Indirect application fitting retains the caller-provided call identity. -/
theorem applyFunctionType_result_id
    {context : Context} {call : ExpressionId} {calleeType : Ty}
    {arguments : List InferredExpression} {expected : Option Ty}
    {state : State} {result : IndirectApplicationResult}
    (success : applyFunctionType context call calleeType arguments expected
      state = .ok result) :
    result.result.id = call := by
  unfold applyFunctionType at success
  simp_all [bind, Except.bind]
  repeat' first | split at success
  all_goals try cases success
  all_goals try have fittedId :=
    withExpected_success_expression_id (by assumption)
  all_goals simp_all [State.fresh]

/-- Attaching result coercions may refine node payloads, but the operation
preserves all occurrence identities and the allocation bound. -/
theorem attachExpressionCoercions_occurrenceBoundExtends
    (state : State) (entries : List ExpressionCoercions) :
    state.OccurrenceBoundExtends
      (attachExpressionCoercions state entries) := by
  unfold attachExpressionCoercions
  induction entries generalizing state with
  | nil => exact .refl state
  | cons entry entries induction =>
      simp only [List.foldl_cons]
      exact
        (State.OccurrenceBoundExtends.modifyExpressionNode
          state entry.expression _).trans
        (induction (state.modifyExpressionNode entry.expression fun node => {
          node with
          type := entry.coercions.foldl (fun _ step => step.target) node.type
          requirements := node.requirements ++
            coercionRequirements entry.coercions
          coercions := node.coercions ++ entry.coercions
        }))

/-- Coercion attachment preserves an older exact node prefix when every
target expression was allocated at or after that prefix's cutoff. -/
theorem attachExpressionCoercions_preserves_nodesPrefix_of_fresh
    (state : State) (entries : List ExpressionCoercions)
    (baseNodes : List Node) (cutoff : Nat)
    (nodesPrefix : baseNodes <+: state.nodes)
    (baseBelow :
      ∀ node ∈ baseNodes, node.occurrenceId.index < cutoff)
    (entriesFresh :
      ∀ entry ∈ entries, cutoff ≤ entry.expression.occurrence.index) :
    baseNodes <+: (attachExpressionCoercions state entries).nodes := by
  unfold attachExpressionCoercions
  induction entries generalizing state with
  | nil => exact nodesPrefix
  | cons entry entries induction =>
      simp only [List.foldl_cons]
      let modify : ExpressionNode → ExpressionNode := fun node => {
        node with
        type := entry.coercions.foldl (fun _ step => step.target) node.type
        requirements := node.requirements ++
          coercionRequirements entry.coercions
        coercions := node.coercions ++ entry.coercions
      }
      have headFresh : cutoff ≤ entry.expression.occurrence.index :=
        entriesFresh entry (by simp)
      have modifiedPrefix :
          baseNodes <+:
            (state.modifyExpressionNode entry.expression modify).nodes :=
        State.modifyExpressionNode_preserves_nodesPrefix_of_fresh
          state baseNodes cutoff entry.expression modify nodesPrefix baseBelow
          headFresh
      apply induction (state := state.modifyExpressionNode entry.expression modify)
        modifiedPrefix
      intro tail member
      exact entriesFresh tail (by simp [member])

/-- Allocating several fresh types advances no occurrence state. -/
theorem freshTypes_occurrenceBoundExtends (count : Nat) (state : State) :
    state.OccurrenceBoundExtends (freshTypes count state).2 := by
  induction count generalizing state with
  | zero => exact .refl state
  | succ count induction =>
      exact (State.OccurrenceBoundExtends.fresh state).trans
        (induction state.fresh.2)

@[simp] theorem freshTypes_nodes (count : Nat) (state : State) :
    (freshTypes count state).2.nodes = state.nodes := by
  induction count generalizing state with
  | zero => rfl
  | succ count induction =>
      simpa [freshTypes, State.fresh] using induction state.fresh.2

@[simp] theorem freshTypes_nextOccurrence (count : Nat) (state : State) :
    (freshTypes count state).2.nextOccurrence = state.nextOccurrence := by
  induction count generalizing state with
  | zero => rfl
  | succ count induction =>
      simpa [freshTypes, State.fresh] using induction state.fresh.2

/-- Freshening a data-constructor instantiation advances no occurrence state. -/
theorem freshDataConstructorInstantiation_occurrenceBoundExtends
    (dataType : ProgramDataSignature)
    (constructor : ProgramDataConstructorSignature) (state : State) :
    state.OccurrenceBoundExtends
      (freshDataConstructorInstantiation dataType constructor state).2 := by
  let step : List Ty × State → TypeParameterId → List Ty × State :=
    fun result _ =>
      (result.1 ++ [result.2.fresh.1], result.2.fresh.2)
  have foldExtends (parameters : List TypeParameterId)
      (accumulator : List Ty × State) :
      accumulator.2.OccurrenceBoundExtends
        (parameters.foldl step accumulator).2 := by
    induction parameters generalizing accumulator with
    | nil => exact .refl accumulator.2
    | cons parameter parameters induction =>
        simp only [List.foldl_cons]
        exact (State.OccurrenceBoundExtends.fresh accumulator.2).trans
          (induction (step accumulator parameter))
  unfold freshDataConstructorInstantiation
  exact foldExtends dataType.parameters ([], state)

@[simp] theorem freshDataConstructorInstantiation_nodes
    (dataType : ProgramDataSignature)
    (constructor : ProgramDataConstructorSignature) (state : State) :
    (freshDataConstructorInstantiation dataType constructor state).2.nodes =
      state.nodes := by
  let step : List Ty × State → TypeParameterId → List Ty × State :=
    fun result _ =>
      (result.1 ++ [result.2.fresh.1], result.2.fresh.2)
  have foldEq (parameters : List TypeParameterId)
      (accumulator : List Ty × State) :
      (parameters.foldl step accumulator).2.nodes =
        accumulator.2.nodes := by
    induction parameters generalizing accumulator with
    | nil => rfl
    | cons parameter parameters induction =>
        simp only [List.foldl_cons]
        simpa [step, State.fresh] using
          induction (step accumulator parameter)
  unfold freshDataConstructorInstantiation
  exact foldEq dataType.parameters ([], state)

@[simp] theorem freshDataConstructorInstantiation_nextOccurrence
    (dataType : ProgramDataSignature)
    (constructor : ProgramDataConstructorSignature) (state : State) :
    (freshDataConstructorInstantiation dataType constructor state).2.nextOccurrence =
      state.nextOccurrence := by
  let step : List Ty × State → TypeParameterId → List Ty × State :=
    fun result _ =>
      (result.1 ++ [result.2.fresh.1], result.2.fresh.2)
  have foldEq (parameters : List TypeParameterId)
      (accumulator : List Ty × State) :
      (parameters.foldl step accumulator).2.nextOccurrence =
        accumulator.2.nextOccurrence := by
    induction parameters generalizing accumulator with
    | nil => rfl
    | cons parameter parameters induction =>
        simp only [List.foldl_cons]
        simpa [step, State.fresh] using
          induction (step accumulator parameter)
  unfold freshDataConstructorInstantiation
  exact foldEq dataType.parameters ([], state)

/-- Lambda-parameter binding changes lexical and type-inference state only. -/
theorem bindLambdaParameters_occurrenceState_eq
    {context : Context} {parameters : List Syntax.LambdaParameter}
    {index : Nat} {seen : List String} {state : State}
    {result : List TypedBinder × List Ty × State}
    (success : bindLambdaParameters context parameters index seen state =
      .ok result) :
    result.2.2.nodes = state.nodes ∧
      result.2.2.nextOccurrence = state.nextOccurrence := by
  induction parameters generalizing index seen state result with
  | nil =>
      simp only [bindLambdaParameters] at success
      injection success with resultEq
      subst result
      exact ⟨rfl, rfl⟩
  | cons parameter rest induction =>
      cases parameterValue : parameter.value with
      | error =>
          simp [bindLambdaParameters, parameterValue, bind, Except.bind]
            at success
      | inferred name =>
          simp only [bindLambdaParameters, parameterValue] at success
          simp only [bind, Except.bind] at success
          repeat' first | split at success
          all_goals try simp_all only [except_pure_eq_ok]
          all_goals try simp_all
          all_goals
            first
            | subst result
            | (change Except.ok _ = Except.ok result at success
               injection success with resultEq
               subst result)
            subst_vars
            have tailEq := induction _ _ _ (by assumption)
            simpa [State.fresh, State.allocateBinder] using tailEq
      | typed marker name sourceType =>
          simp only [bindLambdaParameters, parameterValue] at success
          cases typeResult : resolveSourceType context sourceType with
          | error error =>
              simp [typeResult, bind, Except.bind] at success
          | ok type =>
              simp only [typeResult, bind, Except.bind] at success
              repeat' first | split at success
              all_goals try simp_all only [except_pure_eq_ok]
              all_goals try simp_all
              all_goals
                first
                | subst result
                | (change Except.ok _ = Except.ok result at success
                   injection success with resultEq
                   subst result)
                subst_vars
                have tailEq := induction _ _ _ (by assumption)
                simpa [State.allocateBinder] using tailEq

/-- Lambda-parameter binding preserves the occurrence bound. -/
theorem bindLambdaParameters_occurrenceBoundExtends
    {context : Context} {parameters : List Syntax.LambdaParameter}
    {index : Nat} {seen : List String} {state : State}
    {result : List TypedBinder × List Ty × State}
    (success : bindLambdaParameters context parameters index seen state =
      .ok result) :
    state.OccurrenceBoundExtends result.2.2 := by
  have exactState := bindLambdaParameters_occurrenceState_eq success
  exact .of_nodes_eq_nextOccurrence_eq exactState.1 exactState.2

private def PreservesOccurrenceState {alpha : Type}
    (stateOf : alpha → State) (initial : State)
    (computation : Except Error alpha) : Prop :=
  ∀ result, computation = .ok result →
    (stateOf result).nodes = initial.nodes ∧
      (stateOf result).nextOccurrence = initial.nextOccurrence

/-- Match-pattern traversal never allocates a source occurrence. -/
private theorem inferMatchPatternFlatFuel_preserves_occurrenceState
    (fuel : Nat) (context : Context) (pattern : Syntax.Pattern)
    (expected : Ty) (seen : List String) (state : State) :
    PreservesOccurrenceState InferredPattern.state state
      (inferMatchPatternFlatFuel fuel context pattern expected seen state) := by
  apply inferMatchPatternFlatFuel.induct context
      (motive1 := fun fuel pattern expected seen state =>
        PreservesOccurrenceState InferredPattern.state state
          (inferMatchPatternFlatFuel fuel context pattern expected seen state))
      (motive2 := fun fuel patterns expected seen state =>
        PreservesOccurrenceState InferredPatterns.state state
          (inferMatchPatternsFlatFuel fuel context patterns expected seen state))
  all_goals
    intros
    unfold PreservesOccurrenceState at *
    intro result success
    simp_all [inferMatchPatternFlatFuel, inferMatchPatternsFlatFuel,
      bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals try have exactState :=
      unify_occurrenceState_eq (by assumption)
    all_goals try specialize ih1 _ _ _ heq
    all_goals try specialize ih1 _ _ heq
    all_goals try simp_all [State.fresh, State.addRequirementWithId,
      State.allocateBinder, bind, Except.bind]
    all_goals grind [unify_occurrenceState_eq,
      freshDataConstructorInstantiation_nodes,
      freshDataConstructorInstantiation_nextOccurrence,
      freshTypes_nodes, freshTypes_nextOccurrence]

/-- The public match-pattern wrapper inherits exact occurrence state from its
flat traversal. -/
theorem inferMatchPatternFuel_occurrenceState_eq
    {fuel : Nat} {context : Context} {pattern : Syntax.Pattern}
    {expected : Ty} {state : State} {result : TypedMatchPattern × State}
    (success : inferMatchPatternFuel fuel context pattern expected state =
      .ok result) :
    result.2.nodes = state.nodes ∧
      result.2.nextOccurrence = state.nextOccurrence := by
  unfold inferMatchPatternFuel at success
  cases flatResult :
      inferMatchPatternFlatFuel fuel context pattern expected [] state with
  | error error => simp [flatResult, bind, Except.bind] at success
  | ok inferred =>
      simp only [flatResult, bind, Except.bind] at success
      change Except.ok ({
        source := inferred.source
        type := inferred.state.resolve expected
        resolution := inferred.resolution
        requirements := inferred.requirements
      }, inferred.state) = Except.ok result at success
      injection success with resultEq
      subst result
      exact inferMatchPatternFlatFuel_preserves_occurrenceState fuel context
        pattern expected [] state inferred flatResult

/-- Match-pattern inference preserves the occurrence bound. -/
theorem inferMatchPatternFuel_occurrenceBoundExtends
    {fuel : Nat} {context : Context} {pattern : Syntax.Pattern}
    {expected : Ty} {state : State} {result : TypedMatchPattern × State}
    (success : inferMatchPatternFuel fuel context pattern expected state =
      .ok result) :
    state.OccurrenceBoundExtends result.2 := by
  have exactState := inferMatchPatternFuel_occurrenceState_eq success
  exact .of_nodes_eq_nextOccurrence_eq exactState.1 exactState.2

/-- Recording one expression is safe once its identity has already been
allocated below the current occurrence bound. -/
theorem recordExpression_occurrenceBoundExtends
    (source : Syntax.Expr) (expression : InferredExpression)
    (form : ExpressionForm) (requirements : List RequirementId)
    (coercions : List CoercionStep) (state : State)
    (idBelow : expression.id.occurrence.index < state.nextOccurrence) :
    state.OccurrenceBoundExtends
      (recordExpression source expression form requirements coercions state).2 := by
  unfold recordExpression
  exact State.OccurrenceBoundExtends.recordNode state _ idBelow

/-- Expected-type fitting followed by recording preserves the occurrence
bound for a previously allocated expression identity. -/
theorem recordExpressionWithExpected_occurrenceBoundExtends
    {context : Context} {source : Syntax.Expr} {id : ExpressionId}
    {type : Ty} {form : ExpressionForm} {requirements : List RequirementId}
    {expected : Option Ty} {state : State}
    {result : InferredExpression × State}
    (success : recordExpressionWithExpected context source id type form
      requirements expected state = .ok result)
    (idBelow : id.occurrence.index < state.nextOccurrence) :
    state.OccurrenceBoundExtends result.2 := by
  unfold recordExpressionWithExpected at success
  cases fittedResult : withExpected context state { id, type } expected with
  | error error => simp [fittedResult, bind, Except.bind] at success
  | ok fitted =>
      simp only [fittedResult, bind, Except.bind] at success
      change Except.ok _ = Except.ok result at success
      injection success with resultEq
      subst result
      have fittedExtends := withExpected_occurrenceBoundExtends fittedResult
      have fittedId : fitted.expression.id = id := by
        simpa using withExpected_success_expression_id fittedResult
      have fittedBelow :
          fitted.expression.id.occurrence.index <
            fitted.state.nextOccurrence := by
        rw [fittedId]
        exact Nat.lt_of_lt_of_le idBelow fittedExtends.nextOccurrence_le
      exact fittedExtends.trans
        (recordExpression_occurrenceBoundExtends source fitted.expression form
          (requirements ++ coercionRequirements fitted.coercions)
          fitted.coercions fitted.state fittedBelow)

/-- Invert successful expected-type recording into the exact fit result and
the exact expression node appended to that fit state's node table. -/
theorem recordExpressionWithExpected_success_record
    {context : Context} {source : Syntax.Expr} {id : ExpressionId}
    {type : Ty} {form : ExpressionForm} {requirements : List RequirementId}
    {expected : Option Ty} {state : State}
    {result : InferredExpression × State}
    (success : recordExpressionWithExpected context source id type form
      requirements expected state = .ok result) :
    ∃ fitted,
      withExpected context state { id, type } expected = .ok fitted ∧
      result.1 = fitted.expression ∧
      result.2 = fitted.state.recordNode (.expression {
        id := fitted.expression.id
        span := source.span
        type := fitted.expression.type
        form
        requirements := requirements ++
          coercionRequirements fitted.coercions
        coercions := fitted.coercions
      }) := by
  unfold recordExpressionWithExpected at success
  cases fittedResult : withExpected context state { id, type } expected with
  | error error => simp [fittedResult, bind, Except.bind] at success
  | ok fitted =>
      simp only [fittedResult, bind, Except.bind] at success
      change Except.ok _ = Except.ok result at success
      injection success with resultEq
      subst result
      exact ⟨fitted, rfl, rfl, rfl⟩

/-- The inversion above exposes the appended-node equation without requiring
clients to unfold either recording helper. -/
theorem recordExpressionWithExpected_success_nodes
    {context : Context} {source : Syntax.Expr} {id : ExpressionId}
    {type : Ty} {form : ExpressionForm} {requirements : List RequirementId}
    {expected : Option Ty} {state : State}
    {result : InferredExpression × State}
    (success : recordExpressionWithExpected context source id type form
      requirements expected state = .ok result) :
    ∃ fitted,
      withExpected context state { id, type } expected = .ok fitted ∧
      result.1 = fitted.expression ∧
      result.2.nodes = fitted.state.nodes ++ [.expression {
        id := fitted.expression.id
        span := source.span
        type := fitted.expression.type
        form
        requirements := requirements ++
          coercionRequirements fitted.coercions
        coercions := fitted.coercions
      }] := by
  obtain ⟨fitted, fittedSuccess, resultExpression, resultState⟩ :=
    recordExpressionWithExpected_success_record success
  refine ⟨fitted, fittedSuccess, resultExpression, ?_⟩
  rw [resultState]
  exact State.recordNode_nodes _ _

/-- Recording a selected declaration call preserves occurrence allocation
provided the call-result identity was allocated before the supplied state. -/
theorem recordSelectedCallResult_occurrenceBoundExtends
    (source callee : Syntax.Expr) (name : String)
    (arguments : List InferredExpression) (attempt : CandidateAttemptResult)
    (result : InferredExpression) (trailingCoercions : List CoercionStep)
    (state : State)
    (resultBelow : result.id.occurrence.index < state.nextOccurrence) :
    state.OccurrenceBoundExtends
      (recordSelectedCallResult source callee name arguments attempt result
        trailingCoercions state).2 := by
  let attachedState :=
    attachExpressionCoercions state attempt.argumentCoercions
  have attachedExtends : state.OccurrenceBoundExtends attachedState :=
    attachExpressionCoercions_occurrenceBoundExtends
      state attempt.argumentCoercions
  let allocation := attachedState.allocateExpressionId
  have allocatedExtends :
      attachedState.OccurrenceBoundExtends allocation.2 :=
    State.OccurrenceBoundExtends.allocateExpressionId attachedState
  let calleeExpression : InferredExpression := {
    id := allocation.1
    type := allocation.2.resolve attempt.instantiation.type
  }
  have calleeBelow :
      calleeExpression.id.occurrence.index < allocation.2.nextOccurrence := by
    exact State.allocateExpressionId_index_lt_nextOccurrence attachedState
  let calleeRecord := recordExpression callee calleeExpression
    (.reference name (.declaration attempt.instantiation)) [] [] allocation.2
  have calleeExtends :
      allocation.2.OccurrenceBoundExtends calleeRecord.2 :=
    recordExpression_occurrenceBoundExtends callee calleeExpression
      (.reference name (.declaration attempt.instantiation)) [] [] allocation.2
      calleeBelow
  have beforeResult :=
    attachedExtends.trans (allocatedExtends.trans calleeExtends)
  have resultBelowFinal :
      result.id.occurrence.index < calleeRecord.2.nextOccurrence :=
    Nat.lt_of_lt_of_le resultBelow beforeResult.nextOccurrence_le
  change state.OccurrenceBoundExtends
    (recordExpression source result
      (.call allocation.1 (arguments.map (fun argument => argument.id))
        (.declaration attempt.instantiation))
      (coercionRequirements attempt.callCoercions ++
        attempt.signatureRequirements ++
        coercionRequirements trailingCoercions)
      (attempt.callCoercions ++ trailingCoercions) calleeRecord.2).2
  exact beforeResult.trans
    (recordExpression_occurrenceBoundExtends source result _ _ _ _
      resultBelowFinal)

/-- The ordinary selected-call wrapper inherits the result-recording bound. -/
theorem recordSelectedCall_occurrenceBoundExtends
    (source callee : Syntax.Expr) (name : String)
    (arguments : List InferredExpression) (attempt : CandidateAttemptResult)
    (resultBelow :
      attempt.result.id.occurrence.index < attempt.state.nextOccurrence) :
    attempt.state.OccurrenceBoundExtends
      (recordSelectedCall source callee name arguments attempt).2 := by
  exact recordSelectedCallResult_occurrenceBoundExtends
    source callee name arguments attempt attempt.result [] attempt.state
    resultBelow

/-- Recording an indirect call preserves the occurrence bound once the call
identity returned by application fitting is known to be allocated. -/
theorem recordIndirectCall_occurrenceBoundExtends
    (source : Syntax.Expr) (callee : InferredExpression)
    (arguments : List InferredExpression) (result : IndirectApplicationResult)
    (resultBelow :
      result.result.id.occurrence.index < result.state.nextOccurrence) :
    result.state.OccurrenceBoundExtends
      (recordIndirectCall source callee arguments result).2 := by
  unfold recordIndirectCall
  exact recordExpression_occurrenceBoundExtends _ _ _ _ _ _ resultBelow

/-- Selected-call recording retains any exact older prefix when every delayed
argument-coercion target is fresh relative to that prefix. -/
theorem recordSelectedCallResult_preserves_nodesPrefix_of_fresh
    (source callee : Syntax.Expr) (name : String)
    (arguments : List InferredExpression) (attempt : CandidateAttemptResult)
    (result : InferredExpression) (trailingCoercions : List CoercionStep)
    (state : State) (baseNodes : List Node) (cutoff : Nat)
    (nodesPrefix : baseNodes <+: state.nodes)
    (baseBelow :
      ∀ node ∈ baseNodes, node.occurrenceId.index < cutoff)
    (entriesFresh : ∀ entry ∈ attempt.argumentCoercions,
      cutoff ≤ entry.expression.occurrence.index) :
    baseNodes <+:
      (recordSelectedCallResult source callee name arguments attempt result
        trailingCoercions state).2.nodes := by
  let attachedState :=
    attachExpressionCoercions state attempt.argumentCoercions
  have attachedPrefix : baseNodes <+: attachedState.nodes :=
    attachExpressionCoercions_preserves_nodesPrefix_of_fresh
      state attempt.argumentCoercions baseNodes cutoff nodesPrefix baseBelow
      entriesFresh
  let allocation := attachedState.allocateExpressionId
  have allocationNodes : allocation.2.nodes = attachedState.nodes := by
    rfl
  let calleeExpression : InferredExpression := {
    id := allocation.1
    type := allocation.2.resolve attempt.instantiation.type
  }
  let calleeRecord := recordExpression callee calleeExpression
    (.reference name (.declaration attempt.instantiation)) [] [] allocation.2
  have calleePrefix : baseNodes <+: calleeRecord.2.nodes := by
    exact (allocationNodes ▸ attachedPrefix).trans
      (State.recordNode_nodesPrefix allocation.2 (.expression {
        id := calleeExpression.id
        span := callee.span
        type := calleeExpression.type
        form := .reference name (.declaration attempt.instantiation)
      }))
  change baseNodes <+:
    (recordExpression source result
      (.call allocation.1 (arguments.map (fun argument => argument.id))
        (.declaration attempt.instantiation))
      (coercionRequirements attempt.callCoercions ++
        attempt.signatureRequirements ++
        coercionRequirements trailingCoercions)
      (attempt.callCoercions ++ trailingCoercions) calleeRecord.2).2.nodes
  exact calleePrefix.trans (State.recordNode_nodesPrefix calleeRecord.2 _)

/-- Invert selected-call recording into the exact synthetic callee node and
the exact call node appended after coercion attachment. -/
theorem recordSelectedCallResult_success_nodes
    {source callee : Syntax.Expr} {name : String}
    {arguments : List InferredExpression} {attempt : CandidateAttemptResult}
    {result : InferredExpression} {trailingCoercions : List CoercionStep}
    {state : State} {recorded : InferredExpression × State}
    (success : recordSelectedCallResult source callee name arguments attempt
      result trailingCoercions state = recorded) :
    recorded.1 = result ∧
      recorded.2.nodes =
        let attachedState :=
          attachExpressionCoercions state attempt.argumentCoercions
        let allocation := attachedState.allocateExpressionId
        let calleeExpression : InferredExpression := {
          id := allocation.1
          type := allocation.2.resolve attempt.instantiation.type
        }
        attachedState.nodes ++ [
          .expression {
            id := calleeExpression.id
            span := callee.span
            type := calleeExpression.type
            form := .reference name (.declaration attempt.instantiation)
          },
          .expression {
            id := result.id
            span := source.span
            type := result.type
            form := .call allocation.1
              (arguments.map (fun argument => argument.id))
              (.declaration attempt.instantiation)
            requirements :=
              coercionRequirements attempt.callCoercions ++
                attempt.signatureRequirements ++
                coercionRequirements trailingCoercions
            coercions := attempt.callCoercions ++ trailingCoercions
          }
        ] := by
  subst recorded
  simp [recordSelectedCallResult, recordExpression, State.recordNode,
    List.append_assoc]

/-- Builtin-function argument unification allocates no source occurrences. -/
theorem unifyBuiltinFunctionArgumentsEqual_occurrenceState_eq
    {arguments : List InferredExpression} {parameters : List Ty}
    {state next : State}
    (success : unifyBuiltinFunctionArgumentsEqual arguments parameters state =
      .ok next) :
    next.nodes = state.nodes ∧
      next.nextOccurrence = state.nextOccurrence := by
  induction arguments generalizing parameters state next with
  | nil =>
      simp only [unifyBuiltinFunctionArgumentsEqual] at success
      injection success with nextEq
      subst next
      exact ⟨rfl, rfl⟩
  | cons argument arguments induction =>
      cases parameters with
      | nil =>
          simp only [unifyBuiltinFunctionArgumentsEqual] at success
          injection success with nextEq
          subst next
          exact ⟨rfl, rfl⟩
      | cons parameter parameters =>
          simp only [unifyBuiltinFunctionArgumentsEqual] at success
          cases unifyResult : unify state argument.type parameter with
          | error error =>
              simp [unifyResult, bind, Except.bind] at success
          | ok unifiedState =>
              simp only [unifyResult, bind, Except.bind] at success
              have headEq := unify_occurrenceState_eq unifyResult
              have tailEq := induction success
              exact ⟨tailEq.1.trans headEq.1, tailEq.2.trans headEq.2⟩

/-- Builtin-function argument unification preserves the occurrence bound. -/
theorem unifyBuiltinFunctionArgumentsEqual_occurrenceBoundExtends
    {arguments : List InferredExpression} {parameters : List Ty}
    {state next : State}
    (success : unifyBuiltinFunctionArgumentsEqual arguments parameters state =
      .ok next) :
    state.OccurrenceBoundExtends next := by
  have exactState :=
    unifyBuiltinFunctionArgumentsEqual_occurrenceState_eq success
  exact .of_nodes_eq_nextOccurrence_eq exactState.1 exactState.2

/-- Recording a builtin call preserves the occurrence bound once the caller's
call identity is known to have been allocated. -/
theorem recordBuiltinFunctionCall_occurrenceBoundExtends
    {source callee : Syntax.Expr} {name : String}
    {function : BuiltinFunctionId} {arguments : List InferredExpression}
    {call : ExpressionId} {expected : Option Ty} {state : State}
    {result : InferredExpression × State}
    (success : recordBuiltinFunctionCall source callee name function arguments
      call expected state = .ok result)
    (callBelow : call.occurrence.index < state.nextOccurrence) :
    state.OccurrenceBoundExtends result.2 := by
  unfold recordBuiltinFunctionCall at success
  by_cases arity : arguments.length = function.parameterTypes.length
  · simp only [arity, ↓reduceIte, bind, Except.bind] at success
    cases argumentsResult :
        unifyBuiltinFunctionArgumentsEqual arguments function.parameterTypes
          state with
    | error error =>
        simp [argumentsResult, bind, Except.bind] at success
    | ok argumentsState =>
        simp only [argumentsResult, bind, Except.bind] at success
        have argumentsExtends :
            state.OccurrenceBoundExtends argumentsState :=
          unifyBuiltinFunctionArgumentsEqual_occurrenceBoundExtends
            argumentsResult
        cases expected with
        | none =>
            simp only at success
            let fittedState := argumentsState
            have fittedExtends :
                argumentsState.OccurrenceBoundExtends fittedState :=
              .refl _
            let allocation := fittedState.allocateExpressionId
            let calleeExpression : InferredExpression := {
              id := allocation.1
              type := function.type
            }
            let calleeRecord := recordExpression callee calleeExpression
              (.reference name (.builtinFunction function)) [] [] allocation.2
            have allocatedExtends :
                fittedState.OccurrenceBoundExtends allocation.2 :=
              State.OccurrenceBoundExtends.allocateExpressionId fittedState
            have calleeBelow :
                calleeExpression.id.occurrence.index <
                  allocation.2.nextOccurrence :=
              State.allocateExpressionId_index_lt_nextOccurrence fittedState
            have calleeExtends :
                allocation.2.OccurrenceBoundExtends calleeRecord.2 :=
              recordExpression_occurrenceBoundExtends callee calleeExpression
                (.reference name (.builtinFunction function)) [] [] allocation.2
                calleeBelow
            have beforeResult := argumentsExtends.trans
              (fittedExtends.trans (allocatedExtends.trans calleeExtends))
            have resultBelow :
                call.occurrence.index < calleeRecord.2.nextOccurrence :=
              Nat.lt_of_lt_of_le callBelow beforeResult.nextOccurrence_le
            change Except.ok (recordExpression source {
              id := call
              type := calleeRecord.2.resolve function.returnType
            } (.call allocation.1 (arguments.map (fun argument => argument.id))
              (.builtinFunction function)) [] [] calleeRecord.2) =
                Except.ok result at success
            injection success with resultEq
            subst result
            exact beforeResult.trans
              (recordExpression_occurrenceBoundExtends source _ _ [] [] _
                resultBelow)
        | some expectedType =>
            cases expectedResult :
                unify argumentsState function.returnType expectedType with
            | error error =>
                simp [expectedResult, bind, Except.bind] at success
            | ok fittedState =>
                simp only [expectedResult, bind, Except.bind] at success
                have fittedExtends :
                    argumentsState.OccurrenceBoundExtends fittedState :=
                  unify_occurrenceBoundExtends expectedResult
                let allocation := fittedState.allocateExpressionId
                let calleeExpression : InferredExpression := {
                  id := allocation.1
                  type := function.type
                }
                let calleeRecord := recordExpression callee calleeExpression
                  (.reference name (.builtinFunction function)) [] []
                    allocation.2
                have allocatedExtends :
                    fittedState.OccurrenceBoundExtends allocation.2 :=
                  State.OccurrenceBoundExtends.allocateExpressionId fittedState
                have calleeBelow :
                    calleeExpression.id.occurrence.index <
                      allocation.2.nextOccurrence :=
                  State.allocateExpressionId_index_lt_nextOccurrence fittedState
                have calleeExtends :
                    allocation.2.OccurrenceBoundExtends calleeRecord.2 :=
                  recordExpression_occurrenceBoundExtends callee calleeExpression
                    (.reference name (.builtinFunction function)) [] []
                    allocation.2 calleeBelow
                have beforeResult := argumentsExtends.trans
                  (fittedExtends.trans (allocatedExtends.trans calleeExtends))
                have resultBelow :
                    call.occurrence.index < calleeRecord.2.nextOccurrence :=
                  Nat.lt_of_lt_of_le callBelow beforeResult.nextOccurrence_le
                change Except.ok (recordExpression source {
                  id := call
                  type := calleeRecord.2.resolve function.returnType
                } (.call allocation.1
                  (arguments.map (fun argument => argument.id))
                  (.builtinFunction function)) [] [] calleeRecord.2) =
                    Except.ok result at success
                injection success with resultEq
                subst result
                exact beforeResult.trans
                  (recordExpression_occurrenceBoundExtends source _ _ [] [] _
                    resultBelow)
  · simp [arity, bind, Except.bind] at success

/-- Ordinary unary-operator inference allocates no source occurrences. -/
theorem inferUnaryOperator_occurrenceState_eq
    {context : Context} {operator : Syntax.UnaryOp} {operandType : Ty}
    {expected : Option Ty} {integerLiterals : List IntegerLiteralOrigin}
    {state : State} {result : OperatorInferenceResult}
    (success : inferUnaryOperator context operator operandType expected
      integerLiterals state = .ok result) :
    result.state.nodes = state.nodes ∧
      result.state.nextOccurrence = state.nextOccurrence := by
  unfold inferUnaryOperator at success
  simp_all [bind, Except.bind]
  repeat' first | split at success
  all_goals try cases success
  all_goals try have exactState := unify_occurrenceState_eq (by assumption)
  all_goals try simp_all
  all_goals try simp_all [State.addRequirementsWithIds,
    State.addRequirementWithId]

/-- Ordinary binary-operator inference allocates no source occurrences. -/
theorem inferBinaryOperator_occurrenceState_eq
    {context : Context} {operator : Syntax.BinaryOp} {left right : Ty}
    {expected : Option Ty} {integerLiterals : List IntegerLiteralOrigin}
    {state : State} {result : OperatorInferenceResult}
    (success : inferBinaryOperator context operator left right expected
      integerLiterals state = .ok result) :
    result.state.nodes = state.nodes ∧
      result.state.nextOccurrence = state.nextOccurrence := by
  unfold inferBinaryOperator at success
  simp_all [bind, Except.bind]
  repeat' first | split at success
  all_goals try cases success
  all_goals try have exactState := unify_occurrenceState_eq (by assumption)
  all_goals try simp_all
  all_goals try simp_all [State.addRequirementsWithIds,
    State.addRequirementWithId]
  all_goals grind [unify_occurrenceState_eq]


end Solcore.Frontend.SourceInference.Detail
