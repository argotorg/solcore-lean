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

/-! Small prefix-preservation adapters used by the eventual mutually
recursive occurrence proof.  The primitive state updates below do not touch
the node table, so an arbitrary older prefix remains exact across them. -/

private theorem unify_preserves_nodesPrefix
    {state next : State} {left right : Ty} {baseNodes : List Node}
    (success : unify state left right = .ok next)
    (nodesPrefix : baseNodes <+: state.nodes) :
    baseNodes <+: next.nodes := by
  rw [(unify_occurrenceState_eq success).1]
  exact nodesPrefix

private theorem fresh_preserves_nodesPrefix
    (state : State) {baseNodes : List Node}
    (nodesPrefix : baseNodes <+: state.nodes) :
    baseNodes <+: state.fresh.2.nodes := by
  change baseNodes <+: state.nodes
  exact nodesPrefix

private theorem withLocals_preserves_nodesPrefix
    (state : State) (locals : TypeSystem.Environment)
    {baseNodes : List Node} (nodesPrefix : baseNodes <+: state.nodes) :
    baseNodes <+: (state.withLocals locals).nodes := by
  change baseNodes <+: state.nodes
  exact nodesPrefix

private theorem restoreLexicalScope_preserves_nodesPrefix
    (state : State) (scope : LexicalScope) {baseNodes : List Node}
    (nodesPrefix : baseNodes <+: state.nodes) :
    baseNodes <+: (state.restoreLexicalScope scope).nodes := by
  simpa only [State.restoreLexicalScope_nodes] using nodesPrefix

private theorem allocateBinder_preserves_nodesPrefix
    (state : State) (name : String) (scheme : TypeSystem.Scheme)
    (span : Option Syntax.SourceSpan) (comptime : Bool)
    (schemeRequirements : List LocalSchemeRequirement)
    {baseNodes : List Node} (nodesPrefix : baseNodes <+: state.nodes) :
    baseNodes <+:
      (state.allocateBinder name scheme span comptime
        schemeRequirements).2.nodes := by
  change baseNodes <+: state.nodes
  exact nodesPrefix

private theorem allocateHiddenLocal_preserves_nodesPrefix
    (state : State) {baseNodes : List Node}
    (nodesPrefix : baseNodes <+: state.nodes) :
    baseNodes <+: state.allocateHiddenLocal.2.nodes := by
  change baseNodes <+: state.nodes
  exact nodesPrefix

private theorem allocateExpressionId_preserves_nodesPrefix
    (state : State) {baseNodes : List Node}
    (nodesPrefix : baseNodes <+: state.nodes) :
    baseNodes <+: state.allocateExpressionId.2.nodes := by
  simpa only [State.allocateExpressionId_nodes] using nodesPrefix

private theorem allocateStatementId_preserves_nodesPrefix
    (state : State) {baseNodes : List Node}
    (nodesPrefix : baseNodes <+: state.nodes) :
    baseNodes <+: state.allocateStatementId.2.nodes := by
  simpa only [State.allocateStatementId_nodes] using nodesPrefix

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

/-- Expected-type fitting retains any node prefix visible on entry. -/
private theorem withExpected_preserves_nodesPrefix
    {context : Context} {state : State} {actual : InferredExpression}
    {expected : Option Ty} {result : ExpectationResult}
    {baseNodes : List Node}
    (success : withExpected context state actual expected = .ok result)
    (nodesPrefix : baseNodes <+: state.nodes) :
    baseNodes <+: result.state.nodes := by
  rw [(withExpected_occurrenceState_eq success).1]
  exact nodesPrefix

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

/-- Every delayed coercion emitted by argument fitting targets one of the
input argument occurrences.  Fitting may add coercion payloads, but cannot
invent an unrelated expression identity. -/
theorem fitArguments_some_coercion_expression_mem
    {context : Context} {state : State}
    {arguments : List InferredExpression} {parameters : List Ty}
    {result : ArgumentFitResult}
    (success : fitArguments context state arguments parameters =
      .ok (some result)) :
    ∀ entry ∈ result.coercions,
      entry.expression ∈ arguments.map (fun argument => argument.id) := by
  induction arguments generalizing parameters state result with
  | nil =>
      cases parameters <;> simp [fitArguments] at success
      subst result
      simp
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
                          intro entry member
                          simp only [List.map_cons, List.mem_cons] at member ⊢
                          cases member with
                          | inl headEq =>
                              subst entry
                              exact Or.inl rfl
                          | inr tailMember =>
                              exact Or.inr
                                (induction (result := tail) tailResult entry
                                  tailMember)

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

/-- A retained overload attempt forwards exactly the delayed argument
coercions produced by fitting its input argument spine. -/
theorem tryFunctionCandidate_some_argumentCoercion_expression_mem
    {context : Context} {arguments : List InferredExpression}
    {integerLiteralOrigins : List IntegerLiteralOrigin} {call : ExpressionId}
    {expected : Option Ty} {state : State}
    {signature : ProgramFunctionSignature} {result : CandidateAttemptResult}
    (success : tryFunctionCandidate context arguments integerLiteralOrigins
      call expected state signature = .ok (some result)) :
    ∀ entry ∈ result.argumentCoercions,
      entry.expression ∈ arguments.map (fun argument => argument.id) := by
  unfold tryFunctionCandidate at success
  simp_all [bind, Except.bind]
  repeat' first | split at success
  all_goals try cases success
  all_goals try have fittedProvenance :=
    fitArguments_some_coercion_expression_mem (by assumption)
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

private theorem collectCandidateAttempts_success_argumentCoercion_expression_mem
    {attempt : ProgramFunctionSignature →
      Except Error (Option CandidateAttemptResult)}
    {argumentIds : List ExpressionId}
    (attemptProvenance : ∀ signature result,
      attempt signature = .ok (some result) →
        ∀ entry ∈ result.argumentCoercions,
          entry.expression ∈ argumentIds) :
    ∀ candidates selected,
      selected ∈ (collectCandidateAttempts attempt candidates).successes →
        ∀ entry ∈ selected.attempt.argumentCoercions,
          entry.expression ∈ argumentIds := by
  intro candidates
  induction candidates with
  | nil => simp [collectCandidateAttempts]
  | cons signature candidates induction =>
      intro selected member entry entryMember
      simp only [collectCandidateAttempts] at member
      cases attemptResult : attempt signature with
      | error error =>
          simp only [attemptResult] at member
          exact induction selected member entry entryMember
      | ok result? =>
          cases result? with
          | none =>
              simp only [attemptResult] at member
              exact induction selected member entry entryMember
          | some result =>
              simp only [attemptResult, List.mem_cons] at member
              cases member with
              | inl selectedEq =>
                  subst selected
                  exact attemptProvenance signature result attemptResult entry
                    entryMember
              | inr member =>
                  exact induction selected member entry entryMember

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

/-- Explicit overload ranking cannot introduce delayed coercion targets that
were absent from the caller's argument spine. -/
theorem selectFunctionCandidateFrom_argumentCoercion_expression_mem
    {context : Context} {name : String}
    {candidates : List ProgramFunctionSignature}
    {arguments : List InferredExpression}
    {integerLiteralOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected : Option Ty} {state : State}
    {result : CandidateAttemptResult}
    (success : selectFunctionCandidateFrom context name candidates arguments
      integerLiteralOrigins call expected state = .ok result) :
    ∀ entry ∈ result.argumentCoercions,
      entry.expression ∈ arguments.map (fun argument => argument.id) := by
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
            exact
              collectCandidateAttempts_success_argumentCoercion_expression_mem
                (argumentIds := arguments.map (fun argument => argument.id))
                (fun signature attemptResult attemptSuccess =>
                  tryFunctionCandidate_some_argumentCoercion_expression_mem
                    attemptSuccess)
                candidates candidate member

/-- Freshness of every caller argument transfers to every delayed coercion
target retained by explicit overload selection. -/
theorem selectFunctionCandidateFrom_argumentCoercions_fresh
    {context : Context} {name : String}
    {candidates : List ProgramFunctionSignature}
    {arguments : List InferredExpression}
    {integerLiteralOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected : Option Ty} {state : State}
    {result : CandidateAttemptResult} {cutoff : Nat}
    (success : selectFunctionCandidateFrom context name candidates arguments
      integerLiteralOrigins call expected state = .ok result)
    (argumentsFresh : ∀ argument ∈ arguments,
      cutoff ≤ argument.id.occurrence.index) :
    ∀ entry ∈ result.argumentCoercions,
      cutoff ≤ entry.expression.occurrence.index := by
  intro entry member
  have idMember :=
    selectFunctionCandidateFrom_argumentCoercion_expression_mem success entry
      member
  obtain ⟨argument, argumentMember, argumentId⟩ :=
    List.mem_map.mp idMember
  rw [← argumentId]
  exact argumentsFresh argument argumentMember

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

/-- Visible overload lookup inherits delayed-coercion target provenance from
the explicit selector. -/
theorem selectFunctionCandidate_argumentCoercion_expression_mem
    {context : Context} {name : String}
    {arguments : List InferredExpression}
    {integerLiteralOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected : Option Ty} {state : State}
    {result : CandidateAttemptResult}
    (success : selectFunctionCandidate context name arguments
      integerLiteralOrigins call expected state = .ok result) :
    ∀ entry ∈ result.argumentCoercions,
      entry.expression ∈ arguments.map (fun argument => argument.id) := by
  unfold selectFunctionCandidate at success
  cases candidatesResult : functionsNamed context name with
  | error error =>
      simp [candidatesResult, bind, Except.bind] at success
  | ok candidates =>
      simp only [candidatesResult, bind, Except.bind] at success
      exact selectFunctionCandidateFrom_argumentCoercion_expression_mem success

/-- Ordinary visible overload selection also transfers caller-argument
freshness to every delayed coercion target. -/
theorem selectFunctionCandidate_argumentCoercions_fresh
    {context : Context} {name : String}
    {arguments : List InferredExpression}
    {integerLiteralOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected : Option Ty} {state : State}
    {result : CandidateAttemptResult} {cutoff : Nat}
    (success : selectFunctionCandidate context name arguments
      integerLiteralOrigins call expected state = .ok result)
    (argumentsFresh : ∀ argument ∈ arguments,
      cutoff ≤ argument.id.occurrence.index) :
    ∀ entry ∈ result.argumentCoercions,
      cutoff ≤ entry.expression.occurrence.index := by
  intro entry member
  have idMember :=
    selectFunctionCandidate_argumentCoercion_expression_mem success entry member
  obtain ⟨argument, argumentMember, argumentId⟩ :=
    List.mem_map.mp idMember
  rw [← argumentId]
  exact argumentsFresh argument argumentMember

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

@[simp] theorem attachExpressionCoercions_nextOccurrence
    (state : State) (entries : List ExpressionCoercions) :
    (attachExpressionCoercions state entries).nextOccurrence =
      state.nextOccurrence := by
  unfold attachExpressionCoercions
  induction entries generalizing state with
  | nil => rfl
  | cons entry entries induction =>
      simp only [List.foldl_cons]
      rw [induction]
      exact State.modifyExpressionNode_nextOccurrence state _ _

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

/-- Expression recording appends one node and therefore retains any older
node prefix. -/
private theorem recordExpression_preserves_nodesPrefix
    (source : Syntax.Expr) (expression : InferredExpression)
    (form : ExpressionForm) (requirements : List RequirementId)
    (coercions : List CoercionStep) (state : State)
    {localSchemeInstantiationStart : Option Nat}
    {baseNodes : List Node} (nodesPrefix : baseNodes <+: state.nodes) :
    baseNodes <+:
      (recordExpression source expression form requirements coercions state
        localSchemeInstantiationStart).2.nodes := by
  exact nodesPrefix.trans (State.recordNode_nodesPrefix state _)

/-- Recording one expression is safe once its identity has already been
allocated below the current occurrence bound. -/
theorem recordExpression_occurrenceBoundExtends
    (source : Syntax.Expr) (expression : InferredExpression)
    (form : ExpressionForm) (requirements : List RequirementId)
    (coercions : List CoercionStep) (state : State)
    {localSchemeInstantiationStart : Option Nat}
    (idBelow : expression.id.occurrence.index < state.nextOccurrence) :
    state.OccurrenceBoundExtends
      (recordExpression source expression form requirements coercions state
        localSchemeInstantiationStart).2 := by
  unfold recordExpression
  exact State.OccurrenceBoundExtends.recordNode state _ idBelow

/-- Expected-type fitting followed by recording preserves the occurrence
bound for a previously allocated expression identity. -/
theorem recordExpressionWithExpected_occurrenceBoundExtends
    {context : Context} {source : Syntax.Expr} {id : ExpressionId}
    {type : Ty} {form : ExpressionForm} {requirements : List RequirementId}
    {expected : Option Ty} {state : State}
    {localSchemeInstantiationStart : Option Nat}
    {result : InferredExpression × State}
    (success : recordExpressionWithExpected context source id type form
      requirements expected state localSchemeInstantiationStart = .ok result)
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
          fitted.coercions fitted.state fittedBelow
          (localSchemeInstantiationStart := localSchemeInstantiationStart))

/-- Invert successful expected-type recording into the exact fit result and
the exact expression node appended to that fit state's node table. -/
theorem recordExpressionWithExpected_success_record
    {context : Context} {source : Syntax.Expr} {id : ExpressionId}
    {type : Ty} {form : ExpressionForm} {requirements : List RequirementId}
    {expected : Option Ty} {state : State}
    {localSchemeInstantiationStart : Option Nat}
    {result : InferredExpression × State}
    (success : recordExpressionWithExpected context source id type form
      requirements expected state localSchemeInstantiationStart = .ok result) :
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
        localSchemeInstantiationStart
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
    {localSchemeInstantiationStart : Option Nat}
    {result : InferredExpression × State}
    (success : recordExpressionWithExpected context source id type form
      requirements expected state localSchemeInstantiationStart = .ok result) :
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
        localSchemeInstantiationStart
      }] := by
  obtain ⟨fitted, fittedSuccess, resultExpression, resultState⟩ :=
    recordExpressionWithExpected_success_record success
  refine ⟨fitted, fittedSuccess, resultExpression, ?_⟩
  rw [resultState]
  exact State.recordNode_nodes _ _

/-- Expected-type recording preserves every node prefix visible before
fitting, then appends the newly recorded expression node. -/
private theorem recordExpressionWithExpected_preserves_nodesPrefix
    {context : Context} {source : Syntax.Expr} {id : ExpressionId}
    {type : Ty} {form : ExpressionForm} {requirements : List RequirementId}
    {expected : Option Ty} {state : State}
    {localSchemeInstantiationStart : Option Nat}
    {result : InferredExpression × State} {baseNodes : List Node}
    (success : recordExpressionWithExpected context source id type form
      requirements expected state localSchemeInstantiationStart = .ok result)
    (nodesPrefix : baseNodes <+: state.nodes) :
    baseNodes <+: result.2.nodes := by
  obtain ⟨fitted, fittedSuccess, _, resultState⟩ :=
    recordExpressionWithExpected_success_record success
  rw [resultState]
  exact recordExpression_preserves_nodesPrefix source fitted.expression form
    (requirements ++ coercionRequirements fitted.coercions) fitted.coercions
    fitted.state (withExpected_preserves_nodesPrefix fittedSuccess nodesPrefix)
    (localSchemeInstantiationStart := localSchemeInstantiationStart)

/-- Successful recording retains the caller-supplied local-instantiation
allocator start on the exact expression node returned to the traversal. -/
theorem recordExpressionWithExpected_success_localSchemeInstantiationStart
    {context : Context} {source : Syntax.Expr} {id : ExpressionId}
    {type : Ty} {form : ExpressionForm} {requirements : List RequirementId}
    {expected : Option Ty} {state : State}
    {localSchemeInstantiationStart : Option Nat}
    {result : InferredExpression × State}
    (success : recordExpressionWithExpected context source id type form
      requirements expected state localSchemeInstantiationStart = .ok result) :
    ∃ node,
      .expression node ∈ result.2.nodes ∧
      node.id = result.1.id ∧
      node.localSchemeInstantiationStart = localSchemeInstantiationStart := by
  obtain ⟨fitted, _, resultExpression, resultNodes⟩ :=
    recordExpressionWithExpected_success_nodes success
  let node : ExpressionNode := {
    id := fitted.expression.id
    span := source.span
    type := fitted.expression.type
    form
    requirements := requirements ++
      coercionRequirements fitted.coercions
    coercions := fitted.coercions
    localSchemeInstantiationStart
  }
  refine ⟨node, ?_, ?_, rfl⟩
  · rw [resultNodes]
    simp [node]
  · rw [resultExpression]

/-- Expected-type recording returns the occurrence identity supplied by its
caller, regardless of whether fitting chose unification or coercion. -/
theorem recordExpressionWithExpected_success_id
    {context : Context} {source : Syntax.Expr} {id : ExpressionId}
    {type : Ty} {form : ExpressionForm} {requirements : List RequirementId}
    {expected : Option Ty} {state : State}
    {localSchemeInstantiationStart : Option Nat}
    {result : InferredExpression × State}
    (success : recordExpressionWithExpected context source id type form
      requirements expected state localSchemeInstantiationStart = .ok result) :
    result.1.id = id := by
  obtain ⟨fitted, fittedSuccess, resultExpression, _⟩ :=
    recordExpressionWithExpected_success_record success
  rw [resultExpression]
  exact withExpected_success_expression_id fittedSuccess

/-- Expected-type recording allocates no new occurrence identity; its root ID
was allocated by the enclosing traversal. -/
theorem recordExpressionWithExpected_success_nextOccurrence
    {context : Context} {source : Syntax.Expr} {id : ExpressionId}
    {type : Ty} {form : ExpressionForm} {requirements : List RequirementId}
    {expected : Option Ty} {state : State}
    {localSchemeInstantiationStart : Option Nat}
    {result : InferredExpression × State}
    (success : recordExpressionWithExpected context source id type form
      requirements expected state localSchemeInstantiationStart = .ok result) :
    result.2.nextOccurrence = state.nextOccurrence := by
  obtain ⟨fitted, fittedSuccess, _, resultState⟩ :=
    recordExpressionWithExpected_success_record success
  rw [resultState]
  change fitted.state.nextOccurrence = state.nextOccurrence
  exact (withExpected_occurrenceState_eq fittedSuccess).2

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

/-- Indirect-call recording only appends its outer call node. -/
private theorem recordIndirectCall_preserves_nodesPrefix
    (source : Syntax.Expr) (callee : InferredExpression)
    (arguments : List InferredExpression) (result : IndirectApplicationResult)
    {baseNodes : List Node}
    (nodesPrefix : baseNodes <+: result.state.nodes) :
    baseNodes <+: (recordIndirectCall source callee arguments result).2.nodes := by
  unfold recordIndirectCall
  exact recordExpression_preserves_nodesPrefix _ _ _ _ _ _ nodesPrefix

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

/-- The ordinary selected-call wrapper inherits the anchored prefix theorem;
its only potentially destructive step is coercion attachment to fresh argument
occurrences. -/
private theorem recordSelectedCall_preserves_nodesPrefix_of_fresh
    (source callee : Syntax.Expr) (name : String)
    (arguments : List InferredExpression) (attempt : CandidateAttemptResult)
    (baseNodes : List Node) (cutoff : Nat)
    (nodesPrefix : baseNodes <+: attempt.state.nodes)
    (baseBelow :
      ∀ node ∈ baseNodes, node.occurrenceId.index < cutoff)
    (entriesFresh : ∀ entry ∈ attempt.argumentCoercions,
      cutoff ≤ entry.expression.occurrence.index) :
    baseNodes <+:
      (recordSelectedCall source callee name arguments attempt).2.nodes := by
  unfold recordSelectedCall
  exact recordSelectedCallResult_preserves_nodesPrefix_of_fresh
    source callee name arguments attempt attempt.result [] attempt.state
    baseNodes cutoff nodesPrefix baseBelow entriesFresh

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

/-- Selected-call recording allocates exactly the synthetic callee occurrence;
the call occurrence itself was allocated by the enclosing traversal. -/
@[simp] theorem recordSelectedCallResult_nextOccurrence
    (source callee : Syntax.Expr) (name : String)
    (arguments : List InferredExpression) (attempt : CandidateAttemptResult)
    (result : InferredExpression) (trailingCoercions : List CoercionStep)
    (state : State) :
    (recordSelectedCallResult source callee name arguments attempt result
      trailingCoercions state).2.nextOccurrence = state.nextOccurrence + 1 := by
  unfold recordSelectedCallResult recordExpression
  simp only [State.recordNode_nextOccurrence,
    State.allocateExpressionId_nextOccurrence,
    attachExpressionCoercions_nextOccurrence]

@[simp] theorem recordSelectedCallResult_fst
    (source callee : Syntax.Expr) (name : String)
    (arguments : List InferredExpression) (attempt : CandidateAttemptResult)
    (result : InferredExpression) (trailingCoercions : List CoercionStep)
    (state : State) :
    (recordSelectedCallResult source callee name arguments attempt result
      trailingCoercions state).1 = result := by
  simp [recordSelectedCallResult, recordExpression]

@[simp] theorem recordSelectedCall_fst
    (source callee : Syntax.Expr) (name : String)
    (arguments : List InferredExpression) (attempt : CandidateAttemptResult) :
    (recordSelectedCall source callee name arguments attempt).1 =
      attempt.result := by
  simp [recordSelectedCall]

@[simp] theorem recordSelectedCall_nextOccurrence
    (source callee : Syntax.Expr) (name : String)
    (arguments : List InferredExpression) (attempt : CandidateAttemptResult) :
    (recordSelectedCall source callee name arguments attempt).2.nextOccurrence =
      attempt.state.nextOccurrence + 1 := by
  unfold recordSelectedCall
  exact recordSelectedCallResult_nextOccurrence source callee name arguments
    attempt attempt.result [] attempt.state

@[simp] theorem recordIndirectCall_fst
    (source : Syntax.Expr) (callee : InferredExpression)
    (arguments : List InferredExpression) (result : IndirectApplicationResult) :
    (recordIndirectCall source callee arguments result).1 = result.result := by
  simp [recordIndirectCall, recordExpression, State.recordNode]

@[simp] theorem recordIndirectCall_nextOccurrence
    (source : Syntax.Expr) (callee : InferredExpression)
    (arguments : List InferredExpression) (result : IndirectApplicationResult) :
    (recordIndirectCall source callee arguments result).2.nextOccurrence =
      result.state.nextOccurrence := by
  unfold recordIndirectCall recordExpression
  exact State.recordNode_nextOccurrence _ _

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

/-- Builtin argument unification retains every node prefix visible before the
first argument is checked. -/
private theorem unifyBuiltinFunctionArgumentsEqual_preserves_nodesPrefix
    {arguments : List InferredExpression} {parameters : List Ty}
    {state next : State} {baseNodes : List Node}
    (success : unifyBuiltinFunctionArgumentsEqual arguments parameters state =
      .ok next)
    (nodesPrefix : baseNodes <+: state.nodes) :
    baseNodes <+: next.nodes := by
  rw [(unifyBuiltinFunctionArgumentsEqual_occurrenceState_eq success).1]
  exact nodesPrefix

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

/-- Successful builtin-call recording keeps every input node as an exact
prefix and appends the synthetic callee and outer call nodes. -/
private theorem recordBuiltinFunctionCall_preserves_nodesPrefix
    {source callee : Syntax.Expr} {name : String}
    {function : BuiltinFunctionId} {arguments : List InferredExpression}
    {call : ExpressionId} {expected : Option Ty} {state : State}
    {result : InferredExpression × State} {baseNodes : List Node}
    (success : recordBuiltinFunctionCall source callee name function arguments
      call expected state = .ok result)
    (nodesPrefix : baseNodes <+: state.nodes) :
    baseNodes <+: result.2.nodes := by
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
        have argumentsPrefix : baseNodes <+: argumentsState.nodes :=
          unifyBuiltinFunctionArgumentsEqual_preserves_nodesPrefix
            argumentsResult nodesPrefix
        cases expected with
        | none =>
            simp only at success
            let fittedState := argumentsState
            have fittedPrefix : baseNodes <+: fittedState.nodes :=
              argumentsPrefix
            let allocation := fittedState.allocateExpressionId
            have allocatedPrefix : baseNodes <+: allocation.2.nodes :=
              allocateExpressionId_preserves_nodesPrefix fittedState
                fittedPrefix
            let calleeExpression : InferredExpression := {
              id := allocation.1
              type := function.type
            }
            let calleeRecord := recordExpression callee calleeExpression
              (.reference name (.builtinFunction function)) [] [] allocation.2
            have calleePrefix : baseNodes <+: calleeRecord.2.nodes :=
              recordExpression_preserves_nodesPrefix callee calleeExpression
                (.reference name (.builtinFunction function)) [] [] allocation.2
                allocatedPrefix
            change Except.ok (recordExpression source {
              id := call
              type := calleeRecord.2.resolve function.returnType
            } (.call allocation.1 (arguments.map (fun argument => argument.id))
              (.builtinFunction function)) [] [] calleeRecord.2) =
                Except.ok result at success
            injection success with resultEq
            subst result
            exact recordExpression_preserves_nodesPrefix source _ _ [] []
              calleeRecord.2 calleePrefix
        | some expectedType =>
            cases expectedResult :
                unify argumentsState function.returnType expectedType with
            | error error =>
                simp [expectedResult, bind, Except.bind] at success
            | ok fittedState =>
                simp only [expectedResult, bind, Except.bind] at success
                have fittedPrefix : baseNodes <+: fittedState.nodes :=
                  unify_preserves_nodesPrefix expectedResult argumentsPrefix
                let allocation := fittedState.allocateExpressionId
                have allocatedPrefix : baseNodes <+: allocation.2.nodes :=
                  allocateExpressionId_preserves_nodesPrefix fittedState
                    fittedPrefix
                let calleeExpression : InferredExpression := {
                  id := allocation.1
                  type := function.type
                }
                let calleeRecord := recordExpression callee calleeExpression
                  (.reference name (.builtinFunction function)) [] []
                    allocation.2
                have calleePrefix : baseNodes <+: calleeRecord.2.nodes :=
                  recordExpression_preserves_nodesPrefix callee calleeExpression
                    (.reference name (.builtinFunction function)) [] []
                    allocation.2 allocatedPrefix
                change Except.ok (recordExpression source {
                  id := call
                  type := calleeRecord.2.resolve function.returnType
                } (.call allocation.1
                  (arguments.map (fun argument => argument.id))
                  (.builtinFunction function)) [] [] calleeRecord.2) =
                    Except.ok result at success
                injection success with resultEq
                subst result
                exact recordExpression_preserves_nodesPrefix source _ _ [] []
                  calleeRecord.2 calleePrefix
  · simp [arity, bind, Except.bind] at success

/-- Successful builtin-call recording returns the caller-allocated call
occurrence. -/
theorem recordBuiltinFunctionCall_success_id
    {source callee : Syntax.Expr} {name : String}
    {function : BuiltinFunctionId} {arguments : List InferredExpression}
    {call : ExpressionId} {expected : Option Ty} {state : State}
    {result : InferredExpression × State}
    (success : recordBuiltinFunctionCall source callee name function arguments
      call expected state = .ok result) :
    result.1.id = call := by
  unfold recordBuiltinFunctionCall at success
  simp_all [bind, Except.bind, recordExpression]
  repeat' first | split at success
  all_goals try cases success
  all_goals simp_all [recordExpression]

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

/-- Constructor application records its result at the occurrence identity
allocated by the enclosing expression traversal. -/
theorem inferConstructorApplicationFuel_success_id
    {fuel : Nat} {context : Context} {source : Syntax.Expr}
    {id : ExpressionId} {instantiation : DataConstructorInstantiation}
    {arguments : List Syntax.Expr} {expected : Option Ty} {state : State}
    {result : InferredExpression × State}
    (success : inferConstructorApplicationFuel fuel context source id
      instantiation arguments expected state = .ok result) :
    result.1.id = id := by
  unfold inferConstructorApplicationFuel at success
  simp_all [bind, Except.bind]
  repeat' first | split at success
  all_goals try cases success
  all_goals try have resultId :=
    recordExpressionWithExpected_success_id (by assumption)
  all_goals simp_all [recordExpression]

/-- Every successful expression traversal returns the exact root occurrence
reserved at entry, before any child traversal or coercion fitting runs. -/
theorem inferExprFuel_success_id
    {fuel : Nat} {context : Context} {expression : Syntax.Expr}
    {expected : Option Ty} {state : State}
    {result : InferredExpression × State}
    (success : inferExprFuel fuel context expression expected state =
      .ok result) :
    result.1.id = state.allocateExpressionId.1 := by
  unfold inferExprFuel at success
  simp_all [bind, Except.bind]
  repeat' first | split at success
  all_goals try cases success
  all_goals try have recordId :=
    recordExpressionWithExpected_success_id (by assumption)
  all_goals try have constructorId :=
    inferConstructorApplicationFuel_success_id (by assumption)
  all_goals try have selectedId :=
    selectFunctionCandidateFrom_result_id (by assumption)
  all_goals try have fittedId :=
    withExpected_success_expression_id (by assumption)
  all_goals try have applicationId :=
    applyFunctionType_result_id (by assumption)
  all_goals try have builtinId :=
    recordBuiltinFunctionCall_success_id (by assumption)
  all_goals simp_all [recordSelectedCall, recordSelectedCallResult,
    recordIndirectCall, recordExpression]

/-- The returned root index is exactly the input allocator cutoff. -/
theorem inferExprFuel_success_id_index
    {fuel : Nat} {context : Context} {expression : Syntax.Expr}
    {expected : Option Ty} {state : State}
    {result : InferredExpression × State}
    (success : inferExprFuel fuel context expression expected state =
      .ok result) :
    result.1.id.occurrence.index = state.nextOccurrence := by
  rw [inferExprFuel_success_id success]
  rfl

private theorem allocateExpressionId_success_nextOccurrence
    {state next : State} {id : ExpressionId}
    (success : state.allocateExpressionId = (id, next)) :
    next.nextOccurrence = state.nextOccurrence + 1 := by
  have projected := congrArg (fun result => result.2.nextOccurrence) success
  simpa only [State.allocateExpressionId_nextOccurrence] using projected.symm

private theorem allocateStatementId_success_nextOccurrence
    {state next : State} {id : StatementId}
    (success : state.allocateStatementId = (id, next)) :
    next.nextOccurrence = state.nextOccurrence + 1 := by
  have projected := congrArg (fun result => result.2.nextOccurrence) success
  simpa only [State.allocateStatementId_nextOccurrence] using projected.symm

/-- Successful unification leaves the occurrence counter unchanged. -/
@[simp] private theorem unify_success_nextOccurrence
    {state next : State} {left right : Ty}
    (success : unify state left right = .ok next) :
    next.nextOccurrence = state.nextOccurrence :=
  (unify_occurrenceState_eq success).2

/-- Recording a successful builtin call allocates exactly its synthetic callee
occurrence; the outer call occurrence was allocated by its caller. -/
private theorem recordBuiltinFunctionCall_success_nextOccurrence
    {source callee : Syntax.Expr} {name : String}
    {function : BuiltinFunctionId} {arguments : List InferredExpression}
    {call : ExpressionId} {expected : Option Ty} {state : State}
    {result : InferredExpression × State}
    (success : recordBuiltinFunctionCall source callee name function arguments
      call expected state = .ok result) :
    result.2.nextOccurrence = state.nextOccurrence + 1 := by
  unfold recordBuiltinFunctionCall at success
  simp_all [bind, Except.bind]
  repeat' first | split at success
  all_goals try cases success
  all_goals try have argumentsState :=
    unifyBuiltinFunctionArgumentsEqual_occurrenceState_eq (by assumption)
  all_goals try have expectedState :=
    unify_occurrenceState_eq (by assumption)
  all_goals simp_all [recordExpression, State.recordNode]

private def PreservesNextOccurrence {alpha : Type}
    (stateOf : alpha → State) (initial : State)
    (computation : Except Error alpha) : Prop :=
  ∀ result, computation = .ok result →
    initial.nextOccurrence ≤ (stateOf result).nextOccurrence

private theorem pair_except_nextOccurrence {epsilon alpha beta : Type}
    {computation : Except epsilon (alpha × beta)} {result : alpha × beta}
    {initial : State} {nextOccurrence : beta → Nat}
    (invariant : ∀ value state,
      computation = .ok (value, state) →
        initial.nextOccurrence ≤ nextOccurrence state)
    (success : computation = .ok result) :
    initial.nextOccurrence ≤ nextOccurrence result.2 := by
  rcases result with ⟨value, state⟩
  exact invariant value state success

private theorem pair_eq_nextOccurrence {alpha : Type}
    {result : alpha × State} {initial : State}
    (invariant : ∀ value state, result = (value, state) →
      initial.nextOccurrence ≤ state.nextOccurrence) :
    initial.nextOccurrence ≤ result.2.nextOccurrence := by
  exact invariant result.1 result.2 (Prod.eta result)

private theorem triple_eq_nextOccurrence {alpha beta : Type}
    {result : alpha × beta × State} {initial : State}
    (invariant : ∀ first second state,
      result = (first, second, state) →
        initial.nextOccurrence ≤ state.nextOccurrence) :
    initial.nextOccurrence ≤ result.2.2.nextOccurrence := by
  rcases result with ⟨first, second, state⟩
  exact invariant first second state rfl

set_option maxHeartbeats 800000 in
private theorem inference_preserves_nextOccurrence :
    (∀ fuel context expression expected state,
      PreservesNextOccurrence Prod.snd state
        (inferExprFuel fuel context expression expected state)) ∧
    (∀ fuel context source id instantiation arguments expected state,
      PreservesNextOccurrence Prod.snd state
        (inferConstructorApplicationFuel fuel context source id instantiation
          arguments expected state)) ∧
    (∀ fuel context sources expected state,
      PreservesNextOccurrence Prod.snd state
        (inferConstructorArgumentsFuel fuel context sources expected state)) ∧
    (∀ fuel context statements expectedReturn state,
      PreservesNextOccurrence BlockResult.state state
        (inferStatementsFuel fuel context statements expectedReturn state)) ∧
    (∀ fuel context statement expectedReturn state,
      PreservesNextOccurrence StatementResult.state state
        (inferStatementFuel fuel context statement expectedReturn state)) ∧
    (∀ fuel context items state,
      PreservesNextOccurrence InferredForItems.state state
        (inferForItemsFuel fuel context items state)) ∧
    (∀ fuel context item state,
      PreservesNextOccurrence Prod.snd state
        (inferForItemFuel fuel context item state)) ∧
    (∀ fuel context target state,
      PreservesNextOccurrence Prod.snd state
        (inferPlaceFuel fuel context target state)) ∧
    (∀ fuel context target operator value state,
      PreservesNextOccurrence (fun result => result.2.2) state
        (inferAssignedValueFuel fuel context target operator value state)) ∧
    (∀ fuel context expressions state,
      PreservesNextOccurrence Prod.snd state
        (inferExprsFuel fuel context expressions state)) ∧
    (∀ fuel context scrutineeType expectedReturn outerScope cases state,
      PreservesNextOccurrence MatchCasesResult.state state
        (inferMatchCasesFuel fuel context scrutineeType expectedReturn outerScope
          cases state)) := by
  apply inferExprFuel.mutual_induct
    (motive1 := fun fuel context expression expected state =>
      PreservesNextOccurrence Prod.snd state
        (inferExprFuel fuel context expression expected state))
    (motive2 := fun fuel context source id instantiation arguments expected
        state =>
      PreservesNextOccurrence Prod.snd state
        (inferConstructorApplicationFuel fuel context source id instantiation
          arguments expected state))
    (motive3 := fun fuel context sources expected state =>
      PreservesNextOccurrence Prod.snd state
        (inferConstructorArgumentsFuel fuel context sources expected state))
    (motive4 := fun fuel context statements expectedReturn state =>
      PreservesNextOccurrence BlockResult.state state
        (inferStatementsFuel fuel context statements expectedReturn state))
    (motive5 := fun fuel context statement expectedReturn state =>
      PreservesNextOccurrence StatementResult.state state
        (inferStatementFuel fuel context statement expectedReturn state))
    (motive6 := fun fuel context items state =>
      PreservesNextOccurrence InferredForItems.state state
        (inferForItemsFuel fuel context items state))
    (motive7 := fun fuel context item state =>
      PreservesNextOccurrence Prod.snd state
        (inferForItemFuel fuel context item state))
    (motive8 := fun fuel context target state =>
      PreservesNextOccurrence Prod.snd state
        (inferPlaceFuel fuel context target state))
    (motive9 := fun fuel context target operator value state =>
      PreservesNextOccurrence (fun result => result.2.2) state
        (inferAssignedValueFuel fuel context target operator value state))
    (motive10 := fun fuel context expressions state =>
      PreservesNextOccurrence Prod.snd state
        (inferExprsFuel fuel context expressions state))
    (motive11 := fun fuel context scrutineeType expectedReturn outerScope
        cases state =>
      PreservesNextOccurrence MatchCasesResult.state state
        (inferMatchCasesFuel fuel context scrutineeType expectedReturn outerScope
          cases state))
  case case15 =>
    intros context expression expected state fuel calleeId stateAfterId
      allocationEq keyword parameters returnType body expressionEq bodyInduction
    unfold PreservesNextOccurrence at *
    intro result success
    unfold inferExprFuel at success
    simp_all [bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals try rcases v with ⟨v0a, v0b⟩
    all_goals try rcases v_1 with ⟨v1a, v1b⟩
    all_goals try rcases v_2 with ⟨v2a, v2b⟩
    all_goals try rcases v_3 with ⟨v3a, v3b⟩
    all_goals try rcases v_4 with ⟨v4a, v4b⟩
    all_goals try subst_vars
    all_goals try have bodyNext := bodyInduction _ _ _ (by assumption)
    all_goals try have allocationNext :=
      allocateExpressionId_success_nextOccurrence (by assumption)
    all_goals try have lambdaNext :=
      bindLambdaParameters_occurrenceState_eq (by assumption)
    all_goals try have unifiedNext := unify_occurrenceState_eq (by assumption)
    all_goals try have recordNext :=
      recordExpressionWithExpected_success_nextOccurrence (by assumption)
    all_goals simp_all only [except_pure_eq_ok]
    all_goals simp only [State.restoreLexicalScope]
    all_goals rw [unifiedNext.2]
    all_goals apply Nat.le_trans ?_ bodyNext
    all_goals grind [State.fresh, unify_occurrenceState_eq,
      unify_success_nextOccurrence,
      bindLambdaParameters_occurrenceState_eq]
  case case67 =>
    unfold PreservesNextOccurrence at *
    intros
    simp_all only [inferPlaceFuel]
  case case70 =>
    intros fuel context target operator value state placeInduction
      valueInduction
    unfold PreservesNextOccurrence at *
    intro result success
    unfold inferAssignedValueFuel at success
    simp_all [bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals try have placeNext :=
      pair_except_nextOccurrence placeInduction (by assumption)
    all_goals try have valueNext :=
      pair_except_nextOccurrence (valueInduction _ _) (by assumption)
    all_goals try have unifiedNext :=
      unify_occurrenceState_eq (by assumption)
    all_goals simp_all [Prod.eta]
    all_goals grind [unify_success_nextOccurrence]
  all_goals
    intros
    unfold PreservesNextOccurrence at *
    intro result success
    first
      | unfold inferExprFuel at success
      | unfold inferConstructorApplicationFuel at success
      | unfold inferConstructorArgumentsFuel at success
      | unfold inferStatementsFuel at success
      | unfold inferStatementFuel at success
      | unfold inferForItemsFuel at success
      | unfold inferForItemFuel at success
      | unfold inferPlaceFuel at success
      | unfold inferAssignedValueFuel at success
      | unfold inferExprsFuel at success
      | unfold inferMatchCasesFuel at success
    simp_all [bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals try rcases v with ⟨v0a, v0b⟩
    all_goals try rcases v_1 with ⟨v1a, v1b⟩
    all_goals try rcases v_2 with ⟨v2a, v2b⟩
    all_goals try rcases v_3 with ⟨v3a, v3b⟩
    all_goals try rcases v_4 with ⟨v4a, v4b⟩
    all_goals try subst_vars
    all_goals first
      | specialize ih1 _ _ _ _ (by assumption)
      | specialize ih1 _ _ _ (by assumption)
      | specialize ih1 _ _ (by assumption)
      | skip
    all_goals first
      | specialize ih2 _ _ _ _ (by assumption)
      | specialize ih2 _ _ _ (by assumption)
      | specialize ih2 _ _ (by assumption)
      | skip
    all_goals first
      | specialize ih3 _ _ _ _ (by assumption)
      | specialize ih3 _ _ _ (by assumption)
      | specialize ih3 _ _ (by assumption)
      | skip
    all_goals try have unifiedState :=
      unify_occurrenceState_eq (by assumption)
    all_goals try have recordState :=
      recordExpressionWithExpected_success_nextOccurrence (by assumption)
    all_goals try have lambdaState :=
      bindLambdaParameters_occurrenceState_eq (by assumption)
    all_goals try have patternState :=
      inferMatchPatternFuel_occurrenceState_eq (by assumption)
    all_goals try have unaryState :=
      inferUnaryOperator_occurrenceState_eq (by assumption)
    all_goals try have binaryState :=
      inferBinaryOperator_occurrenceState_eq (by assumption)
    all_goals try have selectionState :=
      selectFunctionCandidateFrom_occurrenceState_eq (by assumption)
    all_goals try have expectedState :=
      withExpected_occurrenceState_eq (by assumption)
    all_goals try have applicationState :=
      applyFunctionType_occurrenceState_eq (by assumption)
    all_goals try have builtinState :=
      recordBuiltinFunctionCall_success_nextOccurrence (by assumption)
    all_goals first
      | have ih1Next := pair_eq_nextOccurrence ih1
      | have ih1Next := triple_eq_nextOccurrence ih1
      | skip
    all_goals first
      | have ih2Next := pair_eq_nextOccurrence ih2
      | have ih2Next := triple_eq_nextOccurrence ih2
      | skip
    all_goals first
      | have ih3Next := pair_eq_nextOccurrence ih3
      | have ih3Next := triple_eq_nextOccurrence ih3
      | skip
    all_goals try simp_all
    all_goals try simp_all [State.fresh, State.addRequirementWithId,
      State.addRequirementsWithIds, State.allocateBinder,
      State.allocateHiddenLocal, State.restoreLexicalScope, State.recordNode,
      bind, Except.bind]
    all_goals try simp_all only [State.allocateExpressionId_nextOccurrence,
      State.allocateStatementId_nextOccurrence]
    all_goals try simp_all [recordExpression]
    all_goals try grind [allocateExpressionId_success_nextOccurrence,
      allocateStatementId_success_nextOccurrence,
      unify_success_nextOccurrence,
      freshDataConstructorInstantiation_nextOccurrence]

/-- Every successful expression traversal monotonically advances its input
occurrence cutoff. -/
theorem inferExprFuel_nextOccurrence_le
    {fuel : Nat} {context : Context} {expression : Syntax.Expr}
    {expected : Option Ty} {state : State}
    {result : InferredExpression × State}
    (success : inferExprFuel fuel context expression expected state =
      .ok result) :
    state.nextOccurrence ≤ result.2.nextOccurrence :=
  inference_preserves_nextOccurrence.1 fuel context expression expected state
    result success

/-- Constructor-application inference monotonically advances occurrences. -/
theorem inferConstructorApplicationFuel_nextOccurrence_le
    {fuel : Nat} {context : Context} {source : Syntax.Expr}
    {id : ExpressionId} {instantiation : DataConstructorInstantiation}
    {arguments : List Syntax.Expr} {expected : Option Ty} {state : State}
    {result : InferredExpression × State}
    (success : inferConstructorApplicationFuel fuel context source id
      instantiation arguments expected state = .ok result) :
    state.nextOccurrence ≤ result.2.nextOccurrence :=
  inference_preserves_nextOccurrence.2.1 fuel context source id instantiation
    arguments expected state result success

/-- Constructor-argument inference monotonically advances occurrences. -/
theorem inferConstructorArgumentsFuel_nextOccurrence_le
    {fuel : Nat} {context : Context} {sources : List Syntax.Expr}
    {expected : List Ty} {state : State}
    {result : List InferredExpression × State}
    (success : inferConstructorArgumentsFuel fuel context sources expected
      state = .ok result) :
    state.nextOccurrence ≤ result.2.nextOccurrence :=
  inference_preserves_nextOccurrence.2.2.1 fuel context sources expected state
    result success

/-- Statement-list inference monotonically advances occurrences. -/
theorem inferStatementsFuel_nextOccurrence_le
    {fuel : Nat} {context : Context} {statements : List Syntax.Statement}
    {expectedReturn : Ty} {state : State} {result : BlockResult}
    (success : inferStatementsFuel fuel context statements expectedReturn state =
      .ok result) :
    state.nextOccurrence ≤ result.state.nextOccurrence :=
  inference_preserves_nextOccurrence.2.2.2.1 fuel context statements
    expectedReturn state result success

/-- Statement inference monotonically advances occurrences. -/
theorem inferStatementFuel_nextOccurrence_le
    {fuel : Nat} {context : Context} {statement : Syntax.Statement}
    {expectedReturn : Ty} {state : State} {result : StatementResult}
    (success : inferStatementFuel fuel context statement expectedReturn state =
      .ok result) :
    state.nextOccurrence ≤ result.state.nextOccurrence :=
  inference_preserves_nextOccurrence.2.2.2.2.1 fuel context statement
    expectedReturn state result success

/-- For-item list inference monotonically advances occurrences. -/
theorem inferForItemsFuel_nextOccurrence_le
    {fuel : Nat} {context : Context} {items : List Syntax.ForItem}
    {state : State} {result : InferredForItems}
    (success : inferForItemsFuel fuel context items state = .ok result) :
    state.nextOccurrence ≤ result.state.nextOccurrence :=
  inference_preserves_nextOccurrence.2.2.2.2.2.1 fuel context items state
    result success

/-- One for-item traversal monotonically advances occurrences. -/
theorem inferForItemFuel_nextOccurrence_le
    {fuel : Nat} {context : Context} {item : Syntax.ForItem}
    {state : State} {result : ForItemForm × State}
    (success : inferForItemFuel fuel context item state = .ok result) :
    state.nextOccurrence ≤ result.2.nextOccurrence :=
  inference_preserves_nextOccurrence.2.2.2.2.2.2.1 fuel context item state
    result success

/-- Place inference monotonically advances occurrences. -/
theorem inferPlaceFuel_nextOccurrence_le
    {fuel : Nat} {context : Context} {target : Syntax.Expr}
    {state : State} {result : PlaceResolution × State}
    (success : inferPlaceFuel fuel context target state = .ok result) :
    state.nextOccurrence ≤ result.2.nextOccurrence :=
  inference_preserves_nextOccurrence.2.2.2.2.2.2.2.1 fuel context target
    state result success

/-- Assigned-value inference monotonically advances occurrences. -/
theorem inferAssignedValueFuel_nextOccurrence_le
    {fuel : Nat} {context : Context} {target : Syntax.Expr}
    {operator : Syntax.ValueAssignOp} {value : Syntax.Expr} {state : State}
    {result : AssignmentResolution × InferredExpression × State}
    (success : inferAssignedValueFuel fuel context target operator value state =
      .ok result) :
    state.nextOccurrence ≤ result.2.2.nextOccurrence :=
  inference_preserves_nextOccurrence.2.2.2.2.2.2.2.2.1 fuel context target
    operator value state result success

/-- Expression-list inference monotonically advances occurrences. -/
theorem inferExprsFuel_nextOccurrence_le
    {fuel : Nat} {context : Context} {expressions : List Syntax.Expr}
    {state : State} {result : List InferredExpression × State}
    (success : inferExprsFuel fuel context expressions state = .ok result) :
    state.nextOccurrence ≤ result.2.nextOccurrence :=
  inference_preserves_nextOccurrence.2.2.2.2.2.2.2.2.2.1 fuel context
    expressions state result success

/-- Every root returned by expression-list inference was allocated at or after
the input state's occurrence cutoff. -/
theorem inferExprsFuel_success_ids_fresh
    {fuel : Nat} {context : Context} {expressions : List Syntax.Expr}
    {state : State} {result : List InferredExpression × State}
    (success : inferExprsFuel fuel context expressions state = .ok result) :
    ∀ expression ∈ result.1,
      state.nextOccurrence ≤ expression.id.occurrence.index := by
  induction fuel generalizing expressions state result with
  | zero =>
      simp [inferExprsFuel] at success
  | succ fuel induction =>
      cases expressions with
      | nil =>
          simp only [inferExprsFuel] at success
          injection success with resultEq
          subst result
          simp
      | cons expression expressions =>
          unfold inferExprsFuel at success
          simp_all [bind, Except.bind]
          repeat' first | split at success
          all_goals try cases success
          all_goals try rcases v with ⟨v0a, v0b⟩
          all_goals try rcases v_1 with ⟨v1a, v1b⟩
          all_goals try subst_vars
          all_goals try have headIndex :=
            inferExprFuel_success_id_index (by assumption)
          all_goals try have headNext :=
            inferExprFuel_nextOccurrence_le (by assumption)
          all_goals try have tailFresh := induction (by assumption)
          all_goals intro current member
          all_goals simp_all only [List.mem_cons]
          all_goals grind

/-- Match-case inference monotonically advances occurrences. -/
theorem inferMatchCasesFuel_nextOccurrence_le
    {fuel : Nat} {context : Context} {scrutineeType expectedReturn : Ty}
    {outerScope : LexicalScope} {cases : List Syntax.MatchCase}
    {state : State} {result : MatchCasesResult}
    (success : inferMatchCasesFuel fuel context scrutineeType expectedReturn
      outerScope cases state = .ok result) :
    state.nextOccurrence ≤ result.state.nextOccurrence :=
  inference_preserves_nextOccurrence.2.2.2.2.2.2.2.2.2.2 fuel context
    scrutineeType expectedReturn outerScope cases state result success

/-! ## Anchored node-prefix preservation

Selected-call fitting is the only traversal step that may rewrite already
recorded expression payloads.  The following adapters package the freshness
side condition which protects an older node prefix in the form needed by the
eventual mutual traversal proof. -/

/-- Explicit overload selection followed by selected-call recording retains
an older anchored prefix when all caller arguments are fresh at its cutoff. -/
theorem selectFunctionCandidateFrom_recordSelectedCall_preserves_nodesPrefix_of_fresh
    {context : Context} {name : String}
    {candidates : List ProgramFunctionSignature}
    {arguments : List InferredExpression}
    {integerLiteralOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected : Option Ty} {state : State}
    {attempt : CandidateAttemptResult} {source callee : Syntax.Expr}
    {baseNodes : List Node} {cutoff : Nat}
    (selection : selectFunctionCandidateFrom context name candidates arguments
      integerLiteralOrigins call expected state = .ok attempt)
    (nodesPrefix : baseNodes <+: state.nodes)
    (baseBelow :
      ∀ node ∈ baseNodes, node.occurrenceId.index < cutoff)
    (argumentsFresh : ∀ argument ∈ arguments,
      cutoff ≤ argument.id.occurrence.index) :
    baseNodes <+:
      (recordSelectedCall source callee name arguments attempt).2.nodes := by
  have attemptPrefix : baseNodes <+: attempt.state.nodes := by
    rw [(selectFunctionCandidateFrom_occurrenceState_eq selection).1]
    exact nodesPrefix
  exact recordSelectedCall_preserves_nodesPrefix_of_fresh source callee name
    arguments attempt baseNodes cutoff attemptPrefix baseBelow
    (selectFunctionCandidateFrom_argumentCoercions_fresh selection
      argumentsFresh)

/-- Expression-list inference supplies exactly the root freshness needed by
the selected-call prefix adapter.  The caller only has to thread the prefix
through the argument traversal itself. -/
theorem inferExprsFuel_selectFunctionCandidateFrom_recordSelectedCall_preserves_nodesPrefix
    {fuel : Nat} {context : Context} {sources : List Syntax.Expr}
    {initial argumentState : State} {arguments : List InferredExpression}
    {name : String} {candidates : List ProgramFunctionSignature}
    {integerLiteralOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected : Option Ty}
    {attempt : CandidateAttemptResult} {source callee : Syntax.Expr}
    {baseNodes : List Node} {cutoff : Nat}
    (argumentsSuccess : inferExprsFuel fuel context sources initial =
      .ok (arguments, argumentState))
    (selection : selectFunctionCandidateFrom context name candidates arguments
      integerLiteralOrigins call expected argumentState = .ok attempt)
    (argumentPrefix : baseNodes <+: argumentState.nodes)
    (baseBelow :
      ∀ node ∈ baseNodes, node.occurrenceId.index < cutoff)
    (cutoffLe : cutoff ≤ initial.nextOccurrence) :
    baseNodes <+:
      (recordSelectedCall source callee name arguments attempt).2.nodes := by
  apply
    selectFunctionCandidateFrom_recordSelectedCall_preserves_nodesPrefix_of_fresh
      selection argumentPrefix baseBelow
  intro argument member
  exact Nat.le_trans cutoffLe
    (inferExprsFuel_success_ids_fresh argumentsSuccess argument member)


end Solcore.Frontend.SourceInference.Detail
