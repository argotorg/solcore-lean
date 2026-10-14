import Solcore.Frontend.SourceInference.RequirementProperties
import Solcore.Frontend.SourceInference.ExpressionProperties

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
namespace Solcore.Frontend.SourceInference.Detail.SelectedMetadata
open TypeSystem

private theorem pureState_eq
    {state next : State}
    (success : (pure state : Except Error State) = .ok next) :
    state = next := by
  change Except.ok state = Except.ok next at success
  exact Except.ok.inj success

private theorem addRequirementsWithIds_integerPatterns_eq
    (state : State) (predicates : List ProgramPredicate) :
    (state.addRequirementsWithIds predicates).2.integerPatterns =
      state.integerPatterns := by
  induction predicates generalizing state with
  | nil => rfl
  | cons predicate predicates induction =>
      simp only [State.addRequirementsWithIds]
      exact (induction (state.addRequirementWithId predicate).2).trans rfl

private theorem commitCoercionPlan_integerPatterns_eq
    (state : State) (plan : List PlannedCoercionStep) :
    (commitCoercionPlan state plan).2.integerPatterns =
      state.integerPatterns := by
  induction plan generalizing state with
  | nil => rfl
  | cons step plan induction =>
      simp only [commitCoercionPlan]
      exact (induction
        ((state.addRequirementWithId step.predicate).2
          |>.addRequirementsWithIds step.methodPredicates).2).trans
        (addRequirementsWithIds_integerPatterns_eq
          (state.addRequirementWithId step.predicate).2
          step.methodPredicates |>.trans rfl)

theorem withExpected_integerPatterns_eq
    {context : Context} {state : State} {actual : InferredExpression}
    {expected : Option Ty} {result : ExpectationResult}
    (success : withExpected context state actual expected = .ok result) :
    result.state.integerPatterns = state.integerPatterns := by
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
                      exact commitCoercionPlan_integerPatterns_eq state plan

private theorem candidateWithExpected_integerPatterns_eq
    {context : Context} {state : State} {actual : InferredExpression}
    {expected : Option Ty} {result : ExpectationResult}
    (success : candidateWithExpected context state actual expected =
      .ok (some result)) :
    result.state.integerPatterns = state.integerPatterns := by
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
      exact withExpected_integerPatterns_eq fittedResult

private theorem fitArguments_integerPatterns_eq
    {context : Context} {state : State}
    {arguments : List InferredExpression} {parameters : List Ty}
    {result : ArgumentFitResult}
    (success : fitArguments context state arguments parameters =
      .ok (some result)) :
    result.state.integerPatterns = state.integerPatterns := by
  induction arguments generalizing parameters state result with
  | nil =>
      cases parameters <;> simp [fitArguments] at success
      subst result
      rfl
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
                          have resultEq : _ = result := Option.some.inj resultEq
                          subst result
                          exact (induction (result := tail) tailResult).trans
                            (candidateWithExpected_integerPatterns_eq
                              fittedResult)

theorem tryFunctionCandidate_integerPatterns_eq
    {context : Context} {arguments : List InferredExpression}
    {integerLiteralOrigins : List IntegerLiteralOrigin} {call : ExpressionId}
    {expected : Option Ty} {state : State}
    {signature : ProgramFunctionSignature} {result : CandidateAttemptResult}
    (success : tryFunctionCandidate context arguments integerLiteralOrigins
      call expected state signature = .ok (some result)) :
    result.state.integerPatterns = state.integerPatterns := by
  unfold tryFunctionCandidate at success
  simp_all [bind, Except.bind]
  repeat' first | split at success
  all_goals try cases success
  all_goals try have fittedArgumentsEq :=
    fitArguments_integerPatterns_eq (by assumption)
  all_goals try have fittedResultEq :=
    candidateWithExpected_integerPatterns_eq (by assumption)
  all_goals
    exact (addRequirementsWithIds_integerPatterns_eq _ _).trans
      (fittedResultEq.trans fittedArgumentsEq)

theorem inferUnaryOperator_integerPatterns_eq
    {context : Context} {operator : Syntax.UnaryOp} {operandType : Ty}
    {expected : Option Ty} {integerLiterals : List IntegerLiteralOrigin}
    {state : State} {result : OperatorInferenceResult}
    (success : inferUnaryOperator context operator operandType expected
      integerLiterals state = .ok result) :
    result.state.integerPatterns = state.integerPatterns := by
  unfold inferUnaryOperator at success
  simp_all [bind, Except.bind]
  repeat' first | split at success
  all_goals try cases success
  all_goals try simp_all
  all_goals try
    have pureEq := pureState_eq (by assumption)
    subst_vars
  all_goals try have unifiedEq :=
    (unify_integerPatternMetadata_eq (by assumption)).1
  all_goals try have requirementsEq :=
    addRequirementsWithIds_integerPatterns_eq _ _
  all_goals grind [unify_integerPatternMetadata_eq,
    addRequirementsWithIds_integerPatterns_eq]

theorem inferBinaryOperator_integerPatterns_eq
    {context : Context} {operator : Syntax.BinaryOp} {left right : Ty}
    {expected : Option Ty} {integerLiterals : List IntegerLiteralOrigin}
    {state : State} {result : OperatorInferenceResult}
    (success : inferBinaryOperator context operator left right expected
      integerLiterals state = .ok result) :
    result.state.integerPatterns = state.integerPatterns := by
  unfold inferBinaryOperator at success
  simp_all [bind, Except.bind]
  repeat' first | split at success
  all_goals try cases success
  all_goals try simp_all
  all_goals try
    have pureEq := pureState_eq (by assumption)
    subst_vars
  all_goals try have unifiedEq :=
    (unify_integerPatternMetadata_eq (by assumption)).1
  all_goals try have requirementsEq :=
    addRequirementsWithIds_integerPatterns_eq _ _
  all_goals grind [unify_integerPatternMetadata_eq,
    addRequirementsWithIds_integerPatterns_eq]

private theorem attachExpressionCoercions_integerPatterns_eq
    (state : State) (entries : List ExpressionCoercions) :
    (attachExpressionCoercions state entries).integerPatterns =
      state.integerPatterns := by
  unfold attachExpressionCoercions
  induction entries generalizing state with
  | nil => rfl
  | cons entry entries induction =>
      simp only [List.foldl_cons]
      exact (induction
        (state.modifyExpressionNode entry.expression fun node => {
          node with
          type := entry.coercions.foldl (fun _ step => step.target) node.type
          requirements :=
            node.requirements ++ coercionRequirements entry.coercions
          coercions := node.coercions ++ entry.coercions
        })).trans rfl

private theorem recordExpression_integerPatterns_eq
    (source : Syntax.Expr) (expression : InferredExpression)
    (form : ExpressionForm) (requirements : List RequirementId)
    (coercions : List CoercionStep) (state : State)
    {localSchemeInstantiationStart : Option Nat} :
    (recordExpression source expression form requirements coercions state
      localSchemeInstantiationStart).2.integerPatterns =
      state.integerPatterns := by
  rfl

@[simp] private theorem allocateExpressionId_integerPatterns_eq (state : State) :
    state.allocateExpressionId.2.integerPatterns = state.integerPatterns := by
  rfl

theorem recordSelectedCallResult_integerPatterns_eq
    (source callee : Syntax.Expr) (name : String)
    (arguments : List InferredExpression) (attempt : CandidateAttemptResult)
    (result : InferredExpression) (trailingCoercions : List CoercionStep)
    (state : State) :
    (recordSelectedCallResult source callee name arguments attempt result
      trailingCoercions state).2.integerPatterns = state.integerPatterns := by
  unfold recordSelectedCallResult
  rw [recordExpression_integerPatterns_eq,
    recordExpression_integerPatterns_eq]
  exact (attachExpressionCoercions_integerPatterns_eq state
    attempt.argumentCoercions)

private theorem unify_integerLiterals_eq
    {before after : State} {left right : Ty}
    (success : unify before left right = .ok after) :
    after.integerLiterals = before.integerLiterals := by
  unfold unify at success
  cases unified : before.inference.unify left right <;>
    simp [liftUnification, unified, bind, Except.bind] at success
  cases success
  rfl

private theorem addRequirementsWithIds_integerLiterals_eq
    (state : State) (predicates : List ProgramPredicate) :
    (state.addRequirementsWithIds predicates).2.integerLiterals =
      state.integerLiterals := by
  induction predicates generalizing state with
  | nil => rfl
  | cons predicate predicates induction =>
      simp only [State.addRequirementsWithIds]
      exact (induction (state.addRequirementWithId predicate).2).trans rfl

private theorem commitCoercionPlan_integerLiterals_eq
    (state : State) (plan : List PlannedCoercionStep) :
    (commitCoercionPlan state plan).2.integerLiterals =
      state.integerLiterals := by
  induction plan generalizing state with
  | nil => rfl
  | cons step plan induction =>
      simp only [commitCoercionPlan]
      exact (induction
        ((state.addRequirementWithId step.predicate).2
          |>.addRequirementsWithIds step.methodPredicates).2).trans
        (addRequirementsWithIds_integerLiterals_eq
          (state.addRequirementWithId step.predicate).2
          step.methodPredicates |>.trans rfl)

theorem withExpected_integerLiterals_eq
    {context : Context} {state : State} {actual : InferredExpression}
    {expected : Option Ty} {result : ExpectationResult}
    (success : withExpected context state actual expected = .ok result) :
    result.state.integerLiterals = state.integerLiterals := by
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
                      exact commitCoercionPlan_integerLiterals_eq state plan

private theorem candidateWithExpected_integerLiterals_eq
    {context : Context} {state : State} {actual : InferredExpression}
    {expected : Option Ty} {result : ExpectationResult}
    (success : candidateWithExpected context state actual expected =
      .ok (some result)) :
    result.state.integerLiterals = state.integerLiterals := by
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
      exact withExpected_integerLiterals_eq fittedResult

private theorem fitArguments_integerLiterals_eq
    {context : Context} {state : State}
    {arguments : List InferredExpression} {parameters : List Ty}
    {result : ArgumentFitResult}
    (success : fitArguments context state arguments parameters =
      .ok (some result)) :
    result.state.integerLiterals = state.integerLiterals := by
  induction arguments generalizing parameters state result with
  | nil =>
      cases parameters <;> simp [fitArguments] at success
      subst result
      rfl
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
                          have resultEq : _ = result := Option.some.inj resultEq
                          subst result
                          exact (induction (result := tail) tailResult).trans
                            (candidateWithExpected_integerLiterals_eq
                              fittedResult)

theorem tryFunctionCandidate_integerLiterals_eq
    {context : Context} {arguments : List InferredExpression}
    {integerLiteralOrigins : List IntegerLiteralOrigin} {call : ExpressionId}
    {expected : Option Ty} {state : State}
    {signature : ProgramFunctionSignature} {result : CandidateAttemptResult}
    (success : tryFunctionCandidate context arguments integerLiteralOrigins
      call expected state signature = .ok (some result)) :
    result.state.integerLiterals = state.integerLiterals := by
  unfold tryFunctionCandidate at success
  simp_all [bind, Except.bind]
  repeat' first | split at success
  all_goals try cases success
  all_goals try have fittedArgumentsEq :=
    fitArguments_integerLiterals_eq (by assumption)
  all_goals try have fittedResultEq :=
    candidateWithExpected_integerLiterals_eq (by assumption)
  all_goals
    exact (addRequirementsWithIds_integerLiterals_eq _ _).trans
      (fittedResultEq.trans fittedArgumentsEq)

theorem inferUnaryOperator_integerLiterals_eq
    {context : Context} {operator : Syntax.UnaryOp} {operandType : Ty}
    {expected : Option Ty} {integerLiterals : List IntegerLiteralOrigin}
    {state : State} {result : OperatorInferenceResult}
    (success : inferUnaryOperator context operator operandType expected
      integerLiterals state = .ok result) :
    result.state.integerLiterals = state.integerLiterals := by
  unfold inferUnaryOperator at success
  simp_all [bind, Except.bind]
  repeat' first | split at success
  all_goals try cases success
  all_goals try simp_all
  all_goals try
    have pureEq := pureState_eq (by assumption)
    subst_vars
  all_goals try have unifiedEq :=
    unify_integerLiterals_eq (by assumption)
  all_goals try have requirementsEq :=
    addRequirementsWithIds_integerLiterals_eq _ _
  all_goals grind [unify_integerLiterals_eq,
    addRequirementsWithIds_integerLiterals_eq]

theorem inferBinaryOperator_integerLiterals_eq
    {context : Context} {operator : Syntax.BinaryOp} {left right : Ty}
    {expected : Option Ty} {integerLiterals : List IntegerLiteralOrigin}
    {state : State} {result : OperatorInferenceResult}
    (success : inferBinaryOperator context operator left right expected
      integerLiterals state = .ok result) :
    result.state.integerLiterals = state.integerLiterals := by
  unfold inferBinaryOperator at success
  simp_all [bind, Except.bind]
  repeat' first | split at success
  all_goals try cases success
  all_goals try simp_all
  all_goals try
    have pureEq := pureState_eq (by assumption)
    subst_vars
  all_goals try have unifiedEq :=
    unify_integerLiterals_eq (by assumption)
  all_goals try have requirementsEq :=
    addRequirementsWithIds_integerLiterals_eq _ _
  all_goals grind [unify_integerLiterals_eq,
    addRequirementsWithIds_integerLiterals_eq]

private theorem attachExpressionCoercions_integerLiterals_eq
    (state : State) (entries : List ExpressionCoercions) :
    (attachExpressionCoercions state entries).integerLiterals =
      state.integerLiterals := by
  unfold attachExpressionCoercions
  induction entries generalizing state with
  | nil => rfl
  | cons entry entries induction =>
      simp only [List.foldl_cons]
      exact (induction
        (state.modifyExpressionNode entry.expression fun node => {
          node with
          type := entry.coercions.foldl (fun _ step => step.target) node.type
          requirements :=
            node.requirements ++ coercionRequirements entry.coercions
          coercions := node.coercions ++ entry.coercions
        })).trans rfl

private theorem recordExpression_integerLiterals_eq
    (source : Syntax.Expr) (expression : InferredExpression)
    (form : ExpressionForm) (requirements : List RequirementId)
    (coercions : List CoercionStep) (state : State)
    {localSchemeInstantiationStart : Option Nat} :
    (recordExpression source expression form requirements coercions state
      localSchemeInstantiationStart).2.integerLiterals =
      state.integerLiterals := by
  rfl

@[simp] private theorem allocateExpressionId_integerLiterals_eq (state : State) :
    state.allocateExpressionId.2.integerLiterals = state.integerLiterals := by
  rfl

/-- Expected-type fitting and expression recording preserve the exact
integer-literal origin ledger supplied by the caller. -/
theorem recordSelectedCallResult_integerLiterals_eq
    (source callee : Syntax.Expr) (name : String)
    (arguments : List InferredExpression) (attempt : CandidateAttemptResult)
    (result : InferredExpression) (trailingCoercions : List CoercionStep)
    (state : State) :
    (recordSelectedCallResult source callee name arguments attempt result
      trailingCoercions state).2.integerLiterals = state.integerLiterals := by
  unfold recordSelectedCallResult
  rw [recordExpression_integerLiterals_eq,
    recordExpression_integerLiterals_eq]
  exact (attachExpressionCoercions_integerLiterals_eq state
    attempt.argumentCoercions)

@[simp] private theorem except_pure_eq_ok {ε α : Type}
    (value result : α) :
    ((pure value : Except ε α) = .ok result) ↔ value = result := by
  change (Except.ok value = Except.ok result) ↔ value = result
  simp

@[simp] private theorem commitCoercionPlan_state_header
    (state : State) (plan : List PlannedCoercionStep) :
    (commitCoercionPlan state plan).2.header = state.header := by
  induction plan generalizing state with
  | nil => rfl
  | cons step rest induction =>
      simp only [commitCoercionPlan]
      rw [induction]
      simp

theorem withExpected_state_header
    {context : Context} {state : State} {actual : InferredExpression}
    {expected : Option Ty} {result : ExpectationResult}
    (success : withExpected context state actual expected = .ok result) :
    result.state.header = state.header := by
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
          | exhausted => simp [withExpected, unification] at success
          | mismatch left right =>
              simp only [withExpected, unification] at success
              cases planResult : coercionPlan? context state
                  (state.resolve actual.type) (state.resolve expected) with
              | error error => simp [planResult, bind, Except.bind] at success
              | ok plan? =>
                  cases plan? with
                  | none => simp [planResult, bind, Except.bind] at success
                  | some plan =>
                      simp only [planResult, bind, Except.bind] at success
                      change Except.ok _ = Except.ok result at success
                      injection success with resultEq
                      subst result
                      exact commitCoercionPlan_state_header state plan

@[simp] private theorem unify_preserves_owner
    {state next : State} {left right : Ty}
    (success : unify state left right = .ok next) :
    next.owner = state.owner := by
  exact congrArg (fun header : State.Header => header.owner)
    (unify_state_header success)

@[simp] private theorem unify_preserves_inputs
    {state next : State} {left right : Ty}
    (success : unify state left right = .ok next) :
    next.inputs = state.inputs := by
  exact congrArg (fun header : State.Header => header.inputs)
    (unify_state_header success)

/-- A successful contextual-constructor lookup supplies allocator-bounded
type arguments, so formation validation bounds every instantiated payload and
the constructor result at the input state's allocator. -/
theorem inferUnaryOperator_state_header
    {context : Context} {operator : Syntax.UnaryOp} {operandType : Ty}
    {expected : Option Ty} {integerLiterals : List IntegerLiteralOrigin}
    {state : State} {result : OperatorInferenceResult}
    (success : inferUnaryOperator context operator operandType expected
      integerLiterals state = .ok result) :
    result.state.header = state.header := by
  unfold inferUnaryOperator at success
  simp_all [bind, Except.bind]
  repeat' first | split at success
  all_goals try cases success
  all_goals try have headerEq := unify_state_header (by assumption)
  all_goals try simp_all
  all_goals simp_all [State.header, State.addRequirementsWithIds,
    State.addRequirementWithId]
  all_goals grind [unify_preserves_owner, unify_preserves_inputs]

theorem inferBinaryOperator_state_header
    {context : Context} {operator : Syntax.BinaryOp} {left right : Ty}
    {expected : Option Ty} {integerLiterals : List IntegerLiteralOrigin}
    {state : State} {result : OperatorInferenceResult}
    (success : inferBinaryOperator context operator left right expected
      integerLiterals state = .ok result) :
    result.state.header = state.header := by
  unfold inferBinaryOperator at success
  simp_all [bind, Except.bind]
  repeat' first | split at success
  all_goals try cases success
  all_goals try have headerEq := unify_state_header (by assumption)
  all_goals try simp_all
  all_goals simp_all [State.header]
  all_goals grind [unify_preserves_owner, unify_preserves_inputs]

private theorem candidateWithExpected_some_state_header
    {context : Context} {state : State} {actual : InferredExpression}
    {expected : Option Ty} {result : ExpectationResult}
    (success : candidateWithExpected context state actual expected =
      .ok (some result)) :
    result.state.header = state.header := by
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
      exact withExpected_state_header fittedResult

private theorem fitArguments_some_state_header
    {context : Context} {state : State}
    {arguments : List InferredExpression} {parameters : List Ty}
    {result : ArgumentFitResult}
    (success : fitArguments context state arguments parameters =
      .ok (some result)) :
    result.state.header = state.header := by
  induction arguments generalizing parameters state result with
  | nil =>
      cases parameters <;> simp [fitArguments] at success
      subst result
      rfl
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
              | none => simp [fittedResult, bind, Except.bind] at success
              | some fitted =>
                  simp only [fittedResult, bind, Except.bind] at success
                  cases tailResult : fitArguments context fitted.state arguments
                      parameters with
                  | error error =>
                      simp [tailResult] at success
                  | ok tail? =>
                      cases tail? with
                      | none => simp [tailResult] at success
                      | some tail =>
                          simp only [tailResult,
                            except_pure_eq_ok] at success
                          have resultEq : _ = result := Option.some.inj success
                          clear success
                          subst result
                          exact (induction tailResult).trans
                            (candidateWithExpected_some_state_header fittedResult)

theorem tryFunctionCandidate_some_state_header
    {context : Context} {arguments : List InferredExpression}
    {integerLiteralOrigins : List IntegerLiteralOrigin} {call : ExpressionId}
    {expected : Option Ty} {state : State}
    {signature : ProgramFunctionSignature} {result : CandidateAttemptResult}
    (success : tryFunctionCandidate context arguments integerLiteralOrigins
      call expected state signature = .ok (some result)) :
    result.state.header = state.header := by
  unfold tryFunctionCandidate at success
  simp_all [bind, Except.bind]
  repeat' first | split at success
  all_goals try cases success
  all_goals try have fitHeader :=
    fitArguments_some_state_header (by assumption)
  all_goals try have expectedHeader :=
    candidateWithExpected_some_state_header (by assumption)
  all_goals try simp_all
  all_goals simp_all [State.header]

end Solcore.Frontend.SourceInference.Detail.SelectedMetadata
