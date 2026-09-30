import Solcore.SourceSemantics.SourceInferenceStatementAssignmentSoundness

/-!
Stable local-binder allocation bounds for the actual statement traversal.
The semantic statement induction needs this bound after every sequential
head, independently of expression typing or finalization.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.SourceInferenceSoundness

open Frontend Frontend.SourceInference TypeSystem

/-- Any successful statement which retains its incoming visible binder stack
preserves that stack's allocation bound. -/
theorem inferStatementFuel_localBindersBelow_of_sameBinders
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {expectedReturn : Ty}
    {initial : State} {result : Detail.StatementResult}
    (below : initial.LocalBindersBelowNextLocal)
    (success : Detail.inferStatementFuel fuel inferenceContext statement
      expectedReturn initial = .ok result)
    (same : result.state.localBinders = initial.localBinders) :
    result.state.LocalBindersBelowNextLocal :=
  State.LocalBindersBelowNextLocal.transport same
    (Detail.inferStatementFuel_nextLocal_le success) below

private theorem inferStatementFuel_localBindersBelow_of_sameScope
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {expectedReturn : Ty}
    {initial : State} {result : Detail.StatementResult}
    (below : initial.LocalBindersBelowNextLocal)
    (success : Detail.inferStatementFuel fuel inferenceContext statement
      expectedReturn initial = .ok result)
    (same : result.state.lexicalScope = initial.lexicalScope) :
    result.state.LocalBindersBelowNextLocal :=
  inferStatementFuel_localBindersBelow_of_sameBinders below success
    (by simpa only [State.lexicalScope] using
      congrArg LexicalScope.binders same)

/-- A real `let` binder is allocated after an initializer state whose visible
binders are already bounded; recording the statement does not alter locals. -/
private theorem letBinding_recordNode_localBindersBelow
    {name : Syntax.Identifier} {initial : State}
    {locals : TypeSystem.Environment} {generalized : Detail.GeneralizedValue}
    {binding : TypedBinder × State} {node : StatementNode}
    (below : initial.LocalBindersBelowNextLocal)
    (allocated : (initial.withLocals locals).allocateBinder name.value
      generalized.scheme (some name.span) false generalized.requirements =
        binding) :
    (binding.2.recordNode (.statement node)).LocalBindersBelowNextLocal := by
  have withLocalsBelow :
      (initial.withLocals locals).LocalBindersBelowNextLocal :=
    State.withLocals_preserves_localBindersBelowNextLocal initial locals below
  have bindingBelow :=
    State.allocateBinder_preserves_localBindersBelowNextLocal
      (initial.withLocals locals) name.value generalized.scheme
      (some name.span) false generalized.requirements withLocalsBelow
  rw [allocated] at bindingBelow
  exact State.recordNode_preserves_localBindersBelowNextLocal
    binding.2 (.statement node) bindingBelow

/-- The uninitialized annotated declaration allocates exactly one visible
binder after the statement-ID step. -/
theorem inferStatementFuel_success_letAnnotatedUninitialized_localBindersBelow
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {name : Syntax.Identifier}
    {sourceType : Syntax.TypeExpr} {expectedReturn : Ty}
    {initial allocated : State} {id : StatementId}
    {result : Detail.StatementResult}
    (statementEq : statement.value =
      .letDecl name (some sourceType) none)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (below : initial.LocalBindersBelowNextLocal) :
    result.state.LocalBindersBelowNextLocal := by
  obtain ⟨_, locals, _, generalized, binding, _, _, _, _, bindingEq,
      resultEq, _⟩ :=
    inferStatementFuel_success_letAnnotatedUninitialized_facts statementEq
      allocationEq success
  have allocatedBelow : allocated.LocalBindersBelowNextLocal := by
    have preserved :=
      State.allocateStatementId_preserves_localBindersBelowNextLocal
        initial below
    simpa only [allocationEq] using preserved
  rw [resultEq]
  exact letBinding_recordNode_localBindersBelow allocatedBelow bindingEq

/-- Inferred-value declarations preserve the binder bound through the actual
initializer traversal before allocating their one visible binder. -/
theorem inferStatementFuel_success_letUnannotatedInitialized_localBindersBelow
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {name : Syntax.Identifier}
    {initializer : Syntax.Expr} {expectedReturn : Ty}
    {initial allocated : State} {id : StatementId}
    {result : Detail.StatementResult}
    (statementEq : statement.value =
      .letDecl name none (some initializer))
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (below : initial.LocalBindersBelowNextLocal) :
    result.state.LocalBindersBelowNextLocal := by
  obtain ⟨inferred, initializerState, locals, _, generalized, binding,
      initializerSuccess, _, _, _, bindingEq, resultEq, _⟩ :=
    inferStatementFuel_success_letUnannotatedInitialized_facts statementEq
      allocationEq success
  have allocatedBelow : allocated.LocalBindersBelowNextLocal := by
    have preserved :=
      State.allocateStatementId_preserves_localBindersBelowNextLocal
        initial below
    simpa only [allocationEq] using preserved
  have initializerBelow : initializerState.LocalBindersBelowNextLocal :=
    Detail.inferExprFuel_preserves_localBindersBelowNextLocal allocatedBelow
      initializerSuccess
  rw [resultEq]
  exact letBinding_recordNode_localBindersBelow initializerBelow bindingEq

/-- An annotated initialized declaration has the same allocation behavior:
source-type resolution does not mutate the state, and initializer inference
preserves the incoming visible binder stack. -/
theorem inferStatementFuel_success_letAnnotatedInitialized_localBindersBelow
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {name : Syntax.Identifier}
    {sourceType : Syntax.TypeExpr} {initializer : Syntax.Expr}
    {expectedReturn : Ty} {initial allocated : State}
    {id : StatementId} {result : Detail.StatementResult}
    (statementEq : statement.value =
      .letDecl name (some sourceType) (some initializer))
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (below : initial.LocalBindersBelowNextLocal) :
    result.state.LocalBindersBelowNextLocal := by
  obtain ⟨resolvedType, inferred, initializerState, locals, _, generalized,
      binding, _, initializerSuccess, _, _, _, bindingEq, resultEq, _⟩ :=
    inferStatementFuel_success_letAnnotatedInitialized_facts statementEq
      allocationEq success
  have allocatedBelow : allocated.LocalBindersBelowNextLocal := by
    have preserved :=
      State.allocateStatementId_preserves_localBindersBelowNextLocal
        initial below
    simpa only [allocationEq] using preserved
  have initializerBelow : initializerState.LocalBindersBelowNextLocal :=
    Detail.inferExprFuel_preserves_localBindersBelowNextLocal allocatedBelow
      initializerSuccess
  rw [resultEq]
  exact letBinding_recordNode_localBindersBelow initializerBelow bindingEq

/-- A match without a default leaves its hidden scrutinee binder visible in
the inference state.  The case traversal restores exactly that scope and
advances the shared binder cutoff monotonically. -/
theorem inferStatementFuel_success_matchWithoutDefault_localBindersBelow
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement}
    {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr}
    {arms : Syntax.MatchArms} {expectedReturn : Ty}
    {initial allocated : State} {id : StatementId}
    {result : Detail.StatementResult}
    (statementEq : statement.value = .matchWith scrutinees arms)
    (defaultEq : arms.value.defaultBody = none)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (below : initial.LocalBindersBelowNextLocal) :
    result.state.LocalBindersBelowNextLocal := by
  obtain ⟨scrutinee, scrutineeState, hiddenScrutinee, hiddenState, checked,
      scrutineeSuccess, hiddenEq, casesSuccess, _, resultEq, _⟩ :=
    inferStatementFuel_success_matchWithoutDefault_facts statementEq defaultEq
      allocationEq success
  have allocatedBelow : allocated.LocalBindersBelowNextLocal := by
    have preserved := State.allocateStatementId_preserves_localBindersBelowNextLocal
      initial below
    simpa only [allocationEq] using preserved
  have scrutineeBelow : scrutineeState.LocalBindersBelowNextLocal :=
    inferMatchScrutineesFuel_preserves_localBindersBelowNextLocal
      allocatedBelow scrutineeSuccess
  have hiddenBelow : hiddenState.LocalBindersBelowNextLocal := by
    have preserved := State.allocateHiddenLocal_preserves_localBindersBelowNextLocal
      scrutineeState scrutineeBelow
    simpa only [hiddenEq] using preserved
  have checkedScope :=
    Detail.inferMatchCasesFuel_success_lexicalScope_eq rfl casesSuccess
  have sameBinders : checked.state.localBinders = hiddenState.localBinders := by
    simpa only [State.lexicalScope] using
      congrArg LexicalScope.binders checkedScope
  have checkedBelow : checked.state.LocalBindersBelowNextLocal :=
    State.LocalBindersBelowNextLocal.transport sameBinders
      (Detail.inferMatchCasesFuel_nextLocal_le casesSuccess) hiddenBelow
  rw [resultEq]
  exact State.recordNode_preserves_localBindersBelowNextLocal checked.state _
    checkedBelow

/-- A default match restores the hidden-binder scope after its default block;
the same allocation bound therefore holds at the retained statement. -/
theorem inferStatementFuel_success_matchWithDefault_localBindersBelow
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement}
    {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr}
    {arms : Syntax.MatchArms} {defaultBody : Syntax.Block}
    {expectedReturn : Ty} {initial allocated : State}
    {id : StatementId} {result : Detail.StatementResult}
    (statementEq : statement.value = .matchWith scrutinees arms)
    (defaultEq : arms.value.defaultBody = some defaultBody)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (below : initial.LocalBindersBelowNextLocal) :
    result.state.LocalBindersBelowNextLocal := by
  obtain ⟨scrutinee, scrutineeState, hiddenScrutinee, hiddenState, checked,
      defaultResult, scrutineeSuccess, hiddenEq, casesSuccess, defaultSuccess,
      _, resultEq, _⟩ :=
    inferStatementFuel_success_matchWithDefault_facts statementEq defaultEq
      allocationEq success
  have allocatedBelow : allocated.LocalBindersBelowNextLocal := by
    have preserved := State.allocateStatementId_preserves_localBindersBelowNextLocal
      initial below
    simpa only [allocationEq] using preserved
  have scrutineeBelow : scrutineeState.LocalBindersBelowNextLocal :=
    inferMatchScrutineesFuel_preserves_localBindersBelowNextLocal
      allocatedBelow scrutineeSuccess
  have hiddenBelow : hiddenState.LocalBindersBelowNextLocal := by
    have preserved := State.allocateHiddenLocal_preserves_localBindersBelowNextLocal
      scrutineeState scrutineeBelow
    simpa only [hiddenEq] using preserved
  have restoredBelow :
      (defaultResult.state.restoreLexicalScope hiddenState.lexicalScope)
        |>.LocalBindersBelowNextLocal :=
    State.restoreLexicalScope_preserves_localBindersBelowNextLocal hiddenBelow
      (Nat.le_trans (Detail.inferMatchCasesFuel_nextLocal_le casesSuccess)
        (Detail.inferStatementsFuel_nextLocal_le defaultSuccess))
  rw [resultEq]
  exact State.recordNode_preserves_localBindersBelowNextLocal _ _ restoredBelow

/-- Ordinary statement branches, including nested blocks and loops, restore
the incoming visible binder stack.  Only `let` and `match` create a binder
that remains in the statement result.  The recursive soundness dispatcher
uses this to transport active-scheme isolation across nonbinding branches. -/
theorem inferStatementFuel_success_nonbinding_sameScope
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {expectedReturn : Ty}
    {initial allocated : State} {id : StatementId}
    {result : Detail.StatementResult}
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (notLet : ∀ name sourceType initializer,
      statement.value ≠ .letDecl name sourceType initializer)
    (notMatch : ∀ scrutinees arms,
      statement.value ≠ .matchWith scrutinees arms) :
    result.state.lexicalScope = initial.lexicalScope := by
  have allocatedScope : allocated.lexicalScope = initial.lexicalScope :=
    Detail.allocateStatementId_success_lexicalScope allocationEq
  cases statementEq : statement.value with
  | letDecl name sourceType initializer =>
      exact False.elim (notLet name sourceType initializer statementEq)
  | matchWith scrutinees arms =>
      exact False.elim (notMatch scrutinees arms statementEq)
  | expression expression trailingSemicolon =>
      obtain ⟨_, expressionState, expressionSuccess, resultEq, _⟩ :=
        inferStatementFuel_success_expression_facts statementEq allocationEq
          success
      rw [resultEq]
      exact (Detail.inferExprFuel_success_lexicalScope_eq
        expressionSuccess).trans allocatedScope
  | assignValue target operator value =>
      obtain ⟨assignment, inferredValue, assignmentState,
          assignmentSuccess, resultEq, _⟩ :=
        inferStatementFuel_success_assignValue_facts statementEq allocationEq
          success
      rw [resultEq]
      exact (Detail.inferAssignedValueFuel_success_lexicalScope_eq
        assignmentSuccess).trans allocatedScope
  | assignBitNot target operatorSpan =>
      obtain ⟨place, placeState, unified, placeSuccess, unifySuccess, _,
          resultEq, _⟩ :=
        inferStatementFuel_success_assignBitNot_facts statementEq allocationEq
          success
      rw [resultEq]
      exact (Detail.unify_preserves_lexicalScope unifySuccess).trans
        ((Detail.inferPlaceFuel_success_lexicalScope_eq placeSuccess).trans
          allocatedScope)
  | returnStmt value =>
      cases value with
      | none =>
          obtain ⟨unified, unifySuccess, _, resultEq, _⟩ :=
            inferStatementFuel_success_returnUnit_facts statementEq
              allocationEq success
          rw [resultEq]
          exact (Detail.unify_preserves_lexicalScope unifySuccess).trans
            allocatedScope
      | some value =>
          obtain ⟨inferred, valueState, valueSuccess, resultEq, _⟩ :=
            inferStatementFuel_success_returnValue_facts statementEq
              allocationEq success
          rw [resultEq]
          exact (Detail.inferExprFuel_success_lexicalScope_eq
            valueSuccess).trans allocatedScope
  | ifThen condition thenBody elseBody =>
      cases elseBody with
      | none =>
          obtain ⟨inferredCondition, conditionState, thenResult,
              conditionSuccess, thenSuccess, resultEq, _⟩ :=
            inferStatementFuel_success_ifWithoutElse_facts statementEq
              allocationEq success
          rw [resultEq]
          exact (Detail.inferExprFuel_success_lexicalScope_eq
            conditionSuccess).trans allocatedScope
      | some elseBody =>
          obtain ⟨inferredCondition, conditionState, thenResult, elseResult,
              conditionSuccess, thenSuccess, elseSuccess, resultEq, _⟩ :=
            inferStatementFuel_success_ifWithElse_facts statementEq
              allocationEq success
          rw [resultEq]
          exact (Detail.inferExprFuel_success_lexicalScope_eq
            conditionSuccess).trans allocatedScope
  | block body =>
      obtain ⟨bodyResult, bodySuccess, resultEq, _⟩ :=
        inferStatementFuel_success_block_facts statementEq allocationEq success
      rw [resultEq]
      exact allocatedScope
  | forLoop headerSpan initializer condition post body =>
      obtain ⟨initializerResult, inferredCondition, conditionState,
          bodyResult, postResult, initializerSuccess, conditionSuccess,
          bodySuccess, postSuccess, resultEq, _⟩ :=
        inferStatementFuel_success_forLoop_facts statementEq allocationEq
          success
      rw [resultEq]
      exact allocatedScope
  | whileLoop condition body =>
      obtain ⟨inferredCondition, conditionState, bodyResult, conditionSuccess,
          bodySuccess, resultEq, _⟩ :=
        inferStatementFuel_success_whileLoop_facts statementEq allocationEq
          success
      rw [resultEq]
      exact (Detail.inferExprFuel_success_lexicalScope_eq
        conditionSuccess).trans allocatedScope
  | breakStmt =>
      obtain ⟨_, resultEq, _⟩ :=
        inferStatementFuel_success_break_facts statementEq allocationEq
          success
      rw [resultEq]
      exact allocatedScope
  | continueStmt =>
      obtain ⟨_, resultEq, _⟩ :=
        inferStatementFuel_success_continue_facts statementEq allocationEq
          success
      rw [resultEq]
      exact allocatedScope
  | assembly body =>
      simp [Detail.inferStatementFuel, statementEq] at success
  | error =>
      simp [Detail.inferStatementFuel, statementEq] at success

/-- Every successful statement inference result has bounded visible local
identities.  This combines ordinary lexical restoration with the two forms
that allocate a binder retained in the inference result. -/
theorem inferStatementFuel_preserves_localBindersBelowNextLocal
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {expectedReturn : Ty}
    {initial : State} {result : Detail.StatementResult}
    (below : initial.LocalBindersBelowNextLocal)
    (success : Detail.inferStatementFuel fuel inferenceContext statement
      expectedReturn initial = .ok result) :
    result.state.LocalBindersBelowNextLocal := by
  cases fuel with
  | zero => simp [Detail.inferStatementFuel] at success
  | succ fuel =>
      rcases allocationEq : initial.allocateStatementId with ⟨id, allocated⟩
      cases statementEq : statement.value
      case letDecl name sourceType initializer =>
          cases sourceType with
          | none =>
              cases initializer with
              | none =>
                  simp [Detail.inferStatementFuel, allocationEq, statementEq,
                    bind, Except.bind]
                    at success
              | some initializer =>
                  exact inferStatementFuel_success_letUnannotatedInitialized_localBindersBelow
                    statementEq allocationEq success below
          | some sourceType =>
              cases initializer with
              | none =>
                  exact inferStatementFuel_success_letAnnotatedUninitialized_localBindersBelow
                    statementEq allocationEq success below
              | some initializer =>
                  exact inferStatementFuel_success_letAnnotatedInitialized_localBindersBelow
                    statementEq allocationEq success below
      case matchWith scrutinees arms =>
          cases defaultEq : arms.value.defaultBody with
          | none =>
              exact inferStatementFuel_success_matchWithoutDefault_localBindersBelow
                statementEq defaultEq allocationEq success below
          | some defaultBody =>
              exact inferStatementFuel_success_matchWithDefault_localBindersBelow
                statementEq defaultEq allocationEq success below
      all_goals
        apply inferStatementFuel_localBindersBelow_of_sameScope below success
        apply inferStatementFuel_success_nonbinding_sameScope allocationEq
          success
        · intro name sourceType initializer
          simp [statementEq]
        · intro scrutinees arms
          simp [statementEq]

end Solcore.SourceSemantics.SourceInferenceSoundness
