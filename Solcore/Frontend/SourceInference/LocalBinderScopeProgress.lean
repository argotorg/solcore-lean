import Solcore.Frontend.SourceInference.LocalLetRequirementTiming

/-! Scope restoration and the monotone binder allocator prevent retired
local identities from being reintroduced by later statement inference. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
namespace Solcore.Frontend.SourceInference.LocalBinderScopeProgress
open TypeSystem Detail

structure Progress (before after : State) : Prop where
  next : before.nextLocal ≤ after.nextLocal
  old : ∀ binder ∈ after.localBinders, binder.id.binderIndex < before.nextLocal →
    binder ∈ before.localBinders

theorem Progress.refl (state : State) : Progress state state :=
  ⟨Nat.le_refl _, fun _ present _ => present⟩

theorem Progress.trans {first middle last : State}
    (left : Progress first middle) (right : Progress middle last) : Progress first last :=
  ⟨Nat.le_trans left.next right.next, fun binder present older =>
    left.old binder (right.old binder present (Nat.lt_of_lt_of_le older left.next)) older⟩

theorem Progress.of_scope {before after : State}
    (next : before.nextLocal ≤ after.nextLocal)
    (same : after.lexicalScope = before.lexicalScope) : Progress before after := by
  refine ⟨next, ?_⟩
  have binders := congrArg LexicalScope.binders same
  change after.localBinders = before.localBinders at binders
  intro binder present _
  rw [binders] at present
  exact present

theorem expression {fuel : Nat} {context : Context} {expression : Syntax.Expr}
    {expected : Option Ty} {before : State} {result : InferredExpression × State}
    (accepted : inferExprFuel fuel context expression expected before = .ok result) :
    Progress before result.2 :=
  .of_scope (inferExprFuel_nextLocal_le accepted) (inferExprFuel_success_lexicalScope_eq accepted)

private theorem expression_binders {fuel : Nat} {context : Context} {expression : Syntax.Expr}
    {expected : Option Ty} {before : State} {result : InferredExpression × State}
    (accepted : inferExprFuel fuel context expression expected before = .ok result) :
    result.2.localBinders = before.localBinders :=
  congrArg LexicalScope.binders (inferExprFuel_success_lexicalScope_eq accepted)

private theorem expressions_binders {fuel : Nat} {context : Context} {expressions : List Syntax.Expr}
    {before : State} {result : List InferredExpression × State}
    (accepted : inferExprsFuel fuel context expressions before = .ok result) :
    result.2.localBinders = before.localBinders :=
  congrArg LexicalScope.binders (inferExprsFuel_success_lexicalScope_eq accepted)

private theorem place_binders {fuel : Nat} {context : Context} {expression : Syntax.Expr}
    {before : State} {result : PlaceResolution × State}
    (accepted : inferPlaceFuel fuel context expression before = .ok result) :
    result.2.localBinders = before.localBinders :=
  congrArg LexicalScope.binders (inferPlaceFuel_success_lexicalScope_eq accepted)

private theorem assigned_binders {fuel : Nat} {context : Context} {target value : Syntax.Expr}
    {operator : Syntax.ValueAssignOp} {before after : State} {assignment : AssignmentResolution}
    {inferred : InferredExpression}
    (accepted : inferAssignedValueFuel fuel context target operator value before = .ok (assignment, inferred, after)) :
    after.localBinders = before.localBinders :=
  congrArg LexicalScope.binders (inferAssignedValueFuel_success_lexicalScope_eq accepted)

private theorem unified_binders {before after : State} {left right : Ty}
    (accepted : unify before left right = .ok after) : after.localBinders = before.localBinders :=
  congrArg LexicalScope.binders (unify_preserves_lexicalScope accepted)

private theorem cases_binders {fuel : Nat} {context : Context} {scrutinee expected : Ty}
    {arms : List Syntax.MatchCase} {before : State} {result : MatchCasesResult}
    (accepted : inferMatchCasesFuel fuel context scrutinee expected before.lexicalScope arms before = .ok result) :
    result.state.localBinders = before.localBinders :=
  congrArg LexicalScope.binders (inferMatchCasesFuel_success_lexicalScope_eq rfl accepted)

private theorem statement_binders (state : State) :
    state.allocateStatementId.2.localBinders = state.localBinders := rfl
private theorem statement_next (state : State) :
    state.allocateStatementId.2.nextLocal = state.nextLocal := rfl
private theorem expressionId_binders (state : State) :
    state.allocateExpressionId.2.localBinders = state.localBinders := rfl

private theorem exceptPure_eq_ok {epsilon alpha : Type} (value result : alpha) :
    ((pure value : Except epsilon alpha) = .ok result) ↔ value = result :=
  by change (Except.ok value = Except.ok result) ↔ value = result; simp

private theorem exceptThrow_ne_ok {epsilon alpha : Type} (error : epsilon) (value : alpha) :
    (throw error : Except epsilon alpha) ≠ .ok value := by
  intro impossible
  cases impossible

/-- Every visible binder older than this statement's allocator boundary was
already visible on entry. Nested lexical scopes cannot resurrect a retired ID. -/
theorem statement {fuel : Nat} {context : Context} {statement : Syntax.Statement}
    {expected : Ty} {before : State} {result : StatementResult}
    (accepted : inferStatementFuel fuel context statement expected before = .ok result) :
    Progress before result.state := by
  refine ⟨inferStatementFuel_nextLocal_le accepted, ?_⟩
  cases fuel with
  | zero => simp [inferStatementFuel] at accepted
  | succ fuel =>
      unfold inferStatementFuel at accepted
      cases form : statement.value <;> simp only [form, bind, Except.bind] at accepted
      all_goals repeat' first | split at accepted
      all_goals try cases accepted
      all_goals try simp_all only [exceptPure_eq_ok, exceptThrow_ne_ok]
      all_goals try subst_vars
      all_goals try have exprBinders := expression_binders (by assumption)
      all_goals try have exprNext := inferExprFuel_nextLocal_le (by assumption)
      all_goals try have exprsBinders := expressions_binders (by assumption)
      all_goals try have placeBinders := place_binders (by assumption)
      all_goals try have assignedBinders := assigned_binders (by assumption)
      all_goals try have unifiedBinders := unified_binders (by assumption)
      all_goals try have casesBinders := cases_binders (by assumption)
      all_goals simp_all only [State.recordNode, State.restoreLexicalScope, State.lexicalScope,
        State.allocateBinder, State.allocateHiddenLocal, statement_binders, statement_next, expressionId_binders]
      all_goals intro binder member older
      all_goals try exact member
      all_goals try (rcases List.mem_cons.mp member with current | old
                     · subst binder; simp only at older; omega
                     · exact old)
      all_goals try trivial

/-- The same exclusion survives the actual source-ordered statement fold. -/
theorem statements {fuel : Nat} {context : Context}
    {sourceStatements : List Syntax.Statement} {expected : Ty} {before : State} {result : BlockResult}
    (accepted : inferStatementsFuel fuel context sourceStatements expected before = .ok result) :
    Progress before result.state := by
  induction fuel generalizing sourceStatements before result with
  | zero => simp [inferStatementsFuel] at accepted
  | succ fuel ih =>
      cases sourceStatements with
      | nil =>
          simp only [inferStatementsFuel, Except.ok.injEq] at accepted
          cases accepted
          exact .refl before
      | cons head tail =>
          simp only [inferStatementsFuel] at accepted
          cases first : inferStatementFuel fuel context head expected before with
          | error error => simp [first, bind, Except.bind] at accepted
          | ok firstResult =>
              have headProgress := statement first
              cases tail with
              | nil =>
                  simp only [first, bind, Except.bind, exceptPure_eq_ok] at accepted
                  cases accepted
                  exact headProgress
              | cons next rest =>
                  cases following : inferStatementsFuel fuel context (next :: rest) expected firstResult.state with
                  | error error => simp [first, following, bind, Except.bind] at accepted
                  | ok followingResult =>
                      have tailProgress := ih following
                      simp only [first, following, bind, Except.bind, exceptPure_eq_ok] at accepted
                      cases accepted
                      exact headProgress.trans tailProgress

/-- A later successful lookup cannot recover an older binder that was absent
when this inference segment began. -/
theorem Progress.lookup_retired_absent {before after : State}
    (progress : Progress before after) {name : String} {binder : TypedBinder}
    (older : binder.id.binderIndex < before.nextLocal)
    (absent : binder ∉ before.localBinders) : after.lookupBinder? name ≠ some binder := by
  intro found
  exact absent (progress.old binder (State.lookupBinder?_eq_some_facts found).1 older)

theorem statements_lookup_retired_absent {fuel : Nat} {context : Context}
    {sourceStatements : List Syntax.Statement} {expected : Ty} {before : State} {result : BlockResult}
    (accepted : inferStatementsFuel fuel context sourceStatements expected before = .ok result)
    {name : String} {binder : TypedBinder}
    (older : binder.id.binderIndex < before.nextLocal)
    (absent : binder ∉ before.localBinders) : result.state.lookupBinder? name ≠ some binder :=
  (statements accepted).lookup_retired_absent older absent

end Solcore.Frontend.SourceInference.LocalBinderScopeProgress
