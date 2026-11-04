import Solcore.Frontend.SourceInference.Internal.LocalReadOrigins

/-!
# Local read scopes

Inference cannot create a reference to a retired local, and local requirements reach their
initializer in time.
-/

section
-- leanmerge: from Solcore.Frontend.SourceInference.LocalLetRequirementTiming
/-! Local-read requirements must reach the actual initializer return state
before they can constrain its enclosing generalization. These receipts expose
that exact executable boundary; no final-ledger fact is moved backwards. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.Frontend.SourceInference.LocalLetRequirementTiming
open TypeSystem Detail

/-- The source compiler's literal result after the initializer has returned. -/
def finish (statement : Syntax.Statement) (name : Syntax.Identifier)
    (initial : State) (value : InferredExpression) (ready : State) : StatementResult :=
  let locals := ready.binderEnvironment.apply ready.inference.substitution
  let generalized := generalizeValue ready locals initial.nextRequirement (ready.resolve value.type)
  let binding := (ready.withLocals locals).allocateBinder name.value generalized.scheme
    (some name.span) false generalized.requirements
  { id := initial.allocateStatementId.1
    type := .unit
    hasValue := false
    sawReturn := false
    state := binding.2.recordNode (.statement {
      id := initial.allocateStatementId.1
      span := statement.span
      type := .unit
      form := .letDecl binding.1 (some value.id) }) }

/-- The initializer's expected type is taken from the actual optional source
annotation resolution. -/
inductive Annotation (context : Context) : Option Syntax.TypeExpr → Option Ty → Prop where
  | none : Annotation context none none
  | some {syntaxType : Syntax.TypeExpr} {type : Ty}
      (accepted : resolveSourceType context syntaxType = .ok type) :
      Annotation context (some syntaxType) (some type)

/-- Actual initialized-let execution retains its initializer inference and
its exact pre-generalization state. -/
structure Receipt (fuel : Nat) (context : Context) (statement : Syntax.Statement)
    (initial : State) (result : StatementResult) where
  name : Syntax.Identifier
  initializer : Syntax.Expr
  annotation : Option Syntax.TypeExpr
  expected : Option Ty
  annotationAccepted : Annotation context annotation expected
  form : statement.value = .letDecl name annotation (some initializer)
  value : InferredExpression
  ready : State
  child : inferExprFuel fuel context initializer expected initial.allocateStatementId.2 = .ok (value, ready)
  completed : result = finish statement name initial value ready

/-- Inversion is restricted to the real unannotated initialized branch. -/
theorem of_accepted {fuel : Nat} {context : Context} {statement : Syntax.Statement}
    {name : Syntax.Identifier} {initializer : Syntax.Expr} {expected : Ty}
    {initial : State} {result : StatementResult}
    (form : statement.value = .letDecl name none (some initializer))
    (accepted : inferStatementFuel (fuel + 1) context statement expected initial = .ok result) :
    Nonempty (Receipt fuel context statement initial result) := by
  unfold inferStatementFuel at accepted
  simp only [form, bind, Except.bind] at accepted
  cases child : inferExprFuel fuel context initializer none initial.allocateStatementId.2 with
  | error error => simp [child] at accepted
  | ok pair =>
      rcases pair with ⟨value, ready⟩
      simp only [child, pure, Pure.pure, Except.pure] at accepted
      refine ⟨⟨name, initializer, none, none, .none, form, value, ready, child, ?_⟩⟩
      exact (Except.ok.inj accepted).symm

/-- Both optional-annotation branches are inverted from the real statement
computation; no binder shape is used to guess the source annotation. -/
theorem of_initialized_accepted {fuel : Nat} {context : Context} {statement : Syntax.Statement}
    {name : Syntax.Identifier} {annotation : Option Syntax.TypeExpr} {initializer : Syntax.Expr}
    {expected : Ty} {initial : State} {result : StatementResult}
    (form : statement.value = .letDecl name annotation (some initializer))
    (accepted : inferStatementFuel (fuel + 1) context statement expected initial = .ok result) :
    Nonempty (Receipt fuel context statement initial result) := by
  cases annotation with
  | none => exact of_accepted form accepted
  | some syntaxType =>
      unfold inferStatementFuel at accepted
      simp only [form, bind, Except.bind] at accepted
      cases resolved : resolveSourceType context syntaxType with
      | error error => simp [resolved] at accepted
      | ok type =>
          cases child : inferExprFuel fuel context initializer (some type) initial.allocateStatementId.2 with
          | error error => simp [resolved, child] at accepted
          | ok pair =>
              rcases pair with ⟨value, ready⟩
              simp only [resolved, child, pure, Pure.pure, Except.pure] at accepted
              refine ⟨⟨name, initializer, some syntaxType, some type, .some resolved,
                form, value, ready, child, ?_⟩⟩
              exact (Except.ok.inj accepted).symm

namespace Receipt
variable {fuel : Nat} {context : Context} {statement : Syntax.Statement}
    {initial : State} {result : StatementResult}

def locals (receipt : Receipt fuel context statement initial result) : Environment :=
  receipt.ready.binderEnvironment.apply receipt.ready.inference.substitution

def generalized (receipt : Receipt fuel context statement initial result) : GeneralizedValue :=
  generalizeValue receipt.ready receipt.locals initial.nextRequirement
    (receipt.ready.resolve receipt.value.type)

def binding (receipt : Receipt fuel context statement initial result) : TypedBinder × State :=
  (receipt.ready.withLocals receipt.locals).allocateBinder receipt.name.value receipt.generalized.scheme
    (some receipt.name.span) false receipt.generalized.requirements

/-- The recorded binder is the exact result of this generalization, not a
reconstructed scheme sharing only its final type. -/
theorem recorded (receipt : Receipt fuel context statement initial result) :
    .statement {
      id := initial.allocateStatementId.1
      span := statement.span
      type := .unit
      form := .letDecl receipt.binding.1 (some receipt.value.id) } ∈ result.state.nodes := by
  have nodes := congrArg (fun value : StatementResult => value.state.nodes) receipt.completed
  rw [nodes]
  exact List.mem_append_right _ (List.mem_singleton_self _)

/-- Real origin propagation stops at the initializer's returned state. -/
theorem ready_origins (receipt : Receipt fuel context statement initial result)
    (wellFormed : initial.RequirementsWellFormed)
    (allocated : initial.DirectRequirementsAllocated)
    (origins : LocalReadEvents.Origins initial) : LocalReadEvents.Origins receipt.ready :=
  (LocalReadEvents.inferExprFuel_origins_progress receipt.child).origins wellFormed allocated origins

/-- A local read already recorded during initializer inference contributes
its actual operational batch at the enclosing let's own cutoff. -/
theorem local_operational (receipt : Receipt fuel context statement initial result)
    (wellFormed : initial.RequirementsWellFormed)
    (allocated : initial.DirectRequirementsAllocated)
    (origins : LocalReadEvents.Origins initial)
    {node : ExpressionNode} (member : .expression node ∈ receipt.ready.nodes)
    {name : String} {binder : Resolved.LocalId}
    (form : node.form = .reference name (.local binder)) :
    ∃ lookup : LocalReadEvents.Lookup,
      node.id = lookup.id ∧
      node.form = .reference lookup.name.value (.local lookup.binder.id) ∧
      node.localSchemeInstantiationStart = some lookup.allocated.inference.next ∧
      lookup.batch.1 <+: node.requirements ∧
      RequirementPredicatesCorrespond receipt.ready.requirements lookup.predicates lookup.batch.1 ∧
      (∀ requirement ∈ receipt.ready.requirements, requirement.id ∈ lookup.batch.1 →
        requirement ∈ generalizeValueBlockingRequirements receipt.ready initial.nextRequirement) := by
  obtain ⟨lookup, id, actualForm, start, batchPrefix, predicates, blocked⟩ :=
    LocalReadEvents.Origin.operational
      (receipt.ready_origins wellFormed allocated origins node member name binder form)
  exact ⟨lookup, id, actualForm, start, batchPrefix, predicates,
    fun requirement present issued => blocked requirement present issued initial.nextRequirement⟩

/-- Variables of a genuinely blocking row cannot be quantified by this
particular executable generalization. -/
theorem excludes_blocking_variable (receipt : Receipt fuel context statement initial result)
    {requirement : Requirement}
    (blocked : requirement ∈ generalizeValueBlockingRequirements receipt.ready initial.nextRequirement)
    {metavariable : TypeVarId}
    (present : metavariable ∈ TypedTraitResolution.predicateVariables
      (applyPredicate receipt.ready requirement.predicate)) :
    metavariable ∉ receipt.generalized.scheme.quantified := by
  have blockedVariable : metavariable ∈ generalizeValueBlockedVariables receipt.ready receipt.locals
      initial.nextRequirement :=
    (mem_generalizeValueBlockedVariables_iff _ _ _ _).mpr (.inr ⟨requirement, blocked, present⟩)
  intro quantified
  change metavariable ∈ (generalizeValue receipt.ready receipt.locals initial.nextRequirement
    (receipt.ready.resolve receipt.value.type)).scheme.quantified at quantified
  rw [generalizeValue_scheme_quantified] at quantified
  have excluded := (List.mem_filter.mp quantified).2
  have contained : (generalizeValueBlockedVariables receipt.ready receipt.locals
      initial.nextRequirement).contains metavariable = true := List.contains_iff_mem.mpr blockedVariable
  rw [contained] at excluded
  cases excluded

/-- The same actual lookup both supplies its original predicate batch and
prevents those operational predicate variables from being generalized by the
enclosing let. This conclusion is about the initializer return state. -/
theorem local_generalization (receipt : Receipt fuel context statement initial result)
    (wellFormed : initial.RequirementsWellFormed)
    (allocated : initial.DirectRequirementsAllocated)
    (origins : LocalReadEvents.Origins initial)
    {node : ExpressionNode} (member : .expression node ∈ receipt.ready.nodes)
    {name : String} {binder : Resolved.LocalId}
    (form : node.form = .reference name (.local binder)) :
    ∃ lookup : LocalReadEvents.Lookup,
      node.id = lookup.id ∧
      node.form = .reference lookup.name.value (.local lookup.binder.id) ∧
      node.localSchemeInstantiationStart = some lookup.allocated.inference.next ∧
      lookup.batch.1 <+: node.requirements ∧
      RequirementPredicatesCorrespond receipt.ready.requirements lookup.predicates lookup.batch.1 ∧
      (∀ requirement ∈ receipt.ready.requirements, requirement.id ∈ lookup.batch.1 →
        ∀ metavariable ∈ TypedTraitResolution.predicateVariables (applyPredicate receipt.ready requirement.predicate),
          metavariable ∉ receipt.generalized.scheme.quantified) := by
  obtain ⟨lookup, id, actualForm, start, batchPrefix, predicates, blocked⟩ :=
    receipt.local_operational wellFormed allocated origins member form
  exact ⟨lookup, id, actualForm, start, batchPrefix, predicates,
    fun requirement present issued _ variableMember =>
      receipt.excludes_blocking_variable (blocked requirement present issued) variableMember⟩

/-- Initializer inference restores the exact entering lexical binder stack. -/
theorem ready_binders (receipt : Receipt fuel context statement initial result) :
    receipt.ready.localBinders = initial.localBinders := by
  exact congrArg LexicalScope.binders (inferExprFuel_success_lexicalScope_eq receipt.child)

/-- The only binder added after the initializer returns is this let's real
new binder; nested initializer locals are not installed in its continuation. -/
theorem result_binders (receipt : Receipt fuel context statement initial result) :
    result.state.localBinders = receipt.binding.1 :: initial.localBinders := by
  have binders := congrArg (fun value : StatementResult => value.state.localBinders) receipt.completed
  calc
    result.state.localBinders = receipt.binding.1 :: receipt.ready.localBinders := binders
    _ = receipt.binding.1 :: initial.localBinders := by rw [receipt.ready_binders]

/-- A later lookup immediately after this generalization selects either an
entering binder or this let's fresh binder, with their exact allocator bounds. -/
theorem lookup_after_generalization (receipt : Receipt fuel context statement initial result)
    (below : initial.LocalBindersBelowNextLocal) {name : String} {binder : TypedBinder}
    (found : result.state.lookupBinder? name = some binder) :
    binder.id.binderIndex < initial.nextLocal ∨ binder.id.binderIndex = receipt.ready.nextLocal := by
  have present := (State.lookupBinder?_eq_some_facts found).1
  rw [receipt.result_binders] at present
  rcases List.mem_cons.mp present with current | entering
  · right
    rw [current]
    rfl
  · exact .inl (below binder entering)

/-- A binder created and retired inside the initializer cannot be recovered
by any lookup at the actual enclosing let's continuation. -/
theorem retired_lookup_absent (receipt : Receipt fuel context statement initial result)
    (below : initial.LocalBindersBelowNextLocal) {retired : Resolved.LocalId}
    (created : initial.nextLocal ≤ retired.binderIndex)
    (retiredBeforeReturn : retired.binderIndex < receipt.ready.nextLocal)
    {name : String} {binder : TypedBinder} (same : binder.id = retired) :
    result.state.lookupBinder? name ≠ some binder := by
  intro found
  have bounds := receipt.lookup_after_generalization below found
  rw [same] at bounds
  omega

end Receipt
end Solcore.Frontend.SourceInference.LocalLetRequirementTiming
end

section
-- leanmerge: from Solcore.Frontend.SourceInference.LocalBinderScopeProgress
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
end

section
-- leanmerge: from Solcore.Frontend.SourceInference.LocalHeaderRequirementTiming
/-! Initialized for-header declarations retain their exact inference return
state, optional annotation and allocation. Their operational requirements
constrain generalization at the actual entry cutoff. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.Frontend.SourceInference.LocalHeaderRequirementTiming
open TypeSystem Detail
open LocalLetRequirementTiming (Annotation)

/-- The actual header allocation immediately after initializer inference. -/
def finish (name : Syntax.Identifier) (initial : State)
    (value : InferredExpression) (ready : State) : ForItemForm × State :=
  let locals := ready.binderEnvironment.apply ready.inference.substitution
  let generalized := generalizeValue ready locals initial.nextRequirement (ready.resolve value.type)
  let binding := (ready.withLocals locals).allocateBinder name.value generalized.scheme
    (some name.span) false generalized.requirements
  (.letDecl binding.1 (some value.id), binding.2)

/-- Actual initialized-let execution retains its initializer inference and
its exact pre-generalization state. -/
structure Receipt (fuel : Nat) (context : Context) (statement : Syntax.ForItem)
    (initial : State) (result : ForItemForm × State) where
  name : Syntax.Identifier
  initializer : Syntax.Expr
  annotation : Option Syntax.TypeExpr
  expected : Option Ty
  annotationAccepted : Annotation context annotation expected
  form : statement.value = .letDecl name annotation (some initializer)
  value : InferredExpression
  ready : State
  child : inferExprFuel fuel context initializer expected initial = .ok (value, ready)
  completed : result = finish name initial value ready

/-- Inversion is restricted to the real unannotated initialized branch. -/
theorem of_accepted {fuel : Nat} {context : Context} {statement : Syntax.ForItem}
    {name : Syntax.Identifier} {initializer : Syntax.Expr}
    {initial : State} {result : ForItemForm × State}
    (form : statement.value = .letDecl name none (some initializer))
    (accepted : inferForItemFuel (fuel + 1) context statement initial = .ok result) :
    Nonempty (Receipt fuel context statement initial result) := by
  unfold inferForItemFuel at accepted
  simp only [form, bind, Except.bind] at accepted
  cases child : inferExprFuel fuel context initializer none initial with
  | error error => simp [child] at accepted
  | ok pair =>
      rcases pair with ⟨value, ready⟩
      simp only [child, pure, Pure.pure, Except.pure] at accepted
      refine ⟨⟨name, initializer, none, none, .none, form, value, ready, child, ?_⟩⟩
      exact (Except.ok.inj accepted).symm

/-- Both optional-annotation branches are inverted from the real statement
computation; no binder shape is used to guess the source annotation. -/
theorem of_initialized_accepted {fuel : Nat} {context : Context} {statement : Syntax.ForItem}
    {name : Syntax.Identifier} {annotation : Option Syntax.TypeExpr} {initializer : Syntax.Expr}
    {initial : State} {result : ForItemForm × State}
    (form : statement.value = .letDecl name annotation (some initializer))
    (accepted : inferForItemFuel (fuel + 1) context statement initial = .ok result) :
    Nonempty (Receipt fuel context statement initial result) := by
  cases annotation with
  | none => exact of_accepted form accepted
  | some syntaxType =>
      unfold inferForItemFuel at accepted
      simp only [form, bind, Except.bind] at accepted
      cases resolved : resolveSourceType context syntaxType with
      | error error => simp [resolved] at accepted
      | ok type =>
          cases child : inferExprFuel fuel context initializer (some type) initial with
          | error error => simp [resolved, child] at accepted
          | ok pair =>
              rcases pair with ⟨value, ready⟩
              simp only [resolved, child, pure, Pure.pure, Except.pure] at accepted
              refine ⟨⟨name, initializer, some syntaxType, some type, .some resolved,
                form, value, ready, child, ?_⟩⟩
              exact (Except.ok.inj accepted).symm

namespace Receipt
variable {fuel : Nat} {context : Context} {statement : Syntax.ForItem}
    {initial : State} {result : ForItemForm × State}

def locals (receipt : Receipt fuel context statement initial result) : Environment :=
  receipt.ready.binderEnvironment.apply receipt.ready.inference.substitution

def generalized (receipt : Receipt fuel context statement initial result) : GeneralizedValue :=
  generalizeValue receipt.ready receipt.locals initial.nextRequirement
    (receipt.ready.resolve receipt.value.type)

def binding (receipt : Receipt fuel context statement initial result) : TypedBinder × State :=
  (receipt.ready.withLocals receipt.locals).allocateBinder receipt.name.value receipt.generalized.scheme
    (some receipt.name.span) false receipt.generalized.requirements

/-- Header inference returns this exact binder and initializer occurrence. -/
theorem recorded (receipt : Receipt fuel context statement initial result) :
    result.1 = .letDecl receipt.binding.1 (some receipt.value.id) := by
  exact congrArg Prod.fst receipt.completed

/-- Real origin propagation stops at the initializer's returned state. -/
theorem ready_origins (receipt : Receipt fuel context statement initial result)
    (wellFormed : initial.RequirementsWellFormed)
    (allocated : initial.DirectRequirementsAllocated)
    (origins : LocalReadEvents.Origins initial) : LocalReadEvents.Origins receipt.ready :=
  (LocalReadEvents.inferExprFuel_origins_progress receipt.child).origins wellFormed allocated origins

/-- A local read already recorded during initializer inference contributes
its actual operational batch at the enclosing let's own cutoff. -/
theorem local_operational (receipt : Receipt fuel context statement initial result)
    (wellFormed : initial.RequirementsWellFormed)
    (allocated : initial.DirectRequirementsAllocated)
    (origins : LocalReadEvents.Origins initial)
    {node : ExpressionNode} (member : .expression node ∈ receipt.ready.nodes)
    {name : String} {binder : Resolved.LocalId}
    (form : node.form = .reference name (.local binder)) :
    ∃ lookup : LocalReadEvents.Lookup,
      node.id = lookup.id ∧
      node.form = .reference lookup.name.value (.local lookup.binder.id) ∧
      node.localSchemeInstantiationStart = some lookup.allocated.inference.next ∧
      lookup.batch.1 <+: node.requirements ∧
      RequirementPredicatesCorrespond receipt.ready.requirements lookup.predicates lookup.batch.1 ∧
      (∀ requirement ∈ receipt.ready.requirements, requirement.id ∈ lookup.batch.1 →
        requirement ∈ generalizeValueBlockingRequirements receipt.ready initial.nextRequirement) := by
  obtain ⟨lookup, id, actualForm, start, batchPrefix, predicates, blocked⟩ :=
    LocalReadEvents.Origin.operational
      (receipt.ready_origins wellFormed allocated origins node member name binder form)
  exact ⟨lookup, id, actualForm, start, batchPrefix, predicates,
    fun requirement present issued => blocked requirement present issued initial.nextRequirement⟩

/-- Variables of a genuinely blocking row cannot be quantified by this
particular executable generalization. -/
theorem excludes_blocking_variable (receipt : Receipt fuel context statement initial result)
    {requirement : Requirement}
    (blocked : requirement ∈ generalizeValueBlockingRequirements receipt.ready initial.nextRequirement)
    {metavariable : TypeVarId}
    (present : metavariable ∈ TypedTraitResolution.predicateVariables
      (applyPredicate receipt.ready requirement.predicate)) :
    metavariable ∉ receipt.generalized.scheme.quantified := by
  have blockedVariable : metavariable ∈ generalizeValueBlockedVariables receipt.ready receipt.locals
      initial.nextRequirement :=
    (mem_generalizeValueBlockedVariables_iff _ _ _ _).mpr (.inr ⟨requirement, blocked, present⟩)
  intro quantified
  change metavariable ∈ (generalizeValue receipt.ready receipt.locals initial.nextRequirement
    (receipt.ready.resolve receipt.value.type)).scheme.quantified at quantified
  rw [generalizeValue_scheme_quantified] at quantified
  have excluded := (List.mem_filter.mp quantified).2
  have contained : (generalizeValueBlockedVariables receipt.ready receipt.locals
      initial.nextRequirement).contains metavariable = true := List.contains_iff_mem.mpr blockedVariable
  rw [contained] at excluded
  cases excluded

/-- The same actual lookup both supplies its original predicate batch and
prevents those operational predicate variables from being generalized by the
enclosing let. This conclusion is about the initializer return state. -/
theorem local_generalization (receipt : Receipt fuel context statement initial result)
    (wellFormed : initial.RequirementsWellFormed)
    (allocated : initial.DirectRequirementsAllocated)
    (origins : LocalReadEvents.Origins initial)
    {node : ExpressionNode} (member : .expression node ∈ receipt.ready.nodes)
    {name : String} {binder : Resolved.LocalId}
    (form : node.form = .reference name (.local binder)) :
    ∃ lookup : LocalReadEvents.Lookup,
      node.id = lookup.id ∧
      node.form = .reference lookup.name.value (.local lookup.binder.id) ∧
      node.localSchemeInstantiationStart = some lookup.allocated.inference.next ∧
      lookup.batch.1 <+: node.requirements ∧
      RequirementPredicatesCorrespond receipt.ready.requirements lookup.predicates lookup.batch.1 ∧
      (∀ requirement ∈ receipt.ready.requirements, requirement.id ∈ lookup.batch.1 →
        ∀ metavariable ∈ TypedTraitResolution.predicateVariables (applyPredicate receipt.ready requirement.predicate),
          metavariable ∉ receipt.generalized.scheme.quantified) := by
  obtain ⟨lookup, id, actualForm, start, batchPrefix, predicates, blocked⟩ :=
    receipt.local_operational wellFormed allocated origins member form
  exact ⟨lookup, id, actualForm, start, batchPrefix, predicates,
    fun requirement present issued _ variableMember =>
      receipt.excludes_blocking_variable (blocked requirement present issued) variableMember⟩

/-- Initializer inference restores the exact entering lexical binder stack. -/
theorem ready_binders (receipt : Receipt fuel context statement initial result) :
    receipt.ready.localBinders = initial.localBinders := by
  exact congrArg LexicalScope.binders (inferExprFuel_success_lexicalScope_eq receipt.child)

/-- The only binder added after the initializer returns is this let's real
new binder; nested initializer locals are not installed in its continuation. -/
theorem result_binders (receipt : Receipt fuel context statement initial result) :
    result.2.localBinders = receipt.binding.1 :: initial.localBinders := by
  have binders := congrArg (fun value : ForItemForm × State => value.2.localBinders) receipt.completed
  calc
    result.2.localBinders = receipt.binding.1 :: receipt.ready.localBinders := binders
    _ = receipt.binding.1 :: initial.localBinders := by rw [receipt.ready_binders]

/-- A later lookup immediately after this generalization selects either an
entering binder or this let's fresh binder, with their exact allocator bounds. -/
theorem lookup_after_generalization (receipt : Receipt fuel context statement initial result)
    (below : initial.LocalBindersBelowNextLocal) {name : String} {binder : TypedBinder}
    (found : result.2.lookupBinder? name = some binder) :
    binder.id.binderIndex < initial.nextLocal ∨ binder.id.binderIndex = receipt.ready.nextLocal := by
  have present := (State.lookupBinder?_eq_some_facts found).1
  rw [receipt.result_binders] at present
  rcases List.mem_cons.mp present with current | entering
  · right
    rw [current]
    rfl
  · exact .inl (below binder entering)

/-- A binder created and retired inside the initializer cannot be recovered
by any lookup at the actual enclosing let's continuation. -/
theorem retired_lookup_absent (receipt : Receipt fuel context statement initial result)
    (below : initial.LocalBindersBelowNextLocal) {retired : Resolved.LocalId}
    (created : initial.nextLocal ≤ retired.binderIndex)
    (retiredBeforeReturn : retired.binderIndex < receipt.ready.nextLocal)
    {name : String} {binder : TypedBinder} (same : binder.id = retired) :
    result.2.lookupBinder? name ≠ some binder := by
  intro found
  have bounds := receipt.lookup_after_generalization below found
  rw [same] at bounds
  omega

end Receipt
end Solcore.Frontend.SourceInference.LocalHeaderRequirementTiming
end

section
-- leanmerge: from Solcore.Frontend.SourceInference.LocalReadScopeProgress
/-! A successful inference segment may preserve an earlier local-reference
occurrence or create a reference to a visible or freshly allocated binder.
The relation retains exact occurrence and local identities. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.Frontend.SourceInference.LocalReadScopeProgress
open TypeSystem Detail

def Absent (id : Resolved.LocalId) (binders : List TypedBinder) : Prop :=
  ∀ binder ∈ binders, binder.id ≠ id

def ReadAt (nodes : List Node) (occurrence : ExpressionId) (localId : Resolved.LocalId) : Prop :=
  ∃ node, .expression node ∈ nodes ∧ node.id = occurrence ∧
    ∃ name, node.form = .reference name (.local localId)

def ReadsFrom (localId : Resolved.LocalId) (before after : List Node) : Prop :=
  ∀ occurrence, ReadAt after occurrence localId → ReadAt before occurrence localId

structure Fields (beforeNext : Nat) (beforeBinders : List TypedBinder) (beforeNodes : List Node)
    (afterNext : Nat) (afterBinders : List TypedBinder) (afterNodes : List Node) : Prop where
  next : beforeNext ≤ afterNext
  absent : ∀ id, id.binderIndex < beforeNext → Absent id beforeBinders → Absent id afterBinders
  reads : ∀ id, id.binderIndex < beforeNext → Absent id beforeBinders → ReadsFrom id beforeNodes afterNodes

abbrev Progress (before after : State) : Prop :=
  Fields before.nextLocal before.localBinders before.nodes after.nextLocal after.localBinders after.nodes

namespace Fields

theorem refl (next : Nat) (binders : List TypedBinder) (nodes : List Node) :
    Fields next binders nodes next binders nodes :=
  ⟨Nat.le_refl _, fun _ _ absent => absent, fun _ _ _ _ read => read⟩

theorem trans {bn mn an : Nat} {bb mb ab : List TypedBinder} {bs ms ads : List Node}
    (first : Fields bn bb bs mn mb ms) (second : Fields mn mb ms an ab ads) :
    Fields bn bb bs an ab ads := by
  refine ⟨Nat.le_trans first.next second.next, ?_, ?_⟩
  · intro id older absent
    exact second.absent id (Nat.lt_of_lt_of_le older first.next) (first.absent id older absent)
  · intro id older absent occurrence read
    exact first.reads id older absent occurrence
      (second.reads id (Nat.lt_of_lt_of_le older first.next) (first.absent id older absent) occurrence read)

/-- Restoring a genuine saved outer scope changes no recorded occurrence. -/
theorem restore {bn an : Nat} {bb ab outer : List TypedBinder} {bs ads : List Node}
    (progress : Fields bn bb bs an ab ads) (saved : outer ⊆ bb) :
    Fields bn bb bs an outer ads :=
  ⟨progress.next, fun _ _ absent binder member => absent binder (saved member), progress.reads⟩

theorem advance (next after : Nat) (binders : List TypedBinder) (nodes : List Node)
    (grown : next ≤ after) : Fields next binders nodes after binders nodes :=
  ⟨grown, fun _ _ absent => absent, fun _ _ _ _ read => read⟩

theorem allocate (next : Nat) (binders : List TypedBinder) (nodes : List Node)
    (binder : TypedBinder) (fresh : binder.id.binderIndex = next) :
    Fields next binders nodes (next + 1) (binder :: binders) nodes := by
  refine ⟨Nat.le_succ _, ?_, fun _ _ _ _ read => read⟩
  intro id older absent actual member same
  rcases List.mem_cons.mp member with current | old
  · subst actual
    have index := congrArg Resolved.LocalId.binderIndex same
    rw [fresh] at index
    omega
  · exact absent actual old same

theorem statement (next : Nat) (binders : List TypedBinder) (nodes : List Node)
    (node : StatementNode) : Fields next binders nodes next binders (nodes ++ [.statement node]) := by
  refine ⟨Nat.le_refl _, fun _ _ absent => absent, ?_⟩
  intro id _ _ occurrence ⟨expression, member, same, name, form⟩
  rcases List.mem_append.mp member with old | fresh
  · exact ⟨expression, old, same, name, form⟩
  · cases List.mem_singleton.mp fresh

theorem expression (next : Nat) (binders : List TypedBinder) (nodes : List Node)
    (node : ExpressionNode)
    (allowed : ∀ name id, node.form = .reference name (.local id) →
      next ≤ id.binderIndex ∨ ∃ binder ∈ binders, binder.id = id) :
    Fields next binders nodes next binders (nodes ++ [.expression node]) := by
  refine ⟨Nat.le_refl _, fun _ _ absent => absent, ?_⟩
  intro id older absent occurrence ⟨expression, member, same, name, form⟩
  rcases List.mem_append.mp member with old | fresh
  · exact ⟨expression, old, same, name, form⟩
  · cases List.mem_singleton.mp fresh
    rcases allowed name id form with later | ⟨binder, present, sameBinder⟩
    · omega
    · exact False.elim (absent binder present sameBinder)

end Fields

namespace Progress

theorem refl (state : State) : Progress state state := Fields.refl _ _ _

theorem trans {before middle after : State} (first : Progress before middle)
    (second : Progress middle after) : Progress before after := Fields.trans first second

theorem of_unchanged {before after : State}
    (next : before.nextLocal ≤ after.nextLocal)
    (binders : after.localBinders = before.localBinders)
    (nodes : after.nodes = before.nodes) : Progress before after := by
  refine ⟨next, ?_, ?_⟩
  · intro id _ absent
    simpa only [binders] using absent
  · intro id _ _ occurrence read
    simpa only [nodes] using read

theorem of_nodes_eq {before after : State}
    (scope : LocalBinderScopeProgress.Progress before after)
    (nodes : after.nodes = before.nodes) : Progress before after := by
  refine ⟨scope.next, ?_, ?_⟩
  · intro id older absent binder member same
    apply absent binder
    · apply scope.old binder member
      simpa only [same] using older
    · exact same
  · intro _ _ _ occurrence read
    simpa only [nodes] using read

/-- The useful consequence of the relation: a reference to an older, invisible
binder must already be recorded before this inference segment. -/
theorem retired_read {before after : State} (progress : Progress before after)
    {id : Resolved.LocalId} (older : id.binderIndex < before.nextLocal)
    (absent : Absent id before.localBinders) {node : ExpressionNode}
    (member : .expression node ∈ after.nodes) {name : String}
    (form : node.form = .reference name (.local id)) : ReadAt before.nodes node.id id :=
  progress.reads id older absent node.id ⟨node, member, rfl, name, form⟩

theorem recordStatement (state : State) (node : StatementNode) :
    Progress state (state.recordNode (.statement node)) := .statement _ _ _ _

theorem recordExpression (state : State) (node : ExpressionNode)
    (allowed : ∀ name id, node.form = .reference name (.local id) →
      state.nextLocal ≤ id.binderIndex ∨ ∃ binder ∈ state.localBinders, binder.id = id) :
    Progress state (state.recordNode (.expression node)) := .expression _ _ _ _ allowed

theorem allocateBinder (state : State) (name : String) (scheme : Scheme)
    (span : Option Syntax.SourceSpan) (comptime : Bool) (requirements : List LocalSchemeRequirement) :
    Progress state (state.allocateBinder name scheme span comptime requirements).2 :=
  .allocate _ _ _ _ rfl

theorem allocateHiddenLocal (state : State) : Progress state state.allocateHiddenLocal.2 :=
  Fields.advance _ _ _ _ (Nat.le_succ _)

theorem modifyStatementNode (state : State) (id : StatementId) (modify : StatementNode → StatementNode) :
    Progress state (state.modifyStatementNode id modify) := by
  refine ⟨Nat.le_refl _, fun _ _ absent => absent, ?_⟩
  intro localId _ _ occurrence ⟨expression, member, actualId, name, form⟩
  obtain ⟨node, present, same⟩ := List.mem_map.mp member
  cases node with
  | expression old =>
      have sameExpression := Node.expression.inj same
      rw [← sameExpression] at actualId form
      exact ⟨old, present, actualId, name, form⟩
  | statement old =>
      simp only at same
      split at same <;> cases same

theorem modifyExpressionNode (state : State) (id : ExpressionId) (modify : ExpressionNode → ExpressionNode)
    (sameForm : ∀ node, (modify node).form = node.form) :
    Progress state (state.modifyExpressionNode id modify) := by
  refine ⟨Nat.le_refl _, fun _ _ absent => absent, ?_⟩
  intro localId _ _ occurrence ⟨expression, member, actualId, name, form⟩
  obtain ⟨node, present, same⟩ := List.mem_map.mp member
  cases node with
  | statement old => cases same
  | expression old =>
      simp only at same
      split at same
      · rename_i selected
        have sameExpression := Node.expression.inj same
        rw [← sameExpression] at actualId form
        exact ⟨old, present, selected.trans actualId, name, (sameForm old).symm.trans form⟩
      · have sameExpression := Node.expression.inj same
        rw [← sameExpression] at actualId form
        exact ⟨old, present, actualId, name, form⟩

theorem attachExpressionCoercions (state : State) (entries : List ExpressionCoercions) :
    Progress state (Detail.attachExpressionCoercions state entries) := by
  induction entries generalizing state with
  | nil => exact .refl _
  | cons entry rest ih =>
      exact (modifyExpressionNode state entry.expression
        (fun node => appendExpressionCoercions node entry.coercions) (fun _ => rfl)).trans
          (ih _)

end Progress
end Solcore.Frontend.SourceInference.LocalReadScopeProgress
end

section
-- leanmerge: from Solcore.Frontend.SourceInference.LocalReadRetiredInterval
/-! Reads of locals retired by an initializer stay inside that initializer's
recorded nodes. Restoring an enclosing scope is justified by its actual ID
bound, even when that scope is no longer a subset of the current binders. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.Frontend.SourceInference.LocalReadScopeProgress

structure Barrier (low high : Nat) (readyNodes : List Node) (state : State) : Prop where
  allocated : high ≤ state.nextLocal
  absent : ∀ id : Resolved.LocalId, low ≤ id.binderIndex → id.binderIndex < high →
    Absent id state.localBinders
  reads : ∀ id : Resolved.LocalId, low ≤ id.binderIndex → id.binderIndex < high →
    ReadsFrom id readyNodes state.nodes

namespace Barrier

theorem progress {low high : Nat} {readyNodes : List Node} {before after : State}
    (barrier : Barrier low high readyNodes before) (step : Progress before after) :
    Barrier low high readyNodes after := by
  refine ⟨Nat.le_trans barrier.allocated step.next, ?_, ?_⟩
  · intro id lower upper
    exact step.absent id (Nat.lt_of_lt_of_le upper barrier.allocated)
      (barrier.absent id lower upper)
  · intro id lower upper occurrence read
    exact barrier.reads id lower upper occurrence
      (step.reads id (Nat.lt_of_lt_of_le upper barrier.allocated)
        (barrier.absent id lower upper) occurrence read)

theorem restore {low high : Nat} {readyNodes : List Node} {state : State}
    (barrier : Barrier low high readyNodes state) (scope : LexicalScope)
    (absent : ∀ id : Resolved.LocalId, low ≤ id.binderIndex → id.binderIndex < high →
      Absent id scope.binders) :
    Barrier low high readyNodes (state.restoreLexicalScope scope) :=
  ⟨barrier.allocated, absent, barrier.reads⟩

theorem restore_below {low high : Nat} {readyNodes : List Node} {state : State}
    (barrier : Barrier low high readyNodes state) (scope : LexicalScope)
    (below : ∀ binder ∈ scope.binders, binder.id.binderIndex < low) :
    Barrier low high readyNodes (state.restoreLexicalScope scope) := by
  apply barrier.restore scope
  intro id lower _ binder present same
  have upper := below binder present
  rw [same] at upper
  omega

theorem restore_saved {low high : Nat} {readyNodes : List Node} {state initial : State}
    (barrier : Barrier low high readyNodes state) (scope : LexicalScope)
    (saved : scope.binders ⊆ initial.localBinders)
    (below : initial.LocalBindersBelowNextLocal) (entered : initial.nextLocal ≤ low) :
    Barrier low high readyNodes (state.restoreLexicalScope scope) := by
  apply barrier.restore_below scope
  intro binder present
  exact Nat.lt_of_lt_of_le (below binder (saved present)) entered

theorem of_unchanged {low high : Nat} {readyNodes : List Node} {before after : State}
    (barrier : Barrier low high readyNodes before)
    (next : before.nextLocal ≤ after.nextLocal)
    (binders : after.localBinders = before.localBinders)
    (nodes : after.nodes = before.nodes) : Barrier low high readyNodes after :=
  barrier.progress (Progress.of_unchanged next binders nodes)

theorem read {low high : Nat} {readyNodes : List Node} {state : State}
    (barrier : Barrier low high readyNodes state) {id : Resolved.LocalId}
    (lower : low ≤ id.binderIndex) (upper : id.binderIndex < high)
    {node : ExpressionNode} (member : .expression node ∈ state.nodes)
    {name : String} (form : node.form = .reference name (.local id)) :
    ReadAt readyNodes node.id id :=
  barrier.reads id lower upper node.id ⟨node, member, rfl, name, form⟩

end Barrier
end Solcore.Frontend.SourceInference.LocalReadScopeProgress
end

section
-- leanmerge: from Solcore.Frontend.SourceInference.LocalReadScopeHelpers
/-! Helper computations preserve exact local-reference identities. Actual local
identifier inference adds only the binder selected by its real lexical lookup. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.Frontend.SourceInference.LocalReadScopeProgress
open TypeSystem Detail

namespace Progress

theorem unify {state next : State} {left right : Ty}
    (accepted : unify state left right = .ok next) : Progress state next :=
  of_unchanged (Nat.le_of_eq (localReadScope_unify_preserves_nextLocal accepted).symm)
    (congrArg LexicalScope.binders (unify_preserves_lexicalScope accepted))
    (unify_occurrenceState_eq accepted).1

theorem withExpected {context : Context} {state : State} {actual : InferredExpression}
    {expected : Option Ty} {result : ExpectationResult}
    (accepted : Detail.withExpected context state actual expected = .ok result) : Progress state result.state :=
  of_unchanged (Nat.le_of_eq (localReadScope_withExpected_nextLocal accepted).symm)
    (congrArg LexicalScope.binders (localReadScope_withExpected_lexicalScope accepted))
    (withExpected_occurrenceState_eq accepted).1

theorem selectFunctionCandidateFrom {context : Context} {name : String}
    {candidates : List ProgramFunctionSignature} {arguments : List InferredExpression}
    {integerLiteralOrigins : List IntegerLiteralOrigin} {call : ExpressionId} {expected : Option Ty}
    {state : State} {result : CandidateAttemptResult}
    (accepted : Detail.selectFunctionCandidateFrom context name candidates arguments integerLiteralOrigins
      call expected state = .ok result) : Progress state result.state :=
  of_unchanged (Nat.le_of_eq (localReadScope_selectFunctionCandidateFrom_nextLocal accepted).symm)
    (congrArg LexicalScope.binders (localReadScope_selectFunctionCandidateFrom_lexicalScope accepted))
    (selectFunctionCandidateFrom_occurrenceState_eq accepted).1

theorem inferUnaryOperator {context : Context} {operator : Syntax.UnaryOp} {operandType : Ty}
    {expected : Option Ty} {integerLiterals : List IntegerLiteralOrigin}
    {state : State} {result : OperatorInferenceResult}
    (accepted : Detail.inferUnaryOperator context operator operandType expected integerLiterals state = .ok result) :
    Progress state result.state :=
  of_unchanged (Nat.le_of_eq (localReadScope_inferUnaryOperator_nextLocal accepted).symm)
    (congrArg LexicalScope.binders (localReadScope_inferUnaryOperator_lexicalScope accepted))
    (inferUnaryOperator_occurrenceState_eq accepted).1

theorem inferBinaryOperator {context : Context} {operator : Syntax.BinaryOp} {left right : Ty}
    {expected : Option Ty} {integerLiterals : List IntegerLiteralOrigin}
    {state : State} {result : OperatorInferenceResult}
    (accepted : Detail.inferBinaryOperator context operator left right expected integerLiterals state = .ok result) :
    Progress state result.state :=
  of_unchanged (Nat.le_of_eq (localReadScope_inferBinaryOperator_nextLocal accepted).symm)
    (congrArg LexicalScope.binders (localReadScope_inferBinaryOperator_lexicalScope accepted))
    (inferBinaryOperator_occurrenceState_eq accepted).1

theorem applyFunctionType {context : Context} {call : ExpressionId} {calleeType : Ty}
    {arguments : List InferredExpression} {expected : Option Ty}
    {state : State} {result : IndirectApplicationResult}
    (accepted : Detail.applyFunctionType context call calleeType arguments expected state = .ok result) :
    Progress state result.state :=
  of_unchanged (Nat.le_of_eq (localReadScope_applyFunctionType_nextLocal accepted).symm)
    (congrArg LexicalScope.binders (localReadScope_applyFunctionType_lexicalScope accepted))
    (applyFunctionType_occurrenceState_eq accepted).1

theorem recordExpressionWithExpected {context : Context} {source : Syntax.Expr} {id : ExpressionId}
    {type : Ty} {form : ExpressionForm} {requirements : List RequirementId} {expected : Option Ty}
    {state : State} {start : Option Nat} {result : InferredExpression × State}
    (accepted : Detail.recordExpressionWithExpected context source id type form requirements expected state start = .ok result)
    (nonlocal : LocalReadEvents.Nonlocal form) : Progress state result.2 := by
  obtain ⟨fitted, fit, _, recorded⟩ := Detail.recordExpressionWithExpected_success_record accepted
  rw [recorded]
  apply (withExpected fit).trans
  apply recordExpression
  intro name localId same
  exact False.elim (nonlocal name localId same)

theorem recordNonlocal (state : State) (source : Syntax.Expr) (expression : InferredExpression)
    (form : ExpressionForm) (requirements : List RequirementId) (coercions : List CoercionStep)
    (start : Option Nat) (nonlocal : LocalReadEvents.Nonlocal form) :
    Progress state (Detail.recordExpression source expression form requirements coercions state start).2 := by
  apply recordExpression
  intro name localId same
  exact False.elim (nonlocal name localId same)

/-- The only new local reference in this branch names the actual looked-up
entry. A retired local identity cannot be manufactured by a type match. -/
theorem localIdentifier {fuel : Nat} {context : Context} {expression : Syntax.Expr}
    {expected : Option Ty} {initial allocated : State} {id : ExpressionId}
    {name : Syntax.Identifier} {binder : TypedBinder} {result : InferredExpression × State}
    (form : expression.value = .identifier name)
    (allocation : initial.allocateExpressionId = (id, allocated))
    (found : allocated.lookupBinder? name.value = some binder)
    (accepted : inferExprFuel (fuel + 1) context expression expected initial = .ok result) :
    Progress initial result.2 := by
  have scope := inferExprFuel_success_lexicalScope_eq accepted
  have binders := congrArg LexicalScope.binders scope
  change result.2.localBinders = initial.localBinders at binders
  refine ⟨inferExprFuel_nextLocal_le accepted, ?_, ?_⟩
  · intro localId _ absent
    simpa only [binders] using absent
  · intro localId _ absent occurrence ⟨node, member, sameId, readForm⟩
    have recorded := Detail.inferExprFuel_success_localIdentifier_record form allocation found accepted
    obtain ⟨fitted, fit, _, nodes⟩ := Detail.recordExpressionWithExpected_success_nodes recorded
    rw [nodes] at member
    rcases List.mem_append.mp member with old | fresh
    · have sameNodes := (Detail.withExpected_occurrenceState_eq fit).1
      rw [sameNodes] at old
      rw [State.addRequirementsWithIds_nodes] at old
      have allocatedEq : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
      change .expression node ∈ allocated.nodes at old
      rw [allocatedEq] at old
      exact ⟨node, old, sameId, readForm⟩
    · cases List.mem_singleton.mp fresh
      obtain ⟨actualName, actualForm⟩ := readForm
      have sameBinder : binder.id = localId := by cases actualForm; rfl
      have present := (State.lookupBinder?_eq_some_facts found).1
      have allocatedEq : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
      rw [allocatedEq] at present
      exact False.elim (absent binder present sameBinder)


theorem fresh (state : State) : Progress state state.fresh.2 := Fields.refl _ _ _

theorem freshTypes (count : Nat) (state : State) : Progress state (Detail.freshTypes count state).2 := by
  induction count generalizing state with
  | zero => exact .refl _
  | succ count ih => exact (fresh state).trans (ih state.fresh.2)

theorem freshDataConstructorInstantiation (dataType : ProgramDataSignature)
    (constructor : ProgramDataConstructorSignature) (state : State) :
    Progress state (Detail.freshDataConstructorInstantiation dataType constructor state).2 := by
  let step : List Ty × State → TypeParameterId → List Ty × State :=
    fun result _ => (result.1 ++ [result.2.fresh.1], result.2.fresh.2)
  have fold (parameters : List TypeParameterId) (accumulator : List Ty × State) :
      Progress accumulator.2 (parameters.foldl step accumulator).2 := by
    induction parameters generalizing accumulator with
    | nil => exact .refl _
    | cons parameter parameters ih => exact (fresh accumulator.2).trans (ih (step accumulator parameter))
  unfold Detail.freshDataConstructorInstantiation
  exact fold dataType.parameters ([], state)

theorem addRequirementWithId (state : State) (predicate : ProgramPredicate) :
    Progress state (state.addRequirementWithId predicate).2 := Fields.refl _ _ _

theorem addRequirementsWithIds (state : State) (predicates : List ProgramPredicate) :
    Progress state (state.addRequirementsWithIds predicates).2 := by
  induction predicates generalizing state with
  | nil => exact .refl _
  | cons predicate rest ih =>
      exact (addRequirementWithId state predicate).trans (ih (state.addRequirementWithId predicate).2)

theorem bindLambdaParameters {context : Context} {parameters : List Syntax.LambdaParameter}
    {index : Nat} {seen : List String} {state : State} {result : List TypedBinder × List Ty × State}
    (accepted : Detail.bindLambdaParameters context parameters index seen state = .ok result) :
    Progress state result.2.2 := by
  induction parameters generalizing index seen state result with
  | nil =>
      simp only [Detail.bindLambdaParameters, Except.ok.injEq] at accepted
      cases accepted
      exact .refl _
  | cons parameter rest ih =>
      cases form : parameter.value with
      | error => simp [Detail.bindLambdaParameters, form, bind, Except.bind] at accepted
      | inferred name =>
          simp only [Detail.bindLambdaParameters, form, bind, Except.bind] at accepted
          repeat' first | split at accepted
          all_goals try cases accepted
          all_goals try simp_all only [pure, Except.pure, Except.ok.injEq]
          all_goals try subst_vars
          all_goals have tail := ih (by assumption)
          all_goals exact (fresh state).trans ((allocateBinder _ _ _ _ _ _).trans tail)
      | typed marker name syntaxType =>
          simp only [Detail.bindLambdaParameters, form] at accepted
          cases resolved : resolveSourceType context syntaxType with
          | error error => simp [resolved, bind, Except.bind] at accepted
          | ok type =>
              simp only [resolved, bind, Except.bind] at accepted
              repeat' first | split at accepted
              all_goals try cases accepted
              all_goals try simp_all only [pure, Except.pure, Except.ok.injEq]
              all_goals try subst_vars
              all_goals have tail := ih (by assumption)
              all_goals exact (allocateBinder _ _ _ _ _ _).trans tail

theorem recordSelectedCallResult (source callee : Syntax.Expr) (name : String)
    (arguments : List InferredExpression) (attempt : CandidateAttemptResult)
    (result : InferredExpression) (trailing : List CoercionStep) (state : State) :
    Progress state (Detail.recordSelectedCallResult source callee name arguments attempt result trailing state).2 := by
  unfold Detail.recordSelectedCallResult
  apply (attachExpressionCoercions _ _).trans
  apply (recordNonlocal _ _ _ (.reference name (.declaration attempt.instantiation)) _ _ _
    (by intro _ _ impossible; cases impossible)).trans
  exact recordNonlocal _ _ _ (.call _ _ (.declaration attempt.instantiation)) _ _ _
    (by intro _ _ impossible; cases impossible)

theorem recordSelectedCall (source callee : Syntax.Expr) (name : String)
    (arguments : List InferredExpression) (attempt : CandidateAttemptResult) :
    Progress attempt.state (Detail.recordSelectedCall source callee name arguments attempt).2 :=
  recordSelectedCallResult _ _ _ _ _ _ _ _

theorem recordIndirectCall (source : Syntax.Expr) (callee : InferredExpression)
    (arguments : List InferredExpression) (result : IndirectApplicationResult) :
    Progress result.state (Detail.recordIndirectCall source callee arguments result).2 :=
  recordNonlocal _ _ _ _ _ _ _ (by intro _ _ impossible; cases impossible)


private theorem exceptPure_eq_ok {epsilon alpha : Type} (value result : alpha) :
    ((pure value : Except epsilon alpha) = .ok result) ↔ value = result := by
  change (Except.ok value = Except.ok result) ↔ value = result
  simp

private theorem exceptThrow_ne_ok {epsilon alpha : Type} (error : epsilon) (value : alpha) :
    (throw error : Except epsilon alpha) ≠ .ok value := by
  intro impossible
  cases impossible

private def Preserves {alpha : Type} (stateOf : alpha → State)
    (initial : State) (computation : Except Error alpha) : Prop :=
  ∀ result, computation = .ok result → Progress initial (stateOf result)

private theorem patternFlat (fuel : Nat) (context : Context) (pattern : Syntax.Pattern)
    (expected : Ty) (seen : List String) (state : State) :
    Preserves InferredPattern.state state
      (inferMatchPatternFlatFuel fuel context pattern expected seen state) := by
  apply inferMatchPatternFlatFuel.induct context
    (motive1 := fun fuel pattern expected seen state =>
      Preserves InferredPattern.state state
        (inferMatchPatternFlatFuel fuel context pattern expected seen state))
    (motive2 := fun fuel patterns expected seen state =>
      Preserves InferredPatterns.state state
        (inferMatchPatternsFlatFuel fuel context patterns expected seen state))
  all_goals
    intros
    unfold Preserves at *
    intro result success
    simp_all [inferMatchPatternFlatFuel, inferMatchPatternsFlatFuel, bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals try simp_all only [exceptPure_eq_ok, exceptThrow_ne_ok]
    all_goals try have unifyProgress := unify (by assumption)
    all_goals try specialize ih1 _ _ _ heq
    all_goals try specialize ih1 _ _ heq
    all_goals try specialize ih2 _ heq
    all_goals try exact allocateBinder _ _ _ _ _ _
    all_goals try exact Progress.refl _
    all_goals try assumption
    all_goals try exact addRequirementWithId _ _
    all_goals try exact (addRequirementWithId _ _).trans unifyProgress
    all_goals try simp_all only [Prod.mk.injEq]
    all_goals try subst_vars
    all_goals dsimp only [Progress, State.fresh, State.allocateBinder, State.addRequirementWithId] at *
    all_goals grind [Fields.trans, freshDataConstructorInstantiation, freshTypes]

theorem inferMatchPatternFuel {fuel : Nat} {context : Context} {pattern : Syntax.Pattern}
    {expected : Ty} {state : State} {result : TypedMatchPattern × State}
    (success : Detail.inferMatchPatternFuel fuel context pattern expected state = .ok result) :
    Progress state result.2 := by
  unfold Detail.inferMatchPatternFuel at success
  cases flatResult : inferMatchPatternFlatFuel fuel context pattern expected [] state with
  | error error => simp [flatResult, bind, Except.bind] at success
  | ok inferred =>
      simp only [flatResult, bind, Except.bind] at success
      change Except.ok ({
        source := inferred.source
        type := inferred.state.resolve expected
        resolution := inferred.resolution
        requirements := inferred.requirements
      }, inferred.state) = Except.ok result at success
      cases success
      exact patternFlat fuel context pattern expected [] state inferred flatResult


private theorem builtinArguments {arguments : List InferredExpression} {parameters : List Ty}
    {state next : State}
    (accepted : unifyBuiltinFunctionArgumentsEqual arguments parameters state = .ok next) :
    Progress state next := by
  induction arguments generalizing parameters state next with
  | nil =>
      simp only [unifyBuiltinFunctionArgumentsEqual, Except.ok.injEq] at accepted
      cases accepted
      exact .refl _
  | cons argument arguments ih =>
      cases parameters with
      | nil =>
          simp only [unifyBuiltinFunctionArgumentsEqual, Except.ok.injEq] at accepted
          cases accepted
          exact .refl _
      | cons parameter parameters =>
          simp only [unifyBuiltinFunctionArgumentsEqual] at accepted
          cases unified : Detail.unify state argument.type parameter with
          | error error => simp [unified, bind, Except.bind] at accepted
          | ok ready =>
              simp only [unified, bind, Except.bind] at accepted
              exact (unify unified).trans (ih accepted)

theorem recordBuiltinFunctionCall {source callee : Syntax.Expr} {name : String}
    {function : BuiltinFunctionId} {arguments : List InferredExpression}
    {call : ExpressionId} {expected : Option Ty} {state : State}
    {result : InferredExpression × State}
    (accepted : Detail.recordBuiltinFunctionCall source callee name function arguments call expected state = .ok result) :
    Progress state result.2 := by
  unfold Detail.recordBuiltinFunctionCall at accepted
  simp_all [bind, Except.bind]
  repeat' first | split at accepted
  all_goals try cases accepted
  all_goals try simp_all only [exceptPure_eq_ok, exceptThrow_ne_ok]
  all_goals try subst_vars
  all_goals have argumentsProgress := builtinArguments (by assumption)
  all_goals try have unifiedProgress := unify (by assumption)
  all_goals dsimp only [Progress, Detail.recordExpression, State.recordNode,
    State.allocateExpressionId] at *
  all_goals refine Fields.trans ?_ (Fields.expression _ _ _ _ ?_)
  all_goals try (intro _ _ impossible; cases impossible)
  all_goals refine Fields.trans ?_ (Fields.expression _ _ _ _ ?_)
  all_goals try (intro _ _ impossible; cases impossible)
  all_goals first
    | exact argumentsProgress
    | exact argumentsProgress.trans unifiedProgress

end Progress
end Solcore.Frontend.SourceInference.LocalReadScopeProgress
end

section
-- leanmerge: from Solcore.Frontend.SourceInference.LocalReadScopeInference
/-! Actual inference cannot create a reference to a retired older local ID.
Match recursion retains the genuine saved outer-scope membership. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace Solcore.Frontend.SourceInference.LocalReadScopeProgress
open TypeSystem Detail

@[simp] private theorem exceptPure_eq_ok {epsilon alpha : Type} (value result : alpha) :
    ((pure value : Except epsilon alpha) = .ok result) ↔ value = result := by
  change (Except.ok value = Except.ok result) ↔ value = result
  simp

private def PreservesScope {alpha : Type} (stateOf : alpha → State)
    (initial : State) (computation : Except Error alpha) : Prop :=
  ∀ result, computation = .ok result → Progress initial (stateOf result)

private theorem pair_success_scope_progress {alpha : Type}
    {operation : alpha × State} {value : alpha} {next initial : State}
    (operationSubset : Progress initial operation.2)
    (success : operation = (value, next)) :
    Progress initial next := by
  simpa [success] using operationSubset

private theorem pair_eq_property {alpha beta : Type} {result : alpha × beta}
    {property : beta → Prop}
    (invariant : ∀ value state, result = (value, state) → property state) :
    property result.2 := by
  rcases result with ⟨value, state⟩
  exact invariant value state rfl

private theorem pair_except_property {epsilon alpha beta : Type}
    {computation : Except epsilon (alpha × beta)} {result : alpha × beta}
    {property : beta → Prop}
    (invariant : ∀ value state,
      computation = .ok (value, state) → property state)
    (success : computation = .ok result) :
    property result.2 := by
  rcases result with ⟨value, state⟩
  exact invariant value state success

private theorem anchored_pair_except_property {epsilon alpha beta : Type}
    {anchor : alpha × State}
    {computation : alpha → State → Except epsilon (beta × State)}
    {initial state : State} {result : beta × State}
    (_anchorInvariant : ∀ value next,
      (Except.ok anchor : Except epsilon (alpha × State)) =
          Except.ok (value, next) →
        Progress initial next)
    (invariant : ∀ value state result next,
      computation value state = .ok (result, next) →
        Progress state next)
    (success : computation anchor.1 state = .ok result) :
    Progress state result.2 := by
  rcases anchor with ⟨value, anchorState⟩
  rcases result with ⟨result, next⟩
  exact invariant value state result next success


private theorem allocateExpressionId_success_scope_progress
    {state next : State} {id : ExpressionId}
    (success : state.allocateExpressionId = (id, next)) :
    Progress state next :=
  pair_success_scope_progress
    (Progress.refl state) success

private theorem allocateStatementId_success_scope_progress
    {state next : State} {id : StatementId}
    (success : state.allocateStatementId = (id, next)) :
    Progress state next :=
  pair_success_scope_progress
    (Progress.refl state) success

private theorem state_fresh_success_scope_progress
    {state next : State} {type : Ty}
    (success : state.fresh = (type, next)) :
    Progress state next :=
  pair_success_scope_progress (Progress.refl state)
    success

private theorem allocateHiddenLocal_success_scope_progress
    {state next : State} {id : Resolved.LocalId}
    (success : state.allocateHiddenLocal = (id, next)) :
    Progress state next :=
  pair_success_scope_progress
    (Progress.allocateHiddenLocal state) success

private theorem addRequirementWithId_success_scope_progress
    {state next : State} {predicate : ProgramPredicate}
    {requirement : RequirementId}
    (success : state.addRequirementWithId predicate = (requirement, next)) :
    Progress state next :=
  pair_success_scope_progress
    (Progress.addRequirementWithId state predicate) success

private theorem addRequirementsWithIds_success_scope_progress
    {state next : State} {predicates : List ProgramPredicate}
    {requirements : List RequirementId}
    (success : state.addRequirementsWithIds predicates = (requirements, next)) :
    Progress state next :=
  pair_success_scope_progress
    (Progress.addRequirementsWithIds state predicates) success

private theorem allocateBinder_success_scope_progress
    {state next : State} {name : String} {scheme : Scheme}
    {span : Option Syntax.SourceSpan} {comptime : Bool}
    {schemeRequirements : List LocalSchemeRequirement} {binder : TypedBinder}
    (success : state.allocateBinder name scheme span comptime
      schemeRequirements = (binder, next)) :
    Progress state next :=
  pair_success_scope_progress
    (Progress.allocateBinder state name scheme span comptime schemeRequirements) success

private theorem freshDataConstructorInstantiation_success_scope_progress
    {dataType : ProgramDataSignature}
    {constructor : ProgramDataConstructorSignature}
    {state next : State} {instantiation : DataConstructorInstantiation}
    (success : freshDataConstructorInstantiation dataType constructor state =
      (instantiation, next)) :
    Progress state next :=
  pair_success_scope_progress
    (Progress.freshDataConstructorInstantiation dataType constructor
      state) success

private theorem freshTypes_success_scope_progress
    {count : Nat} {state next : State} {types : List Ty}
    (success : freshTypes count state = (types, next)) :
    Progress state next :=
  pair_success_scope_progress
    (Progress.freshTypes count state) success

private theorem syntheticTuple_result_scope_progress
    {elements : List InferredExpression} {span : Syntax.SourceSpan}
    {state : State} {result : InferredExpression × State}
    (success : (pure ({
        id := state.allocateExpressionId.fst
        type := Ty.productMany (elements.map (·.type))
      }, state.allocateExpressionId.snd.recordNode (.expression {
        id := state.allocateExpressionId.fst
        span
        type := Ty.productMany (elements.map (·.type))
        form := .tuple (elements.map (·.id))
      })) : Except Error (InferredExpression × State)) = .ok result) :
    Progress state result.snd := by
  have resultEq : ({
      id := state.allocateExpressionId.fst
      type := Ty.productMany (elements.map (·.type))
    }, state.allocateExpressionId.snd.recordNode (.expression {
      id := state.allocateExpressionId.fst
      span
      type := Ty.productMany (elements.map (·.type))
      form := .tuple (elements.map (·.id))
    })) = result := by
    simpa only [exceptPure_eq_ok] using success
  rw [← resultEq]
  exact Progress.recordExpression _ _ (by intro _ _ impossible; cases impossible)

private theorem syntheticTuple_pair_scope_progress
    {elements : List InferredExpression} {span : Syntax.SourceSpan}
    {state : State} {result : InferredExpression × State}
    (success : ({
        id := state.allocateExpressionId.fst
        type := Ty.productMany (elements.map (·.type))
      }, state.allocateExpressionId.snd.recordNode (.expression {
        id := state.allocateExpressionId.fst
        span
        type := Ty.productMany (elements.map (·.type))
        form := .tuple (elements.map (·.id))
      })) = result) :
    Progress state result.snd := by
  rw [← success]
  exact Progress.recordExpression _ _ (by intro _ _ impossible; cases impossible)

private theorem pure_pair_result_scope_progress {epsilon alpha : Type}
    {value : alpha} {next initial : State} {result : alpha × State}
    (nextSubset : Progress initial next)
    (success : (pure (value, next) : Except epsilon (alpha × State)) =
      .ok result) :
    Progress initial result.snd := by
  have resultEq : (value, next) = result := by
    simpa only [exceptPure_eq_ok] using success
  rw [← resultEq]
  exact nextSubset

private theorem restored_pair_result_scope_progress {alpha : Type}
    {value : alpha} {state initial : State} {scope : LexicalScope}
    {result : alpha × State}
    (subset : Progress initial state)
    (saved : scope.binders ⊆ initial.localBinders)
    (success : (value, state.restoreLexicalScope scope) = result) :
    Progress initial result.snd := by
  rw [← success]
  exact Fields.restore subset saved


private theorem hidden_start {next after : Nat} {binders afterBinders : List TypedBinder}
    {nodes afterNodes : List Node}
    (progress : Fields (next + 1) binders nodes after afterBinders afterNodes) :
    Fields next binders nodes after afterBinders afterNodes :=
  Fields.trans (Fields.advance _ _ _ _ (Nat.le_succ _)) progress

private theorem restored_start {next after : Nat} {binders afterBinders : List TypedBinder}
    {nodes afterNodes : List Node}
    (progress : Fields next binders nodes after afterBinders afterNodes) :
    Fields next binders nodes after binders afterNodes :=
  Fields.restore progress (fun _ member => member)

private theorem restored_then {bn mn an : Nat} {bb mb ab : List TypedBinder}
    {bs ms ads : List Node}
    (initialStep : Fields bn bb bs mn mb ms)
    (suffix : Fields mn bb ms an ab ads) : Fields bn bb bs an ab ads :=
  Fields.trans (Fields.restore initialStep (fun _ member => member)) suffix

private theorem restored_saved_then {bn mn an : Nat} {bb mb ab outer : List TypedBinder}
    {bs ms ads : List Node}
    (initialStep : Fields bn bb bs mn mb ms) (saved : outer ⊆ bb)
    (suffix : Fields mn outer ms an ab ads) : Fields bn bb bs an ab ads :=
  Fields.trans (Fields.restore initialStep saved) suffix

private theorem binders_self (binders : List TypedBinder) : binders ⊆ binders :=
  fun _ member => member

set_option maxHeartbeats 2000000 in
private theorem inferFuel_scope_progress_internal :
    (∀ fuel context expression expected state,
      PreservesScope Prod.snd state
        (inferExprFuel fuel context expression expected state)) ∧
    (∀ fuel context source id instantiation arguments expected state,
      PreservesScope Prod.snd state
        (inferConstructorApplicationFuel fuel context source id instantiation
          arguments expected state)) ∧
    (∀ fuel context sources expected state,
      PreservesScope Prod.snd state
        (inferConstructorArgumentsFuel fuel context sources expected state)) ∧
    (∀ fuel context statements expectedReturn state,
      PreservesScope BlockResult.state state
        (inferStatementsFuel fuel context statements expectedReturn state)) ∧
    (∀ fuel context statement expectedReturn state,
      PreservesScope StatementResult.state state
        (inferStatementFuel fuel context statement expectedReturn state)) ∧
    (∀ fuel context items state,
      PreservesScope InferredForItems.state state
        (inferForItemsFuel fuel context items state)) ∧
    (∀ fuel context item state,
      PreservesScope Prod.snd state
        (inferForItemFuel fuel context item state)) ∧
    (∀ fuel context target state,
      PreservesScope Prod.snd state
        (inferPlaceFuel fuel context target state)) ∧
    (∀ fuel context target operator value state,
      PreservesScope (fun result => result.2.2) state
        (inferAssignedValueFuel fuel context target operator value state)) ∧
    (∀ fuel context expressions state,
      PreservesScope Prod.snd state
        (inferExprsFuel fuel context expressions state)) ∧
    (∀ fuel context scrutineeType expectedReturn outerScope cases state,
      outerScope.binders ⊆ state.localBinders →
      PreservesScope MatchCasesResult.state state
        (inferMatchCasesFuel fuel context scrutineeType expectedReturn outerScope
          cases state)) := by
  apply inferExprFuel.mutual_induct
    (motive1 := fun fuel context expression expected state =>
      PreservesScope Prod.snd state
        (inferExprFuel fuel context expression expected state))
    (motive2 := fun fuel context source id instantiation arguments expected
        state =>
      PreservesScope Prod.snd state
        (inferConstructorApplicationFuel fuel context source id instantiation
          arguments expected state))
    (motive3 := fun fuel context sources expected state =>
      PreservesScope Prod.snd state
        (inferConstructorArgumentsFuel fuel context sources expected state))
    (motive4 := fun fuel context statements expectedReturn state =>
      PreservesScope BlockResult.state state
        (inferStatementsFuel fuel context statements expectedReturn state))
    (motive5 := fun fuel context statement expectedReturn state =>
      PreservesScope StatementResult.state state
        (inferStatementFuel fuel context statement expectedReturn state))
    (motive6 := fun fuel context items state =>
      PreservesScope InferredForItems.state state
        (inferForItemsFuel fuel context items state))
    (motive7 := fun fuel context item state =>
      PreservesScope Prod.snd state
        (inferForItemFuel fuel context item state))
    (motive8 := fun fuel context target state =>
      PreservesScope Prod.snd state
        (inferPlaceFuel fuel context target state))
    (motive9 := fun fuel context target operator value state =>
      PreservesScope (fun result => result.2.2) state
        (inferAssignedValueFuel fuel context target operator value state))
    (motive10 := fun fuel context expressions state =>
      PreservesScope Prod.snd state
        (inferExprsFuel fuel context expressions state))
    (motive11 := fun fuel context scrutineeType expectedReturn outerScope
        cases state =>
      outerScope.binders ⊆ state.localBinders →
      PreservesScope MatchCasesResult.state state
        (inferMatchCasesFuel fuel context scrutineeType expectedReturn outerScope
          cases state))
  case case44 =>
    intros context statement expectedReturn state fuel id stateAfterId
      statementIdEq scrutinees arms statementEq sources notSingleton
      casesInduction bodyInduction expressionsInduction
    unfold PreservesScope at *
    intro result success
    have statementIdSubset :=
      allocateStatementId_success_scope_progress statementIdEq
    unfold inferStatementFuel at success
    simp only [statementIdEq, statementEq, bind, Except.bind] at success
    repeat' first | split at success
    all_goals try cases success
    all_goals try exact (notSingleton _ (by assumption)).elim
    all_goals try have expressionsSubset :=
      expressionsInduction _ (by assumption)
    all_goals try have casesSubset :=
      casesInduction _ _ (fun _ member => member) _ (by assumption)
    all_goals try have bodySubset :=
      bodyInduction _ _ _ (by assumption)
    all_goals try have tupleSubset :=
      syntheticTuple_result_scope_progress (by assumption)
    all_goals try have tupleSubset :=
      syntheticTuple_pair_scope_progress (by assumption)
    all_goals try have defaultSubset :=
      pure_pair_result_scope_progress casesSubset (by assumption)
    all_goals simp_all only [exceptPure_eq_ok]
    all_goals try have restoredSubset :=
      restored_pair_result_scope_progress bodySubset (by simpa only [State.lexicalScope] using (List.Subset.refl _)) (by assumption)
    all_goals try
      have restoredWhole := restored_pair_result_scope_progress
        (Progress.trans casesSubset bodySubset) (fun _ member => member) (by assumption)
    all_goals try simp_all
    all_goals try exact Progress.refl _
    all_goals try exact Progress.refl _
    all_goals try exact Progress.recordStatement _ _
    all_goals try dsimp only [Progress,
      State.recordNode, State.allocateExpressionId, State.allocateStatementId,
      State.allocateHiddenLocal, State.allocateBinder, State.restoreLexicalScope,
      State.withLocals, State.fresh, State.lexicalScope, State.addRequirementWithId, State.addRequirementsWithIds, recordExpression, recordIndirectCall]
    all_goals try dsimp only [Progress, State.recordNode, State.allocateExpressionId,
      State.allocateStatementId, State.allocateHiddenLocal, State.allocateBinder,
      State.restoreLexicalScope, State.withLocals, State.fresh, State.lexicalScope, State.addRequirementWithId, State.addRequirementsWithIds,
      Detail.recordExpression, Detail.recordIndirectCall] at *
    all_goals first
      | apply Fields.trans (second := Fields.statement _ _ _ _)
      | apply Fields.trans (second := Fields.expression _ _ _ _
          (by change ∀ _ _, (.call _ _ (.indirect _) : ExpressionForm) = _ → _; intro _ _ impossible; cases impossible))
      | apply Fields.trans (second := Fields.expression _ _ _ _
          (by change ∀ _ _, (.constructor _ _ : ExpressionForm) = _ → _; intro _ _ impossible; cases impossible))
      | skip
    all_goals try
      exact Fields.trans statementIdSubset
        (Fields.trans expressionsSubset (Fields.trans tupleSubset (hidden_start restoredWhole)))
    all_goals try solve | grind [Fields.trans, Fields.restore, Fields.refl, hidden_start, restored_start, restored_then, restored_saved_then, binders_self]
  case case70 =>
    intros fuel context target operator value state placeInduction valueInduction
    unfold PreservesScope at *
    intro result success
    unfold inferAssignedValueFuel at success
    simp_all [bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals try simp_all only [exceptPure_eq_ok]
    all_goals try rcases v with ⟨place, placeState⟩
    all_goals try rcases v_2 with ⟨inferred, resultState⟩
    all_goals
      have placeSubset := pair_except_property placeInduction rfl
    all_goals try have valueSubset :=
      valueInduction place v_1 inferred resultState (by assumption)
    all_goals try
      have valueSubset := anchored_pair_except_property placeInduction
        valueInduction (by assumption)
    all_goals try have valueSubset :=
      pair_except_property (valueInduction _ _) (by assumption)
    all_goals try have unifiedSubset :=
      Progress.unify (by assumption)
    all_goals simp_all
    all_goals try exact Progress.refl _
    all_goals try exact Progress.refl _
    all_goals try exact Progress.recordStatement _ _
    all_goals try dsimp only [Progress,
      State.recordNode, State.allocateExpressionId, State.allocateStatementId,
      State.allocateHiddenLocal, State.allocateBinder, State.restoreLexicalScope,
      State.withLocals, State.fresh, State.lexicalScope, State.addRequirementWithId, State.addRequirementsWithIds, recordExpression, recordIndirectCall]
    all_goals try dsimp only [Progress, State.recordNode, State.allocateExpressionId,
      State.allocateStatementId, State.allocateHiddenLocal, State.allocateBinder,
      State.restoreLexicalScope, State.withLocals, State.fresh, State.lexicalScope, State.addRequirementWithId, State.addRequirementsWithIds,
      Detail.recordExpression, Detail.recordIndirectCall] at *
    all_goals first
      | apply Fields.trans (second := Fields.statement _ _ _ _)
      | apply Fields.trans (second := Fields.expression _ _ _ _
          (by change ∀ _ _, (.call _ _ (.indirect _) : ExpressionForm) = _ → _; intro _ _ impossible; cases impossible))
      | apply Fields.trans (second := Fields.expression _ _ _ _
          (by change ∀ _ _, (.constructor _ _ : ExpressionForm) = _ → _; intro _ _ impossible; cases impossible))
      | skip
    all_goals try solve | grind [Fields.trans, Fields.restore, Fields.refl, hidden_start, restored_start, binders_self]
  case case67 =>
    unfold PreservesScope at *
    intros
    simp_all only [inferPlaceFuel]
  all_goals
    intros
    unfold PreservesScope at *
    intro result success
    try exact Progress.localIdentifier (by assumption) (by assumption) (by assumption) success
  all_goals
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
    try simp_all [bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals try simp_all only [exceptPure_eq_ok]
    all_goals try rcases v with ⟨v0a, v0b⟩
    all_goals try rcases v_1 with ⟨v1a, v1b⟩
    all_goals try rcases v_2 with ⟨v2a, v2b⟩
    all_goals try rcases v_3 with ⟨v3a, v3b⟩
    all_goals try rcases v_4 with ⟨v4a, v4b⟩
    all_goals try subst_vars
    all_goals first
      | have ih1Subset := pair_eq_property ih1
      | have ih1Subset := pair_except_property ih1 (by assumption)
      | have ih1Subset := pair_except_property (ih1 _ _) (by assumption)
      | skip
    all_goals first
      | have ih2Subset := pair_eq_property ih2
      | have ih2Subset := pair_except_property ih2 (by assumption)
      | have ih2Subset := pair_except_property (ih2 _ _) (by assumption)
      | skip
    all_goals first
      | have ih3Subset := pair_eq_property ih3
      | have ih3Subset := pair_except_property ih3 (by assumption)
      | have ih3Subset := pair_except_property (ih3 _ _) (by assumption)
      | skip
    all_goals try have unifiedSubset :=
      Progress.unify (by assumption)
    all_goals try have expressionIdSubset :=
      allocateExpressionId_success_scope_progress (by assumption)
    all_goals try have statementIdSubset :=
      allocateStatementId_success_scope_progress (by assumption)
    all_goals try have freshSubset :=
      state_fresh_success_scope_progress (by assumption)
    all_goals try have hiddenLocalSubset :=
      allocateHiddenLocal_success_scope_progress (by assumption)
    all_goals try have requirementSubset :=
      addRequirementWithId_success_scope_progress (by assumption)
    all_goals try have requirementsSubset :=
      addRequirementsWithIds_success_scope_progress (by assumption)
    all_goals try have binderSubset :=
      allocateBinder_success_scope_progress (by assumption)
    all_goals try have constructorSubset :=
      freshDataConstructorInstantiation_success_scope_progress (by
        assumption)
    all_goals try have typesSubset :=
      freshTypes_success_scope_progress (by assumption)
    all_goals try have recordSubset :=
      Progress.recordExpressionWithExpected (by assumption) (by intro _ _ impossible; cases impossible)
    all_goals try have issuedRecord :=
      (Progress.addRequirementWithId _ _).trans recordSubset
    all_goals try have batchRecord :=
      (Progress.addRequirementsWithIds _ _).trans recordSubset
    all_goals try exact Fields.trans expressionIdSubset (Fields.trans (Progress.addRequirementWithId _ _) recordSubset)
    all_goals try exact Fields.trans expressionIdSubset (Fields.trans (Progress.addRequirementsWithIds _ _) recordSubset)
    all_goals try have lambdaSubset :=
      Progress.bindLambdaParameters (by assumption)
    all_goals try have afterLambdaSubset := Progress.trans lambdaSubset unifiedSubset
    all_goals try have patternSubset :=
      Progress.inferMatchPatternFuel (by assumption)
    all_goals try have unarySubset :=
      Progress.inferUnaryOperator (by assumption)
    all_goals try have binarySubset :=
      Progress.inferBinaryOperator (by assumption)
    all_goals try have selectionSubset :=
      Progress.selectFunctionCandidateFrom (by assumption)
    all_goals try have expectedSubset :=
      Progress.withExpected (by assumption)
    all_goals try have applicationSubset :=
      Progress.applyFunctionType (by assumption)
    all_goals try have builtinSubset :=
      Progress.recordBuiltinFunctionCall (by assumption)
    all_goals try simp_all
    all_goals try exact Progress.addRequirementWithId _ _
    all_goals try exact Progress.refl _
    all_goals try exact Progress.refl _
    all_goals try exact Progress.recordStatement _ _
    all_goals try dsimp only [Progress,
      State.recordNode, State.allocateExpressionId, State.allocateStatementId,
      State.allocateHiddenLocal, State.allocateBinder, State.restoreLexicalScope,
      State.withLocals, State.fresh, State.lexicalScope, State.addRequirementWithId, State.addRequirementsWithIds, recordExpression, recordIndirectCall]
    all_goals try dsimp only [Progress, State.recordNode, State.allocateExpressionId,
      State.allocateStatementId, State.allocateHiddenLocal, State.allocateBinder,
      State.restoreLexicalScope, State.withLocals, State.fresh, State.lexicalScope, State.addRequirementWithId, State.addRequirementsWithIds,
      Detail.recordExpression, Detail.recordIndirectCall] at *
    all_goals first
      | apply Fields.trans (second := Fields.statement _ _ _ _)
      | apply Fields.trans (second := Fields.expression _ _ _ _
          (by change ∀ _ _, (.call _ _ (.indirect _) : ExpressionForm) = _ → _; intro _ _ impossible; cases impossible))
      | apply Fields.trans (second := Fields.expression _ _ _ _
          (by change ∀ _ _, (.constructor _ _ : ExpressionForm) = _ → _; intro _ _ impossible; cases impossible))
      | skip
    all_goals try solve | grind
      [Fields.trans, Fields.restore, Fields.refl, hidden_start, restored_start, binders_self,
        Progress.unify, Progress.addRequirementWithId,
        Progress.addRequirementsWithIds,
        Progress.freshDataConstructorInstantiation,
        Progress.freshTypes,

        Progress.recordSelectedCallResult,
        Progress.recordSelectedCall,
        Progress.recordIndirectCall, Progress.recordStatement, Progress.modifyStatementNode]
  all_goals expose_names
  all_goals try solve
    | apply Fields.trans expressionIdSubset
      apply Fields.trans (ih2 v.fst v.snd rfl)
      apply Fields.trans (ih1 v.snd v_1.fst v_1.snd heq_1)
      apply Fields.trans selectionSubset
      apply Fields.trans expectedSubset
      exact Progress.recordSelectedCallResult _ _ _ _ _ _ _ _
  all_goals try solve
    | exact Fields.trans expressionIdSubset
        (restored_then (Fields.trans (Progress.trans lambdaSubset (Progress.unify heq_2))
          (Fields.trans (ih1 v_2 v_1 v_3 heq_4) unifiedSubset)) recordSubset)
  all_goals try solve
    | exact Fields.trans expressionIdSubset
        (restored_then (Fields.trans (Progress.trans lambdaSubset (Progress.unify heq_2))
          (Fields.trans (ih1 snd_1 v_1 v_2 heq_4) unifiedSubset)) recordSubset)
  all_goals try solve
    | exact Fields.trans expressionIdSubset
        (restored_then (Fields.trans lambdaSubset
          (Fields.trans (ih1 v_1 v.2.2 v_2 heq_3) unifiedSubset)) recordSubset)
  all_goals try solve
    | exact Fields.trans expressionIdSubset
        (restored_then (Fields.trans lambdaSubset
          (Fields.trans (ih1 v.2.2.fresh.1 v.2.2.fresh.2 v_1 heq_2) unifiedSubset)) recordSubset)
  all_goals try solve
    | have sameSource : source = source_1 := by grind
      rw [sameSource] at ih1
      have expressionStep := ih1 v.fst v.snd heq_1
      have casesStep := ih3 v.fst v.snd.allocateHiddenLocal.2 (fun _ member => member) v_1 heq_2
      exact Fields.trans statementIdSubset (Fields.trans expressionStep (hidden_start casesStep))
  all_goals try solve
    | have sameSource : source = source_1 := by grind
      rw [sameSource] at ih1
      have expressionStep := ih1 v.fst v.snd heq_1
      have casesStep := ih3 v.fst v.snd.allocateHiddenLocal.2 (fun _ member => member) v_1 heq_2
      have bodyStep := ih2 v_1 elseBody_1 v_2 heq_4
      exact Fields.trans statementIdSubset
        (Fields.trans expressionStep (restored_start (hidden_start (Fields.trans casesStep bodyStep))))
  all_goals try solve
    | have conditionStep := ih3 v v_1.fst v_1.snd heq_1
      have bodyStep := ih2 v_1.snd v_2 heq_2
      have postStep := ih1 v v_2 v_3 heq_3
      exact Fields.trans statementIdSubset
        (restored_start (Fields.trans ih4 (restored_then (Fields.trans conditionStep bodyStep) postStep)))
  all_goals try solve
    | have bodyStep := ih2 v.snd v_1 heq_1
      have tailStep := ih1 v_1 (fun _ member => member) v_2 heq_2
      exact Fields.trans (Fields.restore (Fields.trans patternSubset bodyStep) h) tailStep

  all_goals try solve
    | have conditionStep := ih3 v.fst v.snd rfl
      have thenStep := ih2 v.snd v_1 heq_1
      have elseStep := ih1 v.snd v_1 elseBody_1 v_2 heq_2
      exact Fields.trans statementIdSubset
        (Fields.trans conditionStep (restored_start (restored_then thenStep elseStep)))

  all_goals try solve
    | refine Fields.trans ?_ (Fields.allocate _ _ _ _ ?_)
      · grind [Fields.trans, Fields.refl]
      · rfl


theorem inferExprFuel_scope_progress
    {fuel : Nat} {context : Context} {expression : Syntax.Expr}
    {expected : Option Ty} {state : State}
    {result : InferredExpression × State}
    (success : inferExprFuel fuel context expression expected state =
      .ok result) :
    Progress state result.2 := by
  exact inferFuel_scope_progress_internal.1 fuel context expression
    expected state result success

theorem inferConstructorApplicationFuel_scope_progress
    {fuel : Nat} {context : Context} {source : Syntax.Expr}
    {id : ExpressionId} {instantiation : DataConstructorInstantiation}
    {arguments : List Syntax.Expr} {expected : Option Ty} {state : State}
    {result : InferredExpression × State}
    (success : inferConstructorApplicationFuel fuel context source id
      instantiation arguments expected state = .ok result) :
    Progress state result.2 := by
  exact inferFuel_scope_progress_internal.2.1 fuel context source id
    instantiation arguments expected state result success

theorem inferConstructorArgumentsFuel_scope_progress
    {fuel : Nat} {context : Context} {sources : List Syntax.Expr}
    {expected : List Ty} {state : State}
    {result : List InferredExpression × State}
    (success : inferConstructorArgumentsFuel fuel context sources expected
      state = .ok result) :
    Progress state result.2 := by
  exact inferFuel_scope_progress_internal.2.2.1 fuel context sources
    expected state result success

theorem inferStatementsFuel_scope_progress
    {fuel : Nat} {context : Context} {statements : List Syntax.Statement}
    {expectedReturn : Ty} {state : State} {result : BlockResult}
    (success : inferStatementsFuel fuel context statements expectedReturn state =
      .ok result) :
    Progress state result.state := by
  exact inferFuel_scope_progress_internal.2.2.2.1 fuel context
    statements expectedReturn state result success

theorem inferStatementFuel_scope_progress
    {fuel : Nat} {context : Context} {statement : Syntax.Statement}
    {expectedReturn : Ty} {state : State} {result : StatementResult}
    (success : inferStatementFuel fuel context statement expectedReturn state =
      .ok result) :
    Progress state result.state := by
  exact inferFuel_scope_progress_internal.2.2.2.2.1 fuel context
    statement expectedReturn state result success

theorem inferForItemsFuel_scope_progress
    {fuel : Nat} {context : Context} {items : List Syntax.ForItem}
    {state : State} {result : InferredForItems}
    (success : inferForItemsFuel fuel context items state = .ok result) :
    Progress state result.state := by
  exact inferFuel_scope_progress_internal.2.2.2.2.2.1 fuel context
    items state result success

theorem inferForItemFuel_scope_progress
    {fuel : Nat} {context : Context} {item : Syntax.ForItem}
    {state : State} {result : ForItemForm × State}
    (success : inferForItemFuel fuel context item state = .ok result) :
    Progress state result.2 := by
  exact inferFuel_scope_progress_internal.2.2.2.2.2.2.1 fuel context
    item state result success

theorem inferPlaceFuel_scope_progress
    {fuel : Nat} {context : Context} {target : Syntax.Expr}
    {state : State} {result : PlaceResolution × State}
    (success : inferPlaceFuel fuel context target state = .ok result) :
    Progress state result.2 := by
  exact inferFuel_scope_progress_internal.2.2.2.2.2.2.2.1 fuel
    context target state result success

theorem inferAssignedValueFuel_scope_progress
    {fuel : Nat} {context : Context} {target : Syntax.Expr}
    {operator : Syntax.ValueAssignOp} {value : Syntax.Expr} {state : State}
    {result : AssignmentResolution × InferredExpression × State}
    (success : inferAssignedValueFuel fuel context target operator value state =
      .ok result) :
    Progress state result.2.2 := by
  exact inferFuel_scope_progress_internal.2.2.2.2.2.2.2.2.1 fuel
    context target operator value state result success

theorem inferExprsFuel_scope_progress
    {fuel : Nat} {context : Context} {expressions : List Syntax.Expr}
    {state : State} {result : List InferredExpression × State}
    (success : inferExprsFuel fuel context expressions state = .ok result) :
    Progress state result.2 := by
  exact inferFuel_scope_progress_internal.2.2.2.2.2.2.2.2.2.1 fuel
    context expressions state result success

theorem inferMatchCasesFuel_scope_progress
    {fuel : Nat} {context : Context} {scrutineeType expectedReturn : Ty}
    {outerScope : LexicalScope} {cases : List Syntax.MatchCase}
    {state : State} {result : MatchCasesResult}
    (saved : outerScope.binders ⊆ state.localBinders)
    (success : inferMatchCasesFuel fuel context scrutineeType expectedReturn
      outerScope cases state = .ok result) :
    Progress state result.state := by
  exact inferFuel_scope_progress_internal.2.2.2.2.2.2.2.2.2.2 fuel
    context scrutineeType expectedReturn outerScope cases state saved result success

end Solcore.Frontend.SourceInference.LocalReadScopeProgress
end
