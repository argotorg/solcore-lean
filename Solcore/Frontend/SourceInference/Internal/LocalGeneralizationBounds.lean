import Solcore.Frontend.SourceInference.Internal.LocalGeneralization
import Solcore.Frontend.SourceInference.Internal.LocalReadScopes

/-!
# Local generalization bounds

The bounded event traversal of local generalization.
-/

section
-- leanmerge: from Solcore.Frontend.SourceInference.LocalGeneralizationBoundedProgress
/-! A traversal distinguishes declarations already present on entry from the
new generalization events it creates. Only new events use the traversal's
allocator cutoff to justify restoring its saved outer lexical scope. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.Frontend.SourceInference.LocalGeneralizationBoundaries
open TypeSystem Detail
open LocalGeneralizationEvents (Ready)

def PriorStatement (nodes : List Node) (node : StatementNode) : Prop :=
  ∃ prior : StatementNode, .statement prior ∈ nodes ∧ prior.id = node.id ∧ prior.form = node.form

def Coverage (entry : State) (state : State) : Prop :=
  ∀ node : StatementNode, .statement node ∈ state.nodes →
    PriorStatement entry.nodes node ∨ StatementSince entry.nextLocal state node

structure Progress (before after : State) : Prop where
  reads : LocalReadEvents.Progress before after
  scope : LocalReadScopeProgress.Progress before after
  binders : before.LocalBindersBelowNextLocal → after.LocalBindersBelowNextLocal
  events : Ready before → before.LocalBindersBelowNextLocal → Coverage before after

namespace Progress

theorem of_retained {before after : State}
    (retained : ∀ node : StatementNode, .statement node ∈ after.nodes → PriorStatement before.nodes node)
    (reads : LocalReadEvents.Progress before after)
    (scope : LocalReadScopeProgress.Progress before after)
    (binders : before.LocalBindersBelowNextLocal → after.LocalBindersBelowNextLocal) : Progress before after :=
  ⟨reads, scope, binders, fun _ _ node member => .inl (retained node member)⟩

theorem refl (state : State) : Progress state state := by
  refine ⟨LocalReadEvents.Progress.refl _, LocalReadScopeProgress.Progress.refl _, fun below => below, ?_⟩
  intro _ _ node present
  exact .inl ⟨node, present, rfl, rfl⟩

theorem trans {before middle after : State} (first : Progress before middle) (second : Progress middle after) :
    Progress before after := by
  refine ⟨first.reads.trans second.reads, first.scope.trans second.scope,
    fun below => second.binders (first.binders below), ?_⟩
  intro ready below node present
  rcases second.events (ready.progress first.reads) (first.binders below) node present with old | fresh
  · obtain ⟨prior, member, sameId, sameForm⟩ := old
    rcases first.events ready below prior member with old | fresh
    · obtain ⟨original, present, originalId, originalForm⟩ := old
      exact .inl ⟨original, present, originalId.trans sameId, originalForm.trans sameForm⟩
    · exact .inr ((fresh.progress second.scope).same_form sameForm.symm)
  · exact .inr (fresh.weaken first.scope.next)

/-- Existing entry nodes stay classified as entry nodes. New events carry the
entry cutoff, so scope restoration uses real earlier binder identities. -/
theorem restore {before state : State} (progress : Progress before state) (scope : LexicalScope)
    (saved : scope.binders ⊆ before.localBinders) : Progress before (state.restoreLexicalScope scope) := by
  refine ⟨progress.reads, progress.scope.restore saved, ?_, ?_⟩
  · intro below binder member
    exact Nat.lt_of_lt_of_le (below binder (saved member)) progress.scope.next
  · intro ready below node present
    rcases progress.events ready below node present with old | fresh
    · exact .inl old
    · exact .inr (fresh.restore_saved scope saved below (Nat.le_refl _))

theorem of_nodes_eq {before after : State}
    (nodes : after.nodes = before.nodes) (reads : LocalReadEvents.Progress before after)
    (scope : LocalReadScopeProgress.Progress before after)
    (binders : before.LocalBindersBelowNextLocal → after.LocalBindersBelowNextLocal) : Progress before after := by
  refine ⟨reads, scope, binders, ?_⟩
  intro _ _ node member
  exact .inl ⟨node, nodes ▸ member, rfl, rfl⟩

theorem recordStatement (state : State) (node : StatementNode)
    (event : StatementSince state.nextLocal state node) : Progress state (state.recordNode (.statement node)) := by
  refine ⟨LocalReadEvents.Progress.recordStatement _ _, LocalReadScopeProgress.Progress.recordStatement _ _,
    fun below => below, ?_⟩
  intro _ _ actual member
  rcases List.mem_append.mp member with old | fresh
  · exact .inl ⟨actual, old, rfl, rfl⟩
  · cases List.mem_singleton.mp fresh
    exact .inr (event.progress (LocalReadScopeProgress.Progress.recordStatement _ _))

/-- An append of an expression cannot introduce a declaration event. The
actual expression rule supplies its read ledger and binder-scope evidence. -/
theorem appendExpression {before after : State} (node : ExpressionNode)
    (nodes : after.nodes = before.nodes ++ [.expression node])
    (reads : LocalReadEvents.Progress before after)
    (scope : LocalReadScopeProgress.Progress before after)
    (binders : before.LocalBindersBelowNextLocal → after.LocalBindersBelowNextLocal) : Progress before after := by
  refine ⟨reads, scope, binders, ?_⟩
  intro _ _ statement present
  rw [nodes] at present
  rcases List.mem_append.mp present with old | fresh
  · exact .inl ⟨statement, old, rfl, rfl⟩
  · cases List.mem_singleton.mp fresh

/-- A genuine map which retains statement identity and form creates no new
generalization event; expression coercion changes are permitted. -/
theorem mapNodes {before after : State} (modify : Node → Node)
    (nodes : after.nodes = before.nodes.map modify)
    (statements : ∀ source target, modify source = .statement target →
      ∃ prior : StatementNode, source = .statement prior ∧ prior.id = target.id ∧ prior.form = target.form)
    (reads : LocalReadEvents.Progress before after)
    (scope : LocalReadScopeProgress.Progress before after)
    (binders : before.LocalBindersBelowNextLocal → after.LocalBindersBelowNextLocal) : Progress before after := by
  refine ⟨reads, scope, binders, ?_⟩
  intro _ _ statement present
  rw [nodes] at present
  obtain ⟨source, member, same⟩ := List.mem_map.mp present
  obtain ⟨prior, sourceForm, sameId, sameForm⟩ := statements source statement same
  exact .inl ⟨prior, sourceForm ▸ member, sameId, sameForm⟩

end Progress
end Solcore.Frontend.SourceInference.LocalGeneralizationBoundaries
end

section
-- leanmerge: from Solcore.Frontend.SourceInference.InitializedBinderAllocation
/-! The existing event traversal bounds every recorded initialized binder by
the actual local allocator. This includes initialized for-header binders. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.Frontend.SourceInference.LocalGeneralizationBoundaries
open TypeSystem Detail
open LocalGeneralizationEvents (Ready)

def InitializedBindersAllocated (state : State) : Prop :=
  ∀ node ∈ state.nodes, ∀ binder ∈ node.initializedLetBinders,
    binder.id.binderIndex ≤ state.nextLocal

theorem InitializedBindersAllocated.empty {state : State} (empty : state.nodes = []) :
    InitializedBindersAllocated state := by
  intro node member
  rw [empty] at member
  cases member

/-- A boundary records the exact binder allocated after its initializer. -/
theorem Boundary.binderIndex {binder : TypedBinder} {initializer : ExpressionId}
    {low high : Nat} {nodes : List Node}
    (boundary : Boundary binder initializer low high nodes) :
    binder.id.binderIndex = high := by
  cases boundary with
  | statement receipt _ _ => rfl
  | header receipt _ _ => rfl

theorem OriginSince.allocated {entry : Nat} {state : State}
    {binder : TypedBinder} {initializer : ExpressionId}
    (origin : OriginSince entry state binder initializer) :
    binder.id.binderIndex ≤ state.nextLocal := by
  obtain ⟨low, high, nodes, _, boundary, barrier⟩ := origin
  rw [boundary.binderIndex]
  exact barrier.allocated

theorem ItemSince.allocated {entry : Nat} {state : State} {item : ForItemForm}
    (origin : ItemSince entry state item) :
    ∀ binder ∈ item.initializedLetBinders, binder.id.binderIndex ≤ state.nextLocal := by
  intro binder member
  cases item with
  | letDecl selected initializer =>
    cases initializer with
    | none => cases member
    | some initializer =>
      have same : binder = selected := List.mem_singleton.mp member
      subst binder
      exact (origin selected initializer rfl).allocated
  | expression | assignValue | assignBitNot => cases member

theorem ItemsSince.allocated {entry : Nat} {state : State} {items : List ForItemForm}
    (origin : ItemsSince entry state items) :
    ∀ binder ∈ items.flatMap ForItemForm.initializedLetBinders,
      binder.id.binderIndex ≤ state.nextLocal := by
  intro binder member
  obtain ⟨item, present, bound⟩ := List.mem_flatMap.mp member
  exact (origin item present).allocated binder bound

theorem StatementSince.allocated {entry : Nat} {state : State} {node : StatementNode}
    (origin : StatementSince entry state node) :
    ∀ binder ∈ node.form.initializedLetBinders, binder.id.binderIndex ≤ state.nextLocal := by
  intro binder member
  cases form : node.form with
  | letDecl selected initializer =>
    cases initializer with
    | none => simp [form, StatementForm.initializedLetBinders] at member
    | some initializer =>
      have same : binder = selected := by
        simpa only [form, StatementForm.initializedLetBinders, List.mem_singleton] using member
      subst binder
      have actual : OriginSince entry state selected initializer := by
        simpa only [StatementSince, form] using origin
      exact actual.allocated
  | forLoop initializer condition post body =>
    have actual : ItemsSince entry state initializer ∧ ItemsSince entry state post := by
      simpa only [StatementSince, form] using origin
    simp only [form, StatementForm.initializedLetBinders, List.mem_append] at member
    exact member.elim (actual.1.allocated binder) (actual.2.allocated binder)
  | returnStmt | expression | assignValue | assignBitNot | ifThen | block
  | matchWith | whileLoop | breakStmt | continueStmt =>
    simp [form, StatementForm.initializedLetBinders] at member

/-- Old declarations retain their complete form; new declarations expose their
actual allocation boundary. Both cases use the same operational progress. -/
theorem Progress.initializedAllocated {before after : State}
    (progress : Progress before after) (ready : Ready before)
    (below : before.LocalBindersBelowNextLocal)
    (allocated : InitializedBindersAllocated before) :
    InitializedBindersAllocated after := by
  intro node member binder bound
  cases node with
  | expression expression => cases bound
  | statement statement =>
    rcases progress.events ready below statement member with old | fresh
    · obtain ⟨prior, present, _, sameForm⟩ := old
      have boundBefore : binder ∈ (Node.statement prior).initializedLetBinders := by
        change binder ∈ prior.form.initializedLetBinders
        rw [sameForm]
        exact bound
      exact Nat.le_trans (allocated _ present _ boundBefore) progress.scope.next
    · exact fresh.allocated binder bound

end Solcore.Frontend.SourceInference.LocalGeneralizationBoundaries
end

section
-- leanmerge: from Solcore.Frontend.SourceInference.LocalGeneralizationBoundedInitialization
/-! Initialized statements and header items close their actual initializer
traversal. Earlier events and nested events remain distinct when the new
binder is allocated and its enclosing statement is recorded. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.Frontend.SourceInference.LocalGeneralizationBoundaries
open TypeSystem Detail
open LocalGeneralizationEvents (Ready)

namespace Progress

theorem initializedStatement {fuel : Nat} {context : Context} {statement : Syntax.Statement}
    {initial : State} {result : StatementResult} {expected : Ty}
    (receipt : LocalLetRequirementTiming.Receipt fuel context statement initial result)
    (accepted : inferStatementFuel (fuel + 1) context statement expected initial = .ok result)
    (child : Progress initial.allocateStatementId.2 receipt.ready) : Progress initial result.state := by
  have suffix : LocalReadScopeProgress.Progress receipt.ready result.state := by
    rw [congrArg StatementResult.state receipt.completed]
    exact (LocalReadScopeProgress.Progress.allocateBinder (receipt.ready.withLocals receipt.locals)
      receipt.name.value receipt.generalized.scheme (some receipt.name.span) false receipt.generalized.requirements).trans
        (LocalReadScopeProgress.Progress.recordStatement _ _)
  refine ⟨LocalReadEvents.inferStatementFuel_origins_progress accepted,
    child.scope.trans suffix, ?_, ?_⟩
  · intro below
    have readyBelow := child.binders below
    rw [congrArg StatementResult.state receipt.completed]
    exact State.allocateBinder_preserves_localBindersBelowNextLocal _ _ _ _ _ _
      (State.withLocals_preserves_localBindersBelowNextLocal _ _ readyBelow)
  · intro ready below node present
    have nodes := congrArg (fun value : StatementResult => value.state.nodes) receipt.completed
    rw [nodes] at present
    rcases List.mem_append.mp present with earlier | recorded
    · rcases child.events ⟨ready.wellFormed, ready.allocated, ready.origins⟩ below node earlier with old | fresh
      · exact .inl old
      · exact .inr (fresh.progress suffix)
    · cases Node.statement.inj (List.mem_singleton.mp recorded)
      exact .inr (StatementSince.of_let receipt ready below rfl)

theorem initializedHeader {fuel : Nat} {context : Context} {item : Syntax.ForItem}
    {initial : State} {result : ForItemForm × State}
    (receipt : LocalHeaderRequirementTiming.Receipt fuel context item initial result)
    (accepted : inferForItemFuel (fuel + 1) context item initial = .ok result)
    (child : Progress initial receipt.ready) : Progress initial result.2 := by
  have suffix : LocalReadScopeProgress.Progress receipt.ready result.2 := by
    rw [congrArg Prod.snd receipt.completed]
    exact LocalReadScopeProgress.Progress.allocateBinder (receipt.ready.withLocals receipt.locals)
      receipt.name.value receipt.generalized.scheme (some receipt.name.span) false receipt.generalized.requirements
  refine ⟨LocalReadEvents.inferForItemFuel_origins_progress accepted,
    child.scope.trans suffix, ?_, ?_⟩
  · intro below
    have readyBelow := child.binders below
    rw [congrArg Prod.snd receipt.completed]
    exact State.allocateBinder_preserves_localBindersBelowNextLocal _ _ _ _ _ _
      (State.withLocals_preserves_localBindersBelowNextLocal _ _ readyBelow)
  · intro ready below node present
    have nodes : result.2.nodes = receipt.ready.nodes :=
      congrArg (fun value : ForItemForm × State => value.2.nodes) receipt.completed
    rw [nodes] at present
    rcases child.events ready below node present with old | fresh
    · exact .inl old
    · exact .inr (fresh.progress suffix)

end Progress
end Solcore.Frontend.SourceInference.LocalGeneralizationBoundaries
end

section
-- leanmerge: from Solcore.Frontend.SourceInference.LocalGeneralizationRetainedStatements
/-! Expression recording and evidence attachment preserve the identity and form
of every existing statement. These maps do not create declaration events. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.Frontend.SourceInference.LocalGeneralizationBoundaries
open TypeSystem Detail

def RetainedStatements (before after : List Node) : Prop :=
  ∀ node : StatementNode, .statement node ∈ after → PriorStatement before node

namespace RetainedStatements

theorem refl (nodes : List Node) : RetainedStatements nodes nodes :=
  fun node member => ⟨node, member, rfl, rfl⟩

theorem trans {before middle after : List Node} (first : RetainedStatements before middle)
    (second : RetainedStatements middle after) : RetainedStatements before after := by
  intro node member
  obtain ⟨prior, present, sameId, sameForm⟩ := second node member
  obtain ⟨original, originalPresent, originalId, originalForm⟩ := first prior present
  exact ⟨original, originalPresent, originalId.trans sameId, originalForm.trans sameForm⟩

theorem expression (nodes : List Node) (node : ExpressionNode) :
    RetainedStatements nodes (nodes ++ [.expression node]) := by
  intro statement present
  rcases List.mem_append.mp present with old | fresh
  · exact ⟨statement, old, rfl, rfl⟩
  · cases List.mem_singleton.mp fresh

theorem modifyExpressionNode (state : State) (id : ExpressionId) (modify : ExpressionNode → ExpressionNode) :
    RetainedStatements state.nodes (state.modifyExpressionNode id modify).nodes := by
  intro statement present
  obtain ⟨node, member, same⟩ := List.mem_map.mp present
  cases node with
  | expression node => simp only at same; split at same <;> cases same
  | statement original => cases same; exact ⟨_, member, rfl, rfl⟩

theorem modifyStatementNode (state : State) (id : StatementId) (modify : StatementNode → StatementNode)
    (sameForm : ∀ node, (modify node).form = node.form) :
    RetainedStatements state.nodes (state.modifyStatementNode id modify).nodes := by
  intro statement present
  obtain ⟨node, member, same⟩ := List.mem_map.mp present
  cases node with
  | expression node => cases same
  | statement original =>
      simp only at same
      split at same
      · rename_i selected
        cases same
        exact ⟨original, member, selected, (sameForm original).symm⟩
      · cases same
        exact ⟨_, member, rfl, rfl⟩

theorem attachExpressionCoercions (state : State) (entries : List Detail.ExpressionCoercions) :
    RetainedStatements state.nodes (Detail.attachExpressionCoercions state entries).nodes := by
  unfold Detail.attachExpressionCoercions
  induction entries generalizing state with
  | nil => exact .refl _
  | cons entry rest ih => exact (modifyExpressionNode _ _ _).trans (ih _)

theorem recordExpression (state : State) (source : Syntax.Expr) (expression : InferredExpression)
    (form : ExpressionForm) (requirements : List RequirementId) (coercions : List CoercionStep)
    (start : Option Nat := none) :
    RetainedStatements state.nodes (Detail.recordExpression source expression form requirements coercions state start).2.nodes :=
  RetainedStatements.expression _ _

theorem recordExpressionWithExpected {context : Context} {source : Syntax.Expr} {id : ExpressionId} {type : Ty}
    {form : ExpressionForm} {requirements : List RequirementId} {expected : Option Ty} {state : State}
    {start : Option Nat} {result : InferredExpression × State}
    (accepted : Detail.recordExpressionWithExpected context source id type form requirements expected state start = .ok result) :
    RetainedStatements state.nodes result.2.nodes := by
  obtain ⟨fitted, fit, _, recorded⟩ := Detail.recordExpressionWithExpected_success_record accepted
  rw [recorded]
  have same := (Detail.withExpected_occurrenceState_eq fit).1
  change RetainedStatements state.nodes (fitted.state.nodes ++ _)
  rw [same]
  exact .expression _ _

theorem recordSelectedCallResult (source callee : Syntax.Expr) (name : String)
    (arguments : List InferredExpression) (attempt : CandidateAttemptResult)
    (result : InferredExpression) (trailingCoercions : List CoercionStep) (state : State) :
    RetainedStatements state.nodes
      (Detail.recordSelectedCallResult source callee name arguments attempt result trailingCoercions state).2.nodes := by
  unfold Detail.recordSelectedCallResult
  exact (attachExpressionCoercions _ _).trans ((recordExpression _ _ _ _ _ _ _).trans (recordExpression _ _ _ _ _ _ _))

end RetainedStatements
end Solcore.Frontend.SourceInference.LocalGeneralizationBoundaries
end

section
-- leanmerge: from Solcore.Frontend.SourceInference.LocalGeneralizationBoundedHelpers
/-! Actual helper computations introduce no declaration events. Their genuine
ledger and lexical-scope receipts transport already recorded boundaries. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.Frontend.SourceInference.LocalGeneralizationBoundaries
open TypeSystem Detail

namespace Progress

theorem of_unchanged {before after : State}
    (nodes : after.nodes = before.nodes) (binders : after.localBinders = before.localBinders)
    (reads : LocalReadEvents.Progress before after)
    (scope : LocalReadScopeProgress.Progress before after) : Progress before after :=
  of_nodes_eq nodes reads scope (fun below => State.LocalBindersBelowNextLocal.transport binders scope.next below)

theorem unify {state next : State} {left right : Ty}
    (accepted : Detail.unify state left right = .ok next) : Progress state next :=
  of_unchanged (unify_occurrenceState_eq accepted).1
    (congrArg LexicalScope.binders (unify_preserves_lexicalScope accepted))
    (LocalReadEvents.Progress.unify accepted) (LocalReadScopeProgress.Progress.unify accepted)

theorem withExpected {context : Context} {state : State} {actual : InferredExpression}
    {expected : Option Ty} {result : ExpectationResult}
    (accepted : Detail.withExpected context state actual expected = .ok result) : Progress state result.state :=
  of_unchanged (withExpected_occurrenceState_eq accepted).1
    (congrArg LexicalScope.binders (localReadScope_withExpected_lexicalScope accepted))
    (LocalReadEvents.Progress.withExpected accepted) (LocalReadScopeProgress.Progress.withExpected accepted)

theorem selectFunctionCandidateFrom {context : Context} {name : String}
    {candidates : List ProgramFunctionSignature} {arguments : List InferredExpression}
    {integerLiteralOrigins : List IntegerLiteralOrigin} {call : ExpressionId} {expected : Option Ty}
    {state : State} {result : CandidateAttemptResult}
    (accepted : Detail.selectFunctionCandidateFrom context name candidates arguments integerLiteralOrigins
      call expected state = .ok result) : Progress state result.state :=
  of_unchanged (selectFunctionCandidateFrom_occurrenceState_eq accepted).1
    (congrArg LexicalScope.binders (localReadScope_selectFunctionCandidateFrom_lexicalScope accepted))
    (LocalReadEvents.Progress.selectFunctionCandidateFrom accepted)
    (LocalReadScopeProgress.Progress.selectFunctionCandidateFrom accepted)

theorem inferUnaryOperator {context : Context} {operator : Syntax.UnaryOp} {operandType : Ty}
    {expected : Option Ty} {integerLiterals : List IntegerLiteralOrigin}
    {state : State} {result : OperatorInferenceResult}
    (accepted : Detail.inferUnaryOperator context operator operandType expected integerLiterals state = .ok result) :
    Progress state result.state :=
  of_unchanged (inferUnaryOperator_occurrenceState_eq accepted).1
    (congrArg LexicalScope.binders (localReadScope_inferUnaryOperator_lexicalScope accepted))
    (LocalReadEvents.Progress.inferUnaryOperator accepted) (LocalReadScopeProgress.Progress.inferUnaryOperator accepted)

theorem inferBinaryOperator {context : Context} {operator : Syntax.BinaryOp} {left right : Ty}
    {expected : Option Ty} {integerLiterals : List IntegerLiteralOrigin}
    {state : State} {result : OperatorInferenceResult}
    (accepted : Detail.inferBinaryOperator context operator left right expected integerLiterals state = .ok result) :
    Progress state result.state :=
  of_unchanged (inferBinaryOperator_occurrenceState_eq accepted).1
    (congrArg LexicalScope.binders (localReadScope_inferBinaryOperator_lexicalScope accepted))
    (LocalReadEvents.Progress.inferBinaryOperator accepted) (LocalReadScopeProgress.Progress.inferBinaryOperator accepted)

theorem applyFunctionType {context : Context} {call : ExpressionId} {calleeType : Ty}
    {arguments : List InferredExpression} {expected : Option Ty}
    {state : State} {result : IndirectApplicationResult}
    (accepted : Detail.applyFunctionType context call calleeType arguments expected state = .ok result) :
    Progress state result.state :=
  of_unchanged (applyFunctionType_occurrenceState_eq accepted).1
    (congrArg LexicalScope.binders (localReadScope_applyFunctionType_lexicalScope accepted))
    (LocalReadEvents.Progress.applyFunctionType accepted) (LocalReadScopeProgress.Progress.applyFunctionType accepted)

theorem fresh (state : State) : Progress state state.fresh.2 :=
  of_unchanged rfl rfl (LocalReadEvents.Progress.of_nodes_eq rfl (State.DirectRequirementsProgress.refl _))
    (LocalReadScopeProgress.Progress.fresh _)

theorem allocateExpressionId (state : State) : Progress state state.allocateExpressionId.2 :=
  of_unchanged rfl rfl (LocalReadEvents.Progress.of_nodes_eq rfl (State.DirectRequirementsProgress.refl _))
    (LocalReadScopeProgress.Progress.refl _)

theorem allocateStatementId (state : State) : Progress state state.allocateStatementId.2 :=
  of_unchanged rfl rfl (LocalReadEvents.Progress.of_nodes_eq rfl (State.DirectRequirementsProgress.refl _))
    (LocalReadScopeProgress.Progress.refl _)

theorem allocateHiddenLocal (state : State) : Progress state state.allocateHiddenLocal.2 :=
  of_unchanged rfl rfl (LocalReadEvents.Progress.of_nodes_eq rfl (State.DirectRequirementsProgress.refl _))
    (LocalReadScopeProgress.Progress.allocateHiddenLocal _)

theorem allocateBinder (state : State) (name : String) (scheme : Scheme)
    (span : Option Syntax.SourceSpan) (comptime : Bool) (requirements : List LocalSchemeRequirement) :
    Progress state (state.allocateBinder name scheme span comptime requirements).2 :=
  of_nodes_eq rfl (LocalReadEvents.Progress.of_nodes_eq rfl (State.DirectRequirementsProgress.refl _))
    (LocalReadScopeProgress.Progress.allocateBinder _ _ _ _ _ _)
    (State.allocateBinder_preserves_localBindersBelowNextLocal _ _ _ _ _ _)

theorem freshTypes (count : Nat) (state : State) : Progress state (Detail.freshTypes count state).2 :=
  of_nodes_eq (Detail.freshTypes_nodes _ _) (LocalReadEvents.Progress.freshTypes _ _)
    (LocalReadScopeProgress.Progress.freshTypes _ _)
    (Detail.freshTypes_preserves_localBindersBelowNextLocal _ _)

theorem freshDataConstructorInstantiation (dataType : ProgramDataSignature)
    (constructor : ProgramDataConstructorSignature) (state : State) :
    Progress state (Detail.freshDataConstructorInstantiation dataType constructor state).2 :=
  of_nodes_eq (Detail.freshDataConstructorInstantiation_nodes _ _ _)
    (LocalReadEvents.Progress.freshDataConstructorInstantiation _ _ _)
    (LocalReadScopeProgress.Progress.freshDataConstructorInstantiation _ _ _)
    (Detail.freshDataConstructorInstantiation_preserves_localBindersBelowNextLocal _ _ _)

theorem addRequirementWithId (state : State) (predicate : ProgramPredicate) :
    Progress state (state.addRequirementWithId predicate).2 :=
  of_unchanged rfl rfl (LocalReadEvents.Progress.addRequirementWithId _ _)
    (LocalReadScopeProgress.Progress.addRequirementWithId _ _)

theorem addRequirementsWithIds (state : State) (predicates : List ProgramPredicate) :
    Progress state (state.addRequirementsWithIds predicates).2 :=
  of_nodes_eq (State.addRequirementsWithIds_nodes _ _)
    (LocalReadEvents.Progress.addRequirementsWithIds _ _) (LocalReadScopeProgress.Progress.addRequirementsWithIds _ _)
    (State.addRequirementsWithIds_preserves_localBindersBelowNextLocal _ _)


theorem recordExpressionWithExpected {context : Context} {source : Syntax.Expr} {id : ExpressionId}
    {type : Ty} {form : ExpressionForm} {requirements : List RequirementId} {expected : Option Ty}
    {state : State} {start : Option Nat} {result : InferredExpression × State}
    (accepted : Detail.recordExpressionWithExpected context source id type form requirements expected state start = .ok result)
    (nonlocal : LocalReadEvents.Nonlocal form) : Progress state result.2 := by
  apply of_retained (RetainedStatements.recordExpressionWithExpected accepted)
    (LocalReadEvents.Progress.recordExpressionWithExpected accepted nonlocal)
    (LocalReadScopeProgress.Progress.recordExpressionWithExpected accepted nonlocal)
  intro below
  obtain ⟨fitted, fit, _, recorded⟩ := Detail.recordExpressionWithExpected_success_record accepted
  rw [recorded]
  exact (withExpected fit).binders below

theorem localIdentifier {fuel : Nat} {context : Context} {expression : Syntax.Expr}
    {expected : Option Ty} {initial allocated : State} {id : ExpressionId}
    {name : Syntax.Identifier} {binder : TypedBinder} {result : InferredExpression × State}
    (form : expression.value = .identifier name)
    (allocation : initial.allocateExpressionId = (id, allocated))
    (found : allocated.lookupBinder? name.value = some binder)
    (accepted : inferExprFuel (fuel + 1) context expression expected initial = .ok result) :
    Progress initial result.2 := by
  apply of_retained ?_ (LocalReadEvents.Progress.localIdentifier form allocation found accepted)
    (LocalReadScopeProgress.Progress.localIdentifier form allocation found accepted)
    (fun below => inferExprFuel_preserves_localBindersBelowNextLocal below accepted)
  have retained := RetainedStatements.recordExpressionWithExpected
    (Detail.inferExprFuel_success_localIdentifier_record form allocation found accepted)
  rw [State.addRequirementsWithIds_nodes] at retained
  have allocationState : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
  simpa only [RetainedStatements, allocationState, State.allocateExpressionId_nodes] using retained

theorem modifyStatementNode (state : State) (id : StatementId) (modify : StatementNode → StatementNode)
    (forms : ∀ node, (modify node).form = node.form) : Progress state (state.modifyStatementNode id modify) :=
  of_retained (RetainedStatements.modifyStatementNode state id modify forms)
    (LocalReadEvents.Progress.modifyStatementNode _ _ _)
    (LocalReadScopeProgress.Progress.modifyStatementNode _ _ _) (fun below => below)

private theorem attachExpressionCoercions_binders (state : State) (entries : List ExpressionCoercions) :
    (Detail.attachExpressionCoercions state entries).localBinders = state.localBinders := by
  unfold Detail.attachExpressionCoercions
  induction entries generalizing state with
  | nil => rfl
  | cons head tail ih => exact ih _

theorem recordSelectedCallResult (source callee : Syntax.Expr) (name : String)
    (arguments : List InferredExpression) (attempt : CandidateAttemptResult)
    (result : InferredExpression) (trailing : List CoercionStep) (state : State) :
    Progress state (Detail.recordSelectedCallResult source callee name arguments attempt result trailing state).2 := by
  have scope := LocalReadScopeProgress.Progress.recordSelectedCallResult source callee name arguments attempt result trailing state
  apply of_retained (RetainedStatements.recordSelectedCallResult _ _ _ _ _ _ _ _)
    (LocalReadEvents.Progress.recordSelectedCallResult _ _ _ _ _ _ _ _) scope
  intro below
  apply State.LocalBindersBelowNextLocal.transport (before := state) ?_ scope.next below
  change (Detail.attachExpressionCoercions state attempt.argumentCoercions).localBinders = state.localBinders
  exact attachExpressionCoercions_binders _ _

theorem recordSelectedCall (source callee : Syntax.Expr) (name : String)
    (arguments : List InferredExpression) (attempt : CandidateAttemptResult) :
    Progress attempt.state (Detail.recordSelectedCall source callee name arguments attempt).2 :=
  recordSelectedCallResult _ _ _ _ _ _ _ _

theorem recordIndirectCall (source : Syntax.Expr) (callee : InferredExpression)
    (arguments : List InferredExpression) (result : IndirectApplicationResult) :
    Progress result.state (Detail.recordIndirectCall source callee arguments result).2 :=
  of_retained (RetainedStatements.recordExpression _ _ _ _ _ _ _)
    (LocalReadEvents.Progress.recordIndirectCall _ _ _ _) (LocalReadScopeProgress.Progress.recordIndirectCall _ _ _ _)
    (fun below => below)

end Progress
end Solcore.Frontend.SourceInference.LocalGeneralizationBoundaries
end

section
-- leanmerge: from Solcore.Frontend.SourceInference.LocalGeneralizationBoundedAuxiliaryHelpers
/-! Parameter, pattern, and builtin helper computations preserve the bounded
checker event invariant through their actual successful execution. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.Frontend.SourceInference.LocalGeneralizationBoundaries
open TypeSystem Detail
namespace Progress

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

theorem inferMatchPatternFuel {fuel : Nat} {context : Context} {pattern : Syntax.Pattern}
    {expected : Ty} {state : State} {result : TypedMatchPattern × State}
    (accepted : Detail.inferMatchPatternFuel fuel context pattern expected state = .ok result) :
    Progress state result.2 := by
  apply of_nodes_eq (inferMatchPatternFuel_occurrenceState_eq accepted).1
    (LocalReadEvents.Progress.inferMatchPatternFuel accepted)
    (LocalReadScopeProgress.Progress.inferMatchPatternFuel accepted)
  intro below
  unfold Detail.inferMatchPatternFuel at accepted
  cases flatRun : inferMatchPatternFlatFuel fuel context pattern expected [] state with
  | error error => simp [flatRun, bind, Except.bind] at accepted
  | ok inferred =>
      simp only [flatRun, bind, Except.bind] at accepted
      change Except.ok ({
        source := inferred.source
        type := inferred.state.resolve expected
        resolution := inferred.resolution
        requirements := inferred.requirements
      }, inferred.state) = Except.ok result at accepted
      cases accepted
      exact inferMatchPatternFlatFuel_preserves_localBindersBelowNextLocal
        fuel context pattern expected [] state inferred below flatRun

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

private theorem builtinCall_binders {source callee : Syntax.Expr} {name : String}
    {function : BuiltinFunctionId} {arguments : List InferredExpression}
    {call : ExpressionId} {expected : Option Ty} {state : State}
    {result : InferredExpression × State}
    (accepted : Detail.recordBuiltinFunctionCall source callee name function arguments call expected state = .ok result)
    (below : state.LocalBindersBelowNextLocal) : result.2.LocalBindersBelowNextLocal := by
  unfold Detail.recordBuiltinFunctionCall at accepted
  simp_all [bind, Except.bind]
  repeat' first | split at accepted
  all_goals try cases accepted
  all_goals try simp_all only [pure, Except.pure, Except.ok.injEq]
  all_goals try subst_vars
  all_goals have argumentsProgress := builtinArguments (by assumption)
  all_goals try have unifiedProgress := unify (by assumption)
  all_goals first
    | exact argumentsProgress.binders below
    | exact unifiedProgress.binders (argumentsProgress.binders below)

theorem recordBuiltinFunctionCall {source callee : Syntax.Expr} {name : String}
    {function : BuiltinFunctionId} {arguments : List InferredExpression}
    {call : ExpressionId} {expected : Option Ty} {state : State}
    {result : InferredExpression × State}
    (accepted : Detail.recordBuiltinFunctionCall source callee name function arguments call expected state = .ok result) :
    Progress state result.2 := by
  apply of_retained ?_ (LocalReadEvents.Progress.recordBuiltinFunctionCall accepted)
    (LocalReadScopeProgress.Progress.recordBuiltinFunctionCall accepted) (builtinCall_binders accepted)
  obtain ⟨calleeId, nodes⟩ := Detail.recordBuiltinFunctionCall_success_nodes accepted
  rw [nodes]
  intro statement present
  rcases List.mem_append.mp present with old | fresh
  · exact ⟨statement, old, rfl, rfl⟩
  · simp at fresh

end Progress
end Solcore.Frontend.SourceInference.LocalGeneralizationBoundaries
end

section
-- leanmerge: from Solcore.Frontend.SourceInference.LocalGeneralizationBoundedOrigins
/-! The completed traversal transports entry events and newly created events
through the same reached state, while retaining their separate allocator bounds. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.Frontend.SourceInference.LocalGeneralizationBoundaries
open TypeSystem Detail
open LocalGeneralizationEvents (Ready)

def OriginsSince (entry : Nat) (state : State) : Prop :=
  ∀ node : StatementNode, .statement node ∈ state.nodes → StatementSince entry state node

theorem OriginsSince.empty {entry : Nat} {state : State} (empty : state.nodes = []) : OriginsSince entry state := by
  intro _ member
  rw [empty] at member
  cases member

theorem Progress.origins {entry : Nat} {before after : State} (progress : Progress before after)
    (ready : Ready before) (below : before.LocalBindersBelowNextLocal) (entered : entry ≤ before.nextLocal)
    (origins : OriginsSince entry before) : OriginsSince entry after := by
  intro node present
  rcases progress.events ready below node present with old | fresh
  · obtain ⟨prior, member, _, sameForm⟩ := old
    exact ((origins prior member).progress progress.scope).same_form sameForm.symm
  · exact fresh.weaken entered

/-- An enclosing statement may aggregate initializer events that precede its
own recording. The existing traversal cutoff is retained for those events. -/
theorem Progress.recordAfter {before state : State} (progress : Progress before state)
    (node : StatementNode) (event : StatementSince before.nextLocal state node) :
    Progress before (state.recordNode (.statement node)) := by
  have step := LocalReadScopeProgress.Progress.recordStatement state node
  refine ⟨progress.reads.trans (LocalReadEvents.Progress.recordStatement _ _), progress.scope.trans step,
    progress.binders, ?_⟩
  intro ready below actual member
  rcases List.mem_append.mp member with old | fresh
  · rcases progress.events ready below actual old with old | fresh
    · exact .inl old
    · exact .inr (fresh.progress step)
  · cases Node.statement.inj (List.mem_singleton.mp fresh)
    exact .inr (event.progress step)

/-- At a genuine empty function entry all final events come from this traversal;
there are no pre-existing nodes whose origin could be assumed. -/
theorem Progress.empty_entry {before after : State} (progress : Progress before after)
    (ready : Ready before) (below : before.LocalBindersBelowNextLocal) (empty : before.nodes = []) :
    OriginsSince before.nextLocal after :=
  progress.origins ready below (Nat.le_refl _) (OriginsSince.empty empty)

end Solcore.Frontend.SourceInference.LocalGeneralizationBoundaries
end

section
-- leanmerge: from Solcore.Frontend.SourceInference.LocalGeneralizationBoundedPrimitives
/-! Small state updates used by the actual bounded event traversal. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.Frontend.SourceInference.LocalGeneralizationBoundaries
open TypeSystem Detail
namespace Progress

theorem recordExpression (state : State) (node : ExpressionNode)
    (nonlocal : LocalReadEvents.Nonlocal node.form) : Progress state (state.recordNode (.expression node)) :=
  appendExpression node rfl (LocalReadEvents.ProgressFields.expression _ _ _ _ _ nonlocal)
    (LocalReadScopeProgress.Progress.recordExpression _ _ (fun name id form => (nonlocal name id form).elim)) (fun below => below)

theorem withLocals (state : State) (locals : List (String × Scheme)) :
    Progress state (state.withLocals locals) :=
  of_unchanged rfl rfl (LocalReadEvents.Progress.refl _) (LocalReadScopeProgress.Progress.refl _)

end Progress
end Solcore.Frontend.SourceInference.LocalGeneralizationBoundaries
end

section
-- leanmerge: from Solcore.Frontend.SourceInference.LocalGeneralizationBoundedRestoration
/-! Restoring a genuinely saved lexical scope preserves the traversal entry
cutoff. The suffix starts at the exact restored state. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.Frontend.SourceInference.LocalGeneralizationBoundaries
namespace Progress

/-- Restore the scope saved at this traversal's actual entry. -/
theorem restored_start {before middle : State} (initialStep : Progress before middle) :
    Progress before (middle.restoreLexicalScope before.lexicalScope) :=
  initialStep.restore before.lexicalScope (fun _ member => member)

/-- Continue from the exact state produced by restoring the entry scope. -/
theorem restored_then {before middle after : State}
    (initialStep : Progress before middle)
    (suffix : Progress (middle.restoreLexicalScope before.lexicalScope) after) :
    Progress before after :=
  initialStep.restored_start.trans suffix

/-- Restore a previously saved scope only with its actual binder membership. -/
theorem restored_saved_then {before middle after : State} {scope : LexicalScope}
    (initialStep : Progress before middle) (saved : scope.binders ⊆ before.localBinders)
    (suffix : Progress (middle.restoreLexicalScope scope) after) :
    Progress before after :=
  (initialStep.restore scope saved).trans suffix

/-- Actual pair-result equality exposes the restored state without changing
which traversal entry supplied the saved-scope evidence. -/
theorem restored_pair_result {alpha : Type} {value : alpha} {before middle : State}
    {scope : LexicalScope} {result : alpha × State}
    (initialStep : Progress before middle) (saved : scope.binders ⊆ before.localBinders)
    (completed : (value, middle.restoreLexicalScope scope) = result) :
    Progress before result.2 := by
  rw [← completed]
  exact initialStep.restore scope saved

/-- A successful pure return retains the exact restored pair-result state. -/
theorem restored_pure_result {epsilon alpha : Type} {value : alpha} {before middle : State}
    {scope : LexicalScope} {result : alpha × State}
    (initialStep : Progress before middle) (saved : scope.binders ⊆ before.localBinders)
    (completed : (pure (value, middle.restoreLexicalScope scope) : Except epsilon (alpha × State)) = .ok result) :
    Progress before result.2 := by
  change Except.ok (value, middle.restoreLexicalScope scope) = Except.ok result at completed
  exact initialStep.restored_pair_result saved (Except.ok.inj completed)

end Progress
end Solcore.Frontend.SourceInference.LocalGeneralizationBoundaries
end

section
-- leanmerge: from Solcore.Frontend.SourceInference.LocalGeneralizationBoundedInference
/-! Actual inference cannot create a reference to a retired older local ID.
Match recursion retains the genuine saved outer-scope membership. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace Solcore.Frontend.SourceInference.LocalGeneralizationBoundaries
open TypeSystem Detail
open LocalGeneralizationEvents (Ready)

@[simp] private theorem exceptPure_eq_ok {epsilon alpha : Type} (value result : alpha) :
    ((pure value : Except epsilon alpha) = .ok result) ↔ value = result := by
  change (Except.ok value = Except.ok result) ↔ value = result
  simp

private theorem annotation_none {context : Context} {expected : Option Ty}
    (accepted : LocalLetRequirementTiming.Annotation context none expected) : expected = none := by
  cases accepted
  rfl

private theorem annotation_some {context : Context} {syntaxType : Syntax.TypeExpr} {expected : Option Ty}
    (accepted : LocalLetRequirementTiming.Annotation context (some syntaxType) expected) :
    ∃ type, expected = some type := by
  cases accepted
  exact ⟨_, rfl⟩

private def PreservesBoundaries {alpha : Type} (stateOf : alpha → State)
    (initial : State) (computation : Except Error alpha) : Prop :=
  ∀ result, computation = .ok result → Progress initial (stateOf result)

private theorem pair_success_boundaries_progress {alpha : Type}
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


private theorem allocateExpressionId_success_boundaries_progress
    {state next : State} {id : ExpressionId}
    (success : state.allocateExpressionId = (id, next)) :
    Progress state next :=
  pair_success_boundaries_progress
    (Progress.allocateExpressionId state) success

private theorem allocateStatementId_success_boundaries_progress
    {state next : State} {id : StatementId}
    (success : state.allocateStatementId = (id, next)) :
    Progress state next :=
  pair_success_boundaries_progress
    (Progress.allocateStatementId state) success

private theorem state_fresh_success_boundaries_progress
    {state next : State} {type : Ty}
    (success : state.fresh = (type, next)) :
    Progress state next :=
  pair_success_boundaries_progress (Progress.fresh state)
    success

private theorem allocateHiddenLocal_success_boundaries_progress
    {state next : State} {id : Resolved.LocalId}
    (success : state.allocateHiddenLocal = (id, next)) :
    Progress state next :=
  pair_success_boundaries_progress
    (Progress.allocateHiddenLocal state) success

private theorem addRequirementWithId_success_boundaries_progress
    {state next : State} {predicate : ProgramPredicate}
    {requirement : RequirementId}
    (success : state.addRequirementWithId predicate = (requirement, next)) :
    Progress state next :=
  pair_success_boundaries_progress
    (Progress.addRequirementWithId state predicate) success

private theorem addRequirementsWithIds_success_boundaries_progress
    {state next : State} {predicates : List ProgramPredicate}
    {requirements : List RequirementId}
    (success : state.addRequirementsWithIds predicates = (requirements, next)) :
    Progress state next :=
  pair_success_boundaries_progress
    (Progress.addRequirementsWithIds state predicates) success

private theorem allocateBinder_success_boundaries_progress
    {state next : State} {name : String} {scheme : Scheme}
    {span : Option Syntax.SourceSpan} {comptime : Bool}
    {schemeRequirements : List LocalSchemeRequirement} {binder : TypedBinder}
    (success : state.allocateBinder name scheme span comptime
      schemeRequirements = (binder, next)) :
    Progress state next :=
  pair_success_boundaries_progress
    (Progress.allocateBinder state name scheme span comptime schemeRequirements) success

private theorem freshDataConstructorInstantiation_success_boundaries_progress
    {dataType : ProgramDataSignature}
    {constructor : ProgramDataConstructorSignature}
    {state next : State} {instantiation : DataConstructorInstantiation}
    (success : freshDataConstructorInstantiation dataType constructor state =
      (instantiation, next)) :
    Progress state next :=
  pair_success_boundaries_progress
    (Progress.freshDataConstructorInstantiation dataType constructor
      state) success

private theorem freshTypes_success_boundaries_progress
    {count : Nat} {state next : State} {types : List Ty}
    (success : freshTypes count state = (types, next)) :
    Progress state next :=
  pair_success_boundaries_progress
    (Progress.freshTypes count state) success

private theorem syntheticTuple_result_boundaries_progress
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
  exact (Progress.allocateExpressionId state).trans (Progress.recordExpression _ _ (by intro _ _ impossible; cases impossible))

private theorem syntheticTuple_pair_boundaries_progress
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
  exact (Progress.allocateExpressionId state).trans (Progress.recordExpression _ _ (by intro _ _ impossible; cases impossible))

private theorem pure_pair_result_boundaries_progress {epsilon alpha : Type}
    {value : alpha} {next initial : State} {result : alpha × State}
    (nextSubset : Progress initial next)
    (success : (pure (value, next) : Except epsilon (alpha × State)) =
      .ok result) :
    Progress initial result.snd := by
  have resultEq : (value, next) = result := by
    simpa only [exceptPure_eq_ok] using success
  rw [← resultEq]
  exact nextSubset

private theorem restored_pair_result_boundaries_progress {alpha : Type}
    {value : alpha} {state initial : State} {scope : LexicalScope}
    {result : alpha × State}
    (subset : Progress initial state)
    (saved : scope.binders ⊆ initial.localBinders)
    (success : (value, state.restoreLexicalScope scope) = result) :
    Progress initial result.snd := by
  rw [← success]
  exact subset.restore scope saved


set_option maxHeartbeats 2000000 in
private theorem inferFuel_boundaries_progress_internal :
    (∀ fuel context expression expected state,
      PreservesBoundaries Prod.snd state
        (inferExprFuel fuel context expression expected state)) ∧
    (∀ fuel context source id instantiation arguments expected state,
      PreservesBoundaries Prod.snd state
        (inferConstructorApplicationFuel fuel context source id instantiation
          arguments expected state)) ∧
    (∀ fuel context sources expected state,
      PreservesBoundaries Prod.snd state
        (inferConstructorArgumentsFuel fuel context sources expected state)) ∧
    (∀ fuel context statements expectedReturn state,
      PreservesBoundaries BlockResult.state state
        (inferStatementsFuel fuel context statements expectedReturn state)) ∧
    (∀ fuel context statement expectedReturn state,
      PreservesBoundaries StatementResult.state state
        (inferStatementFuel fuel context statement expectedReturn state)) ∧
    (∀ fuel context items state,
      PreservesBoundaries InferredForItems.state state
        (inferForItemsFuel fuel context items state)) ∧
    (∀ fuel context item state,
      PreservesBoundaries Prod.snd state
        (inferForItemFuel fuel context item state)) ∧
    (∀ fuel context target state,
      PreservesBoundaries Prod.snd state
        (inferPlaceFuel fuel context target state)) ∧
    (∀ fuel context target operator value state,
      PreservesBoundaries (fun result => result.2.2) state
        (inferAssignedValueFuel fuel context target operator value state)) ∧
    (∀ fuel context expressions state,
      PreservesBoundaries Prod.snd state
        (inferExprsFuel fuel context expressions state)) ∧
    (∀ fuel context scrutineeType expectedReturn outerScope cases state,
      outerScope.binders ⊆ state.localBinders →
      PreservesBoundaries MatchCasesResult.state state
        (inferMatchCasesFuel fuel context scrutineeType expectedReturn outerScope
          cases state)) := by
  apply inferExprFuel.mutual_induct
    (motive1 := fun fuel context expression expected state =>
      PreservesBoundaries Prod.snd state
        (inferExprFuel fuel context expression expected state))
    (motive2 := fun fuel context source id instantiation arguments expected
        state =>
      PreservesBoundaries Prod.snd state
        (inferConstructorApplicationFuel fuel context source id instantiation
          arguments expected state))
    (motive3 := fun fuel context sources expected state =>
      PreservesBoundaries Prod.snd state
        (inferConstructorArgumentsFuel fuel context sources expected state))
    (motive4 := fun fuel context statements expectedReturn state =>
      PreservesBoundaries BlockResult.state state
        (inferStatementsFuel fuel context statements expectedReturn state))
    (motive5 := fun fuel context statement expectedReturn state =>
      PreservesBoundaries StatementResult.state state
        (inferStatementFuel fuel context statement expectedReturn state))
    (motive6 := fun fuel context items state =>
      PreservesBoundaries InferredForItems.state state
        (inferForItemsFuel fuel context items state))
    (motive7 := fun fuel context item state =>
      PreservesBoundaries Prod.snd state
        (inferForItemFuel fuel context item state))
    (motive8 := fun fuel context target state =>
      PreservesBoundaries Prod.snd state
        (inferPlaceFuel fuel context target state))
    (motive9 := fun fuel context target operator value state =>
      PreservesBoundaries (fun result => result.2.2) state
        (inferAssignedValueFuel fuel context target operator value state))
    (motive10 := fun fuel context expressions state =>
      PreservesBoundaries Prod.snd state
        (inferExprsFuel fuel context expressions state))
    (motive11 := fun fuel context scrutineeType expectedReturn outerScope
        cases state =>
      outerScope.binders ⊆ state.localBinders →
      PreservesBoundaries MatchCasesResult.state state
        (inferMatchCasesFuel fuel context scrutineeType expectedReturn outerScope
          cases state))
  case case34 =>
    intro context statement expected state fuel id allocated allocation name initializer form ih
    intro result accepted
    obtain ⟨receipt⟩ := LocalLetRequirementTiming.of_accepted form accepted
    have sameAnnotation : receipt.annotation = none := by
      have same := receipt.form.symm.trans form
      exact (Syntax.StatementValue.letDecl.inj same).2.1
    have sameExpected : receipt.expected = none := by
      exact annotation_none (sameAnnotation ▸ receipt.annotationAccepted)
    have sameInitializer : receipt.initializer = initializer := by
      have same := receipt.form.symm.trans form
      exact Option.some.inj (Syntax.StatementValue.letDecl.inj same).2.2
    apply Progress.initializedStatement receipt accepted
    have allocationState : state.allocateStatementId.2 = allocated := congrArg Prod.snd allocation
    rw [allocationState]
    exact ih _ (by simpa only [allocationState, sameInitializer, sameExpected] using receipt.child)
  case case35 =>
    intro context statement expected state fuel id allocated allocation name syntaxType initializer form ih
    intro result accepted
    obtain ⟨receipt⟩ := LocalLetRequirementTiming.of_initialized_accepted form accepted
    have sameAnnotation : receipt.annotation = some syntaxType := by
      have same := receipt.form.symm.trans form
      exact (Syntax.StatementValue.letDecl.inj same).2.1
    have sameInitializer : receipt.initializer = initializer := by
      have same := receipt.form.symm.trans form
      exact Option.some.inj (Syntax.StatementValue.letDecl.inj same).2.2
    have expectedSome : ∃ type, receipt.expected = some type := by
      exact annotation_some (sameAnnotation ▸ receipt.annotationAccepted)
    obtain ⟨type, sameExpected⟩ := expectedSome
    apply Progress.initializedStatement receipt accepted
    have allocationState : state.allocateStatementId.2 = allocated := congrArg Prod.snd allocation
    rw [allocationState]
    exact ih type _ (by simpa only [allocationState, sameInitializer, sameExpected] using receipt.child)
  case case45 =>
    intro context statement expected initial fuel id allocated allocation headerSpan initializers condition post body form initIH condIH bodyIH postIH
    intro result accepted
    have original := accepted
    unfold inferStatementFuel at accepted
    simp only [allocation, form, bind, Except.bind] at accepted
    cases initRun : inferForItemsFuel fuel context initializers allocated with
    | error error => simp [initRun, bind, Except.bind] at accepted
    | ok initResult =>
      cases condRun : inferExprFuel fuel context condition (some .bool) initResult.state with
      | error error => simp [initRun, condRun, bind, Except.bind] at accepted
      | ok pair =>
        rcases pair with ⟨test, testState⟩
        let loopContext := { context with loopDepth := context.loopDepth + 1 }
        cases bodyRun : inferStatementsFuel fuel loopContext body.value expected testState with
        | error error => simp [initRun, condRun, loopContext, bodyRun, bind, Except.bind] at accepted
        | ok bodyResult =>
          let afterBody := bodyResult.state.restoreLexicalScope initResult.state.lexicalScope
          cases postRun : inferForItemsFuel fuel loopContext post afterBody with
          | error error => simp [initRun, condRun, loopContext, bodyRun, afterBody, postRun, bind, Except.bind] at accepted
          | ok postResult =>
            simp only [initRun, condRun, bodyRun, postRun, loopContext, afterBody, bind, Except.bind,
              pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
            cases accepted
            have allocP := allocateStatementId_success_boundaries_progress allocation
            have initP := initIH _ initRun
            have condP := condIH initResult _ condRun
            have bodyP := bodyIH testState _ bodyRun
            have postP := postIH initResult bodyResult _ postRun
            have loopP := (condP.trans bodyP).restore initResult.state.lexicalScope (fun _ member => member)
            have headerP := (initP.trans (loopP.trans postP)).restore allocated.lexicalScope (fun _ member => member)
            have history := allocP.trans headerP
            have allocatedBinders : allocated.localBinders = initial.localBinders := by
              have same : initial.allocateStatementId.2 = allocated := congrArg Prod.snd allocation
              rw [← same]
              rfl
            let recordedNode : StatementNode := {
              id := id
              span := statement.span
              type := .unit
              form := .forLoop initResult.items test.id postResult.items bodyResult.statements
            }
            have recorded := LocalReadScopeProgress.Progress.recordStatement
              (postResult.state.restoreLexicalScope allocated.lexicalScope) recordedNode
            refine ⟨history.reads.trans (LocalReadEvents.Progress.recordStatement _ _), history.scope.trans recorded,
              history.binders, ?_⟩
            intro ready below node present
            have readyAlloc := ready.progress allocP.reads
            have belowAlloc := allocP.binders below
            have readyInit := readyAlloc.progress initP.reads
            have belowInit := initP.binders belowAlloc
            have readyBody := readyInit.progress loopP.reads
            have belowBody := loopP.binders belowInit
            rcases List.mem_append.mp present with old | fresh
            · rcases history.events ready below node old with old | event
              · exact .inl old
              · exact .inr (event.progress recorded)
            · cases Node.statement.inj (List.mem_singleton.mp fresh)
              have initBounds := ((inferForItemsFuel_boundaries initRun readyAlloc belowAlloc).progress loopP.scope).progress postP.scope
              have postBounds := inferForItemsFuel_boundaries postRun readyBody belowBody
              have initNext : initial.nextLocal ≤ allocated.nextLocal := allocP.scope.next
              have postEntry := Nat.le_trans initNext (Nat.le_trans initP.scope.next loopP.scope.next)
              have initialRestored := (initBounds.weaken initNext).restore_saved allocated.lexicalScope
                (initial := initial) (by simpa only [State.lexicalScope, allocatedBinders] using (List.Subset.refl initial.localBinders)) below (Nat.le_refl _)
              have postRestored := (postBounds.weaken postEntry).restore_saved allocated.lexicalScope
                (initial := initial) (by simpa only [State.lexicalScope, allocatedBinders] using (List.Subset.refl initial.localBinders)) below (Nat.le_refl _)
              exact .inr ⟨initialRestored.progress recorded, postRestored.progress recorded⟩
  case case44 =>
    intros context statement expectedReturn state fuel id stateAfterId
      statementIdEq scrutinees arms statementEq sources notSingleton
      casesInduction bodyInduction expressionsInduction
    unfold PreservesBoundaries at *
    intro result success
    have statementIdSubset :=
      allocateStatementId_success_boundaries_progress statementIdEq
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
      syntheticTuple_result_boundaries_progress (by assumption)
    all_goals try have tupleSubset :=
      syntheticTuple_pair_boundaries_progress (by assumption)
    all_goals try have defaultSubset :=
      pure_pair_result_boundaries_progress casesSubset (by assumption)
    all_goals simp_all only [exceptPure_eq_ok]
    all_goals try have restoredSubset :=
      restored_pair_result_boundaries_progress bodySubset (by simpa only [State.lexicalScope] using (List.Subset.refl _)) (by assumption)
    all_goals try
      have restoredWhole := restored_pair_result_boundaries_progress
        (Progress.trans casesSubset bodySubset) (fun _ member => member) (by assumption)
    all_goals try simp_all
    all_goals try exact Progress.refl _
    all_goals try exact Progress.recordStatement _ _ (by trivial)
    all_goals try solve | grind [Progress.trans, Progress.recordSelectedCallResult, Progress.recordSelectedCall,
      Progress.recordIndirectCall, Progress.fresh, Progress.withLocals, Progress.allocateBinder]
    all_goals first
      | apply Progress.trans (second := Progress.recordStatement _ _ (by trivial))
      | apply Progress.trans (second := Progress.recordExpression _ _ (by
          intro _ _ impossible; cases impossible))
      | skip
    all_goals try solve | grind [Progress.trans, Progress.restore, Progress.refl]
    all_goals try solve
      | exact statementIdSubset.trans (expressionsSubset.trans (tupleSubset.trans
          ((Progress.allocateHiddenLocal _).trans defaultSubset)))
    all_goals try solve
      | exact statementIdSubset.trans (expressionsSubset.trans (tupleSubset.trans
          ((Progress.allocateHiddenLocal _).trans restoredWhole)))
  case case70 =>
    intros fuel context target operator value state placeInduction valueInduction
    unfold PreservesBoundaries at *
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
    all_goals try exact Progress.recordStatement _ _ (by trivial)
    all_goals try solve | grind [Progress.trans, Progress.recordSelectedCallResult, Progress.recordSelectedCall,
      Progress.recordIndirectCall, Progress.fresh, Progress.withLocals, Progress.allocateBinder]
    all_goals first
      | apply Progress.trans (second := Progress.recordStatement _ _ (by trivial))
      | apply Progress.trans (second := Progress.recordExpression _ _ (by
          intro _ _ impossible; cases impossible))
      | skip
    all_goals try solve | grind [Progress.trans, Progress.restore, Progress.refl]
  case case67 =>
    unfold PreservesBoundaries at *
    intros
    simp_all only [inferPlaceFuel]
  all_goals
    intros
    unfold PreservesBoundaries at *
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
      allocateExpressionId_success_boundaries_progress (by assumption)
    all_goals try have statementIdSubset :=
      allocateStatementId_success_boundaries_progress (by assumption)
    all_goals try have freshSubset :=
      state_fresh_success_boundaries_progress (by assumption)
    all_goals try have hiddenLocalSubset :=
      allocateHiddenLocal_success_boundaries_progress (by assumption)
    all_goals try have requirementSubset :=
      addRequirementWithId_success_boundaries_progress (by assumption)
    all_goals try have requirementsSubset :=
      addRequirementsWithIds_success_boundaries_progress (by assumption)
    all_goals try have binderSubset :=
      allocateBinder_success_boundaries_progress (by assumption)
    all_goals try have constructorSubset :=
      freshDataConstructorInstantiation_success_boundaries_progress (by
        assumption)
    all_goals try have typesSubset :=
      freshTypes_success_boundaries_progress (by assumption)
    all_goals try have recordSubset :=
      Progress.recordExpressionWithExpected (by assumption) (by intro _ _ impossible; cases impossible)
    all_goals try have issuedRecord :=
      (Progress.addRequirementWithId _ _).trans recordSubset
    all_goals try have batchRecord :=
      (Progress.addRequirementsWithIds _ _).trans recordSubset
    all_goals try exact Progress.trans expressionIdSubset (Progress.trans (Progress.addRequirementWithId _ _) recordSubset)
    all_goals try exact Progress.trans expressionIdSubset (Progress.trans (Progress.addRequirementsWithIds _ _) recordSubset)
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
    all_goals try exact Progress.recordStatement _ _ (by trivial)
    all_goals try solve | grind [Progress.trans, Progress.recordSelectedCallResult, Progress.recordSelectedCall,
      Progress.recordIndirectCall, Progress.fresh, Progress.withLocals, Progress.allocateBinder]
    all_goals first
      | apply Progress.trans (second := Progress.recordStatement _ _ (by trivial))
      | apply Progress.trans (second := Progress.recordExpression _ _ (by
          intro _ _ impossible; cases impossible))
      | skip
    all_goals try solve | grind
      [Progress.trans, Progress.restore, Progress.refl,
        Progress.unify, Progress.addRequirementWithId,
        Progress.addRequirementsWithIds,
        Progress.freshDataConstructorInstantiation,
        Progress.freshTypes, Progress.fresh, Progress.allocateBinder, Progress.allocateHiddenLocal, Progress.allocateExpressionId, Progress.allocateStatementId,

        Progress.recordSelectedCallResult,
        Progress.recordSelectedCall,
        Progress.recordIndirectCall, Progress.recordStatement, Progress.modifyStatementNode, Progress.withLocals]

  all_goals expose_names
  all_goals try solve
    | apply Progress.trans expressionIdSubset
      apply Progress.trans (Progress.fresh state_1)
      apply Progress.trans (Progress.addRequirementWithId _ (ProgramSignatures.builtinIntPredicate (Ty.variable metavariable)))
      apply Progress.trans (second := recordSubset)
      exact Progress.of_unchanged rfl rfl (LocalReadEvents.Progress.refl _) (LocalReadScopeProgress.Progress.refl _)
  all_goals try solve
    | apply Progress.trans expressionIdSubset
      apply Progress.trans (second := batchRecord)
      exact Progress.of_unchanged rfl rfl (LocalReadEvents.Progress.refl _) (LocalReadScopeProgress.Progress.refl _)
  all_goals try solve
    | exact expressionIdSubset.trans
        ((lambdaSubset.trans ((Progress.unify heq_2).trans
          ((ih1 v_2 v_1 v_3 heq_4).trans unifiedSubset))).restored_then recordSubset)
  all_goals try solve
    | exact expressionIdSubset.trans
        ((lambdaSubset.trans ((Progress.unify heq_2).trans
          ((ih1 snd_1 v_1 v_2 heq_4).trans unifiedSubset))).restored_then recordSubset)
  all_goals try solve
    | exact expressionIdSubset.trans
        ((lambdaSubset.trans ((ih1 v_1 v.2.2 v_2 heq_3).trans unifiedSubset)).restored_then recordSubset)
  all_goals try solve
    | exact expressionIdSubset.trans
        ((lambdaSubset.trans ((Progress.fresh _).trans
          ((ih1 v.2.2.fresh.1 v.2.2.fresh.2 v_1 heq_2).trans unifiedSubset))).restored_then recordSubset)
  all_goals try solve
    | apply Progress.trans (second := Progress.allocateBinder _ _ _ _ _ _)
      apply Progress.trans (second := Progress.withLocals _ _)
      first
      | exact statementIdSubset
      | exact Progress.refl _
      | exact ih1 v.fst v.snd rfl
      | exact ih1 v v_1.fst v_1.snd heq_1
  all_goals try solve
    | have condStep := ih3 v.1 v.2 rfl
      exact statementIdSubset.trans (condStep.trans ((ih2 v.2 v_1 heq_1).restored_start))
  all_goals try solve
    | have condStep := ih3 v.1 v.2 rfl
      have thenStep := ih2 v.2 v_1 heq_1
      have elseStep := ih1 v.2 v_1 elseBody_1 v_2 heq_2
      exact statementIdSubset.trans (condStep.trans ((thenStep.restored_then elseStep).restored_start))
  all_goals try solve
    | exact statementIdSubset.trans ih1.restored_start
  all_goals try solve
    | have sameSource : source = source_1 := by grind
      rw [sameSource] at ih1
      have exprStep := ih1 v.1 v.2 heq_1
      have casesStep := ih3 v.1 v.2.allocateHiddenLocal.2 (fun _ member => member) v_1 heq_2
      exact statementIdSubset.trans (exprStep.trans ((Progress.allocateHiddenLocal _).trans casesStep))
  all_goals try solve
    | have sameSource : source = source_1 := by grind
      rw [sameSource] at ih1
      have exprStep := ih1 v.1 v.2 heq_1
      have casesStep := ih3 v.1 v.2.allocateHiddenLocal.2 (fun _ member => member) v_1 heq_2
      have bodyStep := ih2 v_1 elseBody_1 v_2 heq_4
      exact statementIdSubset.trans (exprStep.trans ((Progress.allocateHiddenLocal _).trans
        (casesStep.trans bodyStep).restored_start))
  all_goals try solve
    | have condStep := ih2 v.1 v.2 rfl
      exact statementIdSubset.trans (condStep.trans ((ih1 v.2 v_1 heq_1).restored_start))
  all_goals try solve
    | exact Progress.restored_saved_then (patternSubset.trans (ih2 v.2 v_1 heq_1)) h
        (ih1 v_1 (fun _ member => member) v_2 heq_2)


theorem inferExprFuel_boundaries_progress
    {fuel : Nat} {context : Context} {expression : Syntax.Expr}
    {expected : Option Ty} {state : State}
    {result : InferredExpression × State}
    (success : inferExprFuel fuel context expression expected state =
      .ok result) :
    Progress state result.2 := by
  exact inferFuel_boundaries_progress_internal.1 fuel context expression
    expected state result success

theorem inferConstructorApplicationFuel_boundaries_progress
    {fuel : Nat} {context : Context} {source : Syntax.Expr}
    {id : ExpressionId} {instantiation : DataConstructorInstantiation}
    {arguments : List Syntax.Expr} {expected : Option Ty} {state : State}
    {result : InferredExpression × State}
    (success : inferConstructorApplicationFuel fuel context source id
      instantiation arguments expected state = .ok result) :
    Progress state result.2 := by
  exact inferFuel_boundaries_progress_internal.2.1 fuel context source id
    instantiation arguments expected state result success

theorem inferConstructorArgumentsFuel_boundaries_progress
    {fuel : Nat} {context : Context} {sources : List Syntax.Expr}
    {expected : List Ty} {state : State}
    {result : List InferredExpression × State}
    (success : inferConstructorArgumentsFuel fuel context sources expected
      state = .ok result) :
    Progress state result.2 := by
  exact inferFuel_boundaries_progress_internal.2.2.1 fuel context sources
    expected state result success

theorem inferStatementsFuel_boundaries_progress
    {fuel : Nat} {context : Context} {statements : List Syntax.Statement}
    {expectedReturn : Ty} {state : State} {result : BlockResult}
    (success : inferStatementsFuel fuel context statements expectedReturn state =
      .ok result) :
    Progress state result.state := by
  exact inferFuel_boundaries_progress_internal.2.2.2.1 fuel context
    statements expectedReturn state result success

theorem inferStatementFuel_boundaries_progress
    {fuel : Nat} {context : Context} {statement : Syntax.Statement}
    {expectedReturn : Ty} {state : State} {result : StatementResult}
    (success : inferStatementFuel fuel context statement expectedReturn state =
      .ok result) :
    Progress state result.state := by
  exact inferFuel_boundaries_progress_internal.2.2.2.2.1 fuel context
    statement expectedReturn state result success

theorem inferForItemsFuel_boundaries_progress
    {fuel : Nat} {context : Context} {items : List Syntax.ForItem}
    {state : State} {result : InferredForItems}
    (success : inferForItemsFuel fuel context items state = .ok result) :
    Progress state result.state := by
  exact inferFuel_boundaries_progress_internal.2.2.2.2.2.1 fuel context
    items state result success

theorem inferForItemFuel_boundaries_progress
    {fuel : Nat} {context : Context} {item : Syntax.ForItem}
    {state : State} {result : ForItemForm × State}
    (success : inferForItemFuel fuel context item state = .ok result) :
    Progress state result.2 := by
  exact inferFuel_boundaries_progress_internal.2.2.2.2.2.2.1 fuel context
    item state result success

theorem inferPlaceFuel_boundaries_progress
    {fuel : Nat} {context : Context} {target : Syntax.Expr}
    {state : State} {result : PlaceResolution × State}
    (success : inferPlaceFuel fuel context target state = .ok result) :
    Progress state result.2 := by
  exact inferFuel_boundaries_progress_internal.2.2.2.2.2.2.2.1 fuel
    context target state result success

theorem inferAssignedValueFuel_boundaries_progress
    {fuel : Nat} {context : Context} {target : Syntax.Expr}
    {operator : Syntax.ValueAssignOp} {value : Syntax.Expr} {state : State}
    {result : AssignmentResolution × InferredExpression × State}
    (success : inferAssignedValueFuel fuel context target operator value state =
      .ok result) :
    Progress state result.2.2 := by
  exact inferFuel_boundaries_progress_internal.2.2.2.2.2.2.2.2.1 fuel
    context target operator value state result success

theorem inferExprsFuel_boundaries_progress
    {fuel : Nat} {context : Context} {expressions : List Syntax.Expr}
    {state : State} {result : List InferredExpression × State}
    (success : inferExprsFuel fuel context expressions state = .ok result) :
    Progress state result.2 := by
  exact inferFuel_boundaries_progress_internal.2.2.2.2.2.2.2.2.2.1 fuel
    context expressions state result success

theorem inferMatchCasesFuel_boundaries_progress
    {fuel : Nat} {context : Context} {scrutineeType expectedReturn : Ty}
    {outerScope : LexicalScope} {cases : List Syntax.MatchCase}
    {state : State} {result : MatchCasesResult}
    (saved : outerScope.binders ⊆ state.localBinders)
    (success : inferMatchCasesFuel fuel context scrutineeType expectedReturn
      outerScope cases state = .ok result) :
    Progress state result.state := by
  exact inferFuel_boundaries_progress_internal.2.2.2.2.2.2.2.2.2.2 fuel
    context scrutineeType expectedReturn outerScope cases state saved result success

end Solcore.Frontend.SourceInference.LocalGeneralizationBoundaries
end
