import Solcore.Frontend.SourceInference.Internal.LocalReadScopes
import Solcore.Frontend.SourceInference.Internal.ExpressionProperties

/-!
# Local generalization

Initialized bindings keep the inference action that generalized them, and its boundaries.
-/

section
-- leanmerge: from Solcore.Frontend.SourceInference.LocalGeneralizationEvents
/-! Initialized bindings retain the exact inference action that generalized
its initializer. Statement declarations and for headers remain distinct. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.Frontend.SourceInference.LocalGeneralizationEvents
open TypeSystem Detail

structure Ready (state : State) : Prop where
  wellFormed : state.RequirementsWellFormed
  allocated : state.DirectRequirementsAllocated
  origins : LocalReadEvents.Origins state

theorem Ready.progress {before after : State} (ready : Ready before)
    (progress : LocalReadEvents.Progress before after) : Ready after :=
  ⟨progress.ledger.wellFormed ready.wellFormed,
    progress.ledger.allocated ready.wellFormed ready.allocated,
    progress.origins ready.wellFormed ready.allocated ready.origins⟩

inductive Origin : TypedBinder → ExpressionId → Prop where
  | statement {fuel context source initial result}
      (receipt : LocalLetRequirementTiming.Receipt fuel context source initial result)
      (ready : Ready initial) : Origin receipt.binding.1 receipt.value.id
  | header {fuel context source initial result}
      (receipt : LocalHeaderRequirementTiming.Receipt fuel context source initial result)
      (ready : Ready initial) : Origin receipt.binding.1 receipt.value.id

def Item (item : ForItemForm) : Prop :=
  ∀ binder initializer, item = .letDecl binder (some initializer) → Origin binder initializer

def Items (items : List ForItemForm) : Prop := ∀ item ∈ items, Item item

def Statement (node : StatementNode) : Prop :=
  match node.form with
  | .letDecl binder (some initializer) => Origin binder initializer
  | .forLoop initial _ post _ => Items initial ∧ Items post
  | _ => True

def Origins (nodes : List Node) : Prop :=
  ∀ node, .statement node ∈ nodes → Statement node

theorem Origins.empty : Origins [] := by intro _ impossible; cases impossible

theorem Origins.expression {nodes : List Node} (origins : Origins nodes) (node : ExpressionNode) :
    Origins (nodes ++ [.expression node]) := by
  intro statement present
  rcases List.mem_append.mp present with previous | fresh
  · exact origins statement previous
  · cases List.mem_singleton.mp fresh

theorem Origins.statement {nodes : List Node} (origins : Origins nodes)
    (node : StatementNode) (event : Statement node) : Origins (nodes ++ [.statement node]) := by
  intro statement present
  rcases List.mem_append.mp present with previous | fresh
  · exact origins statement previous
  · cases List.mem_singleton.mp fresh
    exact event

theorem Origins.mapExpressions {nodes : List Node} (origins : Origins nodes)
    (modify : ExpressionNode → ExpressionNode) :
    Origins (nodes.map (fun node => match node with
      | .expression expression => .expression (modify expression)
      | .statement statement => .statement statement)) := by
  intro statement present
  obtain ⟨node, member, selected⟩ := List.mem_map.mp present
  cases node with
  | expression expression => cases selected
  | statement original =>
    cases selected
    exact origins _ member

theorem Statement.same_form {before after : StatementNode} (origin : Statement before)
    (same : after.form = before.form) : Statement after := by
  unfold Statement
  rw [same]
  exact origin

theorem Origins.mapStatements {nodes : List Node} (origins : Origins nodes)
    (modify : StatementNode → StatementNode) (forms : ∀ node, (modify node).form = node.form) :
    Origins (nodes.map (fun node => match node with
      | .expression expression => .expression expression
      | .statement statement => .statement (modify statement))) := by
  intro statement present
  obtain ⟨node, member, selected⟩ := List.mem_map.mp present
  cases node with
  | expression expression => cases selected
  | statement original =>
    cases selected
    exact (origins original member).same_form (forms original)

theorem Item.of_header {fuel context source initial result}
    (receipt : LocalHeaderRequirementTiming.Receipt fuel context source initial result)
    (ready : Ready initial) : Item result.1 := by
  intro binder initializer same
  rw [receipt.recorded] at same
  cases same
  exact .header receipt ready

theorem Statement.of_let {fuel context source initial result}
    (receipt : LocalLetRequirementTiming.Receipt fuel context source initial result)
    (ready : Ready initial) {node : StatementNode}
    (form : node.form = .letDecl receipt.binding.1 (some receipt.value.id)) : Statement node := by
  unfold Statement
  rw [form]
  exact .statement receipt ready

end Solcore.Frontend.SourceInference.LocalGeneralizationEvents
end

section
-- leanmerge: from Solcore.Frontend.SourceInference.LocalGeneralizationBinderRetention
/-! Inference can attach evidence to expression nodes while preserving every
initialized declaration. Retention therefore tracks binders in statement
forms, independently of changes to expression nodes. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.Frontend.SourceInference.LocalGeneralizationEvents
open TypeSystem Detail

def BindersRetained (before after : List Node) : Prop :=
  before.flatMap Node.initializedLetBinders ⊆ after.flatMap Node.initializedLetBinders

namespace BindersRetained

theorem refl (nodes : List Node) : BindersRetained nodes nodes := fun _ present => present

theorem trans {before middle after : List Node}
    (first : BindersRetained before middle) (second : BindersRetained middle after) :
    BindersRetained before after := fun _ present => second (first present)

theorem append (nodes suffix : List Node) : BindersRetained nodes (nodes ++ suffix) := by
  intro binder present
  rw [List.flatMap_append]
  exact List.mem_append_left _ present

theorem modifyExpressionNode (state : State) (id : ExpressionId)
    (modify : ExpressionNode → ExpressionNode) :
    BindersRetained state.nodes (state.modifyExpressionNode id modify).nodes := by
  intro binder present
  obtain ⟨node, member, inside⟩ := List.mem_flatMap.mp present
  cases node with
  | expression node => cases inside
  | statement node =>
    exact List.mem_flatMap.mpr ⟨.statement node,
      List.mem_map.mpr ⟨.statement node, member, rfl⟩, inside⟩

theorem modifyStatementNode (state : State) (id : StatementId)
    (modify : StatementNode → StatementNode)
    (sameForm : ∀ node, (modify node).form = node.form) :
    BindersRetained state.nodes (state.modifyStatementNode id modify).nodes := by
  intro binder present
  obtain ⟨node, member, inside⟩ := List.mem_flatMap.mp present
  cases node with
  | expression node => cases inside
  | statement node =>
    by_cases selected : node.id = id
    · refine List.mem_flatMap.mpr ⟨.statement { modify node with id := id },
        List.mem_map.mpr ⟨.statement node, member, ?_⟩, ?_⟩
      · simp [selected]
      · simpa only [Node.initializedLetBinders, sameForm] using inside
    · refine List.mem_flatMap.mpr ⟨.statement node,
        List.mem_map.mpr ⟨.statement node, member, ?_⟩, inside⟩
      simp [selected]

theorem attachExpressionCoercions (state : State) (entries : List ExpressionCoercions) :
    BindersRetained state.nodes (Detail.attachExpressionCoercions state entries).nodes := by
  unfold Detail.attachExpressionCoercions
  induction entries generalizing state with
  | nil => exact .refl _
  | cons entry rest ih => exact (modifyExpressionNode _ _ _).trans (ih _)

theorem recordExpression (state : State) (source : Syntax.Expr)
    (expression : InferredExpression) (form : ExpressionForm)
    (requirements : List RequirementId) (coercions : List CoercionStep)
    (start : Option Nat := none) :
    BindersRetained state.nodes
      (Detail.recordExpression source expression form requirements coercions state start).2.nodes :=
  append _ _

theorem recordExpressionWithExpected {context : Context} {source : Syntax.Expr}
    {id : ExpressionId} {type : Ty} {form : ExpressionForm}
    {requirements : List RequirementId} {expected : Option Ty} {state : State}
    {start : Option Nat} {result : InferredExpression × State}
    (accepted : Detail.recordExpressionWithExpected context source id type form
      requirements expected state start = .ok result) :
    BindersRetained state.nodes result.2.nodes := by
  obtain ⟨fitted, fit, _, recorded⟩ := Detail.recordExpressionWithExpected_success_record accepted
  rw [recorded]
  have same := (Detail.withExpected_occurrenceState_eq fit).1
  change BindersRetained state.nodes (fitted.state.nodes ++ _)
  rw [same]
  exact append _ _

theorem recordSelectedCallResult (source callee : Syntax.Expr) (name : String)
    (arguments : List InferredExpression) (attempt : CandidateAttemptResult)
    (result : InferredExpression) (trailingCoercions : List CoercionStep) (state : State) :
    BindersRetained state.nodes
      (Detail.recordSelectedCallResult source callee name arguments attempt result
        trailingCoercions state).2.nodes := by
  unfold Detail.recordSelectedCallResult
  exact (attachExpressionCoercions _ _).trans
    ((recordExpression _ _ _ _ _ _ _).trans (recordExpression _ _ _ _ _ _ _))

end BindersRetained
end Solcore.Frontend.SourceInference.LocalGeneralizationEvents
end

section
-- leanmerge: from Solcore.Frontend.SourceInference.LocalGeneralizationBoundaries
/-! Generalization events retain an interval of initializer-local identities.
The final state is explicit: later reads of a retired initializer local must
come from the recorded initializer, including across saved scope restoration. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.Frontend.SourceInference.LocalGeneralizationBoundaries
open TypeSystem Detail
open LocalGeneralizationEvents (Ready)
open LocalReadScopeProgress (Barrier Progress)

/-- Both event constructors retain the actual initializer entry, return state,
annotation resolution and generalization cutoff. -/
inductive Boundary : TypedBinder → ExpressionId → Nat → Nat → List Node → Prop where
  | statement {fuel context source initial result}
      (receipt : LocalLetRequirementTiming.Receipt fuel context source initial result)
      (ready : Ready initial) (below : initial.LocalBindersBelowNextLocal) :
      Boundary receipt.binding.1 receipt.value.id initial.nextLocal receipt.ready.nextLocal receipt.ready.nodes
  | header {fuel context source initial result}
      (receipt : LocalHeaderRequirementTiming.Receipt fuel context source initial result)
      (ready : Ready initial) (below : initial.LocalBindersBelowNextLocal) :
      Boundary receipt.binding.1 receipt.value.id initial.nextLocal receipt.ready.nextLocal receipt.ready.nodes

/-- The event occurred after a real traversal entry boundary. This lower bound
justifies restoring outer binders saved before the event's initializer. -/
def OriginSince (entry : Nat) (state : State) (binder : TypedBinder) (initializer : ExpressionId) : Prop :=
  ∃ low high nodes, entry ≤ low ∧ Boundary binder initializer low high nodes ∧ Barrier low high nodes state

def ItemSince (entry : Nat) (state : State) (item : ForItemForm) : Prop :=
  ∀ binder initializer, item = .letDecl binder (some initializer) → OriginSince entry state binder initializer

def ItemsSince (entry : Nat) (state : State) (items : List ForItemForm) : Prop :=
  ∀ item ∈ items, ItemSince entry state item

def StatementSince (entry : Nat) (state : State) (node : StatementNode) : Prop :=
  match node.form with
  | .letDecl binder (some initializer) => OriginSince entry state binder initializer
  | .forLoop initial _ post _ => ItemsSince entry state initial ∧ ItemsSince entry state post
  | _ => True

namespace OriginSince

theorem weaken {entry earlier : Nat} {state : State} {binder : TypedBinder} {initializer : ExpressionId}
    (origin : OriginSince entry state binder initializer) (before : earlier ≤ entry) :
    OriginSince earlier state binder initializer := by
  obtain ⟨low, high, nodes, entered, event, barrier⟩ := origin
  exact ⟨low, high, nodes, Nat.le_trans before entered, event, barrier⟩

theorem progress {entry : Nat} {before after : State} {binder : TypedBinder} {initializer : ExpressionId}
    (origin : OriginSince entry before binder initializer) (step : Progress before after) :
    OriginSince entry after binder initializer := by
  obtain ⟨low, high, nodes, entered, event, barrier⟩ := origin
  exact ⟨low, high, nodes, entered, event, barrier.progress step⟩

/-- The exact saved scope is checked against the actual entry allocator bound;
it need not still be a subset of the current binder stack. -/
theorem restore_saved {entry : Nat} {state initial : State} {binder : TypedBinder} {initializer : ExpressionId}
    (origin : OriginSince entry state binder initializer) (scope : LexicalScope)
    (saved : scope.binders ⊆ initial.localBinders) (below : initial.LocalBindersBelowNextLocal)
    (entered : initial.nextLocal ≤ entry) :
    OriginSince entry (state.restoreLexicalScope scope) binder initializer := by
  obtain ⟨low, high, nodes, later, event, barrier⟩ := origin
  exact ⟨low, high, nodes, later, event,
    barrier.restore_saved scope saved below (Nat.le_trans entered later)⟩

/-- Erasing the continuation evidence preserves the genuine inference event. -/
theorem origin {entry : Nat} {state : State} {binder : TypedBinder} {initializer : ExpressionId}
    (bounded : OriginSince entry state binder initializer) : LocalGeneralizationEvents.Origin binder initializer := by
  obtain ⟨low, high, nodes, _, event, _⟩ := bounded
  cases event with
  | statement receipt ready _ => exact .statement receipt ready
  | header receipt ready _ => exact .header receipt ready

end OriginSince

namespace ItemSince

theorem progress {entry : Nat} {before after : State} {item : ForItemForm}
    (origin : ItemSince entry before item) (step : Progress before after) : ItemSince entry after item :=
  fun _ _ same => (origin _ _ same).progress step

theorem weaken {entry earlier : Nat} {state : State} {item : ForItemForm}
    (origin : ItemSince entry state item) (before : earlier ≤ entry) : ItemSince earlier state item :=
  fun _ _ same => (origin _ _ same).weaken before

theorem restore_saved {entry : Nat} {state initial : State} {item : ForItemForm}
    (origin : ItemSince entry state item) (scope : LexicalScope)
    (saved : scope.binders ⊆ initial.localBinders) (below : initial.LocalBindersBelowNextLocal)
    (entered : initial.nextLocal ≤ entry) : ItemSince entry (state.restoreLexicalScope scope) item :=
  fun _ _ same => (origin _ _ same).restore_saved scope saved below entered

end ItemSince

namespace ItemsSince

theorem progress {entry : Nat} {before after : State} {items : List ForItemForm}
    (origin : ItemsSince entry before items) (step : Progress before after) : ItemsSince entry after items :=
  fun _ member => (origin _ member).progress step

theorem weaken {entry earlier : Nat} {state : State} {items : List ForItemForm}
    (origin : ItemsSince entry state items) (before : earlier ≤ entry) : ItemsSince earlier state items :=
  fun _ member => (origin _ member).weaken before

theorem restore_saved {entry : Nat} {state initial : State} {items : List ForItemForm}
    (origin : ItemsSince entry state items) (scope : LexicalScope)
    (saved : scope.binders ⊆ initial.localBinders) (below : initial.LocalBindersBelowNextLocal)
    (entered : initial.nextLocal ≤ entry) : ItemsSince entry (state.restoreLexicalScope scope) items :=
  fun _ member => (origin _ member).restore_saved scope saved below entered

end ItemsSince

namespace StatementSince

theorem progress {entry : Nat} {before after : State} {node : StatementNode}
    (origin : StatementSince entry before node) (step : Progress before after) : StatementSince entry after node := by
  unfold StatementSince at *
  split at origin
  · exact origin.progress step
  · exact ⟨origin.1.progress step, origin.2.progress step⟩
  · trivial

theorem weaken {entry earlier : Nat} {state : State} {node : StatementNode}
    (origin : StatementSince entry state node) (before : earlier ≤ entry) : StatementSince earlier state node := by
  unfold StatementSince at *
  split at origin
  · exact origin.weaken before
  · exact ⟨origin.1.weaken before, origin.2.weaken before⟩
  · trivial

theorem restore_saved {entry : Nat} {state initial : State} {node : StatementNode}
    (origin : StatementSince entry state node) (scope : LexicalScope)
    (saved : scope.binders ⊆ initial.localBinders) (below : initial.LocalBindersBelowNextLocal)
    (entered : initial.nextLocal ≤ entry) : StatementSince entry (state.restoreLexicalScope scope) node := by
  unfold StatementSince at *
  split at origin
  · exact origin.restore_saved scope saved below entered
  · exact ⟨origin.1.restore_saved scope saved below entered, origin.2.restore_saved scope saved below entered⟩
  · trivial

theorem same_form {entry : Nat} {state : State} {before after : StatementNode}
    (origin : StatementSince entry state before) (same : after.form = before.form) :
    StatementSince entry state after := by
  unfold StatementSince
  rw [same]
  exact origin

end StatementSince
end Solcore.Frontend.SourceInference.LocalGeneralizationBoundaries
end

section
-- leanmerge: from Solcore.Frontend.SourceInference.LocalGeneralizationRetiredInterval
/-! Actual initialized let receipts establish the retired-local interval at
the return of the initializer. Header declarations and ordinary statements
retain their respective allocation and node-recording behavior. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.Frontend.SourceInference
open TypeSystem Detail LocalReadScopeProgress

namespace LocalLetRequirementTiming.Receipt
variable {fuel : Nat} {context : Context} {statement : Syntax.Statement}
    {initial : State} {result : StatementResult}

theorem retired_interval (receipt : Receipt fuel context statement initial result)
    (below : initial.LocalBindersBelowNextLocal) :
    Barrier initial.nextLocal receipt.ready.nextLocal receipt.ready.nodes result.state := by
  have next := congrArg (fun value : StatementResult => value.state.nextLocal) receipt.completed
  change result.state.nextLocal = receipt.ready.nextLocal + 1 at next
  have nodes := congrArg (fun value : StatementResult => value.state.nodes) receipt.completed
  refine ⟨by rw [next]; omega, ?_, ?_⟩
  · intro id created retired binder present same
    rw [receipt.result_binders] at present
    rcases List.mem_cons.mp present with current | entering
    · subst binder
      have index := congrArg Resolved.LocalId.binderIndex same
      change receipt.ready.nextLocal = id.binderIndex at index
      omega
    · have older := below binder entering
      rw [same] at older
      omega
  · intro id _ _ occurrence ⟨expression, member, same, name, form⟩
    rw [nodes] at member
    rcases List.mem_append.mp member with old | recorded
    · exact ⟨expression, old, same, name, form⟩
    · cases List.mem_singleton.mp recorded

end LocalLetRequirementTiming.Receipt

namespace LocalHeaderRequirementTiming.Receipt
variable {fuel : Nat} {context : Context} {item : Syntax.ForItem}
    {initial : State} {result : ForItemForm × State}

theorem retired_interval (receipt : Receipt fuel context item initial result)
    (below : initial.LocalBindersBelowNextLocal) :
    Barrier initial.nextLocal receipt.ready.nextLocal receipt.ready.nodes result.2 := by
  have next := congrArg (fun value : ForItemForm × State => value.2.nextLocal) receipt.completed
  change result.2.nextLocal = receipt.ready.nextLocal + 1 at next
  have nodes : result.2.nodes = receipt.ready.nodes :=
    congrArg (fun value : ForItemForm × State => value.2.nodes) receipt.completed
  refine ⟨by rw [next]; omega, ?_, ?_⟩
  · intro id created retired binder present same
    rw [receipt.result_binders] at present
    rcases List.mem_cons.mp present with current | entering
    · subst binder
      have index := congrArg Resolved.LocalId.binderIndex same
      change receipt.ready.nextLocal = id.binderIndex at index
      omega
    · have older := below binder entering
      rw [same] at older
      omega
  · intro id _ _ occurrence read
    simpa only [nodes] using read

end LocalHeaderRequirementTiming.Receipt
end Solcore.Frontend.SourceInference
end

section
-- leanmerge: from Solcore.Frontend.SourceInference.LocalGeneralizationBoundaryReceipts
/-! Authentic initialized declarations establish their continuation boundary.
Operational local requirements are recovered at the initializer return state,
so the final node table is never treated as an earlier inference ledger. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.Frontend.SourceInference.LocalGeneralizationBoundaries
open TypeSystem Detail
open LocalGeneralizationEvents (Ready)
open LocalReadScopeProgress (ReadAt)

namespace OriginSince

theorem statement {fuel context source initial result}
    (receipt : LocalLetRequirementTiming.Receipt fuel context source initial result)
    (ready : Ready initial) (below : initial.LocalBindersBelowNextLocal) :
    OriginSince initial.nextLocal result.state receipt.binding.1 receipt.value.id :=
  ⟨_, _, _, Nat.le_refl _, .statement receipt ready below, receipt.retired_interval below⟩

theorem header {fuel context source initial result}
    (receipt : LocalHeaderRequirementTiming.Receipt fuel context source initial result)
    (ready : Ready initial) (below : initial.LocalBindersBelowNextLocal) :
    OriginSince initial.nextLocal result.2 receipt.binding.1 receipt.value.id :=
  ⟨_, _, _, Nat.le_refl _, .header receipt ready below, receipt.retired_interval below⟩

end OriginSince

theorem ItemSince.of_header {fuel context source initial result}
    (receipt : LocalHeaderRequirementTiming.Receipt fuel context source initial result)
    (ready : Ready initial) (below : initial.LocalBindersBelowNextLocal) :
    ItemSince initial.nextLocal result.2 result.1 := by
  intro binder initializer same
  rw [receipt.recorded] at same
  cases same
  exact OriginSince.header receipt ready below

theorem StatementSince.of_let {fuel context source initial result}
    (receipt : LocalLetRequirementTiming.Receipt fuel context source initial result)
    (ready : Ready initial) (below : initial.LocalBindersBelowNextLocal) {node : StatementNode}
    (form : node.form = .letDecl receipt.binding.1 (some receipt.value.id)) :
    StatementSince initial.nextLocal result.state node := by
  unfold StatementSince
  rw [form]
  exact OriginSince.statement receipt ready below

/-- The exact lookup requirements at the generalization boundary exclude their
variables from the recorded binder's quantified variables. -/
theorem Boundary.local_generalization {binder : TypedBinder} {initializer : ExpressionId}
    {low high : Nat} {nodes : List Node} (boundary : Boundary binder initializer low high nodes)
    {node : ExpressionNode} (member : .expression node ∈ nodes) {name : String} {localId : Resolved.LocalId}
    (form : node.form = .reference name (.local localId)) :
    ∃ ready : State, ∃ lookup : LocalReadEvents.Lookup,
      ready.nodes = nodes ∧ node.id = lookup.id ∧
      node.form = .reference lookup.name.value (.local lookup.binder.id) ∧
      node.localSchemeInstantiationStart = some lookup.allocated.inference.next ∧
      lookup.batch.1 <+: node.requirements ∧
      RequirementPredicatesCorrespond ready.requirements lookup.predicates lookup.batch.1 ∧
      (∀ requirement ∈ ready.requirements, requirement.id ∈ lookup.batch.1 →
        ∀ metavariable ∈ TypedTraitResolution.predicateVariables (applyPredicate ready requirement.predicate),
          metavariable ∉ binder.scheme.quantified) := by
  cases boundary with
  | statement receipt ready below =>
      obtain ⟨lookup, id, actualForm, start, batchPrefix, predicates, blocked⟩ :=
        receipt.local_generalization ready.wellFormed ready.allocated ready.origins member form
      exact ⟨receipt.ready, lookup, rfl, id, actualForm, start, batchPrefix, predicates, blocked⟩
  | header receipt ready below =>
      obtain ⟨lookup, id, actualForm, start, batchPrefix, predicates, blocked⟩ :=
        receipt.local_generalization ready.wellFormed ready.allocated ready.origins member form
      exact ⟨receipt.ready, lookup, rfl, id, actualForm, start, batchPrefix, predicates, blocked⟩

/-- A continuation read of an initializer-local ID is pulled back to the exact
initializer occurrence before applying the real generalization result. -/
theorem Boundary.retired_read_generalization {binder : TypedBinder} {initializer : ExpressionId}
    {low high : Nat} {nodes : List Node} {state : State}
    (boundary : Boundary binder initializer low high nodes)
    (barrier : LocalReadScopeProgress.Barrier low high nodes state)
    {node : ExpressionNode} (member : .expression node ∈ state.nodes) {name : String} {localId : Resolved.LocalId}
    (form : node.form = .reference name (.local localId))
    (created : low ≤ localId.binderIndex) (retired : localId.binderIndex < high) :
    ∃ ready : State, ∃ original : ExpressionNode, ∃ lookup : LocalReadEvents.Lookup,
      ready.nodes = nodes ∧ .expression original ∈ ready.nodes ∧ original.id = node.id ∧
      original.id = lookup.id ∧ lookup.binder.id = localId ∧ original.form = .reference lookup.name.value (.local lookup.binder.id) ∧
      original.localSchemeInstantiationStart = some lookup.allocated.inference.next ∧
      lookup.batch.1 <+: original.requirements ∧
      RequirementPredicatesCorrespond ready.requirements lookup.predicates lookup.batch.1 ∧
      (∀ requirement ∈ ready.requirements, requirement.id ∈ lookup.batch.1 →
        ∀ metavariable ∈ TypedTraitResolution.predicateVariables (applyPredicate ready requirement.predicate),
          metavariable ∉ binder.scheme.quantified) := by
  obtain ⟨original, present, same, actualName, actualForm⟩ := barrier.read created retired member form
  obtain ⟨ready, lookup, actualNodes, id, reference, start, batchPrefix, predicates, blocked⟩ :=
    boundary.local_generalization present actualForm
  have sameLocal : lookup.binder.id = localId :=
    ReferenceResolution.local.inj (ExpressionForm.reference.inj (reference.symm.trans actualForm)).2
  exact ⟨ready, original, lookup, actualNodes, actualNodes.symm ▸ present, same,
    id, sameLocal, reference, start, batchPrefix, predicates, blocked⟩

end Solcore.Frontend.SourceInference.LocalGeneralizationBoundaries
end

section
-- leanmerge: from Solcore.Frontend.SourceInference.LocalGeneralizationHeaderBoundaries
/-! Each actual header initializer retains its retired-read boundary through
the remaining header items. Later initializers use their real entry states. -/
set_option autoImplicit false
set_option Elab.async false
set_option linter.unusedSimpArgs false
namespace Solcore.Frontend.SourceInference.LocalGeneralizationBoundaries
open TypeSystem Detail
open LocalGeneralizationEvents (Ready)

theorem inferForItemFuel_boundary {fuel : Nat} {context : Context} {item : Syntax.ForItem}
    {state : State} {result : ForItemForm × State}
    (accepted : inferForItemFuel fuel context item state = .ok result)
    (ready : Ready state) (below : state.LocalBindersBelowNextLocal) :
    ItemSince state.nextLocal result.2 result.1 := by
  cases fuel with
  | zero => simp [inferForItemFuel, throw] at accepted
  | succ fuel =>
    cases form : item.value with
    | letDecl name annotation initializer =>
      cases initializer with
      | some initializer =>
        obtain ⟨receipt⟩ := LocalHeaderRequirementTiming.of_initialized_accepted form accepted
        exact ItemSince.of_header receipt ready below
      | none =>
        unfold inferForItemFuel at accepted
        simp only [form, bind, Except.bind] at accepted
        repeat' first | split at accepted
        all_goals simp_all [ItemSince, pure, Pure.pure, Except.pure, throw]
        all_goals subst_vars
        all_goals simp_all [ItemSince]
    | expression expression | assignValue target operator value | assignBitNot target token =>
      unfold inferForItemFuel at accepted
      simp only [form, bind, Except.bind] at accepted
      repeat' first | split at accepted
      all_goals simp_all [ItemSince, pure, Pure.pure, Except.pure, throw]
      all_goals subst_vars
      all_goals simp_all [ItemSince]

theorem inferForItemsFuel_boundaries {fuel : Nat} {context : Context} {items : List Syntax.ForItem}
    {state : State} {result : InferredForItems}
    (accepted : inferForItemsFuel fuel context items state = .ok result)
    (ready : Ready state) (below : state.LocalBindersBelowNextLocal) :
    ItemsSince state.nextLocal result.state result.items := by
  induction items generalizing state result with
  | nil =>
    simp only [inferForItemsFuel, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
    cases accepted
    intro item impossible
    cases impossible
  | cons item items ih =>
    unfold inferForItemsFuel at accepted
    cases first : inferForItemFuel fuel context item state with
    | error error => simp [first, bind, Except.bind] at accepted
    | ok pair =>
      rcases pair with ⟨head, next⟩
      cases tail : inferForItemsFuel fuel context items next with
      | error error => simp [first, tail, bind, Except.bind, Functor.map, Except.map] at accepted
      | ok rest =>
        simp only [first, tail, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
        cases accepted
        intro value member
        rcases List.mem_cons.mp member with same | remaining
        · cases same
          have following := LocalReadScopeProgress.inferForItemsFuel_scope_progress tail
          exact (inferForItemFuel_boundary first ready below).progress following
        · exact ((ih tail (ready.progress (LocalReadEvents.inferForItemFuel_origins_progress first))
            (inferForItemFuel_preserves_localBindersBelowNextLocal below first)) value remaining).weaken
              (inferForItemFuel_nextLocal_le first)

end Solcore.Frontend.SourceInference.LocalGeneralizationBoundaries
end

section
-- leanmerge: from Solcore.Frontend.SourceInference.LocalGeneralizationForBoundary
/-! A real for-statement carries header generalization boundaries through its
condition, body, post items, and both actual lexical scope restorations. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.Frontend.SourceInference.LocalGeneralizationBoundaries
open TypeSystem Detail
open LocalGeneralizationEvents (Ready)

/-- Every initialized header binder of the actual returned for node has its
initializer-local reads contained in the real initializer return state. -/
theorem inferStatementFuel_for_boundary {fuel : Nat} {context : Context}
    {statement : Syntax.Statement} {expected : Ty} {initial : State} {result : StatementResult}
    {headerSpan : Syntax.SourceSpan} {initializers post : List Syntax.ForItem}
    {condition : Syntax.Expr} {body : Syntax.Located (List Syntax.Statement)}
    (form : statement.value = .forLoop headerSpan initializers condition post body)
    (accepted : inferStatementFuel (fuel + 1) context statement expected initial = .ok result)
    (ready : Ready initial) (below : initial.LocalBindersBelowNextLocal) :
    ∃ node : StatementNode, .statement node ∈ result.state.nodes ∧ node.id = result.id ∧
      StatementSince initial.nextLocal result.state node := by
  unfold inferStatementFuel at accepted
  simp only [form, bind, Except.bind] at accepted
  let allocated := initial.allocateStatementId.2
  cases initRun : inferForItemsFuel fuel context initializers allocated with
  | error error => simp [allocated, initRun] at accepted
  | ok initResult =>
    cases condRun : inferExprFuel fuel context condition (some .bool) initResult.state with
    | error error => simp [allocated, initRun, condRun] at accepted
    | ok pair =>
      rcases pair with ⟨test, testState⟩
      let loopContext := { context with loopDepth := context.loopDepth + 1 }
      cases bodyRun : inferStatementsFuel fuel loopContext body.value expected testState with
      | error error => simp [allocated, initRun, condRun, loopContext, bodyRun] at accepted
      | ok bodyResult =>
        let afterBody := bodyResult.state.restoreLexicalScope initResult.state.lexicalScope
        cases postRun : inferForItemsFuel fuel loopContext post afterBody with
        | error error => simp [allocated, initRun, condRun, loopContext, bodyRun, afterBody, postRun] at accepted
        | ok postResult =>
          simp only [allocated, initRun, condRun, loopContext, bodyRun, afterBody, postRun,
            pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
          cases accepted
          have readyAllocated : Ready allocated := ⟨ready.wellFormed, ready.allocated, ready.origins⟩
          have belowAllocated : allocated.LocalBindersBelowNextLocal := below
          have readyInit := readyAllocated.progress (LocalReadEvents.inferForItemsFuel_origins_progress initRun)
          have belowInit := inferForItemsFuel_preserves_localBindersBelowNextLocal belowAllocated initRun
          have condScope := LocalReadScopeProgress.inferExprFuel_scope_progress condRun
          have bodyScope := LocalReadScopeProgress.inferStatementsFuel_scope_progress bodyRun
          have loopScope : LocalReadScopeProgress.Progress initResult.state afterBody :=
            (condScope.trans bodyScope).restore (fun _ member => member)
          have readyBody : Ready afterBody :=
            (readyInit.progress (LocalReadEvents.inferExprFuel_origins_progress condRun)).progress
              (LocalReadEvents.inferStatementsFuel_origins_progress bodyRun)
          have belowBody : afterBody.LocalBindersBelowNextLocal := by
            intro binder member
            exact Nat.lt_of_lt_of_le (belowInit binder member) loopScope.next
          have initBounds := (inferForItemsFuel_boundaries initRun readyAllocated belowAllocated).progress loopScope
          have postBounds := inferForItemsFuel_boundaries postRun readyBody belowBody
          have initNext := inferForItemsFuel_nextLocal_le initRun
          have postEntry : initial.nextLocal ≤ afterBody.nextLocal := Nat.le_trans initNext loopScope.next
          have postScope := LocalReadScopeProgress.inferForItemsFuel_scope_progress postRun
          have initialAtPost := initBounds.progress postScope
          have initialRestored := initialAtPost.restore_saved allocated.lexicalScope
            (initial := initial) (fun _ member => member) below (Nat.le_refl _)
          have postRestored := (postBounds.weaken postEntry).restore_saved allocated.lexicalScope
            (initial := initial) (fun _ member => member) below (Nat.le_refl _)
          refine ⟨_, List.mem_append_right _ (List.mem_singleton_self _), rfl, ?_⟩
          exact ⟨initialRestored.progress (LocalReadScopeProgress.Progress.recordStatement _ _),
            postRestored.progress (LocalReadScopeProgress.Progress.recordStatement _ _)⟩

end Solcore.Frontend.SourceInference.LocalGeneralizationBoundaries
end

section
-- leanmerge: from Solcore.Frontend.SourceInference.LocalGeneralizationProgress
/-! The actual read-origin progress supplies each nested initializer's entry
invariants. Generalization events preserve exact statement forms. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.Frontend.SourceInference.LocalGeneralizationEvents
open TypeSystem Detail
open State (DirectRequirementsProgress)

structure ProgressFields
    (beforeNodes : List Node) (beforeRows : List Requirement) (beforeNext : Nat) (beforeDirect : List RequirementId)
    (afterNodes : List Node) (afterRows : List Requirement) (afterNext : Nat) (afterDirect : List RequirementId) : Prop where
  reads : LocalReadEvents.ProgressFields beforeNodes beforeRows beforeNext beforeDirect afterNodes afterRows afterNext afterDirect
  events : beforeRows.map (fun requirement => requirement.id.index) = List.range beforeNext →
    beforeDirect ⊆ beforeRows.map Requirement.id →
    LocalReadEvents.OriginsFields beforeNodes beforeRows beforeNext beforeDirect →
    Origins beforeNodes → Origins afterNodes
  retained : BindersRetained beforeNodes afterNodes

abbrev Progress (before after : State) : Prop :=
  ProgressFields before.nodes before.requirements before.nextRequirement before.directCallRequirements
    after.nodes after.requirements after.nextRequirement after.directCallRequirements

theorem ProgressFields.trans
    {bn mn an : List Node} {br mr ar : List Requirement} {bi mi ai : Nat}
    {bd md ad : List RequirementId}
    (first : ProgressFields bn br bi bd mn mr mi md)
    (second : ProgressFields mn mr mi md an ar ai ad) :
    ProgressFields bn br bi bd an ar ai ad :=
  ⟨first.reads.trans second.reads, fun wf allocated reads events =>
    second.events (first.reads.ledger.wellFormed wf)
      (first.reads.ledger.allocated wf allocated) (first.reads.origins wf allocated reads)
      (first.events wf allocated reads events), first.retained.trans second.retained⟩

theorem ProgressFields.statement (nodes : List Node) (rows : List Requirement)
    (next : Nat) (direct : List RequirementId) (node : StatementNode) (event : Statement node) :
    ProgressFields nodes rows next direct (nodes ++ [.statement node]) rows next direct :=
  ⟨LocalReadEvents.ProgressFields.statement _ _ _ _ _, fun _ _ _ origins => origins.statement node event,
    BindersRetained.append _ _⟩

theorem ProgressFields.expression (nodes : List Node) (rows : List Requirement)
    (next : Nat) (direct : List RequirementId) (node : ExpressionNode)
    (nonlocal : LocalReadEvents.Nonlocal node.form) :
    ProgressFields nodes rows next direct (nodes ++ [.expression node]) rows next direct :=
  ⟨LocalReadEvents.ProgressFields.expression _ _ _ _ _ nonlocal, fun _ _ _ origins => origins.expression node,
    BindersRetained.append _ _⟩

namespace Progress
theorem refl (state : State) : Progress state state :=
  ⟨LocalReadEvents.Progress.refl _, fun _ _ _ origins => origins, .refl _⟩
theorem trans {before middle after : State} (first : Progress before middle) (second : Progress middle after) :
    Progress before after := ProgressFields.trans first second

theorem of_nodes_eq {before after : State} (same : after.nodes = before.nodes)
    (ledger : DirectRequirementsProgress before after) : Progress before after :=
  ⟨LocalReadEvents.Progress.of_nodes_eq same ledger, fun _ _ _ origins => same.symm ▸ origins,
    same.symm ▸ BindersRetained.refl _⟩

theorem recordStatement (state : State) (node : StatementNode) (event : Statement node) :
    Progress state (state.recordNode (.statement node)) :=
  ⟨LocalReadEvents.Progress.recordStatement _ _, fun _ _ _ origins => origins.statement node event,
    BindersRetained.append _ _⟩

theorem modifyStatementNode (state : State) (id : StatementId) (modify : StatementNode → StatementNode)
    (forms : ∀ node, (modify node).form = node.form) : Progress state (state.modifyStatementNode id modify) := by
  refine ⟨LocalReadEvents.Progress.modifyStatementNode _ _ _, ?_,
    BindersRetained.modifyStatementNode state id modify forms⟩
  intro _ _ _ origins statement present
  obtain ⟨node, member, same⟩ := List.mem_map.mp present
  cases node with
  | expression node => cases same
  | statement original =>
    simp only at same
    split at same <;> cases same
    · exact (origins original member).same_form (forms original)
    · exact origins _ member

theorem addRequirementWithId (state : State) (predicate : ProgramPredicate) :
    Progress state (state.addRequirementWithId predicate).2 :=
  of_nodes_eq rfl (.addRequirementWithId _ _)

theorem addRequirementsWithIds (state : State) (predicates : List ProgramPredicate) :
    Progress state (state.addRequirementsWithIds predicates).2 :=
  of_nodes_eq (State.addRequirementsWithIds_nodes _ _) (.addRequirementsWithIds _ _)

end Progress

theorem Origins.modifyExpressionNode {state : State} (origins : Origins state.nodes)
    (id : ExpressionId) (modify : ExpressionNode → ExpressionNode) :
    Origins (state.modifyExpressionNode id modify).nodes := by
  intro statement present
  obtain ⟨node, member, same⟩ := List.mem_map.mp present
  cases node with
  | expression node => simp only at same; split at same <;> cases same
  | statement original => cases same; exact origins _ member

theorem Origins.attachExpressionCoercions {state : State} (origins : Origins state.nodes)
    (entries : List Detail.ExpressionCoercions) : Origins (Detail.attachExpressionCoercions state entries).nodes := by
  unfold Detail.attachExpressionCoercions
  induction entries generalizing state with
  | nil => exact origins
  | cons entry rest ih => exact ih (origins.modifyExpressionNode _ _)

theorem Origins.recordExpression {state : State} (origins : Origins state.nodes)
    (source : Syntax.Expr) (expression : InferredExpression) (form : ExpressionForm)
    (requirements : List RequirementId) (coercions : List CoercionStep) (start : Option Nat := none) :
    Origins (Detail.recordExpression source expression form requirements coercions state start).2.nodes :=
  origins.expression _

theorem Origins.recordExpressionWithExpected {state : State} (origins : Origins state.nodes)
    {context : Context} {source : Syntax.Expr} {id : ExpressionId} {type : Ty}
    {form : ExpressionForm} {requirements : List RequirementId} {expected : Option Ty}
    {start : Option Nat} {result : InferredExpression × State}
    (accepted : Detail.recordExpressionWithExpected context source id type form requirements expected state start = .ok result) :
    Origins result.2.nodes := by
  obtain ⟨fitted, fit, _, recorded⟩ := Detail.recordExpressionWithExpected_success_record accepted
  rw [recorded]
  have same := (Detail.withExpected_occurrenceState_eq fit).1
  exact (show Origins fitted.state.nodes from same.symm ▸ origins).expression _

namespace Progress
theorem recordExpressionWithExpected
    {context : Context} {source : Syntax.Expr} {id : ExpressionId} {type : Ty}
    {form : ExpressionForm} {requirements : List RequirementId} {expected : Option Ty} {state : State}
    {start : Option Nat} {result : InferredExpression × State}
    (accepted : Detail.recordExpressionWithExpected context source id type form requirements expected state start = .ok result)
    (nonlocal : LocalReadEvents.Nonlocal form) : Progress state result.2 :=
  ⟨LocalReadEvents.Progress.recordExpressionWithExpected accepted nonlocal,
    fun _ _ _ origins => origins.recordExpressionWithExpected accepted,
    BindersRetained.recordExpressionWithExpected accepted⟩

theorem localIdentifier {fuel : Nat} {context : Context} {expression : Syntax.Expr}
    {expected : Option Ty} {initial allocated : State} {id : ExpressionId}
    {name : Syntax.Identifier} {binder : TypedBinder} {result : InferredExpression × State}
    (form : expression.value = .identifier name)
    (allocation : initial.allocateExpressionId = (id, allocated))
    (found : allocated.lookupBinder? name.value = some binder)
    (accepted : Detail.inferExprFuel (fuel + 1) context expression expected initial = .ok result) :
    Progress initial result.2 := by
  refine ⟨LocalReadEvents.Progress.localIdentifier form allocation found accepted, ?_, ?_⟩
  rotate_left
  · have kept := BindersRetained.recordExpressionWithExpected
      (Detail.inferExprFuel_success_localIdentifier_record form allocation found accepted)
    rw [State.addRequirementsWithIds_nodes] at kept
    have same : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
    simpa only [same, State.allocateExpressionId_nodes] using kept
  intro _ _ _ origins
  apply Origins.recordExpressionWithExpected (accepted := Detail.inferExprFuel_success_localIdentifier_record form allocation found accepted)
  rw [State.addRequirementsWithIds_nodes]
  have same : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
  simpa only [same, State.allocateExpressionId_nodes] using origins

theorem unify {state next : State} {left right : Ty}
    (accepted : unify state left right = .ok next) : Progress state next :=
  ⟨LocalReadEvents.Progress.unify accepted, fun _ _ _ origins =>
    (unify_occurrenceState_eq accepted).1.symm ▸ origins,
    (unify_occurrenceState_eq accepted).1.symm ▸ BindersRetained.refl _⟩

theorem withExpected
    {context : Context} {state : State} {actual : InferredExpression}
    {expected : Option Ty} {result : ExpectationResult}
    (accepted : withExpected context state actual expected = .ok result) :
    Progress state result.state :=
  ⟨LocalReadEvents.Progress.withExpected accepted, fun _ _ _ origins =>
    (withExpected_occurrenceState_eq accepted).1.symm ▸ origins,
    (withExpected_occurrenceState_eq accepted).1.symm ▸ BindersRetained.refl _⟩

theorem selectFunctionCandidateFrom
    {context : Context} {name : String} {candidates : List ProgramFunctionSignature}
    {arguments : List InferredExpression} {integerLiteralOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected : Option Ty} {state : State} {result : CandidateAttemptResult}
    (accepted : selectFunctionCandidateFrom context name candidates arguments
      integerLiteralOrigins call expected state = .ok result) :
    Progress state result.state :=
  ⟨LocalReadEvents.Progress.selectFunctionCandidateFrom accepted, fun _ _ _ origins =>
    (selectFunctionCandidateFrom_occurrenceState_eq accepted).1.symm ▸ origins,
    (selectFunctionCandidateFrom_occurrenceState_eq accepted).1.symm ▸ BindersRetained.refl _⟩

theorem inferUnaryOperator
    {context : Context} {operator : Syntax.UnaryOp} {operandType : Ty}
    {expected : Option Ty} {integerLiterals : List IntegerLiteralOrigin}
    {state : State} {result : OperatorInferenceResult}
    (success : inferUnaryOperator context operator operandType expected
      integerLiterals state = .ok result) :
    Progress state result.state :=
  ⟨LocalReadEvents.Progress.inferUnaryOperator success, fun _ _ _ origins =>
    (inferUnaryOperator_occurrenceState_eq success).1.symm ▸ origins,
    (inferUnaryOperator_occurrenceState_eq success).1.symm ▸ BindersRetained.refl _⟩

theorem inferBinaryOperator
    {context : Context} {operator : Syntax.BinaryOp} {left right : Ty}
    {expected : Option Ty} {integerLiterals : List IntegerLiteralOrigin}
    {state : State} {result : OperatorInferenceResult}
    (success : inferBinaryOperator context operator left right expected
      integerLiterals state = .ok result) :
    Progress state result.state :=
  ⟨LocalReadEvents.Progress.inferBinaryOperator success, fun _ _ _ origins =>
    (inferBinaryOperator_occurrenceState_eq success).1.symm ▸ origins,
    (inferBinaryOperator_occurrenceState_eq success).1.symm ▸ BindersRetained.refl _⟩

theorem applyFunctionType
    {context : Context} {call : ExpressionId} {calleeType : Ty}
    {arguments : List InferredExpression} {expected : Option Ty}
    {state : State} {result : IndirectApplicationResult}
    (success : applyFunctionType context call calleeType arguments expected
      state = .ok result) :
    Progress state result.state :=
  ⟨LocalReadEvents.Progress.applyFunctionType success, fun _ _ _ origins =>
    (applyFunctionType_occurrenceState_eq success).1.symm ▸ origins,
    (applyFunctionType_occurrenceState_eq success).1.symm ▸ BindersRetained.refl _⟩

theorem bindLambdaParameters
    {context : Context} {parameters : List Syntax.LambdaParameter}
    {index : Nat} {seen : List String} {state : State}
    {result : List TypedBinder × List Ty × State}
    (success : bindLambdaParameters context parameters index seen state =
      .ok result) :
    Progress state result.2.2 :=
  ⟨LocalReadEvents.Progress.bindLambdaParameters success, fun _ _ _ origins =>
    (bindLambdaParameters_occurrenceState_eq success).1.symm ▸ origins,
    (bindLambdaParameters_occurrenceState_eq success).1.symm ▸ BindersRetained.refl _⟩

theorem inferMatchPatternFuel
    {fuel : Nat} {context : Context} {pattern : Syntax.Pattern}
    {expected : Ty} {state : State} {result : TypedMatchPattern × State}
    (success : Detail.inferMatchPatternFuel fuel context pattern expected state = .ok result) :
    Progress state result.2 :=
  ⟨LocalReadEvents.Progress.inferMatchPatternFuel success, fun _ _ _ origins =>
    (inferMatchPatternFuel_occurrenceState_eq success).1.symm ▸ origins,
    (inferMatchPatternFuel_occurrenceState_eq success).1.symm ▸ BindersRetained.refl _⟩

theorem freshDataConstructorInstantiation (dataType : ProgramDataSignature)
    (constructor : ProgramDataConstructorSignature) (state : State) :
    Progress state (Detail.freshDataConstructorInstantiation dataType constructor state).2 :=
  of_nodes_eq (Detail.freshDataConstructorInstantiation_nodes _ _ _)
    (Detail.freshDataConstructorInstantiation_direct_progress _ _ _)

theorem freshTypes (count : Nat) (state : State) : Progress state (Detail.freshTypes count state).2 :=
  of_nodes_eq (Detail.freshTypes_nodes _ _) (Detail.freshTypes_direct_progress _ _)

theorem recordSelectedCallResult (source callee : Syntax.Expr) (name : String)
    (arguments : List InferredExpression) (attempt : Detail.CandidateAttemptResult)
    (result : InferredExpression) (trailing : List CoercionStep) (state : State) :
    Progress state (Detail.recordSelectedCallResult source callee name arguments attempt result trailing state).2 := by
  refine ⟨LocalReadEvents.Progress.recordSelectedCallResult _ _ _ _ _ _ _ _, ?_,
    BindersRetained.recordSelectedCallResult _ _ _ _ _ _ _ _⟩
  intro _ _ _ origins
  unfold Detail.recordSelectedCallResult
  exact (origins.attachExpressionCoercions _).recordExpression _ _ _ _ _ |>.recordExpression _ _ _ _ _

theorem recordSelectedCall (source callee : Syntax.Expr) (name : String)
    (arguments : List InferredExpression) (attempt : Detail.CandidateAttemptResult) :
    Progress attempt.state (Detail.recordSelectedCall source callee name arguments attempt).2 := recordSelectedCallResult _ _ _ _ _ _ _ _

theorem recordIndirectCall (source : Syntax.Expr) (callee : InferredExpression)
    (arguments : List InferredExpression) (result : Detail.IndirectApplicationResult) :
    Progress result.state (Detail.recordIndirectCall source callee arguments result).2 :=
  ⟨LocalReadEvents.Progress.recordIndirectCall _ _ _ _, fun _ _ _ origins => origins.recordExpression _ _ _ _ _,
    BindersRetained.recordExpression _ _ _ _ _ _ _⟩

theorem recordBuiltinFunctionCall
    {source callee : Syntax.Expr} {name : String} {function : BuiltinFunctionId}
    {arguments : List InferredExpression} {call : ExpressionId} {expected : Option Ty} {state : State}
    {result : InferredExpression × State}
    (accepted : Detail.recordBuiltinFunctionCall source callee name function arguments call expected state = .ok result) :
    Progress state result.2 := by
  refine ⟨LocalReadEvents.Progress.recordBuiltinFunctionCall accepted, ?_, ?_⟩
  rotate_left
  · obtain ⟨calleeId, nodes⟩ := Detail.recordBuiltinFunctionCall_success_nodes accepted
    rw [nodes]
    exact BindersRetained.append _ _
  intro _ _ _ origins
  obtain ⟨calleeId, nodes⟩ := Detail.recordBuiltinFunctionCall_success_nodes accepted
  rw [nodes]
  simpa only [List.append_assoc, List.cons_append, List.nil_append] using (origins.expression _).expression _


theorem initializedStatement {fuel : Nat} {context : Context} {statement : Syntax.Statement}
    {initial : State} {result : StatementResult} {expected : Ty}
    (receipt : LocalLetRequirementTiming.Receipt fuel context statement initial result)
    (accepted : inferStatementFuel (fuel + 1) context statement expected initial = .ok result)
    (child : Progress initial.allocateStatementId.2 receipt.ready) : Progress initial result.state := by
  refine ⟨LocalReadEvents.inferStatementFuel_origins_progress accepted, ?_, ?_⟩
  rotate_left
  · rw [receipt.completed]
    exact child.retained.trans (BindersRetained.append _ _)
  intro wf allocated reads events
  have childEvents := child.events wf allocated reads events
  rw [receipt.completed]
  exact childEvents.statement _ (Origin.statement receipt ⟨wf, allocated, reads⟩)

end Progress
end Solcore.Frontend.SourceInference.LocalGeneralizationEvents
end

section
-- leanmerge: from Solcore.Frontend.SourceInference.LocalGeneralizationHeaderEvents
/-! Header events are recovered from the actual returned item sequence,
including the real entry state of each later initializer. -/
set_option autoImplicit false
set_option Elab.async false
set_option linter.unusedSimpArgs false
namespace Solcore.Frontend.SourceInference.LocalGeneralizationEvents
open TypeSystem Detail

theorem inferForItemFuel_event {fuel : Nat} {context : Context} {item : Syntax.ForItem}
    {state : State} {result : ForItemForm × State}
    (accepted : inferForItemFuel fuel context item state = .ok result)
    (ready : Ready state) : Item result.1 := by
  cases fuel with
  | zero => simp [inferForItemFuel, throw] at accepted
  | succ fuel =>
    cases form : item.value with
    | letDecl name annotation initializer =>
      cases initializer with
      | some initializer =>
        obtain ⟨receipt⟩ := LocalHeaderRequirementTiming.of_initialized_accepted form accepted
        exact Item.of_header receipt ready
      | none =>
        unfold inferForItemFuel at accepted
        simp only [form, bind, Except.bind] at accepted
        repeat' first | split at accepted
        all_goals simp_all [Item, pure, Pure.pure, Except.pure, throw]
        all_goals subst_vars
        all_goals simp_all [Item]
    | expression expression | assignValue target operator value | assignBitNot target token =>
      unfold inferForItemFuel at accepted
      simp only [form, bind, Except.bind] at accepted
      repeat' first | split at accepted
      all_goals simp_all [Item, pure, Pure.pure, Except.pure, throw]
      all_goals subst_vars
      all_goals simp_all [Item]

theorem inferForItemsFuel_events {fuel : Nat} {context : Context} {items : List Syntax.ForItem}
    {state : State} {result : InferredForItems}
    (accepted : inferForItemsFuel fuel context items state = .ok result)
    (ready : Ready state) : Items result.items := by
  induction items generalizing state result with
  | nil =>
    simp only [inferForItemsFuel, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
    cases accepted
    intro item impossible
    cases impossible
  | cons item items ih =>
    unfold inferForItemsFuel at accepted
    cases first : inferForItemFuel fuel context item state with
    | error error => simp [first, bind, Except.bind] at accepted
    | ok pair =>
      rcases pair with ⟨head, next⟩
      cases tail : inferForItemsFuel fuel context items next with
      | error error => simp [first, tail, bind, Except.bind, Functor.map, Except.map] at accepted
      | ok rest =>
        simp only [first, tail, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
        cases accepted
        intro value member
        rcases List.mem_cons.mp member with same | remaining
        · cases same
          exact inferForItemFuel_event first ready
        · exact ih tail (ready.progress (LocalReadEvents.inferForItemFuel_origins_progress first)) value remaining

end Solcore.Frontend.SourceInference.LocalGeneralizationEvents
end

section
-- leanmerge: from Solcore.Frontend.SourceInference.LocalGeneralizationInference
/-! Every initialized declaration in successful source inference retains its
actual initializer, optional annotation, and generalization boundary. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace Solcore.Frontend.SourceInference.LocalGeneralizationEvents
open TypeSystem Detail
open State (DirectRequirementsProgress)

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

private def PreservesOrigins {alpha : Type} (stateOf : alpha → State)
    (initial : State) (computation : Except Error alpha) : Prop :=
  ∀ result, computation = .ok result → Progress initial (stateOf result)

private theorem pair_success_origins_progress {alpha : Type}
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


private theorem allocateExpressionId_success_origins_progress
    {state next : State} {id : ExpressionId}
    (success : state.allocateExpressionId = (id, next)) :
    Progress state next :=
  pair_success_origins_progress
    (Progress.of_nodes_eq rfl (DirectRequirementsProgress.refl state)) success

private theorem allocateStatementId_success_origins_progress
    {state next : State} {id : StatementId}
    (success : state.allocateStatementId = (id, next)) :
    Progress state next :=
  pair_success_origins_progress
    (Progress.of_nodes_eq rfl (DirectRequirementsProgress.refl state)) success

private theorem state_fresh_success_origins_progress
    {state next : State} {type : Ty}
    (success : state.fresh = (type, next)) :
    Progress state next :=
  pair_success_origins_progress (Progress.of_nodes_eq rfl (DirectRequirementsProgress.refl state))
    success

private theorem allocateHiddenLocal_success_origins_progress
    {state next : State} {id : Resolved.LocalId}
    (success : state.allocateHiddenLocal = (id, next)) :
    Progress state next :=
  pair_success_origins_progress
    (Progress.of_nodes_eq rfl (DirectRequirementsProgress.refl state)) success

private theorem addRequirementWithId_success_origins_progress
    {state next : State} {predicate : ProgramPredicate}
    {requirement : RequirementId}
    (success : state.addRequirementWithId predicate = (requirement, next)) :
    Progress state next :=
  pair_success_origins_progress
    (Progress.addRequirementWithId state predicate) success

private theorem addRequirementsWithIds_success_origins_progress
    {state next : State} {predicates : List ProgramPredicate}
    {requirements : List RequirementId}
    (success : state.addRequirementsWithIds predicates = (requirements, next)) :
    Progress state next :=
  pair_success_origins_progress
    (Progress.addRequirementsWithIds state predicates) success

private theorem allocateBinder_success_origins_progress
    {state next : State} {name : String} {scheme : Scheme}
    {span : Option Syntax.SourceSpan} {comptime : Bool}
    {schemeRequirements : List LocalSchemeRequirement} {binder : TypedBinder}
    (success : state.allocateBinder name scheme span comptime
      schemeRequirements = (binder, next)) :
    Progress state next :=
  pair_success_origins_progress
    (Progress.of_nodes_eq rfl (DirectRequirementsProgress.refl state)) success

private theorem freshDataConstructorInstantiation_success_origins_progress
    {dataType : ProgramDataSignature}
    {constructor : ProgramDataConstructorSignature}
    {state next : State} {instantiation : DataConstructorInstantiation}
    (success : freshDataConstructorInstantiation dataType constructor state =
      (instantiation, next)) :
    Progress state next :=
  pair_success_origins_progress
    (Progress.freshDataConstructorInstantiation dataType constructor
      state) success

private theorem freshTypes_success_origins_progress
    {count : Nat} {state next : State} {types : List Ty}
    (success : freshTypes count state = (types, next)) :
    Progress state next :=
  pair_success_origins_progress
    (Progress.freshTypes count state) success

private theorem syntheticTuple_result_origins_progress
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
  exact ProgressFields.expression _ _ _ _ _ (by intro _ _ impossible; cases impossible)

private theorem syntheticTuple_pair_origins_progress
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
  exact ProgressFields.expression _ _ _ _ _ (by intro _ _ impossible; cases impossible)

private theorem pure_pair_result_origins_progress {epsilon alpha : Type}
    {value : alpha} {next initial : State} {result : alpha × State}
    (nextSubset : Progress initial next)
    (success : (pure (value, next) : Except epsilon (alpha × State)) =
      .ok result) :
    Progress initial result.snd := by
  have resultEq : (value, next) = result := by
    simpa only [exceptPure_eq_ok] using success
  rw [← resultEq]
  exact nextSubset

private theorem restored_pair_result_origins_progress {alpha : Type}
    {value : alpha} {state initial : State} {scope : LexicalScope}
    {result : alpha × State}
    (subset : Progress initial state)
    (success : (value, state.restoreLexicalScope scope) = result) :
    Progress initial result.snd := by
  rw [← success]
  exact Progress.trans subset
    (Progress.of_nodes_eq rfl (DirectRequirementsProgress.refl state))


set_option maxHeartbeats 2000000 in
private theorem inferFuel_origins_progress_internal :
    (∀ fuel context expression expected state,
      PreservesOrigins Prod.snd state
        (inferExprFuel fuel context expression expected state)) ∧
    (∀ fuel context source id instantiation arguments expected state,
      PreservesOrigins Prod.snd state
        (inferConstructorApplicationFuel fuel context source id instantiation
          arguments expected state)) ∧
    (∀ fuel context sources expected state,
      PreservesOrigins Prod.snd state
        (inferConstructorArgumentsFuel fuel context sources expected state)) ∧
    (∀ fuel context statements expectedReturn state,
      PreservesOrigins BlockResult.state state
        (inferStatementsFuel fuel context statements expectedReturn state)) ∧
    (∀ fuel context statement expectedReturn state,
      PreservesOrigins StatementResult.state state
        (inferStatementFuel fuel context statement expectedReturn state)) ∧
    (∀ fuel context items state,
      PreservesOrigins InferredForItems.state state
        (inferForItemsFuel fuel context items state)) ∧
    (∀ fuel context item state,
      PreservesOrigins Prod.snd state
        (inferForItemFuel fuel context item state)) ∧
    (∀ fuel context target state,
      PreservesOrigins Prod.snd state
        (inferPlaceFuel fuel context target state)) ∧
    (∀ fuel context target operator value state,
      PreservesOrigins (fun result => result.2.2) state
        (inferAssignedValueFuel fuel context target operator value state)) ∧
    (∀ fuel context expressions state,
      PreservesOrigins Prod.snd state
        (inferExprsFuel fuel context expressions state)) ∧
    (∀ fuel context scrutineeType expectedReturn outerScope cases state,
      PreservesOrigins MatchCasesResult.state state
        (inferMatchCasesFuel fuel context scrutineeType expectedReturn outerScope
          cases state)) := by
  apply inferExprFuel.mutual_induct
    (motive1 := fun fuel context expression expected state =>
      PreservesOrigins Prod.snd state
        (inferExprFuel fuel context expression expected state))
    (motive2 := fun fuel context source id instantiation arguments expected
        state =>
      PreservesOrigins Prod.snd state
        (inferConstructorApplicationFuel fuel context source id instantiation
          arguments expected state))
    (motive3 := fun fuel context sources expected state =>
      PreservesOrigins Prod.snd state
        (inferConstructorArgumentsFuel fuel context sources expected state))
    (motive4 := fun fuel context statements expectedReturn state =>
      PreservesOrigins BlockResult.state state
        (inferStatementsFuel fuel context statements expectedReturn state))
    (motive5 := fun fuel context statement expectedReturn state =>
      PreservesOrigins StatementResult.state state
        (inferStatementFuel fuel context statement expectedReturn state))
    (motive6 := fun fuel context items state =>
      PreservesOrigins InferredForItems.state state
        (inferForItemsFuel fuel context items state))
    (motive7 := fun fuel context item state =>
      PreservesOrigins Prod.snd state
        (inferForItemFuel fuel context item state))
    (motive8 := fun fuel context target state =>
      PreservesOrigins Prod.snd state
        (inferPlaceFuel fuel context target state))
    (motive9 := fun fuel context target operator value state =>
      PreservesOrigins (fun result => result.2.2) state
        (inferAssignedValueFuel fuel context target operator value state))
    (motive10 := fun fuel context expressions state =>
      PreservesOrigins Prod.snd state
        (inferExprsFuel fuel context expressions state))
    (motive11 := fun fuel context scrutineeType expectedReturn outerScope
        cases state =>
      PreservesOrigins MatchCasesResult.state state
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
            have allocP := allocateStatementId_success_origins_progress allocation
            have initP := initIH _ initRun
            have condP := condIH initResult _ condRun
            have bodyP := bodyIH testState _ bodyRun
            have postP := postIH initResult bodyResult _ postRun
            have history := allocP.trans (initP.trans (condP.trans (bodyP.trans postP)))
            refine ⟨LocalReadEvents.inferStatementFuel_origins_progress original, ?_,
              history.retained.trans (BindersRetained.append _ _)⟩
            intro wf direct reads events
            have ready : Ready initial := ⟨wf, direct, reads⟩
            have readyAlloc : Ready allocated := ready.progress allocP.reads
            have readyInit : Ready initResult.state := readyAlloc.progress initP.reads
            have readyTest : Ready testState := readyInit.progress condP.reads
            have readyBody : Ready afterBody := readyTest.progress bodyP.reads
            apply (history.events wf direct reads events).statement
            exact ⟨inferForItemsFuel_events initRun readyAlloc,
              inferForItemsFuel_events postRun readyBody⟩
  case case44 =>
    intros context statement expectedReturn state fuel id stateAfterId
      statementIdEq scrutinees arms statementEq sources notSingleton
      casesInduction bodyInduction expressionsInduction
    unfold PreservesOrigins at *
    intro result success
    have statementIdSubset :=
      allocateStatementId_success_origins_progress statementIdEq
    unfold inferStatementFuel at success
    simp only [statementIdEq, statementEq, bind, Except.bind] at success
    repeat' first | split at success
    all_goals try cases success
    all_goals try exact (notSingleton _ (by assumption)).elim
    all_goals try have expressionsSubset :=
      expressionsInduction _ (by assumption)
    all_goals try have casesSubset :=
      casesInduction _ _ _ (by assumption)
    all_goals try have bodySubset :=
      bodyInduction _ _ _ (by assumption)
    all_goals try have tupleSubset :=
      syntheticTuple_result_origins_progress (by assumption)
    all_goals try have tupleSubset :=
      syntheticTuple_pair_origins_progress (by assumption)
    all_goals try have defaultSubset :=
      pure_pair_result_origins_progress casesSubset (by assumption)
    all_goals simp_all only [exceptPure_eq_ok]
    all_goals try have restoredSubset :=
      restored_pair_result_origins_progress bodySubset (by assumption)
    all_goals try simp_all
    all_goals try exact Progress.refl _
    all_goals try exact Progress.of_nodes_eq rfl (DirectRequirementsProgress.refl _)
    all_goals try exact Progress.recordStatement _ _ (by trivial)
    all_goals dsimp only [Progress,
      State.recordNode, State.allocateExpressionId, State.allocateStatementId,
      State.allocateHiddenLocal, State.allocateBinder, State.restoreLexicalScope,
      State.withLocals, State.fresh, recordExpression, recordIndirectCall]
    all_goals dsimp only [Progress, State.recordNode, State.allocateExpressionId,
      State.allocateStatementId, State.allocateHiddenLocal, State.allocateBinder,
      State.restoreLexicalScope, State.withLocals, State.fresh,
      Detail.recordExpression, Detail.recordIndirectCall] at *
    all_goals first
      | apply ProgressFields.trans (second := ProgressFields.statement _ _ _ _ _ (by trivial))
      | apply ProgressFields.trans (second := ProgressFields.expression _ _ _ _ _
          (by change LocalReadEvents.Nonlocal (.call _ _ (.indirect _)); intro _ _ impossible; cases impossible))
      | apply ProgressFields.trans (second := ProgressFields.expression _ _ _ _ _
          (by change LocalReadEvents.Nonlocal (.constructor _ _); intro _ _ impossible; cases impossible))
      | skip
    all_goals grind [ProgressFields.trans]
  case case70 =>
    intros fuel context target operator value state placeInduction valueInduction
    unfold PreservesOrigins at *
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
    all_goals try exact Progress.of_nodes_eq rfl (DirectRequirementsProgress.refl _)
    all_goals try exact Progress.recordStatement _ _ (by trivial)
    all_goals dsimp only [Progress,
      State.recordNode, State.allocateExpressionId, State.allocateStatementId,
      State.allocateHiddenLocal, State.allocateBinder, State.restoreLexicalScope,
      State.withLocals, State.fresh, recordExpression, recordIndirectCall]
    all_goals dsimp only [Progress, State.recordNode, State.allocateExpressionId,
      State.allocateStatementId, State.allocateHiddenLocal, State.allocateBinder,
      State.restoreLexicalScope, State.withLocals, State.fresh,
      Detail.recordExpression, Detail.recordIndirectCall] at *
    all_goals first
      | apply ProgressFields.trans (second := ProgressFields.statement _ _ _ _ _ (by trivial))
      | apply ProgressFields.trans (second := ProgressFields.expression _ _ _ _ _
          (by change LocalReadEvents.Nonlocal (.call _ _ (.indirect _)); intro _ _ impossible; cases impossible))
      | apply ProgressFields.trans (second := ProgressFields.expression _ _ _ _ _
          (by change LocalReadEvents.Nonlocal (.constructor _ _); intro _ _ impossible; cases impossible))
      | skip
    all_goals grind [ProgressFields.trans]
  case case67 =>
    unfold PreservesOrigins at *
    intros
    simp_all only [inferPlaceFuel]
  all_goals
    intros
    unfold PreservesOrigins at *
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
      | specialize ih1 _ _ (by assumption)
      | specialize ih1 _ _ _ (by assumption)
      | specialize ih1 _ _ _ _ (by assumption)
      | skip
    all_goals first
      | specialize ih2 _ _ (by assumption)
      | specialize ih2 _ _ _ (by assumption)
      | specialize ih2 _ _ _ _ (by assumption)
      | skip
    all_goals first
      | specialize ih3 _ _ (by assumption)
      | specialize ih3 _ _ _ (by assumption)
      | specialize ih3 _ _ _ _ (by assumption)
      | skip
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
      allocateExpressionId_success_origins_progress (by assumption)
    all_goals try have statementIdSubset :=
      allocateStatementId_success_origins_progress (by assumption)
    all_goals try have freshSubset :=
      state_fresh_success_origins_progress (by assumption)
    all_goals try have hiddenLocalSubset :=
      allocateHiddenLocal_success_origins_progress (by assumption)
    all_goals try have requirementSubset :=
      addRequirementWithId_success_origins_progress (by assumption)
    all_goals try have requirementsSubset :=
      addRequirementsWithIds_success_origins_progress (by assumption)
    all_goals try have binderSubset :=
      allocateBinder_success_origins_progress (by assumption)
    all_goals try have constructorSubset :=
      freshDataConstructorInstantiation_success_origins_progress (by
        assumption)
    all_goals try have typesSubset :=
      freshTypes_success_origins_progress (by assumption)
    all_goals try have recordSubset :=
      Progress.recordExpressionWithExpected (by assumption) (by intro _ _ impossible; cases impossible)
    all_goals try have issuedRecord :=
      (Progress.addRequirementWithId _ _).trans recordSubset
    all_goals try have batchRecord :=
      (Progress.addRequirementsWithIds _ _).trans recordSubset
    all_goals try exact ProgressFields.trans expressionIdSubset (ProgressFields.trans (Progress.addRequirementWithId _ _) recordSubset)
    all_goals try exact ProgressFields.trans expressionIdSubset (ProgressFields.trans (Progress.addRequirementsWithIds _ _) recordSubset)
    all_goals try have lambdaSubset :=
      Progress.bindLambdaParameters (by assumption)
    all_goals try
      have afterLambdaSubset := Progress.trans lambdaSubset
        (Progress.unify (by assumption))
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
    all_goals try exact Progress.of_nodes_eq rfl (DirectRequirementsProgress.refl _)
    all_goals try exact Progress.recordStatement _ _ (by trivial)
    all_goals dsimp only [Progress,
      State.recordNode, State.allocateExpressionId, State.allocateStatementId,
      State.allocateHiddenLocal, State.allocateBinder, State.restoreLexicalScope,
      State.withLocals, State.fresh, recordExpression, recordIndirectCall]
    all_goals dsimp only [Progress, State.recordNode, State.allocateExpressionId,
      State.allocateStatementId, State.allocateHiddenLocal, State.allocateBinder,
      State.restoreLexicalScope, State.withLocals, State.fresh,
      Detail.recordExpression, Detail.recordIndirectCall] at *
    all_goals first
      | apply ProgressFields.trans (second := ProgressFields.statement _ _ _ _ _ (by trivial))
      | apply ProgressFields.trans (second := ProgressFields.expression _ _ _ _ _
          (by change LocalReadEvents.Nonlocal (.call _ _ (.indirect _)); intro _ _ impossible; cases impossible))
      | apply ProgressFields.trans (second := ProgressFields.expression _ _ _ _ _
          (by change LocalReadEvents.Nonlocal (.constructor _ _); intro _ _ impossible; cases impossible))
      | skip
    all_goals grind
      [ProgressFields.trans,
        Progress.addRequirementWithId,
        Progress.addRequirementsWithIds,
        Progress.freshDataConstructorInstantiation,
        Progress.freshTypes,

        Progress.recordSelectedCallResult,
        Progress.recordSelectedCall,
        Progress.recordIndirectCall, Progress.recordStatement, Progress.modifyStatementNode]


theorem inferExprFuel_origins_progress
    {fuel : Nat} {context : Context} {expression : Syntax.Expr}
    {expected : Option Ty} {state : State}
    {result : InferredExpression × State}
    (success : inferExprFuel fuel context expression expected state =
      .ok result) :
    Progress state result.2 := by
  exact inferFuel_origins_progress_internal.1 fuel context expression
    expected state result success

theorem inferConstructorApplicationFuel_origins_progress
    {fuel : Nat} {context : Context} {source : Syntax.Expr}
    {id : ExpressionId} {instantiation : DataConstructorInstantiation}
    {arguments : List Syntax.Expr} {expected : Option Ty} {state : State}
    {result : InferredExpression × State}
    (success : inferConstructorApplicationFuel fuel context source id
      instantiation arguments expected state = .ok result) :
    Progress state result.2 := by
  exact inferFuel_origins_progress_internal.2.1 fuel context source id
    instantiation arguments expected state result success

theorem inferConstructorArgumentsFuel_origins_progress
    {fuel : Nat} {context : Context} {sources : List Syntax.Expr}
    {expected : List Ty} {state : State}
    {result : List InferredExpression × State}
    (success : inferConstructorArgumentsFuel fuel context sources expected
      state = .ok result) :
    Progress state result.2 := by
  exact inferFuel_origins_progress_internal.2.2.1 fuel context sources
    expected state result success

theorem inferStatementsFuel_origins_progress
    {fuel : Nat} {context : Context} {statements : List Syntax.Statement}
    {expectedReturn : Ty} {state : State} {result : BlockResult}
    (success : inferStatementsFuel fuel context statements expectedReturn state =
      .ok result) :
    Progress state result.state := by
  exact inferFuel_origins_progress_internal.2.2.2.1 fuel context
    statements expectedReturn state result success

theorem inferStatementFuel_origins_progress
    {fuel : Nat} {context : Context} {statement : Syntax.Statement}
    {expectedReturn : Ty} {state : State} {result : StatementResult}
    (success : inferStatementFuel fuel context statement expectedReturn state =
      .ok result) :
    Progress state result.state := by
  exact inferFuel_origins_progress_internal.2.2.2.2.1 fuel context
    statement expectedReturn state result success

theorem inferForItemsFuel_origins_progress
    {fuel : Nat} {context : Context} {items : List Syntax.ForItem}
    {state : State} {result : InferredForItems}
    (success : inferForItemsFuel fuel context items state = .ok result) :
    Progress state result.state := by
  exact inferFuel_origins_progress_internal.2.2.2.2.2.1 fuel context
    items state result success

theorem inferForItemFuel_origins_progress
    {fuel : Nat} {context : Context} {item : Syntax.ForItem}
    {state : State} {result : ForItemForm × State}
    (success : inferForItemFuel fuel context item state = .ok result) :
    Progress state result.2 := by
  exact inferFuel_origins_progress_internal.2.2.2.2.2.2.1 fuel context
    item state result success

theorem inferPlaceFuel_origins_progress
    {fuel : Nat} {context : Context} {target : Syntax.Expr}
    {state : State} {result : PlaceResolution × State}
    (success : inferPlaceFuel fuel context target state = .ok result) :
    Progress state result.2 := by
  exact inferFuel_origins_progress_internal.2.2.2.2.2.2.2.1 fuel
    context target state result success

theorem inferAssignedValueFuel_origins_progress
    {fuel : Nat} {context : Context} {target : Syntax.Expr}
    {operator : Syntax.ValueAssignOp} {value : Syntax.Expr} {state : State}
    {result : AssignmentResolution × InferredExpression × State}
    (success : inferAssignedValueFuel fuel context target operator value state =
      .ok result) :
    Progress state result.2.2 := by
  exact inferFuel_origins_progress_internal.2.2.2.2.2.2.2.2.1 fuel
    context target operator value state result success

theorem inferExprsFuel_origins_progress
    {fuel : Nat} {context : Context} {expressions : List Syntax.Expr}
    {state : State} {result : List InferredExpression × State}
    (success : inferExprsFuel fuel context expressions state = .ok result) :
    Progress state result.2 := by
  exact inferFuel_origins_progress_internal.2.2.2.2.2.2.2.2.2.1 fuel
    context expressions state result success

theorem inferMatchCasesFuel_origins_progress
    {fuel : Nat} {context : Context} {scrutineeType expectedReturn : Ty}
    {outerScope : LexicalScope} {cases : List Syntax.MatchCase}
    {state : State} {result : MatchCasesResult}
    (success : inferMatchCasesFuel fuel context scrutineeType expectedReturn
      outerScope cases state = .ok result) :
    Progress state result.state := by
  exact inferFuel_origins_progress_internal.2.2.2.2.2.2.2.2.2.2 fuel
    context scrutineeType expectedReturn outerScope cases state result success

/-- Successful statement inference retains each initialized declaration's
actual generalization event, including declarations inside for headers. -/
theorem inferStatementsFuel_origins
    {fuel : Nat} {context : Context} {statements : List Syntax.Statement}
    {expectedReturn : Ty} {state : State} {result : Detail.BlockResult}
    (accepted : Detail.inferStatementsFuel fuel context statements expectedReturn state = .ok result)
    (ready : Ready state) (origins : Origins state.nodes) : Origins result.state.nodes :=
  (inferStatementsFuel_origins_progress accepted).events ready.wellFormed ready.allocated ready.origins origins

/-- The initialized binder and expression come from their actual source
inference event; neither annotation nor cutoff is reconstructed from the scheme. -/
theorem inferStatementsFuel_initialized_origin
    {fuel : Nat} {context : Context} {statements : List Syntax.Statement}
    {expectedReturn : Ty} {state : State} {result : Detail.BlockResult}
    (accepted : Detail.inferStatementsFuel fuel context statements expectedReturn state = .ok result)
    (ready : Ready state) (origins : Origins state.nodes) {node : StatementNode}
    (member : Node.statement node ∈ result.state.nodes) {binder : TypedBinder}
    {initializer : ExpressionId} (form : node.form = .letDecl binder (some initializer)) :
    Origin binder initializer := by
  have event := inferStatementsFuel_origins accepted ready origins node member
  simpa only [Statement, form] using event

end Solcore.Frontend.SourceInference.LocalGeneralizationEvents
end

section
-- leanmerge: from Solcore.Frontend.SourceInference.LocalGeneralizationInferenceReceipts
/-! Inference readiness at an initialized declaration comes from the actual
initializer computation. The allocation following it preserves the exact
inference state, so its continuation starts at that computation's return. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.Frontend.SourceInference
open TypeSystem Detail

namespace LocalLetRequirementTiming

theorem Annotation.variablesBelow {context : Context} {source : Option Syntax.TypeExpr}
    {expected : Option Ty} (annotation : Annotation context source expected) (next : Nat) :
    ∀ type ∈ expected, type.VariablesBelow next := by
  cases annotation with
  | none => simp
  | some accepted =>
      intro type member
      cases Option.some.inj member
      exact resolveSourceType_success_variablesBelow accepted next

namespace Receipt
variable {fuel : Nat} {context : Context} {source : Syntax.Statement}
    {initial : State} {result : StatementResult}

theorem inference_eq (receipt : Receipt fuel context source initial result) :
    result.state.inference = receipt.ready.inference :=
  congrArg (fun value : StatementResult => value.state.inference) receipt.completed

theorem initializer_inference (receipt : Receipt fuel context source initial result)
    (ready : initial.InferenceReady)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes)) :
    initial.InferenceProgress receipt.ready ∧ receipt.ready.InferenceReady ∧
      receipt.value.type.VariablesBelow receipt.ready.inference.next := by
  have child := inferExprFuel_inferenceProperties ready.allocateStatementId formation canonical
    (receipt.annotationAccepted.variablesBelow _) receipt.child
  exact ⟨(State.InferenceProgress.allocateStatementId initial ready.solved).trans child.1,
    child.2⟩

theorem continuation (receipt : Receipt fuel context source initial result)
    (solved : receipt.ready.inference.Solved) : receipt.ready.InferenceProgress result.state :=
  State.InferenceProgress.of_inference_eq solved receipt.inference_eq

end Receipt
end LocalLetRequirementTiming

namespace LocalHeaderRequirementTiming.Receipt
variable {fuel : Nat} {context : Context} {source : Syntax.ForItem}
    {initial : State} {result : ForItemForm × State}

theorem inference_eq (receipt : Receipt fuel context source initial result) :
    result.2.inference = receipt.ready.inference :=
  congrArg (fun value : ForItemForm × State => value.2.inference) receipt.completed

theorem initializer_inference (receipt : Receipt fuel context source initial result)
    (ready : initial.InferenceReady)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes)) :
    initial.InferenceProgress receipt.ready ∧ receipt.ready.InferenceReady ∧
      receipt.value.type.VariablesBelow receipt.ready.inference.next :=
  inferExprFuel_inferenceProperties ready formation canonical
    (receipt.annotationAccepted.variablesBelow _) receipt.child

theorem continuation (receipt : Receipt fuel context source initial result)
    (solved : receipt.ready.inference.Solved) : receipt.ready.InferenceProgress result.2 :=
  State.InferenceProgress.of_inference_eq solved receipt.inference_eq

end LocalHeaderRequirementTiming.Receipt
end Solcore.Frontend.SourceInference
end

section
-- leanmerge: from Solcore.Frontend.SourceInference.LocalLetReferenceContainment
/-! References to locals created and retired by an initializer already occur
before its enclosing let generalizes. The continuation is the actual successful
statement inference, not an assumed semantic body law. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.Frontend.SourceInference.LocalLetRequirementTiming.Receipt
open TypeSystem Detail LocalReadScopeProgress

variable {fuel : Nat} {context : Context} {statement : Syntax.Statement}
    {initial : State} {result : StatementResult}

theorem retired_absent (receipt : Receipt fuel context statement initial result)
    (below : initial.LocalBindersBelowNextLocal) {retired : Resolved.LocalId}
    (created : initial.nextLocal ≤ retired.binderIndex)
    (retiredBeforeReturn : retired.binderIndex < receipt.ready.nextLocal) :
    Absent retired result.state.localBinders :=
  (receipt.retired_interval below).absent retired created retiredBeforeReturn

theorem retired_read_at_ready (receipt : Receipt fuel context statement initial result)
    (below : initial.LocalBindersBelowNextLocal) {retired : Resolved.LocalId}
    (created : initial.nextLocal ≤ retired.binderIndex)
    (retiredBeforeReturn : retired.binderIndex < receipt.ready.nextLocal)
    {after : State} (continuation : Progress result.state after)
    {node : ExpressionNode} (member : .expression node ∈ after.nodes)
    {name : String} (form : node.form = .reference name (.local retired)) :
    ReadAt receipt.ready.nodes node.id retired :=
  ((receipt.retired_interval below).progress continuation).read created retiredBeforeReturn member form

/-- A real successful suffix cannot first introduce a reference to one of the
initializer's retired locals. Its original occurrence is already in Ready. -/
theorem statements_retired_read_at_ready (receipt : Receipt fuel context statement initial result)
    (below : initial.LocalBindersBelowNextLocal) {retired : Resolved.LocalId}
    (created : initial.nextLocal ≤ retired.binderIndex)
    (retiredBeforeReturn : retired.binderIndex < receipt.ready.nextLocal)
    {suffixFuel : Nat} {suffixContext : Context} {sourceStatements : List Syntax.Statement}
    {expected : Ty} {after : BlockResult}
    (accepted : inferStatementsFuel suffixFuel suffixContext sourceStatements expected result.state = .ok after)
    {node : ExpressionNode} (member : .expression node ∈ after.state.nodes)
    {name : String} (form : node.form = .reference name (.local retired)) :
    ReadAt receipt.ready.nodes node.id retired :=
  receipt.retired_read_at_ready below created retiredBeforeReturn
    (inferStatementsFuel_scope_progress accepted) member form

end Solcore.Frontend.SourceInference.LocalLetRequirementTiming.Receipt
end
