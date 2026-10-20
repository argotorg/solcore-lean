import Solcore.Frontend.SourceInference.LocalBinderScopeProgress

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
