import Solcore.SourceSemantics.SourceInferenceActualReadCalls

/-! A retained local reference either continues an input occurrence or keeps
its exact issuing lookup from this inference run. Coercion updates preserve
the occurrence and local target in both cases. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution.RelativeLocalRead
open Frontend SourceInference TypeSystem Detail

open ActualLocalRead (lookupCall)

/-- A read either continues an input record or was issued during this run. -/
def Origin (root : CallIndex) (base : List Node) (node : ExpressionNode) : Prop :=
  (∃ previous : ExpressionNode, .expression previous ∈ base ∧
    node.id = previous.id ∧ node.form = previous.form) ∨ ActualLocalRead.Origin root node

def Origins (root : CallIndex) (base nodes : List Node) : Prop :=
  ∀ node, .expression node ∈ nodes → ∀ name binder,
    node.form = .reference name (.local binder) → Origin root base node

variable {root : CallIndex} {base : List Node}

theorem Origins.empty : Origins root base [] := by intro _ impossible; cases impossible

theorem Origin.same_occurrence {before after : ExpressionNode}
    (origin : Origin root base before) (id : after.id = before.id) (form : after.form = before.form) :
    Origin root base after := by
  rcases origin with ⟨previous, member, sameId, sameForm⟩ | current
  · exact .inl ⟨previous, member, id.trans sameId, form.trans sameForm⟩
  · exact .inr (current.same_occurrence id form)

theorem Origins.statement {nodes : List Node} (origins : Origins root base nodes) (node : StatementNode) :
    Origins root base (nodes ++ [.statement node]) := by
  intro expression member name binder form
  rcases List.mem_append.mp member with old | fresh
  · exact origins expression old name binder form
  · cases List.mem_singleton.mp fresh

theorem Origins.expression {nodes : List Node} (origins : Origins root base nodes) (node : ExpressionNode)
    (origin : ∀ name binder, node.form = .reference name (.local binder) → Origin root base node) :
    Origins root base (nodes ++ [.expression node]) := by
  intro expression member name binder form
  rcases List.mem_append.mp member with old | fresh
  · exact origins expression old name binder form
  · cases List.mem_singleton.mp fresh
    exact origin name binder form

theorem Origins.nonlocalExpression {nodes : List Node} (origins : Origins root base nodes) (node : ExpressionNode)
    (nonlocal : LocalReadEvents.Nonlocal node.form) : Origins root base (nodes ++ [.expression node]) :=
  origins.expression node (fun name binder form => (nonlocal name binder form).elim)

theorem Origins.modifyStatementNode {state : State} (origins : Origins root base state.nodes)
    (id : StatementId) (modify : StatementNode → StatementNode) :
    Origins root base (state.modifyStatementNode id modify).nodes := by
  intro expression present name binder form
  obtain ⟨node, member, same⟩ := List.mem_map.mp present
  cases node with
  | expression original => cases same; exact origins _ member name binder form
  | statement original => simp only at same; split at same <;> cases same

theorem Origins.modifyExpressionNode {state : State} (origins : Origins root base state.nodes)
    (id : ExpressionId) (modify : ExpressionNode → ExpressionNode)
    (forms : ∀ node, (modify node).form = node.form) :
    Origins root base (state.modifyExpressionNode id modify).nodes := by
  intro expression present name binder form
  obtain ⟨node, member, same⟩ := List.mem_map.mp present
  cases node with
  | statement original => cases same
  | expression original =>
    simp only at same
    split at same <;> cases same
    · rename_i sameId
      exact (origins _ member name binder ((forms _).symm.trans form)).same_occurrence sameId.symm (forms _)
    · exact origins _ member name binder form

theorem Origins.attachExpressionCoercions {state : State} (origins : Origins root base state.nodes)
    (entries : List Detail.ExpressionCoercions) :
    Origins root base (Detail.attachExpressionCoercions state entries).nodes := by
  unfold Detail.attachExpressionCoercions
  induction entries generalizing state with
  | nil => exact origins
  | cons entry rest ih => exact ih (origins.modifyExpressionNode _ _ (fun _ => rfl))

theorem Origins.recordExpression {state : State} (origins : Origins root base state.nodes)
    (source : Syntax.Expr) (expression : InferredExpression) (form : ExpressionForm)
    (requirements : List RequirementId) (coercions : List CoercionStep) (start : Option Nat := none)
    (nonlocal : LocalReadEvents.Nonlocal form) :
    Origins root base (Detail.recordExpression source expression form requirements coercions state start).2.nodes :=
  origins.nonlocalExpression _ nonlocal

theorem Origins.recordExpressionWithExpected {state : State} (origins : Origins root base state.nodes)
    {context : Context} {source : Syntax.Expr} {id : ExpressionId} {type : Ty}
    {form : ExpressionForm} {requirements : List RequirementId} {expected : Option Ty}
    {start : Option Nat} {result : InferredExpression × State}
    (accepted : Detail.recordExpressionWithExpected context source id type form requirements expected state start = .ok result)
    (nonlocal : LocalReadEvents.Nonlocal form) : Origins root base result.2.nodes := by
  obtain ⟨fitted, fit, _, recorded⟩ := Detail.recordExpressionWithExpected_success_record accepted
  rw [recorded]
  have same := (Detail.withExpected_occurrenceState_eq fit).1
  exact (show Origins root base fitted.state.nodes from same.symm ▸ origins).nonlocalExpression _ nonlocal

/-- Recording the successful local branch preserves the issuing call itself,
rather than replacing it by an arbitrary accepted lookup with the same ID. -/
theorem Lookup.record_origins (lookup : LocalReadEvents.Lookup)
    (here : CallOccurrence root (lookupCall lookup))
    (origins : Origins root base lookup.initial.nodes) : Origins root base lookup.result.2.nodes := by
  have allocated : lookup.allocated = lookup.initial.allocateExpressionId.2 :=
    (congrArg Prod.snd lookup.allocation).symm
  have batchNodes : lookup.batch.2.nodes = lookup.initial.nodes := by
    simp only [LocalReadEvents.Lookup.batch, State.addRequirementsWithIds_nodes,
      LocalReadEvents.Lookup.advanced, allocated, State.allocateExpressionId_nodes]
  obtain ⟨fitted, fit, _, recorded⟩ := Detail.recordExpressionWithExpected_success_record lookup.recorded
  rw [recorded]
  have same : fitted.state.nodes = lookup.initial.nodes :=
    (Detail.withExpected_occurrenceState_eq fit).1.trans batchNodes
  apply (show Origins root base fitted.state.nodes from same.symm ▸ origins).expression
  intro _ _ _
  exact .inr ⟨lookup, Detail.withExpected_success_expression_id fit, rfl, here⟩

/-- Input reads satisfy the relative invariant without any operational origin. -/
theorem Origins.initial (base : List Node) : Origins root base base := by
  intro node member _ _ _
  exact .inl ⟨node, member, rfl, rfl⟩

/-- The earlier absolute API is recovered by resolving the input alternative. -/
theorem Origins.toActual {nodes : List Node} (relative : Origins root base nodes)
    (previous : ActualLocalRead.Origins root base) : ActualLocalRead.Origins root nodes := by
  intro node member name binder form
  rcases relative node member name binder form with old | current
  · obtain ⟨original, present, sameId, sameForm⟩ := old
    exact (previous original present name binder (sameForm.symm.trans form)).same_occurrence sameId sameForm
  · exact current

end Solcore.SourceSemantics.SourceInferenceExecution.RelativeLocalRead
