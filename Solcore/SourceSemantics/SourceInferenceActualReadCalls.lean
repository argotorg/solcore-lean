import Solcore.SourceSemantics.SourceInferenceActualCallGraph
import Solcore.Frontend.SourceInference.LocalReadOriginsHelpers

/-! A retained local reference keeps the exact operational lookup and its
executed path from the same root call. Expression coercions may update the
record's type and requirements, while its occurrence and resolution stay fixed. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution.ActualLocalRead
open Frontend SourceInference TypeSystem Detail

/-- The precise call carried by the existing operational lookup receipt. -/
def lookupCall (lookup : LocalReadEvents.Lookup) : CallIndex :=
  .expression (lookup.fuel + 1) lookup.context lookup.expression lookup.expected
    lookup.initial lookup.result.1 lookup.result.2

def Origin (root : CallIndex) (node : ExpressionNode) : Prop :=
  ∃ lookup : LocalReadEvents.Lookup,
    node.id = lookup.id ∧
    node.form = .reference lookup.name.value (.local lookup.binder.id) ∧
    CallOccurrence root (lookupCall lookup)

def Origins (root : CallIndex) (nodes : List Node) : Prop :=
  ∀ node, .expression node ∈ nodes → ∀ name binder,
    node.form = .reference name (.local binder) → Origin root node

variable {root : CallIndex}

theorem Origins.empty : Origins root [] := by intro _ impossible; cases impossible

theorem Origin.same_occurrence {before after : ExpressionNode}
    (origin : Origin root before) (id : after.id = before.id) (form : after.form = before.form) :
    Origin root after := by
  obtain ⟨lookup, sameId, sameForm, here⟩ := origin
  exact ⟨lookup, id.trans sameId, form.trans sameForm, here⟩

theorem Origins.statement {nodes : List Node} (origins : Origins root nodes) (node : StatementNode) :
    Origins root (nodes ++ [.statement node]) := by
  intro expression member name binder form
  rcases List.mem_append.mp member with old | fresh
  · exact origins expression old name binder form
  · cases List.mem_singleton.mp fresh

theorem Origins.expression {nodes : List Node} (origins : Origins root nodes) (node : ExpressionNode)
    (origin : ∀ name binder, node.form = .reference name (.local binder) → Origin root node) :
    Origins root (nodes ++ [.expression node]) := by
  intro expression member name binder form
  rcases List.mem_append.mp member with old | fresh
  · exact origins expression old name binder form
  · cases List.mem_singleton.mp fresh
    exact origin name binder form

theorem Origins.nonlocalExpression {nodes : List Node} (origins : Origins root nodes) (node : ExpressionNode)
    (nonlocal : LocalReadEvents.Nonlocal node.form) : Origins root (nodes ++ [.expression node]) :=
  origins.expression node (fun name binder form => (nonlocal name binder form).elim)

theorem Origins.modifyStatementNode {state : State} (origins : Origins root state.nodes)
    (id : StatementId) (modify : StatementNode → StatementNode) :
    Origins root (state.modifyStatementNode id modify).nodes := by
  intro expression present name binder form
  obtain ⟨node, member, same⟩ := List.mem_map.mp present
  cases node with
  | expression original => cases same; exact origins _ member name binder form
  | statement original => simp only at same; split at same <;> cases same

theorem Origins.modifyExpressionNode {state : State} (origins : Origins root state.nodes)
    (id : ExpressionId) (modify : ExpressionNode → ExpressionNode)
    (forms : ∀ node, (modify node).form = node.form) :
    Origins root (state.modifyExpressionNode id modify).nodes := by
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

theorem Origins.attachExpressionCoercions {state : State} (origins : Origins root state.nodes)
    (entries : List Detail.ExpressionCoercions) :
    Origins root (Detail.attachExpressionCoercions state entries).nodes := by
  unfold Detail.attachExpressionCoercions
  induction entries generalizing state with
  | nil => exact origins
  | cons entry rest ih => exact ih (origins.modifyExpressionNode _ _ (fun _ => rfl))

theorem Origins.recordExpression {state : State} (origins : Origins root state.nodes)
    (source : Syntax.Expr) (expression : InferredExpression) (form : ExpressionForm)
    (requirements : List RequirementId) (coercions : List CoercionStep) (start : Option Nat := none)
    (nonlocal : LocalReadEvents.Nonlocal form) :
    Origins root (Detail.recordExpression source expression form requirements coercions state start).2.nodes :=
  origins.nonlocalExpression _ nonlocal

theorem Origins.recordExpressionWithExpected {state : State} (origins : Origins root state.nodes)
    {context : Context} {source : Syntax.Expr} {id : ExpressionId} {type : Ty}
    {form : ExpressionForm} {requirements : List RequirementId} {expected : Option Ty}
    {start : Option Nat} {result : InferredExpression × State}
    (accepted : Detail.recordExpressionWithExpected context source id type form requirements expected state start = .ok result)
    (nonlocal : LocalReadEvents.Nonlocal form) : Origins root result.2.nodes := by
  obtain ⟨fitted, fit, _, recorded⟩ := Detail.recordExpressionWithExpected_success_record accepted
  rw [recorded]
  have same := (Detail.withExpected_occurrenceState_eq fit).1
  exact (show Origins root fitted.state.nodes from same.symm ▸ origins).nonlocalExpression _ nonlocal

/-- Recording the successful local branch preserves the issuing call itself,
rather than replacing it by an arbitrary accepted lookup with the same ID. -/
theorem Lookup.record_origins (lookup : LocalReadEvents.Lookup)
    (here : CallOccurrence root (lookupCall lookup))
    (origins : Origins root lookup.initial.nodes) : Origins root lookup.result.2.nodes := by
  have allocated : lookup.allocated = lookup.initial.allocateExpressionId.2 :=
    (congrArg Prod.snd lookup.allocation).symm
  have batchNodes : lookup.batch.2.nodes = lookup.initial.nodes := by
    simp only [LocalReadEvents.Lookup.batch, State.addRequirementsWithIds_nodes,
      LocalReadEvents.Lookup.advanced, allocated, State.allocateExpressionId_nodes]
  obtain ⟨fitted, fit, _, recorded⟩ := Detail.recordExpressionWithExpected_success_record lookup.recorded
  rw [recorded]
  have same : fitted.state.nodes = lookup.initial.nodes :=
    (Detail.withExpected_occurrenceState_eq fit).1.trans batchNodes
  apply (show Origins root fitted.state.nodes from same.symm ▸ origins).expression
  intro _ _ _
  exact ⟨lookup, Detail.withExpected_success_expression_id fit, rfl, here⟩

/-- Guarded lookup proves membership of the complete binder at its actual
issuing state; it does not merely recover a matching local ID. -/
theorem Origin.active {node : ExpressionNode} (origin : Origin root node) :
    ∃ lookup : LocalReadEvents.Lookup,
      node.id = lookup.id ∧
      node.form = .reference lookup.name.value (.local lookup.binder.id) ∧
      CallOccurrence root (lookupCall lookup) ∧
      lookup.binder ∈ lookup.initial.localBinders := by
  obtain ⟨lookup, sameId, sameForm, here⟩ := origin
  refine ⟨lookup, sameId, sameForm, here, ?_⟩
  have member := (State.lookupBinder?_eq_some_facts lookup.found).1
  have allocated : lookup.allocated = lookup.initial.allocateExpressionId.2 :=
    (congrArg Prod.snd lookup.allocation).symm
  rw [allocated] at member
  exact member

end Solcore.SourceSemantics.SourceInferenceExecution.ActualLocalRead
