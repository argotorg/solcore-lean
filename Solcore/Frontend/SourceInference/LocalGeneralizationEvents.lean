import Solcore.Frontend.SourceInference.LocalHeaderRequirementTiming

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
