import Solcore.SourceSemantics.SourceInferenceActualGeneralizationOrigins
import Solcore.Frontend.SourceInference.LocalGeneralizationEvents

/-! Exact-call generalization origins are collected in node-table order and
in header results before the enclosing for statement records them. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution.ActualGeneralization
open Frontend SourceInference TypeSystem Detail
variable {root : CallIndex}

def Item (root : CallIndex) (item : ForItemForm) : Prop :=
  ∀ binder initializer, item = .letDecl binder (some initializer) → Origin root binder initializer

def Items (root : CallIndex) (items : List ForItemForm) : Prop := ∀ item ∈ items, Item root item

def Statement (root : CallIndex) (node : StatementNode) : Prop :=
  match node.form with
  | .letDecl binder (some initializer) => Origin root binder initializer
  | .forLoop initial _ post _ => Items root initial ∧ Items root post
  | _ => True

def Origins (root : CallIndex) (nodes : List Node) : Prop :=
  ∀ node, .statement node ∈ nodes → Statement root node

theorem Origins.empty : Origins root [] := by intro _ impossible; cases impossible

theorem Origins.expression {nodes : List Node} (origins : Origins root nodes) (node : ExpressionNode) :
    Origins root (nodes ++ [.expression node]) := by
  intro statement present
  rcases List.mem_append.mp present with previous | fresh
  · exact origins statement previous
  · cases List.mem_singleton.mp fresh

theorem Origins.statement {nodes : List Node} (origins : Origins root nodes)
    (node : StatementNode) (event : Statement root node) : Origins root (nodes ++ [.statement node]) := by
  intro statement present
  rcases List.mem_append.mp present with previous | fresh
  · exact origins statement previous
  · cases List.mem_singleton.mp fresh
    exact event

theorem Origins.mapExpressions {nodes : List Node} (origins : Origins root nodes)
    (modify : ExpressionNode → ExpressionNode) :
    Origins root (nodes.map (fun node => match node with
      | .expression expression => .expression (modify expression)
      | .statement statement => .statement statement)) := by
  intro statement present
  obtain ⟨node, member, selected⟩ := List.mem_map.mp present
  cases node with
  | expression expression => cases selected
  | statement original =>
    cases selected
    exact origins _ member

theorem Statement.same_form {before after : StatementNode} (origin : Statement root before)
    (same : after.form = before.form) : Statement root after := by
  unfold Statement
  rw [same]
  exact origin

theorem Origins.mapStatements {nodes : List Node} (origins : Origins root nodes)
    (modify : StatementNode → StatementNode) (forms : ∀ node, (modify node).form = node.form) :
    Origins root (nodes.map (fun node => match node with
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
    (here : CallOccurrence root (.forItem (fuel + 1) context source initial result.1 result.2)) : Item root result.1 := by
  intro binder initializer same
  rw [receipt.recorded] at same
  cases same
  exact .header receipt here

theorem Statement.of_let {fuel context source initial result}
    (receipt : LocalLetRequirementTiming.Receipt fuel context source initial result)
    {expectedReturn : Ty}
    (here : CallOccurrence root (.statement (fuel + 1) context source expectedReturn initial result))
    {node : StatementNode}
    (form : node.form = .letDecl receipt.binding.1 (some receipt.value.id)) : Statement root node := by
  unfold Statement
  rw [form]
  exact .statement receipt here

end Solcore.SourceSemantics.SourceInferenceExecution.ActualGeneralization
