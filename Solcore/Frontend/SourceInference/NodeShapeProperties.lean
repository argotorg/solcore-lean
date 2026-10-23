import Solcore.Frontend.SourceInference.Expression
import Solcore.Frontend.SourceInference.StateProperties

/-! Inference may attach coercion metadata to existing expressions. Their
identities and syntax, including child edges and local targets, stay fixed. -/
set_option autoImplicit false

namespace Solcore.Frontend.SourceInference

def SameNodeShape : Node → Node → Prop
  | .expression before, .expression after => before.id = after.id ∧ before.form = after.form
  | .statement before, .statement after => before.id = after.id ∧ before.form = after.form
  | _, _ => False

def NodeShapesPreserved (before after : List Node) : Prop :=
  ∀ node ∈ before, ∃ current ∈ after, SameNodeShape node current

namespace SameNodeShape

theorem refl (node : Node) : SameNodeShape node node := by
  cases node <;> exact ⟨rfl, rfl⟩

theorem trans {before middle after : Node}
    (first : SameNodeShape before middle) (second : SameNodeShape middle after) :
    SameNodeShape before after := by
  cases before <;> cases middle <;> cases after <;>
    simp only [SameNodeShape] at first second ⊢
  all_goals first
  | contradiction
  | exact ⟨first.1.trans second.1, first.2.trans second.2⟩

theorem id {before after : Node} (same : SameNodeShape before after) :
    before.id = after.id := by
  cases before <;> cases after <;> simp only [SameNodeShape] at same
  all_goals first
  | contradiction
  | exact congrArg NodeId.expression same.1
  | exact congrArg NodeId.statement same.1

theorem references {before after : Node} (same : SameNodeShape before after) :
    before.references = after.references := by
  cases before <;> cases after <;> simp only [SameNodeShape] at same
  all_goals first
  | contradiction
  | exact congrArg ExpressionForm.references same.2
  | exact congrArg StatementForm.references same.2

end SameNodeShape

namespace NodeShapesPreserved

theorem refl (nodes : List Node) : NodeShapesPreserved nodes nodes :=
  fun node member => ⟨node, member, .refl node⟩

theorem trans {before middle after : List Node}
    (first : NodeShapesPreserved before middle)
    (second : NodeShapesPreserved middle after) : NodeShapesPreserved before after := by
  intro node member
  obtain ⟨current, present, firstShape⟩ := first node member
  obtain ⟨later, retained, secondShape⟩ := second current present
  exact ⟨later, retained, firstShape.trans secondShape⟩

theorem of_eq {before after : List Node} (same : after = before) :
    NodeShapesPreserved before after := same ▸ refl before

theorem recordNode (state : State) (node : Node) :
    NodeShapesPreserved state.nodes (state.recordNode node).nodes := by
  intro previous member
  exact ⟨previous, List.mem_append_left _ member, .refl previous⟩

theorem modifyExpressionNode (state : State) (id : ExpressionId)
    (modify : ExpressionNode → ExpressionNode)
    (form : ∀ node, (modify node).form = node.form) :
    NodeShapesPreserved state.nodes (state.modifyExpressionNode id modify).nodes := by
  intro node member
  unfold State.modifyExpressionNode
  refine ⟨_, List.mem_map.mpr ⟨node, member, rfl⟩, ?_⟩
  cases node with
  | statement node => exact ⟨rfl, rfl⟩
  | expression node =>
      dsimp
      split
      · rename_i selected
        exact ⟨selected, (form node).symm⟩
      · exact ⟨rfl, rfl⟩

theorem attachExpressionCoercions (state : State)
    (entries : List Detail.ExpressionCoercions) :
    NodeShapesPreserved state.nodes (Detail.attachExpressionCoercions state entries).nodes := by
  unfold Detail.attachExpressionCoercions
  induction entries generalizing state with
  | nil => exact refl _
  | cons entry entries ih =>
      simp only [List.foldl_cons]
      exact (modifyExpressionNode state entry.expression
        (fun node => Detail.appendExpressionCoercions node entry.coercions)
        (fun _ => rfl)).trans (ih _)

end NodeShapesPreserved
end Solcore.Frontend.SourceInference
