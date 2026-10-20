import Solcore.Frontend.SourceInference.LocalGeneralizationBoundedProgress

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
