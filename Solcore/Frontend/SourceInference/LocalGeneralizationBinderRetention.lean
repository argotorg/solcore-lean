import Solcore.Frontend.SourceInference.LocalGeneralizationEvents

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
