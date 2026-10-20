import Solcore.SourceSemantics.SourceInferenceNormalizedBinderFormation

/-! Finalizer capture checks travel backwards along the actual node table.
Header items carry their binders explicitly until the enclosing for node is
recorded. Expression coercion attachment preserves this binder inventory. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
open Frontend SourceInference TypeSystem SourceInferenceSoundness

def NoCaptureBinders (outer : Substitution) (binders : List TypedBinder) : Prop :=
  ∀ binder ∈ binders, Detail.LocalBinderInstantiationNoCapture outer binder

def NoCaptureNodes (outer : Substitution) (nodes : List Node) : Prop :=
  NoCaptureBinders outer (nodes.flatMap Node.initializedLetBinders)

def NoCaptureItems (outer : Substitution) (items : List ForItemForm) : Prop :=
  NoCaptureBinders outer (items.flatMap ForItemForm.initializedLetBinders)

namespace NoCaptureNodes

theorem mono {outer : Substitution} {before after : List Node}
    (formed : NoCaptureNodes outer after) (subset : before ⊆ after) :
    NoCaptureNodes outer before := by
  intro binder member
  obtain ⟨node, present, selected⟩ := List.mem_flatMap.mp member
  exact formed binder (List.mem_flatMap.mpr ⟨node, subset present, selected⟩)

theorem of_prefix {outer : Substitution} {before after : List Node}
    (formed : NoCaptureNodes outer after) (retained : before <+: after) :
    NoCaptureNodes outer before := formed.mono retained.subset

theorem at_statement {outer : Substitution} {nodes : List Node}
    (formed : NoCaptureNodes outer nodes) {node : StatementNode}
    (member : .statement node ∈ nodes) :
    NoCaptureBinders outer node.form.initializedLetBinders :=
  fun binder selected => formed binder (List.mem_flatMap.mpr ⟨_, member, selected⟩)

theorem of_finalizer
    {context : SourceInference.Context} {expectedReturn : Ty} {state : State}
    {roots : List NodeId} {result : SourceInference.Result}
    (resources : FinalInferenceResources context expectedReturn state roots result) :
    NoCaptureNodes result.substitution state.nodes :=
  resources.local_no_capture

theorem modifyExpressionNode_inventory (state : State) (id : ExpressionId)
    (modify : ExpressionNode → ExpressionNode) :
    (state.modifyExpressionNode id modify).nodes.flatMap Node.initializedLetBinders =
      state.nodes.flatMap Node.initializedLetBinders := by
  change (state.nodes.map _).flatMap _ = _
  rw [List.flatMap_map]
  apply congrArg (fun operation : Node → List TypedBinder => state.nodes.flatMap operation)
  funext node
  cases node with
  | expression node => simp only; split <;> rfl
  | statement node => rfl

theorem attachExpressionCoercions_inventory (state : State)
    (entries : List Detail.ExpressionCoercions) :
    (Detail.attachExpressionCoercions state entries).nodes.flatMap Node.initializedLetBinders =
      state.nodes.flatMap Node.initializedLetBinders := by
  unfold Detail.attachExpressionCoercions
  induction entries generalizing state with
  | nil => rfl
  | cons entry rest ih =>
      exact (ih _).trans (modifyExpressionNode_inventory _ _ _)

theorem before_attachExpressionCoercions {outer : Substitution} {state : State}
    {entries : List Detail.ExpressionCoercions}
    (formed : NoCaptureNodes outer (Detail.attachExpressionCoercions state entries).nodes) :
    NoCaptureNodes outer state.nodes := by
  unfold NoCaptureNodes at formed ⊢
  rwa [attachExpressionCoercions_inventory] at formed

theorem for_items {outer : Substitution} {nodes : List Node}
    {id : StatementId} {span : Syntax.SourceSpan} {type : Ty}
    {initializer post : List ForItemForm} {condition : ExpressionId}
    {body : List StatementId}
    (formed : NoCaptureNodes outer nodes)
    (recorded : .statement {
      id := id
      span := span
      type := type
      form := .forLoop initializer condition post body } ∈ nodes) :
    NoCaptureItems outer initializer ∧ NoCaptureItems outer post := by
  have binders := formed.at_statement recorded
  exact ⟨fun binder member => binders binder (List.mem_append_left _ member),
    fun binder member => binders binder (List.mem_append_right _ member)⟩

end NoCaptureNodes

end Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
