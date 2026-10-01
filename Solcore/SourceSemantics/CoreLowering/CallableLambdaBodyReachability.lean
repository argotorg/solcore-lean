import Solcore.SourceSemantics.CoreLowering.CallableLambdaViewEdits

/-! Finite paths through the typed source's actual occurrence references.
Cycles are permitted. A compiler edit is irrelevant to a body only when its
selected expression IDs are explicitly excluded from these paths. Ownership,
unique occurrence IDs and graph well-formedness alone do not give that fact. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableLambdaBodyReachability
open Frontend SourceInference
open CallableLambdaViewEdits

inductive Reaches (source : TypedSource) (roots : List NodeId) : NodeId → Prop where
  | root {id} (member : id ∈ roots) : Reaches source roots id
  | expression {id node child} (parent : Reaches source roots (.expression id))
      (found : source.lookupExpression? id = some node) (edge : child ∈ node.form.references) :
      Reaches source roots child
  | statement {id node child} (parent : Reaches source roots (.statement id))
      (found : source.lookupStatement? id = some node) (edge : child ∈ node.form.references) :
      Reaches source roots child

def Avoids (source : TypedSource) (roots : List NodeId) (changed : List ExpressionId) : Prop :=
  ∀ id ∈ changed, ¬Reaches source roots (.expression id)

theorem Avoids.fresh {source : TypedSource} {roots : List NodeId} {changed : List ExpressionId}
    (avoids : Avoids source roots changed) {id : ExpressionId}
    (reached : Reaches source roots (.expression id)) : id ∉ changed :=
  fun member => avoids id member reached

theorem expression_lookup {source view : TypedSource} {roots : List NodeId} {changed : List ExpressionId}
    (edited : LocalView source view changed) (avoids : Avoids source roots changed)
    {id : ExpressionId} (reached : Reaches source roots (.expression id)) :
    source.lookupExpression? id = view.lookupExpression? id :=
  edited.unchanged id (avoids.fresh reached)

/-- Metadata views preserve reference topology even at edited headers. -/
theorem Reaches.metadata {source view : TypedSource} {roots : List NodeId}
    (metadata : LambdaMetadataViews.MetadataView source view)
    {id : NodeId} (reached : Reaches source roots id) : Reaches view roots id := by
  induction reached with
  | root member => exact .root member
  | expression _ found edge ih =>
    obtain ⟨node, selected, _, sameForm⟩ := metadata.symm.expression found
    exact .expression ih selected (sameForm ▸ edge)
  | statement _ found edge ih => exact .statement ih (metadata.symm.statement found) edge

theorem Avoids.view {source view : TypedSource} {roots : List NodeId} {changed : List ExpressionId}
    (metadata : LambdaMetadataViews.MetadataView source view) (avoids : Avoids source roots changed) :
    Avoids view roots changed :=
  fun id member reached => avoids id member (reached.metadata metadata.symm)

/-- The same finite reference path exists after the actual local edits.
No acyclicity assumption is introduced or derived. -/
theorem Reaches.transport {source view : TypedSource} {roots : List NodeId} {changed : List ExpressionId}
    (edited : LocalView source view changed) (avoids : Avoids source roots changed)
    {id : NodeId} (reached : Reaches source roots id) : Reaches view roots id := by
  induction reached with
  | root member => exact .root member
  | expression parent found edge ih =>
    exact .expression ih ((expression_lookup edited avoids parent).symm.trans found) edge
  | statement parent found edge ih =>
    exact .statement ih (edited.metadata.symm.statement found) edge

/-- Body expression lookups remain exact even when a path revisits a node. -/
theorem body_lookup {source view : TypedSource} {body : List StatementId} {changed : List ExpressionId}
    (edited : LocalView source view changed) (avoids : Avoids source (body.map NodeId.statement) changed)
    {id : ExpressionId} (reached : Reaches source (body.map NodeId.statement) (.expression id)) :
    source.lookupExpression? id = view.lookupExpression? id := expression_lookup edited avoids reached


/-- Source binders come from complete inputs, lambda forms and statement
metadata, all retained by the actual allocation metadata view. -/
theorem declaredBinders {source view : TypedSource}
    (metadata : LambdaMetadataViews.MetadataView source view) :
    SourceCoreDataPlaces.declaredBinders source = SourceCoreDataPlaces.declaredBinders view := by
  unfold SourceCoreDataPlaces.declaredBinders
  rw [metadata.inputs]
  congr 1
  have nodes := metadata.nodes
  generalize source.nodes = left at nodes ⊢
  generalize view.nodes = right at nodes ⊢
  induction nodes with
  | nil => rfl
  | cons node _ ih =>
    cases node with
    | expression sameId sameForm => simp only [List.flatMap_cons, sameForm, ih]
    | statement => simp only [List.flatMap_cons, ih]

theorem rootBinder {source view : TypedSource}
    (metadata : LambdaMetadataViews.MetadataView source view) (id : Resolved.LocalId) :
    SourceCoreDataPlaces.rootBinder source id = SourceCoreDataPlaces.rootBinder view id := by
  unfold SourceCoreDataPlaces.rootBinder
  rw [metadata.owner, declaredBinders metadata]

end Solcore.SourceSemantics.CoreLowering.CallableLambdaBodyReachability
