import Solcore.SourceSemantics.CoreLowering.CallableLambdaBodyReachability

/-! Correspondence restricted to the actual roots of a callable body.
The source table may contain unrelated nodes and different input types.
The relation preserves input identities and the forms read along real paths;
it does not assert typing or execution equivalence by itself. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableBodyMetadataViews
open Frontend SourceInference CallableLambdaBodyReachability LambdaMetadataViews

structure BodyView (source view : TypedSource) (roots : List NodeId) : Prop where
  owner : source.owner = view.owner
  inputs : source.inputs.map TypedBinder.id = view.inputs.map TypedBinder.id
  expression {id : ExpressionId}
      (reached : Reaches source roots (.expression id) ∨ Reaches view roots (.expression id))
      {node : ExpressionNode} (found : view.lookupExpression? id = some node) :
      ∃ original, source.lookupExpression? id = some original ∧
        original.id = node.id ∧ original.form = node.form
  expression_back {id : ExpressionId}
      (reached : Reaches source roots (.expression id) ∨ Reaches view roots (.expression id))
      {node : ExpressionNode} (found : source.lookupExpression? id = some node) :
      ∃ original, view.lookupExpression? id = some original ∧
        original.id = node.id ∧ original.form = node.form
  statement {id : StatementId}
      (reached : Reaches source roots (.statement id) ∨ Reaches view roots (.statement id)) :
      source.lookupStatement? id = view.lookupStatement? id

theorem BodyView.of_metadata {source view : TypedSource}
    (related : MetadataView source view) (roots : List NodeId) :
    BodyView source view roots where
  owner := related.owner
  inputs := congrArg (List.map TypedBinder.id) related.inputs
  expression _ _ found := related.expression found
  expression_back _ _ found := related.symm.expression found
  statement _ := by
    cases found : source.lookupStatement? _ with
    | none =>
      cases other : view.lookupStatement? _ with
      | none => rfl
      | some node => have := related.statement other; simp only [found] at this; cases this
    | some node => exact (related.symm.statement found).symm

theorem BodyView.refl (source : TypedSource) (roots : List NodeId) :
    BodyView source source roots := BodyView.of_metadata (MetadataView.refl source) roots

theorem BodyView.symm {source view : TypedSource} {roots : List NodeId}
    (related : BodyView source view roots) : BodyView view source roots where
  owner := related.owner.symm
  inputs := related.inputs.symm
  expression reached _ found := related.expression_back reached.symm found
  expression_back reached _ found := related.expression reached.symm found
  statement reached := (related.statement reached.symm).symm

theorem BodyView.reaches {source view : TypedSource} {roots : List NodeId}
    (related : BodyView source view roots) {id : NodeId} (reached : Reaches source roots id) :
    Reaches view roots id := by
  induction reached with
  | root member => exact .root member
  | expression parent found edge ih =>
    obtain ⟨node, selected, _, form⟩ := related.expression_back (.inl parent) found
    exact .expression ih selected (form ▸ edge)
  | statement parent found edge ih =>
    exact .statement ih ((related.statement (.inl parent)).symm.trans found) edge

theorem BodyView.trans {source middle view : TypedSource} {roots : List NodeId}
    (first : BodyView source middle roots) (second : BodyView middle view roots) :
    BodyView source view roots where
  owner := first.owner.trans second.owner
  inputs := first.inputs.trans second.inputs
  expression reached _ found := by
    have atMiddle : Reaches middle roots _ :=
      reached.elim first.reaches second.symm.reaches
    obtain ⟨between, foundMiddle, sameId, sameForm⟩ := second.expression (.inl atMiddle) found
    obtain ⟨original, selected, originalId, originalForm⟩ :=
      first.expression (.inr atMiddle) foundMiddle
    exact ⟨original, selected, originalId.trans sameId, originalForm.trans sameForm⟩
  expression_back reached _ found := by
    have atMiddle : Reaches middle roots _ :=
      reached.elim first.reaches second.symm.reaches
    obtain ⟨between, foundMiddle, sameId, sameForm⟩ :=
      first.expression_back (.inr atMiddle) found
    obtain ⟨original, selected, originalId, originalForm⟩ :=
      second.expression_back (.inl atMiddle) foundMiddle
    exact ⟨original, selected, originalId.trans sameId, originalForm.trans sameForm⟩
  statement reached := by
    have atMiddle : Reaches middle roots _ :=
      reached.elim first.reaches second.symm.reaches
    exact (first.statement (.inr atMiddle)).trans (second.statement (.inl atMiddle))

private theorem reaches_from_roots {source : TypedSource} {roots children : List NodeId}
    (parents : ∀ id ∈ children, Reaches source roots id)
    {id : NodeId} (reached : Reaches source children id) : Reaches source roots id := by
  induction reached with
  | root member => exact parents _ member
  | expression _ found edge ih => exact .expression ih found edge
  | statement _ found edge ih => exact .statement ih found edge

/-- A compiler's actual child roots inherit the same correspondence. -/
theorem BodyView.restrict {source view : TypedSource} {roots children : List NodeId}
    (related : BodyView source view roots)
    (parents : ∀ id ∈ children, Reaches source roots id) :
    BodyView source view children where
  owner := related.owner
  inputs := related.inputs
  expression reached _ found := related.expression
    (reached.elim (fun path => .inl (reaches_from_roots parents path))
      (fun path => .inr (reaches_from_roots (fun id member => related.reaches (parents id member)) path)))
    found
  expression_back reached _ found := related.expression_back
    (reached.elim (fun path => .inl (reaches_from_roots parents path))
      (fun path => .inr (reaches_from_roots (fun id member => related.reaches (parents id member)) path)))
    found
  statement reached := related.statement
    (reached.elim (fun path => .inl (reaches_from_roots parents path))
      (fun path => .inr (reaches_from_roots (fun id member => related.reaches (parents id member)) path)))

/-- The initial root comes from the lambda creation occurrence and its actual
body IDs; later expression and statement readers use `reaches`. -/
def lambdaRoots (id : ExpressionId) (body : List StatementId) : List NodeId :=
  .expression id :: body.map NodeId.statement

end Solcore.SourceSemantics.CoreLowering.CallableBodyMetadataViews
