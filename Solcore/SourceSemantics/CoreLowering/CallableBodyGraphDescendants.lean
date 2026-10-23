import Solcore.SourceSemantics.CoreLowering.CallableLambdaBodyReachability
import Solcore.SourceSemantics.Graph

/-! Canonical callable-body reference paths give proper descendants of the
actual parent of the body roots. Every step uses the same source lookup. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableLambdaBodyReachability
open Frontend SourceInference TypeSystem

private theorem expression_child {source : TypedSource} {id : ExpressionId}
    {node : ExpressionNode} (found : source.lookupExpression? id = some node)
    {child : NodeId} (edge : child ∈ node.form.references) :
    DirectChild source (.expression id) child := by
  have contained := lookupExpression?_sound found
  exact ⟨.expression node,
    ⟨contained.1, congrArg NodeId.expression contained.2⟩, edge⟩

private theorem statement_child {source : TypedSource} {id : StatementId}
    {node : StatementNode} (found : source.lookupStatement? id = some node)
    {child : NodeId} (edge : child ∈ node.form.references) :
    DirectChild source (.statement id) child := by
  have contained := lookupStatement?_sound found
  exact ⟨.statement node,
    ⟨contained.1, congrArg NodeId.statement contained.2⟩, edge⟩

/-- Body roots are actual children, so even a root case yields a nonempty
path from the enclosing occurrence. Subsequent steps retain every canonical
reference, including references inside nested initializers. -/
theorem Reaches.descends_of_root_edges {source : TypedSource}
    {roots : List NodeId} {root node : NodeId}
    (path : Reaches source roots node)
    (rootEdges : ∀ child ∈ roots, DirectChild source root child) :
    Descends source root node := by
  induction path with
  | root member => exact .direct (rootEdges _ member)
  | expression _ found edge ih =>
    exact ih.trans (.direct (expression_child found edge))
  | statement _ found edge ih =>
    exact ih.trans (.direct (statement_child found edge))

/-- The exact lambda lookup supplies the body-root edges without a separate
graph-closure premise. The result concerns its actual initializer occurrence. -/
theorem Reaches.descends_from_lambda {source : TypedSource}
    {initializer : ExpressionId} {lambda : ExpressionNode}
    {parameters : List TypedBinder} {result : Ty} {body : List StatementId}
    (found : source.lookupExpression? initializer = some lambda)
    (form : lambda.form = .lambda parameters result body)
    {node : NodeId} (path : Reaches source (body.map NodeId.statement) node) :
    Descends source (.expression initializer) node := by
  apply path.descends_of_root_edges
  intro child member
  apply expression_child found
  simpa only [form, ExpressionForm.references] using member

end Solcore.SourceSemantics.CoreLowering.CallableLambdaBodyReachability
