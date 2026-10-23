import Solcore.SourceSemantics.CoreLowering.CallableBodyMetadataViews

/-! A path from a lambda's initializer and body roots either remains at the
initializer or enters its actual body. The executable lookup fixes that edge. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableLambdaBodyReachability
open Frontend SourceInference TypeSystem CallableBodyMetadataViews

/-- Canonical reference paths from the initializer use its actual lambda
form. Every subsequent step belongs to the same body's root closure. -/
theorem Reaches.lambda_roots_cases {source : TypedSource}
    {initializer : ExpressionId} {lambda : ExpressionNode}
    {parameters : List TypedBinder} {result : Ty} {body : List StatementId}
    (found : source.lookupExpression? initializer = some lambda)
    (form : lambda.form = .lambda parameters result body)
    {node : NodeId} (path : Reaches source (lambdaRoots initializer body) node) :
    node = .expression initializer ∨ Reaches source (body.map NodeId.statement) node := by
  induction path with
  | root member =>
    rcases List.mem_cons.mp member with same | member
    · exact .inl same
    · exact .inr (.root member)
  | @expression id expression child parent selected edge ih =>
    rcases ih with same | reached
    · have sameId : id = initializer := NodeId.expression.inj same
      subst id
      have sameNode : expression = lambda := Option.some.inj (selected.symm.trans found)
      apply Or.inr
      apply Reaches.root
      simpa only [sameNode, form, ExpressionForm.references] using edge
    · exact .inr (.expression reached selected edge)
  | statement _ selected edge ih =>
    rcases ih with same | reached
    · cases same
    · exact .inr (.statement reached selected edge)

end Solcore.SourceSemantics.CoreLowering.CallableLambdaBodyReachability
