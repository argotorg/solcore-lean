import Solcore.SourceSemantics.SourceSpecializationLocalLexicalChildren
import Solcore.SourceSemantics.CoreLowering.CallableBodyViewSubstitution

/-! Actual substituted lookups retain the original lexical child path. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.Frontend.SourceSpecializationWorklist.LocalLambdaLexicalPath
open SourceInference TypeSystem
open Solcore.SourceSemantics.CoreLowering.CallableBodyMetadataViews

theorem statement_child_of_substitution
    {source : TypedSource} {active : Substitution} {roots : List NodeId}
    {id : StatementId} {statement : StatementNode} {child : NodeId}
    (previous : LocalLambdaLexicalPath source roots (.statement id))
    (found : (source.applySubstitution active).lookupStatement? id = some statement)
    (edge : child ∈ statement.form.references) :
    LocalLambdaLexicalPath source roots child := by
  rw [lookupStatement_apply] at found
  obtain ⟨original, actual, rfl⟩ := Option.map_eq_some_iff.mp found
  exact previous.statement_child actual (by
    simpa only [StatementNode.applySubstitution,
      StatementForm.applySubstitution_references] using edge)

theorem expression_child_of_substitution
    {source : TypedSource} {active : Substitution} {roots : List NodeId}
    {id : ExpressionId} {expression : ExpressionNode} {child : NodeId}
    (previous : LocalLambdaLexicalPath source roots (.expression id))
    (found : (source.applySubstitution active).lookupExpression? id = some expression)
    (nonLambda : ∀ parameters result body, expression.form ≠ .lambda parameters result body)
    (edge : child ∈ expression.form.references) :
    LocalLambdaLexicalPath source roots child := by
  rw [lookupExpression_apply] at found
  obtain ⟨original, actual, rfl⟩ := Option.map_eq_some_iff.mp found
  refine previous.expression_child actual ?_ ?_
  · intro parameters result body form
    apply nonLambda (parameters.map (TypedBinder.applySubstitution active))
      (active.apply result) body
    change original.form.applySubstitution active = _
    rw [form]
    rfl
  · simpa only [ExpressionNode.applySubstitution,
      ExpressionForm.applySubstitution_references] using edge

end Solcore.Frontend.SourceSpecializationWorklist.LocalLambdaLexicalPath
