import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalCapturedScopes
import Solcore.SourceSemantics.CoreLowering.CallableBodyViewSubstitution

/-! The retained capture identifies the original lambda header through the
saved body view. Substitution preserves its body occurrence identities. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalCapturedLambdaHeader
open Frontend SourceInference TypeSystem
open CallableBodyMetadataViews CallableLambdaBodyReachability

/-- Invert the actual substituted lookup, retaining the same lambda body.
Parameter and result types may have changed under the substitution. -/
theorem lambda_header_before_substitution
    {source : TypedSource} {active : Substitution} {initializer : ExpressionId}
    {node : ExpressionNode} {parameters : List TypedBinder} {result : Ty}
    {body : List StatementId}
    (found : (source.applySubstitution active).lookupExpression? initializer = some node)
    (form : node.form = .lambda parameters result body) :
    ∃ original originalParameters originalResult,
      source.lookupExpression? initializer = some original ∧
      original.form = .lambda originalParameters originalResult body := by
  rw [lookupExpression_apply] at found
  cases selected : source.lookupExpression? initializer with
  | none => simp only [selected, Option.map_none, reduceCtorEq] at found
  | some original =>
      simp only [selected, Option.map_some, Option.some.injEq] at found
      rw [← found] at form
      cases original with
      | mk id span type actual requirements coercions localStart =>
          cases actual <;>
            simp only [ExpressionNode.applySubstitution, ExpressionForm.applySubstitution,
              reduceCtorEq] at form
          next oldParameters oldResult oldBody =>
            have sameBody := (ExpressionForm.lambda.inj form).2.2
            exact ⟨_, oldParameters, oldResult, rfl, sameBody ▸ rfl⟩

/-- The stored Attachment and the real capture recover a header in the same
original binding source, without asserting whole-source equality. -/
theorem captured_header
    {function : Dynamic.GeneralizedClosure}
    {binding : SourceCoreLocalPolymorphism.Binding} {lexical : Substitution}
    (saved : GeneralizedLocalCapturedScopes.Attachment function binding lexical)
    (captures : Dynamic.GeneralizedClosureCaptures function.definitionContext function.source
      function.captured function.binder function.initializer function)
    (unique : NodeOccurrencesUnique function.source)
    (initializer : function.initializer = binding.initializer) :
    ∃ original parameters result,
      binding.source.lookupExpression? binding.initializer = some original ∧
      original.form = .lambda parameters result function.body := by
  obtain ⟨node, occurrence, form, _⟩ := captures.occurrence
  have found := lookupExpression?_complete unique occurrence
  have reached : Reaches function.source (lambdaRoots function.initializer function.body)
      (.expression function.initializer) := .root (List.mem_cons_self)
  obtain ⟨original, originalFound, _, originalForm⟩ :=
    saved.view.expression_back (.inl reached) found
  rw [initializer] at originalFound
  exact lambda_header_before_substitution originalFound (originalForm.trans form)

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalCapturedLambdaHeader
