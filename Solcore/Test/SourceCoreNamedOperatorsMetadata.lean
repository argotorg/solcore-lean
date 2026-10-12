import Solcore.Test.SourceCoreNamedOperatorsFacts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedLexicalOperatorRoots

/-! Actual finite Source observations retain numeric-literal evidence while
excluding special contextual hooks and indirect calls in this program. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreNamedOperators
open Solcore Frontend SourceInference SourceSemantics CoreLowering

theorem ObservedFactory.no_calls {fixture : CompiledFixture} (observed : ObservedFactory fixture)
    {id : ExpressionId} {node : ExpressionNode}
    (found : observed.row.function.typedBody.lookupExpression? id = some node)
    {callee arguments resolution} (form : node.form = .call callee arguments (.indirect resolution)) : False := by
  rcases observed.expression_cases (lookupExpression?_sound found) with same | same | same | same | same | same | same
  all_goals subst node
  · rw [observed.shape.conditionRead.form] at form; cases form
  · rw [observed.shape.zero.form] at form; cases form
  · rw [observed.shape.comparison.form] at form; cases form
  · rw [observed.shape.argumentRead.form] at form; cases form
  · rw [observed.shape.one.form] at form; cases form
  · rw [observed.shape.difference.form] at form; cases form
  · rw [observed.shape.finalRead.form] at form; cases form

theorem ObservedFactory.metadata {fixture : CompiledFixture} (observed : ObservedFactory fixture)
    (named : CallableIndexedNamedGeneration.Named) :
    CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles.NativeMetadataFor
      fixture.recipe.compiled.indexed named observed.row.function.typedBody := by
  constructor
  · intro id _tree node found
    rcases observed.expression_cases (lookupExpression?_sound found) with same | same | same | same | same | same | same
    all_goals subst node
    · exact .inl observed.shape.conditionRead.requirements
    · exact .inr ⟨_, _, observed.shape.zero.form⟩
    · exact .inl observed.shape.comparison.requirements
    · exact .inl observed.shape.argumentRead.requirements
    · exact .inr ⟨_, _, observed.shape.one.form⟩
    · exact .inl observed.shape.difference.requirements
    · exact .inl observed.shape.finalRead.requirements
  · intro id _tree node found
    rcases observed.expression_cases (lookupExpression?_sound found) with same | same | same | same | same | same | same
    all_goals subst node
    · exact observed.shape.conditionRead.coercions
    · exact (SourceCoreElaboration.validateWordIntegerLiteral_sound observed.shape.zero.accepted).coercions
    · exact observed.shape.comparison.coercions
    · exact observed.shape.argumentRead.coercions
    · exact (SourceCoreElaboration.validateWordIntegerLiteral_sound observed.shape.one.accepted).coercions
    · exact observed.shape.difference.coercions
    · exact observed.shape.finalRead.coercions
  · intro id _tree
    simp only [observed.noLocals, List.find?_nil]
  · intro id _tree node found callee arguments resolution form
    exact False.elim (observed.no_calls found form)
  · intro id _tree node _found name binder _form
    simp only [observed.noLocals, List.any_nil]

end Tests.SourceCoreNamedOperators
