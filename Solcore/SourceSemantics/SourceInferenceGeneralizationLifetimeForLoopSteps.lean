import Solcore.SourceSemantics.SourceInferenceGeneralizationLifetimeBranchSteps
import Solcore.SourceSemantics.SourceInferenceForSuffixPrivacy

/-! An actual for receipt connects all four child calls through both saved scopes. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail
namespace GeneralizationLifetime
variable {whole : TypedSource} {finalSubstitution : Substitution}
    {binder : TypedBinder} {initializer : ExpressionId}
    {event : RetainedGeneralization whole finalSubstitution binder initializer}
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {initializers post : List Syntax.ForItem} {condition : Syntax.Expr}
    {body : Syntax.Block} {expected : Ty} {initial : State} {result : StatementResult}

private structure ForFacts
    (receipt : SourceInference.ForStatementInferenceContinuation.Receipt
      fuel context source initializers condition post body expected initial result) : Prop where
  initReady : receipt.initialized.state.InferenceReady
  initWF : receipt.initialized.state.RequirementsWellFormed
  initialToInit : initial.InferenceProgress receipt.initialized.state
  testReady : receipt.testState.InferenceReady
  testWF : receipt.testState.RequirementsWellFormed
  initialToTest : initial.InferenceProgress receipt.testState
  bodyWF : receipt.bodyResult.state.RequirementsWellFormed
  restoredReady : (receipt.bodyResult.state.restoreLexicalScope receipt.initialized.state.lexicalScope).InferenceReady
  initialToRestored : initial.InferenceProgress
    (receipt.bodyResult.state.restoreLexicalScope receipt.initialized.state.lexicalScope)

private theorem forFacts
    (receipt : SourceInference.ForStatementInferenceContinuation.Receipt
      fuel context source initializers condition post body expected initial result)
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (catalog : LifetimeInferenceContext context)
    (returnBelow : expected.VariablesBelow initial.inference.next) : ForFacts receipt := by
  have allocated := State.InferenceProgress.allocateStatementId initial ready.solved
  have initialized := inferForItemsFuel_inferenceProperties ready.allocateStatementId
    catalog.formation catalog.canonical receipt.initialization
  have initializedWF := (inferForItemsFuel_direct_progress receipt.initialization).wellFormed
    (show initial.allocateStatementId.2.RequirementsWellFormed from wellFormed)
  have test := inferExprFuel_inferenceProperties initialized.2 catalog.formation catalog.canonical
    (by intro type member; cases member; exact Ty.variablesBelow_constructor _ _) receipt.tested
  have testWF := (inferExprFuel_direct_progress receipt.tested).wellFormed initializedWF
  have throughTest := allocated.trans (initialized.1.trans test.1)
  have bodyProperties := inferStatementsFuel_inferenceProperties
    (context := SourceInference.ForStatementInferenceContinuation.loopContext context)
    test.2.1 catalog.formation catalog.canonical (returnBelow.weaken throughTest.next_le) receipt.bodyAccepted
  have bodyWF := (inferStatementsFuel_direct_progress receipt.bodyAccepted).wellFormed testWF
  have restored := State.restoreLexicalScope_inferenceProperties initialized.2
    (test.1.trans bodyProperties.1)
  exact ⟨initialized.2, initializedWF, allocated.trans initialized.1,
    test.2.1, testWF, throughTest, bodyWF, restored.2,
    allocated.trans (initialized.1.trans restored.1)⟩

theorem forLoop_after_post
    (receipt : SourceInference.ForStatementInferenceContinuation.Receipt
      fuel context source initializers condition post body expected initial result)
    {entryNext : Nat} {outputs : List Ty}
    (lifetime : GeneralizationLifetime event entryNext receipt.postResult.state outputs) :
    GeneralizationLifetime event entryNext result.state [result.type] := by
  have privacy := SourceInferenceSoundness.ProtectedVariables.ForStatementInferenceContinuation.Receipt.privacy_after_post
    receipt lifetime.live
  have nextEq := congrArg InferState.next receipt.inference_eq
  have resultType : result.type = .unit := congrArg StatementResult.type receipt.completed
  have atEnd := lifetime.append (newOutputs := [result.type]) (Nat.le_of_eq nextEq.symm)
    privacy.1 privacy.2.1 (by
      intro type member
      cases List.mem_singleton.mp member
      rw [resultType]
      exact safe_closed _ _ (Ty.variablesBelow_constructor 0 _)) privacy.2.2
  exact atEnd.restrict_outputs (by simp)

theorem forLoop_after_body
    (receipt : SourceInference.ForStatementInferenceContinuation.Receipt
      fuel context source initializers condition post body expected initial result)
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (catalog : LifetimeInferenceContext context)
    (returnBelow : expected.VariablesBelow initial.inference.next)
    {entryNext : Nat} {outputs : List Ty}
    (lifetime : GeneralizationLifetime event entryNext receipt.bodyResult.state outputs) :
    GeneralizationLifetime event entryNext result.state [result.type] := by
  have facts := forFacts receipt ready wellFormed catalog returnBelow
  have savedSubset : receipt.initialized.state.localBinders ⊆ receipt.bodyResult.state.localBinders := by
    have same := congrArg LexicalScope.binders (inferExprFuel_success_lexicalScope_eq receipt.tested)
    change receipt.testState.localBinders = receipt.initialized.state.localBinders at same
    rw [← same]
    exact inferStatementsFuel_binders_subset receipt.bodyAccepted
  have restored := lifetime.restoreScope receipt.initialized.state.lexicalScope savedSubset
  have after := restored.inferForItems facts.restoredReady facts.bodyWF
    (catalog.withLoopDepth (context.loopDepth + 1)) receipt.postAccepted
  exact forLoop_after_post receipt after

theorem forLoop_post
    (receipt : SourceInference.ForStatementInferenceContinuation.Receipt
      fuel context source initializers condition post body expected initial result)
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (catalog : LifetimeInferenceContext context)
    (returnBelow : expected.VariablesBelow initial.inference.next)
    (lifetime : GeneralizationLifetime event receipt.bodyResult.state.inference.next receipt.postResult.state []) :
    GeneralizationLifetime event initial.inference.next result.state [result.type] := by
  have facts := forFacts receipt ready wellFormed catalog returnBelow
  exact (forLoop_after_post receipt lifetime).weaken_entry facts.initialToRestored.next_le

theorem forLoop_body
    (receipt : SourceInference.ForStatementInferenceContinuation.Receipt
      fuel context source initializers condition post body expected initial result)
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (catalog : LifetimeInferenceContext context)
    (returnBelow : expected.VariablesBelow initial.inference.next)
    (lifetime : GeneralizationLifetime event receipt.testState.inference.next receipt.bodyResult.state [receipt.bodyResult.type]) :
    GeneralizationLifetime event initial.inference.next result.state [result.type] := by
  have facts := forFacts receipt ready wellFormed catalog returnBelow
  exact (forLoop_after_body receipt ready wellFormed catalog returnBelow lifetime).weaken_entry
    facts.initialToTest.next_le

theorem forLoop_condition
    (receipt : SourceInference.ForStatementInferenceContinuation.Receipt
      fuel context source initializers condition post body expected initial result)
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (catalog : LifetimeInferenceContext context)
    (returnBelow : expected.VariablesBelow initial.inference.next)
    (lifetime : GeneralizationLifetime event receipt.initialized.state.inference.next receipt.testState [receipt.test.type]) :
    GeneralizationLifetime event initial.inference.next result.state [result.type] := by
  have facts := forFacts receipt ready wellFormed catalog returnBelow
  have after := lifetime.inferStatements facts.testReady facts.testWF
    (catalog.withLoopDepth (context.loopDepth + 1))
    (returnBelow.weaken facts.initialToTest.next_le)
    (lifetime.older _ (returnBelow.weaken facts.initialToInit.next_le)) receipt.bodyAccepted
  exact (forLoop_after_body receipt ready wellFormed catalog returnBelow after).weaken_entry
    facts.initialToInit.next_le

theorem forLoop_initializer
    (receipt : SourceInference.ForStatementInferenceContinuation.Receipt
      fuel context source initializers condition post body expected initial result)
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (catalog : LifetimeInferenceContext context)
    (returnBelow : expected.VariablesBelow initial.inference.next)
    (lifetime : GeneralizationLifetime event initial.inference.next receipt.initialized.state []) :
    GeneralizationLifetime event initial.inference.next result.state [result.type] := by
  have facts := forFacts receipt ready wellFormed catalog returnBelow
  have tested := lifetime.inferExpr facts.initReady facts.initWF catalog
    (by intro type member; cases member; exact Ty.variablesBelow_constructor _ _)
    (by intro type member; cases member; exact safe_closed _ _ (Ty.variablesBelow_constructor 0 _)) receipt.tested
  have after := tested.inferStatements facts.testReady facts.testWF
    (catalog.withLoopDepth (context.loopDepth + 1))
    (returnBelow.weaken facts.initialToTest.next_le) (tested.older _ returnBelow) receipt.bodyAccepted
  exact forLoop_after_body receipt ready wellFormed catalog returnBelow after

end GeneralizationLifetime
end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
