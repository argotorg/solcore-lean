import Solcore.SourceSemantics.SourceInferenceForSuffixPrivacy
import Solcore.SourceSemantics.SourceInferenceActiveBlockState

/-! The actual for node retains both header inventories. Its initialized and
restored post states obtain active privacy from the same finalizer. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail

namespace ForStatementInferenceContinuation.Receipt
variable {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {initializers post : List Syntax.ForItem} {condition : Syntax.Expr}
    {body : Syntax.Located (List Syntax.Statement)} {expected : Ty} {initial : State} {result : StatementResult}

theorem headers_retained
    (receipt : SourceInference.ForStatementInferenceContinuation.Receipt fuel context source initializers condition post body expected initial result)
    {evidenceState : State} {roots : List NodeId}
    (retained : result.state.nodes <+: evidenceState.nodes) :
    (receipt.initialized.items.flatMap ForItemForm.initializedLetBinders ++
      receipt.postResult.items.flatMap ForItemForm.initializedLetBinders) ⊆
        (evidenceState.toTypedSource roots).initializedLetBinders := by
  intro binder member
  unfold TypedSource.initializedLetBinders
  exact List.mem_flatMap.mpr ⟨_,retained.subset receipt.recorded,member⟩

/-- Initializer prefixes and the actual body completion establish every state
condition needed to inspect either header list. -/
theorem active_stages
    (receipt : SourceInference.ForStatementInferenceContinuation.Receipt fuel context source initializers condition post body expected initial result)
    {wholeContext : SourceInference.Context} {wholeReturn : Ty}
    {evidenceState : State} {roots : List NodeId} {finalized : SourceInference.Result}
    (resources : FinalInferenceResources wholeContext wholeReturn evidenceState roots finalized)
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (nodesBelow : initial.NodesBelowNextOccurrence)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes))
    (expectedClosed : expected.VariablesBelow 0)
    (active : ActiveHeaderState initial (evidenceState.toTypedSource roots))
    (retained : TypingSourceExtends (result.state.toTypedSource roots) (evidenceState.toTypedSource roots))
    (extension : finalized.substitution.SemanticallyExtends result.state.inference.substitution) :
    ActiveHeaderState receipt.initialized.state (evidenceState.toTypedSource roots) ∧
      ActiveHeaderState (receipt.bodyResult.state.restoreLexicalScope receipt.initialized.state.lexicalScope)
        (evidenceState.toTypedSource roots) := by
  have initProperties := inferForItemsFuel_inferenceProperties ready.allocateStatementId formation canonical receipt.initialization
  have initializedBelow := (inferForItemsFuel_occurrenceBoundExtends receipt.initialization).nodesBelowNextOccurrence
    (State.allocateStatementId_preserves_nodesBelowNextOccurrence initial nodesBelow)
  have initWellFormed := (inferForItemsFuel_direct_progress receipt.initialization).wellFormed wellFormed
  have boolClosed : ∀ type ∈ some Ty.bool, type.VariablesBelow 0 := by
    intro type member
    cases Option.mem_def.mp member
    exact Ty.variablesBelow_constructor _ _
  have testProperties := inferExprFuel_inferenceProperties initProperties.2 formation canonical
    (fun type member => (boolClosed type member).weaken (Nat.zero_le _)) receipt.tested
  have testBelow := (inferExprFuel_occurrenceBoundExtends receipt.tested).nodesBelowNextOccurrence initializedBelow
  have bodyProperties := inferStatementsFuel_inferenceProperties
    (context := SourceInference.ForStatementInferenceContinuation.loopContext context)
    testProperties.2.1 formation canonical (expectedClosed.weaken (Nat.zero_le _)) receipt.bodyAccepted
  have bodyBelow := (inferStatementsFuel_occurrenceBoundExtends receipt.bodyAccepted).nodesBelowNextOccurrence testBelow
  have restored := State.restoreLexicalScope_inferenceProperties initProperties.2 (testProperties.1.trans bodyProperties.1)
  have postProperties := inferForItemsFuel_inferenceProperties
    (context := SourceInference.ForStatementInferenceContinuation.loopContext context)
    restored.2 formation canonical receipt.postAccepted
  have last := State.InferenceProgress.of_inference_eq postProperties.2.solved receipt.inference_eq
  have initExtension := Substitution.SemanticallyExtends.trans extension
    (restored.1.trans (postProperties.1.trans last)).substitution_extends
  have allRetained := headers_retained (roots := roots) receipt retained.nodes_prefix
  have initRetained : receipt.initialized.items.flatMap ForItemForm.initializedLetBinders ⊆
      (evidenceState.toTypedSource roots).initializedLetBinders := by
    intro binder member
    exact allRetained (List.mem_append_left _ member)
  have initializedActive := ActiveHeaderState.inferForItemsFuel
    (initial := initial.allocateStatementId.2) (show ActiveHeaderState initial.allocateStatementId.2
      (evidenceState.toTypedSource roots) from ⟨active.privateVars.congr rfl rfl,active.bound,
      active.backed.congr rfl rfl rfl,active.origins.congr_localBinders rfl⟩)
    resources ready.allocateStatementId wellFormed catalog formation canonical initRetained initExtension receipt.initialization
  have testActive : ActiveHeaderState receipt.testState (evidenceState.toTypedSource roots) := {
    privateVars := initializedActive.privateVars.inferExprFuel initProperties.2 initWellFormed
      initializedActive.bound catalog formation canonical boolClosed receipt.tested
    bound := activeQuantifiersBelowNext_inferExprFuel initializedActive.bound initProperties.2 formation canonical
      (fun type member => (boolClosed type member).weaken (Nat.zero_le _)) receipt.tested
    backed := initializedActive.backed.inferExprFuel initProperties.2 formation canonical
      (fun type member => (boolClosed type member).weaken (Nat.zero_le _)) receipt.tested
    origins := initializedActive.origins.inferExprFuel receipt.tested }
  have testWellFormed := (inferExprFuel_direct_progress receipt.tested).wellFormed initWellFormed
  have bodyNodes : receipt.bodyResult.state.nodes <+: evidenceState.nodes := by
    have beforePost := inferForItemsFuel_preserves_nodesPrefix receipt.postAccepted
      (List.prefix_refl _) bodyBelow (Nat.le_refl _)
    have postNodes : receipt.postResult.state.nodes <+: result.state.nodes := by
      rw [congrArg (fun result : StatementResult => result.state.nodes) receipt.completed]
      exact List.prefix_append _ _
    exact beforePost.trans (postNodes.trans retained.nodes_prefix)
  have bodySource : TypingSourceExtends (receipt.bodyResult.state.toTypedSource roots)
      (evidenceState.toTypedSource roots) := {
    owner_eq := retained.owner_eq.trans ((congrArg (fun result : StatementResult => result.state.owner)
      receipt.completed).trans (inferForItemsFuel_preserves_owner (state := receipt.bodyResult.state.restoreLexicalScope receipt.initialized.state.lexicalScope) receipt.postAccepted))
    nodes_prefix := bodyNodes }
  have bodyExtension := Substitution.SemanticallyExtends.trans extension
    (postProperties.1.trans last).substitution_extends
  have bodyActive := activeState_inferStatementsFuel (context := SourceInference.ForStatementInferenceContinuation.loopContext context) resources testProperties.2.1 testWellFormed testBelow
    catalog formation canonical expectedClosed testActive.privateVars testActive.bound testActive.backed
    testActive.origins bodySource bodyExtension receipt.bodyAccepted
  have savedSubset : receipt.initialized.state.localBinders ⊆ receipt.bodyResult.state.localBinders := by
    have testBinders : receipt.testState.localBinders = receipt.initialized.state.localBinders :=
      congrArg LexicalScope.binders (inferExprFuel_success_lexicalScope_eq receipt.tested)
    rw [← testBinders]
    exact inferStatementsFuel_binders_subset receipt.bodyAccepted
  refine ⟨initializedActive,{
    privateVars := bodyActive.1.restrict savedSubset rfl
    bound := activeQuantifiersBelowNext_transport initializedActive.bound rfl
      (testProperties.1.trans bodyProperties.1).next_le
    backed := initializedActive.backed.transport (List.Subset.refl _)
      ((inferExprFuel_requirements_subset receipt.tested).trans
        (inferStatementsFuel_requirements_subset receipt.bodyAccepted))
      (testProperties.1.trans bodyProperties.1).substitution_extends
    origins := initializedActive.origins.congr_localBinders rfl }⟩

end ForStatementInferenceContinuation.Receipt
end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
