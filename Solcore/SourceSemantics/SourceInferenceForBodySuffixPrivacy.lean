import Solcore.SourceSemantics.SourceInferenceForActiveStages

/-! Locals created by a loop body may be restored before post inference. The
actual saved initialized scope is retained in that body state. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail

namespace ForStatementInferenceContinuation.Receipt
variable {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {initializers post : List Syntax.ForItem} {condition : Syntax.Expr}
    {body : Syntax.Located (List Syntax.Statement)} {expected : Ty} {initial : State} {result : StatementResult}

theorem privacy_after_body
    (receipt : SourceInference.ForStatementInferenceContinuation.Receipt fuel context source initializers condition post body expected initial result)
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes))
    (expectedClosed : expected.VariablesBelow 0)
    {protectedVars : List TypeVarId}
    (bound : ∀ v ∈ protectedVars, v.index < receipt.bodyResult.state.inference.next)
    (live : LiveBindersSafe protectedVars receipt.bodyResult.state) :
    SafeTransport protectedVars receipt.bodyResult.state result.state ∧
      LiveBindersSafe protectedVars result.state ∧
      ∀ row ∈ result.state.requirements, row ∉ receipt.bodyResult.state.requirements →
        PredicateSafe protectedVars result.state row.predicate := by
  have initProperties := inferForItemsFuel_inferenceProperties ready.allocateStatementId formation canonical receipt.initialization
  have initWellFormed := (inferForItemsFuel_direct_progress receipt.initialization).wellFormed wellFormed
  have testProperties := inferExprFuel_inferenceProperties initProperties.2 formation canonical
    (by intro type member; cases Option.mem_def.mp member; exact Ty.variablesBelow_constructor _ _) receipt.tested
  have testWellFormed := (inferExprFuel_direct_progress receipt.tested).wellFormed initWellFormed
  have bodyProperties := inferStatementsFuel_inferenceProperties (context := SourceInference.ForStatementInferenceContinuation.loopContext context)
    testProperties.2.1 formation canonical (expectedClosed.weaken (Nat.zero_le _)) receipt.bodyAccepted
  have bodyWellFormed := (inferStatementsFuel_direct_progress receipt.bodyAccepted).wellFormed testWellFormed
  have restoredProperties := State.restoreLexicalScope_inferenceProperties initProperties.2
    (testProperties.1.trans bodyProperties.1)
  have savedSubset : receipt.initialized.state.localBinders ⊆ receipt.bodyResult.state.localBinders := by
    have testBinders : receipt.testState.localBinders = receipt.initialized.state.localBinders :=
      congrArg LexicalScope.binders (inferExprFuel_success_lexicalScope_eq receipt.tested)
    rw [← testBinders]
    exact inferStatementsFuel_binders_subset receipt.bodyAccepted
  have restoredLive : LiveBindersSafe protectedVars
      (receipt.bodyResult.state.restoreLexicalScope receipt.initialized.state.lexicalScope) :=
    live.restrict savedSubset rfl
  have postPrivacy := inferForItemsFuel_private protectedVars fuel
    (SourceInference.ForStatementInferenceContinuation.loopContext context) post
    (receipt.bodyResult.state.restoreLexicalScope receipt.initialized.state.lexicalScope)
    restoredProperties.2 bodyWellFormed bound restoredLive catalog formation canonical _ receipt.postAccepted
  have finalPrivacy := privacy_after_post receipt postPrivacy.2.1
  exact ⟨postPrivacy.1.trans finalPrivacy.1,finalPrivacy.2.1,
    new_requirements_trans postPrivacy.2.2 finalPrivacy.2.2 finalPrivacy.1⟩

end ForStatementInferenceContinuation.Receipt
end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
