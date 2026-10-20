import Solcore.SourceSemantics.SourceInferenceActiveStatementPosition

/-! A completed actual statement list carries active scheme privacy and
quantifier bounds into the next restored branch or loop header. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail

theorem activeState_inferStatementsFuel
    {wholeContext : SourceInference.Context} {wholeReturn : Ty}
    {evidenceState : State} {roots : List NodeId} {finalized : SourceInference.Result}
    {fuel : Nat} {context : SourceInference.Context} {sources : List Syntax.Statement}
    {expected : Ty} {initial : State} {result : BlockResult}
    (resources : FinalInferenceResources wholeContext wholeReturn evidenceState roots finalized)
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (nodesBelow : initial.NodesBelowNextOccurrence)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (expectedClosed : expected.VariablesBelow 0)
    (privacy : ActiveQuantifiersPrivate initial)
    (bound : ActiveQuantifiersBelowNext initial)
    (backed : LiveTemplatesBacked initial)
    (origins : ActiveBinderCaptureOrigins initial (evidenceState.toTypedSource roots))
    (retained : TypingSourceExtends
      (result.state.toTypedSource roots) (evidenceState.toTypedSource roots))
    (extension : finalized.substitution.SemanticallyExtends result.state.inference.substitution)
    (accepted : inferStatementsFuel fuel context sources expected initial = .ok result) :
    ActiveQuantifiersPrivate result.state ∧ ActiveQuantifiersBelowNext result.state := by
  induction fuel generalizing sources initial result with
  | zero => simp [inferStatementsFuel] at accepted
  | succ fuel ih =>
    have expectedBelow := expectedClosed.weaken (Nat.zero_le initial.inference.next)
    cases sources with
    | nil =>
      simp [inferStatementsFuel] at accepted
      subst result
      exact ⟨privacy, bound⟩
    | cons head rest =>
      cases rest with
      | nil =>
        obtain ⟨statement, headRun, completed⟩ := inferStatementsFuel_success_singleton_facts accepted
        have same : result.state = statement.state := by
          simpa only using congrArg BlockResult.state completed
        rw [same] at retained extension ⊢
        exact ⟨privacy.inferStatementFuel resources ready wellFormed bound catalog formation canonical
          expectedClosed backed origins retained.nodes_prefix extension headRun,
          activeQuantifiersBelowNext_inferStatementFuel bound ready formation canonical expectedBelow headRun⟩
      | cons next tail =>
        obtain ⟨statement, remaining, headRun, tailRun, completed⟩ := inferStatementsFuel_success_cons_facts accepted
        have same : result.state = remaining.state := by
          simpa only using congrArg BlockResult.state completed
        rw [same] at retained extension ⊢
        have headProperties := inferStatementFuel_inferenceProperties ready formation canonical expectedBelow headRun
        have headWellFormed := (inferStatementFuel_direct_progress headRun).wellFormed wellFormed
        have headBelow := (inferStatementFuel_occurrenceBoundExtends headRun).nodesBelowNextOccurrence nodesBelow
        have tailProperties := inferStatementsFuel_inferenceProperties headProperties.2.1 formation canonical
          (expectedBelow.weaken headProperties.1.next_le) tailRun
        have headRetained :=
          (inferStatementsFuel_success_typingSourceExtends tailRun headBelow roots).trans retained
        have headExtension := Substitution.SemanticallyExtends.trans extension tailProperties.1.substitution_extends
        have headPrivacy := privacy.inferStatementFuel resources ready wellFormed bound catalog formation canonical
          expectedClosed backed origins headRetained.nodes_prefix headExtension headRun
        have headBound := activeQuantifiersBelowNext_inferStatementFuel bound ready formation canonical expectedBelow headRun
        exact ih headProperties.2.1 headWellFormed headBelow headPrivacy headBound
          (backed.inferStatementFuel ready formation canonical expectedBelow headRun)
          (inferStatementFuel_captureOrigins headRun origins headRetained) retained extension tailRun

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
