import Solcore.SourceSemantics.SourceInferenceActiveQuantifierPrivacy
import Solcore.SourceSemantics.SourceInferenceActiveQuantifierOrigins

/-! Every active binder's private variables are preserved through real statement
inference. Newly generalized binders obtain privacy from their exact receipt. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail

theorem ActiveQuantifiersPrivate.inferStatementFuel
    {wholeContext : SourceInference.Context} {wholeReturn : Ty}
    {evidenceState : State} {roots : List NodeId} {finalized : SourceInference.Result}
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {expected : Ty} {initial : State} {result : StatementResult}
    (privateVars : ActiveQuantifiersPrivate initial)
    (resources : FinalInferenceResources wholeContext wholeReturn evidenceState roots finalized)
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (bound : ActiveQuantifiersBelowNext initial)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes))
    (expectedClosed : expected.VariablesBelow 0)
    (backed : LiveTemplatesBacked initial)
    (origins : ActiveBinderCaptureOrigins initial (evidenceState.toTypedSource roots))
    (retained : result.state.nodes <+: evidenceState.nodes)
    (extension : finalized.substitution.SemanticallyExtends result.state.inference.substitution)
    (accepted : inferStatementFuel fuel context source expected initial = .ok result) :
    ActiveQuantifiersPrivate result.state := by
  intro binder member
  rcases inferStatementFuel_quantified_origin accepted binder member with old | empty | created
  · have actual := inferStatementFuel_private binder.scheme.quantified fuel context source expected initial
      ready wellFormed (bound binder old) (privateVars binder old) catalog formation canonical
      (expectedClosed.weaken (Nat.zero_le _)) (safe_closed _ _ expectedClosed) result accepted
    exact actual.2.2.1
  · rw [empty]
    exact liveBindersSafe_nil _
  · obtain ⟨childFuel,receipt,rfl⟩ := created
    exact LocalLetRequirementTiming.Receipt.active_privacy resources receipt ready wellFormed formation
      canonical backed origins retained extension

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
