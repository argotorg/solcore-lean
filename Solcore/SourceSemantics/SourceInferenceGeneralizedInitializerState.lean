import Solcore.SourceSemantics.SourceInferenceGeneralizedActualStateInvariant

/-! The actual initialized declaration does not inspect its enclosing return
type. Its state transition therefore supports generalized lambda bodies too. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend SourceInference TypeSystem ProtectedVariables

/-- Reconstruct the exact executed declaration for any enclosing return type.
Both annotation branches reuse the same child and completed result. -/
theorem initializedReceipt_accepted
    {fuel : Nat} {context : SourceInference.Context} {statement : Syntax.Statement}
    {initial : State} {result : Detail.StatementResult}
    (receipt : LocalLetRequirementTiming.Receipt fuel context statement initial result)
    (expectedReturn : Ty) :
    Detail.inferStatementFuel (fuel + 1) context statement expectedReturn initial = .ok result := by
  rcases receipt with ⟨name, initializer, annotation, expected, annotationAccepted,
    form, value, ready, child, completed⟩
  cases annotationAccepted with
  | none =>
    simp [Detail.inferStatementFuel, form, child, completed,
      LocalLetRequirementTiming.finish, bind, Except.bind, pure, Pure.pure, Except.pure]
    rfl
  | some annotationAccepted =>
    simp [Detail.inferStatementFuel, form, annotationAccepted, child, completed,
      LocalLetRequirementTiming.finish, bind, Except.bind, pure, Pure.pure, Except.pure]
    rfl

/-- This exact initializer preserves the generalized operational state without
a restriction on the enclosing function or lambda's expected return type. -/
theorem GeneralizedActualStateInvariant.ofInitializer
    {wholeContext : SourceInference.Context} {wholeReturn : Ty}
    {evidenceState : State} {roots : List NodeId} {finalized : SourceInference.Result}
    {fuel : Nat} {context : SourceInference.Context} {statement : Syntax.Statement}
    {initial : State} {result : Detail.StatementResult}
    (invariant : GeneralizedActualStateInvariant initial (evidenceState.toTypedSource roots))
    (receipt : LocalLetRequirementTiming.Receipt fuel context statement initial result)
    (resources : FinalInferenceResources wholeContext wholeReturn evidenceState roots finalized)
    (ready : initial.InferenceReady)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (retained : result.state.nodes <+: evidenceState.nodes)
    (sourceExtension : TypingSourceExtends
      (result.state.toTypedSource roots) (evidenceState.toTypedSource roots))
    (extension : finalized.substitution.SemanticallyExtends result.state.inference.substitution) :
    GeneralizedActualStateInvariant result.state (evidenceState.toTypedSource roots) := by
  exact invariant.ofStatement resources ready catalog formation canonical
    (show Ty.unit.VariablesBelow 0 from by simp [Ty.VariablesBelow, Ty.unit, Ty.freeVariables])
    retained sourceExtension extension (initializedReceipt_accepted receipt .unit)

end Solcore.SourceSemantics.SourceInferenceSoundness
