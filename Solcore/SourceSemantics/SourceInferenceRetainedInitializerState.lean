import Solcore.SourceSemantics.SourceInferenceGeneralizedInitializerState

/-! An initialized binder needs its own final source origin. Unrelated
expression nodes may change during later coercion selection. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend SourceInference TypeSystem ProtectedVariables

/-- Finalizer privacy uses the retained allocated binder and the actual older
template rows. It does not require a prefix of the whole node table. -/
theorem initializedBinder_privacy
    {wholeContext : SourceInference.Context} {wholeReturn : Ty}
    {evidenceState : State} {roots : List NodeId} {finalized : SourceInference.Result}
    (resources : FinalInferenceResources wholeContext wholeReturn evidenceState roots finalized)
    {fuel : Nat} {context : SourceInference.Context} {statement : Syntax.Statement}
    {initial : State} {result : Detail.StatementResult}
    (receipt : LocalLetRequirementTiming.Receipt fuel context statement initial result)
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (backed : LiveTemplatesBacked initial)
    (origins : ActiveBinderCaptureOrigins initial (evidenceState.toTypedSource roots))
    (retained : receipt.binding.1 ∈ (evidenceState.toTypedSource roots).initializedLetBinders)
    (extension : finalized.substitution.SemanticallyExtends result.state.inference.substitution) :
    LiveBindersSafe receipt.binding.1.scheme.quantified result.state := by
  have readyOrigins := origins.congr_localBinders receipt.ready_binders
  have templates := ProtectedVariables.LocalLetRequirementTiming.Receipt.templates_before
    receipt backed ready wellFormed formation canonical
  have readyExtension : finalized.substitution.SemanticallyExtends receipt.ready.inference.substitution := by
    rwa [receipt.inference_eq] at extension
  have live := allocate_generalized_live_from_finalizer resources initial.nextRequirement
    (receipt.ready.resolve receipt.value.type) receipt.name.value (some receipt.name.span) false
    (readyOrigins.withLocals receipt.locals) readyExtension templates retained
  exact live.transport
    (congrArg (fun result : Detail.StatementResult => result.state.localBinders) receipt.completed)
    (.of_substitution_eq
      (congrArg (fun result : Detail.StatementResult => result.state.inference.substitution) receipt.completed))

/-- The exact initialized binder's retained source origin suffices to carry
all generalized operational fields through its real completed statement. -/
theorem GeneralizedActualStateInvariant.ofRetainedInitializer
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
    (retained : receipt.binding.1 ∈ (evidenceState.toTypedSource roots).initializedLetBinders)
    (extension : finalized.substitution.SemanticallyExtends result.state.inference.substitution) :
    GeneralizedActualStateInvariant result.state (evidenceState.toTypedSource roots) := by
  obtain ⟨pending, ledger⟩ := invariant.ledger
  have accepted := initializedReceipt_accepted receipt .unit
  have closed : Ty.unit.VariablesBelow 0 := by
    simp [Ty.VariablesBelow, Ty.unit, Ty.freeVariables]
  have readyOrigins := invariant.origins.congr_localBinders receipt.ready_binders
  have allocatedOrigins : ActiveBinderCaptureOrigins receipt.binding.2 (evidenceState.toTypedSource roots) :=
    (readyOrigins.withLocals receipt.locals).allocateBinder rfl (.inr retained)
  refine ⟨⟨pending, (actualLedgerFamily (fuel + 1)).statements.statement accepted ledger⟩,
    allocatedOrigins.congr_localBinders
      (congrArg (fun result : Detail.StatementResult => result.state.localBinders) receipt.completed),
    activeQuantifiersBelowNext_inferStatementFuel invariant.quantifiersBelow ready formation canonical
      (closed.weaken (Nat.zero_le _)) accepted,
    ?_, invariant.backed.inferStatementFuel ready formation canonical (closed.weaken (Nat.zero_le _)) accepted⟩
  intro binder member
  rw [receipt.result_binders] at member
  rcases List.mem_cons.mp member with rfl | entering
  · exact initializedBinder_privacy resources receipt ready ledger.requirements formation canonical
      invariant.backed invariant.origins retained extension
  · exact (inferStatementFuel_private binder.scheme.quantified (fuel + 1) context statement .unit initial
      ready ledger.requirements (invariant.quantifiersBelow binder entering)
      (invariant.privacy binder entering) catalog formation canonical
      (closed.weaken (Nat.zero_le _)) (safe_closed _ _ closed) result accepted).2.2.1

end Solcore.SourceSemantics.SourceInferenceSoundness
