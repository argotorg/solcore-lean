import Solcore.SourceSemantics.SourceInferenceActiveStatementPrivacy
import Solcore.SourceSemantics.SourceInferenceActualLedgerSoundness
import Solcore.SourceSemantics.SourceInferenceCaptureOriginDispatcher

/-! Operational state for generalized recursive checking. Privacy and actual
template rows replace the restriction to monomorphic source binders. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend SourceInference TypeSystem ProtectedVariables

structure GeneralizedActualStateInvariant (state : State) (evidenceSource : TypedSource) : Prop where
  ledger : ∃ pending, RecursiveLedgerInvariant state pending
  origins : ActiveBinderCaptureOrigins state evidenceSource
  quantifiersBelow : ActiveQuantifiersBelowNext state
  privacy : ActiveQuantifiersPrivate state
  backed : LiveTemplatesBacked state

namespace GeneralizedActualStateInvariant

theorem requirements {state : State} {source : TypedSource}
    (invariant : GeneralizedActualStateInvariant state source) :
    state.RequirementsWellFormed := by
  obtain ⟨_, ledger⟩ := invariant.ledger
  exact ledger.requirements

theorem initial (owner : Resolved.DeclarationId) (locals : Environment)
    (comptime : List Bool) (evidenceSource : TypedSource)
    (monomorphic : ∀ entry ∈ locals, entry.2.quantified = []) :
    GeneralizedActualStateInvariant (State.initial owner locals comptime) evidenceSource :=
  ⟨⟨[], RecursiveLedgerInvariant.initial owner locals comptime⟩,
    activeBinderCaptureOrigins_initial_mono owner locals comptime evidenceSource monomorphic,
    activeQuantifiersBelowNext_initial_mono owner locals comptime monomorphic,
    ActiveQuantifiersPrivate.initial owner locals comptime monomorphic,
    LiveTemplatesBacked.initial owner locals comptime⟩

private theorem privacy_congr {before after : State}
    (privacy : ActiveQuantifiersPrivate before)
    (binders : after.localBinders = before.localBinders)
    (substitution : after.inference.substitution = before.inference.substitution) :
    ActiveQuantifiersPrivate after := by
  intro binder member
  exact (privacy binder (binders ▸ member)).transport binders
    (.of_substitution_eq substitution)

theorem allocateStatementId {state : State} {source : TypedSource}
    (invariant : GeneralizedActualStateInvariant state source) :
    GeneralizedActualStateInvariant state.allocateStatementId.2 source := by
  obtain ⟨pending, ledger⟩ := invariant.ledger
  exact ⟨⟨pending, ledger.allocateStatementId⟩,
    invariant.origins.congr_localBinders rfl,
    activeQuantifiersBelowNext_transport invariant.quantifiersBelow rfl (Nat.le_refl _),
    privacy_congr invariant.privacy rfl rfl, invariant.backed.congr rfl rfl rfl⟩

theorem allocateExpressionId {state : State} {source : TypedSource}
    (invariant : GeneralizedActualStateInvariant state source) :
    GeneralizedActualStateInvariant state.allocateExpressionId.2 source := by
  obtain ⟨pending, ledger⟩ := invariant.ledger
  exact ⟨⟨pending, ledger.allocateExpressionId⟩,
    invariant.origins.congr_localBinders rfl,
    activeQuantifiersBelowNext_transport invariant.quantifiersBelow rfl (Nat.le_refl _),
    privacy_congr invariant.privacy rfl rfl, invariant.backed.congr rfl rfl rfl⟩

theorem fresh {state : State} {source : TypedSource}
    (invariant : GeneralizedActualStateInvariant state source) :
    GeneralizedActualStateInvariant state.fresh.2 source := by
  obtain ⟨pending, ledger⟩ := invariant.ledger
  exact ⟨⟨pending, ledger.fresh⟩, invariant.origins.congr_localBinders rfl,
    activeQuantifiersBelowNext_transport invariant.quantifiersBelow rfl (Nat.le_succ _),
    privacy_congr invariant.privacy rfl rfl, invariant.backed.congr rfl rfl rfl⟩

theorem withLocals {state : State} {source : TypedSource}
    (invariant : GeneralizedActualStateInvariant state source) (locals : Environment) :
    GeneralizedActualStateInvariant (state.withLocals locals) source := by
  obtain ⟨pending, ledger⟩ := invariant.ledger
  exact ⟨⟨pending, ⟨ledger.requirements,
    ⟨ledger.templates.classified, ledger.templates.unique, ledger.templates.covered⟩⟩⟩,
    invariant.origins.congr_localBinders rfl,
    activeQuantifiersBelowNext_transport invariant.quantifiersBelow rfl (Nat.le_refl _),
    privacy_congr invariant.privacy rfl rfl, invariant.backed.congr rfl rfl rfl⟩

/-- The actual expression call preserves every active scheme. Its optional
expected type must avoid those existing scheme quantifiers at child entry. -/
theorem ofExpression
    {fuel : Nat} {context : SourceInference.Context} {expression : Syntax.Expr}
    {expected : Option Ty} {initial final : State} {value : InferredExpression}
    {source : TypedSource}
    (invariant : GeneralizedActualStateInvariant initial source)
    (ready : initial.InferenceReady)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow initial.inference.next)
    (expectedSafe : ∀ binder ∈ initial.localBinders, ∀ type ∈ expected,
      Safe binder.scheme.quantified initial type)
    (accepted : Detail.inferExprFuel fuel context expression expected initial = .ok (value, final)) :
    GeneralizedActualStateInvariant final source := by
  obtain ⟨pending, ledger⟩ := invariant.ledger
  have properties := Detail.inferExprFuel_inferenceProperties ready formation canonical expectedBelow accepted
  have binders := congrArg LexicalScope.binders (Detail.inferExprFuel_success_lexicalScope_eq accepted)
  change final.localBinders = initial.localBinders at binders
  refine ⟨⟨pending, (actualLedgerFamily fuel).expression accepted ledger⟩,
    invariant.origins.inferExprFuel accepted,
    activeQuantifiersBelowNext_transport invariant.quantifiersBelow binders properties.1.next_le,
    ?_, invariant.backed.inferExprFuel ready formation canonical expectedBelow accepted⟩
  intro binder member
  have entering : binder ∈ initial.localBinders := binders ▸ member
  exact (inferExprFuel_private binder.scheme.quantified fuel context expression expected initial
    ready ledger.requirements (invariant.quantifiersBelow binder entering)
    (invariant.privacy binder entering) catalog formation canonical expectedBelow
    (expectedSafe binder entering) _ accepted).2.2.1

/-- At an original function statement, the actual finalizer provides the
capture checks needed for newly generalized binders. The original return type
is closed; lambda return metavariables need a separate continuation. -/
theorem ofStatement
    {wholeContext : SourceInference.Context} {wholeReturn : Ty}
    {evidenceState : State} {roots : List NodeId} {finalized : SourceInference.Result}
    {fuel : Nat} {context : SourceInference.Context} {statement : Syntax.Statement}
    {expected : Ty} {initial : State} {result : Detail.StatementResult}
    (invariant : GeneralizedActualStateInvariant initial (evidenceState.toTypedSource roots))
    (resources : FinalInferenceResources wholeContext wholeReturn evidenceState roots finalized)
    (ready : initial.InferenceReady)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (expectedClosed : expected.VariablesBelow 0)
    (retained : result.state.nodes <+: evidenceState.nodes)
    (sourceExtension : TypingSourceExtends
      (result.state.toTypedSource roots) (evidenceState.toTypedSource roots))
    (extension : finalized.substitution.SemanticallyExtends result.state.inference.substitution)
    (accepted : Detail.inferStatementFuel fuel context statement expected initial = .ok result) :
    GeneralizedActualStateInvariant result.state (evidenceState.toTypedSource roots) := by
  obtain ⟨pending, ledger⟩ := invariant.ledger
  have expectedBelow := expectedClosed.weaken (Nat.zero_le initial.inference.next)
  exact ⟨⟨pending, (actualLedgerFamily fuel).statements.statement accepted ledger⟩,
    inferStatementFuel_captureOrigins accepted invariant.origins sourceExtension,
    activeQuantifiersBelowNext_inferStatementFuel invariant.quantifiersBelow ready
      formation canonical expectedBelow accepted,
    invariant.privacy.inferStatementFuel resources ready ledger.requirements invariant.quantifiersBelow
      catalog formation canonical expectedClosed invariant.backed invariant.origins retained extension accepted,
    invariant.backed.inferStatementFuel ready formation canonical expectedBelow accepted⟩

end GeneralizedActualStateInvariant
end Solcore.SourceSemantics.SourceInferenceSoundness
