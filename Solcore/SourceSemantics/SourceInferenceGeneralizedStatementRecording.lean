import Solcore.SourceSemantics.SourceInferenceGeneralizedActualStateInvariant

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend SourceInference TypeSystem ProtectedVariables

theorem GeneralizedActualStateInvariant.recordStatement
    {state : State} {source : TypedSource}
    (invariant : GeneralizedActualStateInvariant state source)
    (node : StatementNode)
    (noBindings : statementInitializedLetBindings node.form = []) :
    GeneralizedActualStateInvariant (state.recordNode (.statement node)) source := by
  obtain ⟨pending, ledger⟩ := invariant.ledger
  refine ⟨⟨pending, ledger.recordStatement_noBindings node noBindings⟩,
    invariant.origins.congr_localBinders rfl,
    activeQuantifiersBelowNext_transport invariant.quantifiersBelow rfl (Nat.le_refl _),
    ?_, invariant.backed.congr rfl rfl rfl⟩
  intro binder member
  exact (invariant.privacy binder member).transport rfl (.of_substitution_eq rfl)

/-- Restore only a genuine saved scope whose binders survive the actual child.
The origin witness belongs to that saved scope, while its privacy and ledger
come from the completed child. -/
theorem GeneralizedActualStateInvariant.restoreSaved
    {outer inner : State} {source : TypedSource}
    (invariant : GeneralizedActualStateInvariant inner source)
    (origins : ActiveBinderCaptureOrigins outer source)
    (saved : outer.localBinders ⊆ inner.localBinders) :
    GeneralizedActualStateInvariant (inner.restoreLexicalScope outer.lexicalScope) source := by
  obtain ⟨pending, ledger⟩ := invariant.ledger
  refine ⟨⟨pending, ledger.restoreLexicalScope _⟩, origins.restoreLexicalScope, ?_, ?_, ?_⟩
  · intro binder member
    exact invariant.quantifiersBelow binder (saved member)
  · intro binder member other present
    exact (invariant.privacy binder (saved member) other (saved present)).transport (.of_substitution_eq rfl)
  · intro binder member requirement present
    exact invariant.backed binder (saved member) requirement present

end Solcore.SourceSemantics.SourceInferenceSoundness
