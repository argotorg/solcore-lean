import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalCapturedScopes

/-! A named invocation has the empty active substitution. Any saved lexical
context extending into it is itself empty, so its existing attachment applies. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalCapturedScopes
open Frontend TypeSystem
open GeneralizedLocalBundleContexts (ContextExtension)

private theorem lexical_empty {lexical : Substitution}
    (extension : ContextExtension lexical .empty) : lexical = .empty := by
  cases lexical with
  | nil => rfl
  | cons entry rest =>
    have impossible := extension.domain entry.1 (by simp [Substitution.domain])
    simp [Substitution.empty, Substitution.domain] at impossible

/-- The saved attachment already describes this same closure in the empty
context of a named invocation. -/
theorem Attachment.at_empty {function : Dynamic.GeneralizedClosure}
    {binding : SourceCoreLocalPolymorphism.Binding} {lexical : Substitution}
    (extension : ContextExtension lexical .empty)
    (saved : Attachment function binding lexical) :
    GeneralizedLocalReachedAllocation.Attachment function binding .empty := by
  have same := lexical_empty extension
  exact same ▸ saved.toAttachment

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalCapturedScopes
