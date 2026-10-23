import Solcore.Frontend.SourceCoreLocalEvidence

/-! A successful local-reference authenticator retains the exact binder
identity checked against its actual original node. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SourceAuthenticatedReferenceForm
open Frontend SourceInference SourceCoreLocalEvidence

private theorem bind_ok {α β ε : Type} {action : Except ε α}
    {next : α → Except ε β} {output : β} (accepted : action >>= next = .ok output) :
    ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

/-- The actual form guard identifies the same local binder even when the
reference is authenticated inside a contextual lambda. -/
theorem original_form
    {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {binding : Binding} {parent : Option Prepared} {id : ExpressionId}
    {reference : Reference}
    (accepted : authenticateReference program plan binding parent id = .ok reference) :
    ∃ name, reference.original.form = .reference name (.local binding.binder.id) := by
  unfold authenticateReference at accepted
  obtain ⟨caller, _caller, accepted⟩ := bind_ok accepted
  obtain ⟨⟨active, inherited⟩, _context, accepted⟩ := bind_ok accepted
  obtain ⟨validated, _validated, accepted⟩ := bind_ok accepted
  cases validated
  dsimp only at accepted
  split at accepted
  · next node found =>
    simp only [bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw] at accepted
    split at accepted
    · cases accepted
    · split at accepted
      · next name localId form =>
        split at accepted
        · cases accepted
        · next same =>
          split at accepted
          · next owned ownedEq =>
            obtain ⟨available, _available, accepted⟩ := bind_ok accepted
            obtain ⟨⟨child, witnesses⟩, _factory, accepted⟩ := bind_ok accepted
            obtain ⟨validated, _witnesses, accepted⟩ := bind_ok accepted
            cases validated
            cases accepted
            have sameBinder : localId = binding.binder.id := by
              by_cases equal : localId = binding.binder.id
              · exact equal
              · exact False.elim (same equal)
            exact ⟨name, by simpa only [sameBinder] using form⟩
          · cases accepted
      · cases accepted
  · cases accepted

end Solcore.SourceSemantics.CoreLowering.SourceAuthenticatedReferenceForm
