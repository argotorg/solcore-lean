import Solcore.SourceSemantics.CoreLowering.PreparedLocalBindingOrigins
import Solcore.Frontend.SourceCoreUnifiedPreparationCertificates

/-! Actual compilation retains the source declaration of every native binding,
including bindings with no prepared instances. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationBindingOrigins
open Frontend SourceInference TypeSystem SourceCoreLocalPolymorphism
open PreparedLocalBindingOrigins

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β}
    {output : β} (accepted : action >>= next = .ok output) :
    ∃ intermediate, action = .ok intermediate ∧ next intermediate = .ok output := by
  cases action with
  | error => cases accepted
  | ok intermediate => exact ⟨intermediate, rfl, accepted⟩

private theorem mapError_ok {α ε δ : Type} {action : Except ε α} {change : ε → δ}
    {value : α} (accepted : action.mapError change = .ok value) : action = .ok value := by
  cases action with
  | error => cases accepted
  | ok result => cases accepted; rfl

theorem of_catalog {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {checked : SourceCoreCompatibleCatalog.Checked} {ownership : checked.signatures = program.signatures}
    {fuel : Nat} {base : SourceCoreCompatibleFunctions.Prepared checked}
    (accepted : SourceCoreCompatibleFunctions.prepareWithCatalog program plan checked ownership fuel = .ok base) :
    CatalogOrigins base.plan base.locals := by
  unfold SourceCoreCompatibleFunctions.prepareWithCatalog at accepted
  obtain ⟨executable, _, accepted⟩ := bind_ok accepted
  obtain ⟨locals, prepared, accepted⟩ := bind_ok accepted
  have origins := PreparedLocalBindingOrigins.of_preparation (mapError_ok prepared)
  change CatalogOrigins executable.val locals at origins
  obtain ⟨contexts, _, accepted⟩ := bind_ok accepted
  obtain ⟨functions, _, accepted⟩ := bind_ok accepted
  split at accepted
  · cases accepted
    exact origins
  · obtain ⟨diagnostics, _, accepted⟩ := bind_ok accepted
    split at accepted
    · obtain ⟨table, _, accepted⟩ := bind_ok accepted
      obtain ⟨callableDiagnostics, _, accepted⟩ := bind_ok accepted
      simp only [pure, Except.pure, bind, Except.bind] at accepted
      obtain ⟨assigned, decorated, accepted⟩ := bind_ok accepted
      have origins := PreparedLocalBindingOrigins.with_contracts origins (mapError_ok decorated)
      obtain ⟨closures, _, accepted⟩ := bind_ok accepted
      obtain ⟨sourceInputs, _, accepted⟩ := bind_ok accepted
      obtain ⟨entries, _, accepted⟩ := bind_ok accepted
      cases accepted
      exact origins
    · simp only [pure, Except.pure, bind, Except.bind] at accepted
      obtain ⟨closures, _, accepted⟩ := bind_ok accepted
      obtain ⟨sourceInputs, _, accepted⟩ := bind_ok accepted
      obtain ⟨entries, _, accepted⟩ := bind_ok accepted
      cases accepted
      exact origins

theorem of_automatic {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {fuel : Nat} {automatic : SourceCoreCompatibleFunctions.Automatic}
    (accepted : SourceCoreCompatibleFunctions.prepare program plan fuel = .ok automatic) :
    CatalogOrigins automatic.prepared.plan automatic.prepared.locals := by
  unfold SourceCoreCompatibleFunctions.prepare at accepted
  obtain ⟨executable, _, accepted⟩ := bind_ok accepted
  obtain ⟨locals, _, accepted⟩ := bind_ok accepted
  dsimp only at accepted
  split at accepted
  · cases accepted
  · obtain ⟨base, prepared, accepted⟩ := bind_ok accepted
    cases accepted
    exact of_catalog prepared

theorem of_compiled (compiled : SourceCoreUnifiedCompilation.Compiled) :
    CatalogOrigins compiled.indexed.base.plan compiled.indexed.base.locals := by
  have origins := of_automatic compiled.compatiblePrepared
  have same := SourceCoreUnifiedPreparationCertificates.indexed_base compiled.indexedPrepared
  rw [same]
  exact origins

/-- The selected binding is tied to an actual row and complete source collector entry. -/
theorem at_binding (compiled : SourceCoreUnifiedCompilation.Compiled)
    {caller : Key} {binder : Resolved.LocalId} {binding : Binding}
    (located : compiled.indexed.base.locals.binding caller binder = .ok binding) :
    BindingOrigin compiled.indexed.base.plan binding ∧
      binding.caller = caller ∧ binding.binder.id = binder :=
  PreparedLocalBindingOrigins.at_binding (of_compiled compiled) located

theorem statement_at_binding (compiled : SourceCoreUnifiedCompilation.Compiled)
    {caller : Key} {binder : Resolved.LocalId} {binding : Binding}
    (located : compiled.indexed.base.locals.binding caller binder = .ok binding) :
    ∃ statement, Node.statement statement ∈ binding.source.nodes ∧
      statement.form = .letDecl binding.binder (some binding.initializer) :=
  (at_binding compiled located).1.statement

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationBindingOrigins
