import Solcore.SourceSemantics.CoreLowering.PreparedLocalInstanceMetadata
import Solcore.Frontend.SourceCoreUnifiedPreparationCertificates

/-! The actual public compilation retains the successful preparation needed to
authenticate contextual local lambdas. An arbitrary indexed artifact does not
by itself retain this preparation equation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationLocalMetadata
open Frontend SourceInference TypeSystem SourceCoreLocalPolymorphism
open PreparedLocalInstanceMetadata

def projection (checked : SourceCoreCompatibleCatalog.Checked) (type : Ty) :
    Except SourceCoreLocalPolymorphism.Error Core.Ty :=
  (checked.project type).map (·.type) |>.mapError fun
    | .catalog error => .projection error
    | .metadata _ => .projection (.unsupportedType type)

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
    CatalogMetadata (projection checked) base.locals := by
  unfold SourceCoreCompatibleFunctions.prepareWithCatalog at accepted
  obtain ⟨executable, _, accepted⟩ := bind_ok accepted
  obtain ⟨locals, prepared, accepted⟩ := bind_ok accepted
  have metadata := PreparedLocalInstanceMetadata.of_preparation (mapError_ok prepared)
  change CatalogMetadata (projection checked) locals at metadata
  obtain ⟨contexts, _, accepted⟩ := bind_ok accepted
  obtain ⟨functions, _, accepted⟩ := bind_ok accepted
  split at accepted
  · cases accepted
    exact metadata
  · obtain ⟨diagnostics, _, accepted⟩ := bind_ok accepted
    split at accepted
    · obtain ⟨table, _, accepted⟩ := bind_ok accepted
      obtain ⟨callableDiagnostics, _, accepted⟩ := bind_ok accepted
      simp only [pure, Except.pure, bind, Except.bind] at accepted
      obtain ⟨assigned, decorated, accepted⟩ := bind_ok accepted
      have metadata := PreparedLocalInstanceMetadata.with_contracts metadata (mapError_ok decorated)
      obtain ⟨closures, _, accepted⟩ := bind_ok accepted
      obtain ⟨sourceInputs, _, accepted⟩ := bind_ok accepted
      obtain ⟨entries, _, accepted⟩ := bind_ok accepted
      cases accepted
      exact metadata
    · simp only [pure, Except.pure, bind, Except.bind] at accepted
      obtain ⟨closures, _, accepted⟩ := bind_ok accepted
      obtain ⟨sourceInputs, _, accepted⟩ := bind_ok accepted
      obtain ⟨entries, _, accepted⟩ := bind_ok accepted
      cases accepted
      exact metadata

theorem of_automatic {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {fuel : Nat} {automatic : SourceCoreCompatibleFunctions.Automatic}
    (accepted : SourceCoreCompatibleFunctions.prepare program plan fuel = .ok automatic) :
    CatalogMetadata (projection automatic.checked) automatic.prepared.locals := by
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
    CatalogMetadata (projection compiled.compatible.checked) compiled.indexed.base.locals := by
  have metadata := of_automatic compiled.compatiblePrepared
  have same := SourceCoreUnifiedPreparationCertificates.indexed_base compiled.indexedPrepared
  rw [same]
  exact metadata

/-- The actual compiler, exact binding lookup and lexical context provide the
candidate metadata. No independent whole-catalog property is required. -/
theorem at_context (compiled : SourceCoreUnifiedCompilation.Compiled)
    {caller : Key} {binder : Resolved.LocalId} {binding : Binding}
    {active : Substitution} {candidate : Instance}
    (located : compiled.indexed.base.locals.binding caller binder = .ok binding)
    (member : candidate ∈ binding.atContext active) :
    candidate.origin.caller = caller ∧ candidate.origin.binder.id = binder ∧
      Metadata (projection compiled.compatible.checked) candidate :=
  PreparedLocalInstanceMetadata.at_context (of_compiled compiled) located member

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationLocalMetadata
