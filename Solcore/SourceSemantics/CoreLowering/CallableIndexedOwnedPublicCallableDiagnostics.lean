import Solcore.SourceSemantics.CoreLowering.CallableFaultDiagnosticPreparation
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedStageContracts

/-! The actual public compatible compiler retains the callable diagnostic
factory beside its cached codebook. These finite receipts recover its original
place table and allocator boundary; no stage or invocation law is assumed. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicCallableDiagnostics
open Core Frontend SourceInference

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β}
    {output : β} (accepted : (action >>= next) = .ok output) :
    ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem mapError_ok {α ε δ : Type} {action : Except ε α} {map : ε → δ}
    {output : α} (accepted : action.mapError map = .ok output) : action = .ok output := by
  cases action with
  | error => cases accepted
  | ok => cases accepted; rfl

/-- A genuine present callable context keeps the exact diagnostic preparation
and the same base place inventory in the sealed compatible result. -/
theorem of_catalog {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {checked : SourceCoreCompatibleCatalog.Checked} {ownership : checked.signatures = program.signatures}
    {fuel : Nat} {base : SourceCoreCompatibleFunctions.Prepared checked}
    {native : SourceCoreGeneralFunctions.CallableContext}
    (accepted : SourceCoreCompatibleFunctions.prepareWithCatalog program plan checked ownership fuel = .ok base)
    (present : base.callableContext = some native) :
    ∃ diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial checked),
      base.diagnostics = some diagnostics ∧ base.callableDiagnostics = some native.diagnostics ∧
      SourceCoreCallableFaultSites.prepare base.plan native.table diagnostics.program.rootTable diagnostics.nextReason =
        .ok native.diagnostics := by
  unfold SourceCoreCompatibleFunctions.prepareWithCatalog at accepted
  obtain ⟨executable, _, accepted⟩ := bind_ok accepted
  obtain ⟨locals, _, accepted⟩ := bind_ok accepted
  obtain ⟨contexts, _, accepted⟩ := bind_ok accepted
  obtain ⟨functions, _, accepted⟩ := bind_ok accepted
  split at accepted
  · cases accepted; cases present
  · obtain ⟨diagnostics, _, accepted⟩ := bind_ok accepted
    split at accepted
    · obtain ⟨table, _, accepted⟩ := bind_ok accepted
      obtain ⟨callableDiagnostics, issued, accepted⟩ := bind_ok accepted
      simp only [pure, Except.pure, bind, Except.bind] at accepted
      obtain ⟨locals, _, accepted⟩ := bind_ok accepted
      obtain ⟨closures, _, accepted⟩ := bind_ok accepted
      obtain ⟨sourceInputs, _, accepted⟩ := bind_ok accepted
      obtain ⟨entries, _, accepted⟩ := bind_ok accepted
      cases accepted
      cases Option.some.inj present
      exact ⟨diagnostics, rfl, rfl, mapError_ok issued⟩
    · simp only [pure, Except.pure, bind, Except.bind] at accepted
      obtain ⟨closures, _, accepted⟩ := bind_ok accepted
      obtain ⟨sourceInputs, _, accepted⟩ := bind_ok accepted
      obtain ⟨entries, _, accepted⟩ := bind_ok accepted
      cases accepted; cases present

theorem of_automatic {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {fuel : Nat} {automatic : SourceCoreCompatibleFunctions.Automatic}
    {native : SourceCoreGeneralFunctions.CallableContext}
    (accepted : SourceCoreCompatibleFunctions.prepare program plan fuel = .ok automatic)
    (present : automatic.prepared.callableContext = some native) :
    ∃ diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial automatic.checked),
      automatic.prepared.diagnostics = some diagnostics ∧ automatic.prepared.callableDiagnostics = some native.diagnostics ∧
      SourceCoreCallableFaultSites.prepare automatic.prepared.plan native.table diagnostics.program.rootTable diagnostics.nextReason =
        .ok native.diagnostics := by
  unfold SourceCoreCompatibleFunctions.prepare at accepted
  obtain ⟨executable, _, accepted⟩ := bind_ok accepted
  obtain ⟨locals, _, accepted⟩ := bind_ok accepted
  dsimp only at accepted
  split at accepted
  · cases accepted
  · obtain ⟨base, prepared, accepted⟩ := bind_ok accepted
    cases accepted
    exact of_catalog prepared present

/-- The public sealed preparation is the same actual diagnostic producer. -/
theorem of_compiled (compiled : SourceCoreUnifiedCompilation.Compiled)
    {native : SourceCoreGeneralFunctions.CallableContext}
    (present : compiled.indexed.base.callableContext = some native) :
    ∃ diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked),
      compiled.indexed.base.diagnostics = some diagnostics ∧
      compiled.indexed.base.callableDiagnostics = some native.diagnostics ∧
      SourceCoreCallableFaultSites.prepare compiled.indexed.base.plan native.table diagnostics.program.rootTable diagnostics.nextReason =
        .ok native.diagnostics := by
  have base := SourceCoreUnifiedPreparationCertificates.indexed_base compiled.indexedPrepared
  have own : compiled.compatible.prepared.callableContext = some native := by rwa [base] at present
  have accepted := of_automatic compiled.compatiblePrepared own
  rw [base]
  exact accepted

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicCallableDiagnostics
