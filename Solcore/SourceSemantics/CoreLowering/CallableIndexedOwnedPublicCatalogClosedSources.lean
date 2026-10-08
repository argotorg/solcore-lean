import Solcore.Frontend.SourceCoreUnifiedCompilation
import Solcore.SourceSemantics.CoreLowering.CompatibleCatalogClosedSources

/-! The accepted public compiler retains its actual compatible catalog factory.
The same selected catalog therefore has the Source closure invariant proved by
registration. Catalog ownership comes from the factory equation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicCatalogClosedSources
open Frontend SourceInference

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β}
    {output : β} (accepted : action >>= next = .ok output) :
    ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

/-- The real compatible factory selects this exact catalog from its actual
prepared Source type and metadata inventory. -/
theorem automatic_catalog {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {fuel : Nat} {limits : SourceCoreRawMetadata.Limits}
    {automatic : SourceCoreCompatibleFunctions.Automatic}
    (accepted : SourceCoreCompatibleFunctions.prepare program plan fuel limits = .ok automatic) :
    ∃ types metadata, SourceCoreCompatibleCatalog.prepare program.signatures fuel types metadata limits true =
      .ok automatic.checked := by
  unfold SourceCoreCompatibleFunctions.prepare at accepted
  obtain ⟨executable, _executableMade, accepted⟩ := bind_ok accepted
  obtain ⟨locals, _localsMade, accepted⟩ := bind_ok accepted
  dsimp only at accepted
  split at accepted
  · cases accepted
  · obtain ⟨base, _baseMade, accepted⟩ := bind_ok accepted
    cases accepted
    exact ⟨_, _, by assumption⟩

/-- The sealed public compilation keeps its exact successful catalog factory;
no equality of projected native definitions is used to recover ownership. -/
theorem compiled_catalog (compiled : SourceCoreUnifiedCompilation.Compiled) :
    ∃ types metadata, SourceCoreCompatibleCatalog.prepare compiled.sourceProgram.signatures
      compiled.compilationFuel types metadata {} true = .ok compiled.compatible.checked :=
  automatic_catalog compiled.compatiblePrepared

/-- Actual public preparation proves closure of the selected catalog entries. -/
theorem compiled_closed (compiled : SourceCoreUnifiedCompilation.Compiled) :
    CompatibleCatalogRegistrationPrefix.ClosedSources compiled.compatible.checked.catalog := by
  obtain ⟨types, metadata, accepted⟩ := compiled_catalog compiled
  exact CompatibleCatalogClosedSources.prepare_closed accepted

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicCatalogClosedSources
