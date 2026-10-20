import Solcore.Frontend.SourceCoreUnifiedPreparationCertificates

/-! Indexed compilation requires the actual callable context. Its successful
preparation also supplies callable contracts and the real diagnostic program.
These facts do not depend on a restricted body profile. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedRuntimeFacts
open Frontend SourceInference

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β}
    {output : β} (accepted : action >>= next = .ok output) :
    ∃ intermediate, action = .ok intermediate ∧ next intermediate = .ok output := by
  cases action with
  | error error => cases accepted
  | ok intermediate => exact ⟨intermediate, rfl, accepted⟩

theorem of_catalog {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {checked : SourceCoreCompatibleCatalog.Checked} {ownership : checked.signatures = program.signatures}
    {fuel : Nat} {base : SourceCoreCompatibleFunctions.Prepared checked}
    {native : SourceCoreGeneralFunctions.CallableContext}
    (accepted : SourceCoreCompatibleFunctions.prepareWithCatalog program plan checked ownership fuel = .ok base)
    (present : base.callableContext = some native) :
    checked.catalog.callableContracts = true ∧ ∃ diagnostics, base.diagnostics = some diagnostics := by
  unfold SourceCoreCompatibleFunctions.prepareWithCatalog at accepted
  obtain ⟨executable, _, accepted⟩ := bind_ok accepted
  obtain ⟨locals, _, accepted⟩ := bind_ok accepted
  obtain ⟨contexts, _, accepted⟩ := bind_ok accepted
  obtain ⟨functions, _, accepted⟩ := bind_ok accepted
  split at accepted
  · cases accepted; cases present
  · obtain ⟨diagnostics, _, accepted⟩ := bind_ok accepted
    split at accepted
    · rename_i enabled
      obtain ⟨table, _, accepted⟩ := bind_ok accepted
      obtain ⟨callableDiagnostics, _, accepted⟩ := bind_ok accepted
      simp only [pure, Except.pure, bind, Except.bind] at accepted
      obtain ⟨locals, _, accepted⟩ := bind_ok accepted
      obtain ⟨closures, _, accepted⟩ := bind_ok accepted
      obtain ⟨sourceInputs, _, accepted⟩ := bind_ok accepted
      obtain ⟨entries, _, accepted⟩ := bind_ok accepted
      cases accepted
      exact ⟨enabled, diagnostics, rfl⟩
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
    automatic.checked.catalog.callableContracts = true ∧
      ∃ diagnostics, automatic.prepared.diagnostics = some diagnostics := by
  unfold SourceCoreCompatibleFunctions.prepare at accepted
  obtain ⟨executable, _, accepted⟩ := bind_ok accepted
  obtain ⟨locals, _, accepted⟩ := bind_ok accepted
  dsimp only at accepted
  split at accepted
  · cases accepted
  · obtain ⟨base, prepared, accepted⟩ := bind_ok accepted
    cases accepted
    exact of_catalog prepared present

/-- The indexed artifact itself retains the callable context that rules out
empty-root and disabled-contract preparation branches. -/
theorem of_compiled (compiled : SourceCoreUnifiedCompilation.Compiled) :
    compiled.compatible.checked.catalog.callableContracts = true ∧
      ∃ diagnostics, compiled.indexed.base.diagnostics = some diagnostics := by
  have same := SourceCoreUnifiedPreparationCertificates.indexed_base compiled.indexedPrepared
  have present := (congrArg (fun base => base.callableContext) same).symm.trans
    compiled.indexed.ancestry.graph.inputs.callableSelected
  have actual := of_automatic compiled.compatiblePrepared present
  rw [same]
  exact actual

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedRuntimeFacts
