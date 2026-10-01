import Solcore.Frontend.SourceCoreUnifiedCompilation
import Solcore.Frontend.SourceCoreUnifiedRuntimeCertificates

/-! Actual preparation equations recover source and base ownership. The cached
artifact's native shape does not supply these equalities. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreUnifiedPreparationCertificates
open SourceInference
abbrev Plan := SourceSpecializationWorklist.Plan

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β}
    {value : β} (accepted : action >>= next = .ok value) :
    ∃ intermediate, action = .ok intermediate ∧ next intermediate = .ok value := by
  cases action with
  | error error => cases accepted
  | ok intermediate => exact ⟨intermediate, rfl, accepted⟩

theorem compatible_fields {source : CheckedProgram} {plan : Plan}
    {checked : SourceCoreCompatibleCatalog.Checked} {ownership : checked.signatures = source.signatures}
    {fuel : Nat} {base : SourceCoreCompatibleFunctions.Prepared checked}
    (prepared : SourceCoreCompatibleFunctions.prepareWithCatalog source plan checked ownership fuel = .ok base) :
    base.sourceProgram = source ∧ base.validationPlan = plan := by
  unfold SourceCoreCompatibleFunctions.prepareWithCatalog at prepared
  obtain ⟨executable, _, prepared⟩ := bind_ok prepared
  obtain ⟨locals, _, prepared⟩ := bind_ok prepared
  obtain ⟨contexts, _, prepared⟩ := bind_ok prepared
  obtain ⟨functions, _, prepared⟩ := bind_ok prepared
  split at prepared
  · cases prepared; exact ⟨rfl, rfl⟩
  · obtain ⟨diagnostics, _, prepared⟩ := bind_ok prepared
    split at prepared
    · obtain ⟨table, _, prepared⟩ := bind_ok prepared
      obtain ⟨callableDiagnostics, _, prepared⟩ := bind_ok prepared
      simp only [pure, Except.pure, bind, Except.bind] at prepared
      obtain ⟨locals, _, prepared⟩ := bind_ok prepared
      obtain ⟨closures, _, prepared⟩ := bind_ok prepared
      obtain ⟨sourceInputs, _, prepared⟩ := bind_ok prepared
      obtain ⟨entries, _, prepared⟩ := bind_ok prepared
      cases prepared; exact ⟨rfl, rfl⟩
    · simp only [pure, Except.pure, bind, Except.bind] at prepared
      obtain ⟨closures, _, prepared⟩ := bind_ok prepared
      obtain ⟨sourceInputs, _, prepared⟩ := bind_ok prepared
      obtain ⟨entries, _, prepared⟩ := bind_ok prepared
      cases prepared; exact ⟨rfl, rfl⟩

theorem automatic_fields {source : CheckedProgram} {plan : Plan} {fuel : Nat}
    {automatic : SourceCoreCompatibleFunctions.Automatic}
    (prepared : SourceCoreCompatibleFunctions.prepare source plan fuel = .ok automatic) :
    automatic.prepared.sourceProgram = source ∧ automatic.prepared.validationPlan = plan := by
  unfold SourceCoreCompatibleFunctions.prepare at prepared
  obtain ⟨executable, _, prepared⟩ := bind_ok prepared
  obtain ⟨locals, _, prepared⟩ := bind_ok prepared
  dsimp only at prepared
  split at prepared
  · cases prepared
  · obtain ⟨base, accepted, prepared⟩ := bind_ok prepared
    cases prepared
    exact compatible_fields accepted

theorem indexed_base {checked : SourceCoreCompatibleCatalog.Checked}
    {base : SourceCoreCompatibleFunctions.Prepared checked} {fuel : Nat}
    {program : SourceCoreCallableIndexedPrograms.Prepared checked}
    (prepared : SourceCoreCallableIndexedPrograms.prepare base fuel = .ok program) :
    program.base = base := by
  unfold SourceCoreCallableIndexedPrograms.prepare at prepared
  dsimp only at prepared
  split at prepared
  · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at prepared
  · simp only [pure, Except.pure, bind, Except.bind] at prepared
    split at prepared
    · simp [throw, throwThe, MonadExceptOf.throw] at prepared
    · split at prepared
      · simp [throw, throwThe, MonadExceptOf.throw] at prepared
      · obtain ⟨firstPass, _, prepared⟩ := bind_ok prepared
        split at prepared
        · simp [throw, throwThe, MonadExceptOf.throw] at prepared
        · split at prepared
          · simp [throw, throwThe, MonadExceptOf.throw] at prepared
          · obtain ⟨secondPass, _, prepared⟩ := bind_ok prepared
            obtain ⟨sourceInputs, _, prepared⟩ := bind_ok prepared
            obtain ⟨entries, _, prepared⟩ := bind_ok prepared
            cases prepared
            rfl

theorem compiled_fields (compiled : SourceCoreUnifiedCompilation.Compiled) :
    compiled.indexed.base.sourceProgram = compiled.sourceProgram ∧
      compiled.indexed.base.validationPlan = compiled.validationPlan := by
  rw [indexed_base compiled.indexedPrepared]
  exact automatic_fields compiled.compatiblePrepared

theorem compiled_planPrepared (compiled : SourceCoreUnifiedCompilation.Compiled) :
    SourceCompilationPlan.prepareExecutablePlanEvidence compiled.sourceProgram compiled.validationPlan =
      .ok compiled.indexed.base.plan := by
  have prepared := compiled.indexed.base.planPrepared
  obtain ⟨sourceExact, planExact⟩ := compiled_fields compiled
  rwa [sourceExact, planExact] at prepared

theorem compiled_validation (compiled : SourceCoreUnifiedCompilation.Compiled) :
    SourceCompilationPlan.validateExecutablePlanEvidence compiled.sourceProgram compiled.validationPlan = .ok () := by
  unfold SourceCompilationPlan.validateExecutablePlanEvidence
  rw [compiled_planPrepared compiled]
  rfl

theorem prepare_fields {source : CheckedProgram} {plan : Plan} {fuel : Nat}
    {compiled : SourceCoreUnifiedCompilation.Compiled}
    (prepared : SourceCoreUnifiedCompilation.prepare source plan fuel = .ok compiled) :
    compiled.sourceProgram = source ∧ compiled.validationPlan = plan ∧ compiled.compilationFuel = fuel := by
  unfold SourceCoreUnifiedCompilation.prepare at prepared
  dsimp only at prepared
  split at prepared
  · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at prepared
  · simp only [pure, Except.pure, bind, Except.bind] at prepared
    split at prepared
    · simp [throw, throwThe, MonadExceptOf.throw] at prepared
    · split at prepared
      · simp [throw, throwThe, MonadExceptOf.throw] at prepared
      · cases prepared
        exact ⟨rfl, rfl, rfl⟩

/-- The cached Core adapter's actual successful request has the original
artifact's public source inputs and result, rather than inferred ownership
from an equal native projection. This is a boundary certificate. -/
theorem run_done_specialization {compiled : SourceCoreUnifiedCompilation.Compiled}
    {key : SourceSpecialization.SpecializationKey} {arguments : List SourceTypedRuntime.Value}
    {validationFuel executionFuel : Nat} {initial : SourceTypedRuntime.RuntimeState}
    {result : SourceCoreUnifiedCompilation.Result compiled}
    {value : SourceTypedRuntime.Value} {final : SourceTypedRuntime.RuntimeState}
    (ran : compiled.run key arguments validationFuel executionFuel initial = .ok result)
    (done : result.observation = .done value final) :
    ∃ specialized, SourceCompilationPlan.exactSpecialization compiled.validationPlan key = .ok specialized ∧
      SourceTypedRuntime.PreparedDeepExecution compiled.sourceProgram compiled.validationPlan
        (specialized.function.typedBody.inputs.map (·.scheme.body)) specialized.function.inferredBodyType
        arguments initial value final := by
  obtain ⟨specialized, selected, certificate⟩ := SourceCoreUnifiedRuntime.run_done_specialization ran done
  obtain ⟨sourceExact, planExact⟩ := compiled_fields compiled
  rw [sourceExact, planExact] at certificate
  rw [planExact] at selected
  exact ⟨specialized, selected, certificate⟩

theorem run_resume_done_specialization {compiled : SourceCoreUnifiedCompilation.Compiled}
    {key : SourceSpecialization.SpecializationKey} {arguments : List SourceTypedRuntime.Value}
    {validationFuel executionFuel resumedFuel : Nat} {initial : SourceTypedRuntime.RuntimeState}
    {result resumed : SourceCoreUnifiedCompilation.Result compiled}
    {value : SourceTypedRuntime.Value} {final : SourceTypedRuntime.RuntimeState}
    (ran : compiled.run key arguments validationFuel executionFuel initial = .ok result)
    (continued : result.resume resumedFuel = .ok resumed)
    (done : resumed.observation = .done value final) :
    ∃ specialized, SourceCompilationPlan.exactSpecialization compiled.validationPlan key = .ok specialized ∧
      SourceTypedRuntime.PreparedDeepExecution compiled.sourceProgram compiled.validationPlan
        (specialized.function.typedBody.inputs.map (·.scheme.body)) specialized.function.inferredBodyType
        arguments initial value final := by
  obtain ⟨specialized, selected, certificate⟩ := SourceCoreUnifiedRuntime.Result.requested_done_specialization
    (SourceCoreUnifiedRuntime.Result.resume_requests (SourceCoreUnifiedRuntime.run_requests ran) continued) done
  obtain ⟨sourceExact, planExact⟩ := compiled_fields compiled
  rw [sourceExact, planExact] at certificate
  rw [planExact] at selected
  exact ⟨specialized, selected, certificate⟩

end Solcore.Frontend.SourceCoreUnifiedPreparationCertificates
