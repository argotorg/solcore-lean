import Solcore.SourceSemantics.SourceInferenceActualCaptureEntries
import Solcore.SourceSemantics.SourceCompiledActualBinderRetention
import Solcore.SourceSemantics.SourceCompiledActualBodyInputs
import Solcore.SourceSemantics.SourceInferenceCaptureOrigins

/-! Capture origins at every reached inference entry come from the actual
root initialization and the same body's retained declaration inventory. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference SourceInferenceSoundness

theorem CallOccurrence.captureOrigins
    {root call : CallIndex} {whole : TypedSource}
    (here : CallOccurrence root call) (inputs : root.Inputs)
    (origins : ActiveBinderCaptureOrigins root.initial whole)
    (retained : ∀ {prior}, CallOccurrence root prior → prior.CaptureRetained whole) :
    ActiveBinderCaptureOrigins call.initial whole := by
  induction here with
  | root accepted => exact origins
  | child prior step ih =>
    exact step.captureOrigins (prior.inputs inputs) ih
      (fun next => retained (.child prior next))

end Solcore.SourceSemantics.SourceInferenceExecution

namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledGeneralizedSoundness SourceInferenceExecution
namespace BodySelection
variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}

theorem inferenceCall_captureOrigins (selected : BodySelection compiled row fuel) :
    ActiveBinderCaptureOrigins selected.inferenceCall.initial (evidenceSource selected) := by
  apply activeBinderCaptureOrigins_initial_mono
  intro entry member
  obtain ⟨parameter, _, rfl⟩ := List.mem_map.mp member
  rfl

theorem actualCall_captureOrigins (selected : BodySelection compiled row fuel)
    (checked : checkProgram raw fuel = .ok compiled.program)
    {call : CallIndex} (here : selected.InferenceCall call) :
    ActiveBinderCaptureOrigins call.initial (evidenceSource selected) :=
  here.captureOrigins (selected.inferenceCall_inputs checked) selected.inferenceCall_captureOrigins
    (fun prior => selected.actualCall_binders_retained prior)

end BodySelection
end Solcore.SourceSemantics.SourceCompiledLocalFinalization
