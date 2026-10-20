import Solcore.SourceSemantics.SourceCompiledBodyCallIndex
import Solcore.SourceSemantics.SourceCompiledGeneralizedExpressionContracts
import Solcore.SourceSemantics.SourceInferenceActualCallInputTraversal

/-! The selected body's original initialization supplies ordinary inference
inputs at the root. Actual child-call provenance transports those inputs
through the same successful computation, for ordinary functions and methods. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledGeneralizedSoundness SourceInferenceExecution

namespace BodySelection
variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}

/-- Readiness and the return allocator bound belong to the actual checked
body. The initial requirement ledger and signature catalog are also derived
internally, without an executable profile or semantic body-typing premise. -/
theorem inferenceCall_inputs (selected : BodySelection compiled row fuel)
    (checked : checkProgram raw fuel = .ok compiled.program) :
    selected.inferenceCall.Inputs := by
  have progress := selected.inferenceProgress checked
  have scope := CheckingScope.refl selected
  exact {
    ready := progress.initialReady
    wellFormed := State.initial_requirementsWellFormed _ _ _
    catalog := ⟨scope.catalog checked, scope.formation checked, scope.functionsCanonical checked⟩
    bounds := progress.returnBelow }

/-- Every reached inference call receives the same root's actual state,
catalog and allocator prerequisites through the real child edges. -/
theorem actualCall_inputs (selected : BodySelection compiled row fuel)
    (checked : checkProgram raw fuel = .ok compiled.program)
    {call : CallIndex} (here : selected.InferenceCall call) :
    call.Inputs :=
  CallOccurrence.inputs (selected.inferenceCall_inputs checked) here

end BodySelection
end Solcore.SourceSemantics.SourceCompiledLocalFinalization
