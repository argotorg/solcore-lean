import Solcore.SourceSemantics.SourceInferenceActualBinderContinuation
import Solcore.SourceSemantics.SourceCompiledBodyCallIndex
import Solcore.SourceSemantics.SourceCompiledGeneralizedExpressionContracts

/-! Each actual inference call retains its complete initialized binder
metadata in the selected body's evidence source, including loop headers. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceExecution
open SourceCompiledGeneralizedSoundness

namespace BodySelection
variable {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}

theorem actualCall_binders_retained (selected : BodySelection compiled row fuel)
    {call : CallIndex} (here : selected.InferenceCall call) :
    call.CaptureRetained (evidenceSource selected) := by
  have retained := here.initialized_binders
  have rootInventory :
      selected.inferenceCall.initializedBinders = (evidenceSource selected).initializedLetBinders := by
    simp only [CallIndex.initializedBinders, inferenceCall, CallIndex.final,
      CallIndex.returnedBindings, List.map_nil, List.append_nil, evidenceSource,
      TypedSource.initializedLetBinders, State.toTypedSource, selected.body.returned_nodes]
  rw [rootInventory] at retained
  constructor
  · intro binder present
    exact retained (List.mem_append_left _ present)
  · intro binding present
    exact retained (List.mem_append_right _ (List.mem_map.mpr ⟨binding, present, rfl⟩))

end BodySelection
end Solcore.SourceSemantics.SourceCompiledLocalFinalization
