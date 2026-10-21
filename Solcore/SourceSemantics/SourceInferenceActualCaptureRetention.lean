import Solcore.SourceSemantics.SourceInferenceActualReturnedBindings

/-! The final body retains both recorded declarations and pending header items. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference

structure CallIndex.CaptureRetained (call : CallIndex) (whole : TypedSource) : Prop where
  nodes : (call.final.toTypedSource []).initializedLetBinders ⊆ whole.initializedLetBinders
  returned : ∀ binding ∈ call.returnedBindings, binding.binder ∈ whole.initializedLetBinders

end Solcore.SourceSemantics.SourceInferenceExecution
