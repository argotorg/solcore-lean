import Solcore.SourceSemantics.SourceInferenceActualCallProperties
import Solcore.SourceSemantics.SourceInferenceAssignedValueActualPrefix

/-! The operator fit exposes its actual state and expected-type bounds. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail

def assignmentFit (operator : Syntax.ValueAssignOp) (state : State) (type : Ty) : Except Error State :=
  match operator with | .equal => pure state | _ => Detail.unify state type .word

theorem assignmentFit_properties
    {operator : Syntax.ValueAssignOp} {state fitted : State} {type : Ty}
    (ready : state.InferenceReady) (below : type.VariablesBelow state.inference.next)
    (accepted : assignmentFit operator state type =
      (Except.ok fitted : Except Error State)) :
    state.InferenceProgress fitted ∧ fitted.InferenceReady ∧
    (assignmentExpected operator fitted type).VariablesBelow fitted.inference.next := by
  cases operator <;> simp only [assignmentFit] at accepted ⊢
  all_goals first
  | (change Except.ok state = Except.ok fitted at accepted
     cases Except.ok.inj accepted
     exact ⟨.refl ready.solved, ready, ready.solved.variablesBelow_apply below⟩)
  | (have progress := unify_inferenceProgress ready.solved below (Ty.variablesBelow_constructor _ _) accepted
     exact ⟨progress, unify_preserves_inferenceReady ready below (Ty.variablesBelow_constructor _ _) accepted,
       Ty.variablesBelow_constructor _ _⟩)

end Solcore.SourceSemantics.SourceInferenceExecution
