import Solcore.SourceSemantics.SourceInferenceActualExpressionProgress
import Solcore.SourceSemantics.SourceInferenceActualNonExpressionProgress

/-! Each actual child result reaches the final inference state of its root call.
This composes accepted child computations and never assumes final substitution
agreement for an intermediate state. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution

theorem ChildStep.suffixProgress {parent child : CallIndex}
    (inputs : parent.Inputs) (step : ChildStep parent child) :
    child.final.InferenceProgress parent.final := by
  cases parent <;> first
  | exact step.progress_expression inputs
  | exact step.progress_nonexpression inputs (by trivial)

theorem CallOccurrence.suffixProgress {root call : CallIndex}
    (here : CallOccurrence root call) (inputs : root.Inputs) :
    call.final.InferenceProgress root.final := by
  induction here with
  | root accepted => exact .refl ((inputs.progress accepted).2.1.solved)
  | child prior step ih => exact (step.suffixProgress (prior.inputs inputs)).trans ih

theorem CallOccurrence.final_extension {root call : CallIndex}
    (here : CallOccurrence root call) (inputs : root.Inputs) :
    root.final.inference.substitution.SemanticallyExtends call.final.inference.substitution :=
  (here.suffixProgress inputs).substitution_extends

end Solcore.SourceSemantics.SourceInferenceExecution
