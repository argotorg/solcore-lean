import Solcore.SourceSemantics.SourceInferenceActualExpressionNodeShapes
import Solcore.SourceSemantics.SourceInferenceActualNonExpressionNodeShapes

/-! Existing node identities and syntax survive each actual suffix and the
composition from a child result to its accepted root result. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference

theorem ChildStep.nodeShapes {parent child : CallIndex}
    (step : ChildStep parent child) :
    NodeShapesPreserved child.final.nodes parent.final.nodes := by
  cases parent <;> first
  | exact step.expression_shapes
  | exact step.nonexpression_shapes (by trivial)

theorem CallOccurrence.finalNodeShapes {root call : CallIndex}
    (here : CallOccurrence root call) :
    NodeShapesPreserved call.final.nodes root.final.nodes := by
  induction here with
  | root _ => exact .refl _
  | child _ step ih => exact step.nodeShapes.trans ih

end Solcore.SourceSemantics.SourceInferenceExecution
