import Solcore.SourceSemantics.CoreLowering.EmittedDiagnosticTokenPlan
import Solcore.SourceSemantics.CoreLowering.GenericAssignmentPreparedOrigins

/-! Static preparation facets belong to the same retained emitted plan. Each
assignment atom keeps its chosen head and actual owning site and preparation
parameters. No runtime state or fault interpretation is stored here. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.EmittedDiagnosticPreparedPlan
open Core Frontend SourceInference
open EmittedDiagnosticPlan
variable {tracked : Bool} {diagnosticPolicy : AssignmentDiagnosticPolicy} {source : TypedSource}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Syntax.ValueAssignOp → Word}
  {factory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy source invalidOperand}

/-- Every assignment retains its real selected preparation at its owning site. -/
def PreparedFor
    (invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word)
    (missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word) : Plan factory → Prop
  | .pure => True
  | .pair left right => PreparedFor invalidProjection missingDefault left ∧ PreparedFor invalidProjection missingDefault right
  | .assignment (assignment := assignment) head site _ _ _ _ _ =>
      ∃ fuel, head.PreparedAt site fuel (invalidProjection site assignment.target.root)
        (missingDefault site assignment.target.root)
  | .unary _ _ _ _ => True
  | .selected _ _ _ _ _ _ children =>
      ∀ request member childContext related, PreparedFor invalidProjection missingDefault (children request member childContext related)

/-- The original complete token extraction and plan stay together with their
static preparation facets. -/
structure Produced
    (factory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy source invalidOperand)
    (invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word)
    (invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word)
    (missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word)
    (α : Type) (diagnostics : α → SourceCoreRawMetadata.Registry → FunctionCalls.FaultRep → Prop) where
  original : EmittedDiagnosticTokenPlan.Produced factory invalidUnary α diagnostics
  prepared : PreparedFor invalidProjection missingDefault original.plan

end Solcore.SourceSemantics.CoreLowering.EmittedDiagnosticPreparedPlan
