import Solcore.SourceSemantics.CoreLowering.AssignmentDiagnosticOrigins
import Solcore.SourceSemantics.CoreLowering.CompatibleBitNotStatementHead
import Solcore.SourceSemantics.CoreLowering.GenericMatchScopedContexts

/-! Diagnostic plans retain the genuine local heads and scoped child indices
selected by the original static compiler traversals. Their requirements contain
only pure leaves, concrete local residuals and actual child combinations. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.EmittedDiagnosticPlan
open Core Frontend SourceInference

variable {source : TypedSource} {tracked : Bool} {diagnosticPolicy : AssignmentDiagnosticPolicy}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Syntax.ValueAssignOp → Word}
  (factory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy source invalidOperand)

inductive Plan (factory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy source invalidOperand) : Type where
  | pure : Plan factory
  | pair (left right : Plan factory) : Plan factory
  | assignment {values : SourceCoreCompatibleValues.Context} {context : SourceSemantics.Context}
      {certificate : GenericExpressionMeaning.Certificate} {scope : SourceCoreLocalCell.Scope}
      {administrative : Core.Context} {definitions : DataEnvironment}
      {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
      (head : GenericAssignmentStatements.Head values source context certificate scope administrative definitions assignment operator rhs)
      (site : SourceCoreElaboration.ErrorSite)
      (origin : AssignmentDiagnosticOrigins.OccursFor tracked source site assignment operator rhs)
      (same : head.invalid = invalidOperand site assignment.target.root operator)
      (sourceTyped : ∀ binder, SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder →
        SourceProjectionsHaveType source context binder.scheme.body assignment.target.projections assignment.target.type)
      (rightTyped : ExpressionHasType source context rhs assignment.target.type)
      (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
        SourceCoreRawMetadata.runtimeType assignment.target.type = .integer) : Plan factory
  | unary {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {assignment : AssignmentResolution}
      (head : CompatibleBitNotStatements.Head context scope assignment)
      (writable : ∀ binder, SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder →
        WritableLocal context assignment.target.root binder.scheme.body)
      (bare : assignment.target.projections = [])
      (profile : SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
        SourceCoreRawMetadata.runtimeType assignment.target.type = .integer) : Plan factory
  | selected (requests : List GenericMatchChildren.Request) (parent : SourceSemantics.Context)
      (hiddenIds : List Resolved.LocalId) (scrutineeType : TypeSystem.Ty)
      (cases : List TypedMatchCase) (fallback : Option (List StatementId))
      (children : ∀ request, request ∈ requests → ∀ childContext,
        GenericMatchChildren.ScopedContextFor source parent hiddenIds scrutineeType cases fallback request childContext → Plan factory) : Plan factory

namespace Plan
variable {factory}
/-- The exact emitted predicate is visible through the concrete diagnostic plan. -/
def requirements : Plan factory → SourceCoreRawMetadata.Registry → FunctionCalls.FaultRep → Prop
  | .pure, _, _ => True
  | .pair left right, registry, faults => requirements left registry faults ∧ requirements right registry faults
  | .assignment head _ _ _ _ _ _, registry, faults => factory.residual head registry faults
  | .unary head _ _ _, _, faults => head.Errors faults
  | .selected _ _ _ _ _ _ children, registry, faults =>
    ∀ request member childContext related, requirements (children request member childContext related) registry faults

/-- Local diagnostic receipts concern the exact generated heads and their
original Source typing. They contain no expression or body execution law. -/
structure LocalReceipts (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) : Prop where
  assignment : ∀ {values context certificate scope administrative definitions assignment operator rhs}
    (head : GenericAssignmentStatements.Head values source context certificate scope administrative definitions assignment operator rhs)
    (site : SourceCoreElaboration.ErrorSite)
    (_origin : AssignmentDiagnosticOrigins.OccursFor tracked source site assignment operator rhs)
    (_same : head.invalid = invalidOperand site assignment.target.root operator)
    (_sourceTyped : ∀ binder, SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder →
      SourceProjectionsHaveType source context binder.scheme.body assignment.target.projections assignment.target.type)
    (_rightTyped : ExpressionHasType source context rhs assignment.target.type)
    (_profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
      SourceCoreRawMetadata.runtimeType assignment.target.type = .integer), factory.residual head registry faults
  unary : ∀ {context scope assignment} (head : CompatibleBitNotStatements.Head context scope assignment)
    (_writable : ∀ binder, SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder →
      WritableLocal context assignment.target.root binder.scheme.body)
    (_bare : assignment.target.projections = [])
    (_profile : SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
      SourceCoreRawMetadata.runtimeType assignment.target.type = .integer), head.Errors faults

/-- This finite static interpreter follows only the retained diagnostic plan. -/
theorem interpret {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (receipts : LocalReceipts (factory := factory) registry faults) : (plan : Plan factory) → requirements plan registry faults
  | .pure => True.intro
  | .pair left right => ⟨interpret receipts left, interpret receipts right⟩
  | .assignment head site origin same sourceTyped rightTyped profile =>
      receipts.assignment head site origin same sourceTyped rightTyped profile
  | .unary head writable bare profile => receipts.unary head writable bare profile
  | .selected _ _ _ _ _ _ children => fun request member childContext related =>
      interpret receipts (children request member childContext related)
end Plan

/-- The original extraction and its exact emitted diagnostic equation travel
as one witness. The code, Tree and materialization remain original. -/
structure Produced (α : Type) (diagnostics : α → SourceCoreRawMetadata.Registry → FunctionCalls.FaultRep → Prop) where
  original : α
  plan : Plan factory
  equation : ∀ registry faults, diagnostics original registry faults = plan.requirements registry faults

namespace Produced
variable {factory} {α : Type} {diagnostics : α → SourceCoreRawMetadata.Registry → FunctionCalls.FaultRep → Prop}
theorem interpreted (produced : Produced factory α diagnostics) {registry : SourceCoreRawMetadata.Registry}
    {faults : FunctionCalls.FaultRep} (receipts : Plan.LocalReceipts (factory := factory) registry faults) :
    diagnostics produced.original registry faults :=
  (produced.equation registry faults).symm ▸ produced.plan.interpret receipts
end Produced
end Solcore.SourceSemantics.CoreLowering.EmittedDiagnosticPlan
