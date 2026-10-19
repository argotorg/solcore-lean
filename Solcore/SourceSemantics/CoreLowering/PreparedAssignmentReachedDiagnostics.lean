import Solcore.SourceSemantics.CoreLowering.PreparedBranchingCatalogSites
import Solcore.SourceSemantics.CoreLowering.ProtectedStateProjectedAssignmentHeads
import Solcore.SourceSemantics.CoreLowering.ProjectedBitNotDiagnosticOrigins
import Solcore.SourceSemantics.CoreLowering.GenericProjectedBitNotPreparedOrigins

/-! Compiler origins and preparation equations are interpreted at the actual
receiving table and reached caller. This internal port is filled from the
public diagnostic authority before statement execution. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.PreparedAssignmentReachedDiagnostics
open Core Frontend SourceInference GeneralHeap CompatiblePayload
universe u v
variable {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
  (source : TypedSource)
  (invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word)
  (missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word)
  (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)

def AssignmentReady : Prop :=
  ∀ {context : SourceSemantics.Context} {certificate : GenericExpressionMeaning.Certificate}
    {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    (head : GenericAssignmentStatements.Head values source context certificate scope administrative ambient.definitions assignment operator rhs)
    {site : SourceCoreElaboration.ErrorSite} {fuel : Nat},
    AssignmentDiagnosticOrigins.Occurs source site assignment operator rhs →
    context.signatures = values.checked.signatures →
    assignment.target.projections ≠ [] →
    head.PreparedAt site fuel (invalidProjection site assignment.target.root)
      (missingDefault site assignment.target.root) →
    SourceAssignmentHasType source context assignment operator rhs →
    ∀ {environment : Dynamic.Environment} {initialIndex : ProtectedStateTransition.Index}
      (initial : protocol.State initialIndex),
    ProtectedPlaceReachedDiagnostics.ShapeErrors values registry functions protocol source context certificate
      scope administrative environment assignment.target head.prepared operator head.invalid initial faults head.shape

def UnaryReady : Prop :=
  ∀ {context : SourceSemantics.Context} {certificate : GenericExpressionMeaning.Certificate}
    {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {assignment : AssignmentResolution}
    (head : CompatibleProjectedBitNotStatements.Head values source context certificate scope administrative
      ambient.definitions assignment)
    {site : SourceCoreElaboration.ErrorSite} {fuel : Nat},
    ProjectedBitNotDiagnosticOrigins.Occurs source site assignment →
    context.signatures = values.checked.signatures →
    head.PreparedAt site fuel (invalidProjection site assignment.target.root)
      (missingDefault site assignment.target.root) →
    ∀ {type : TypeSystem.Ty}, SourcePlaceHasType source context assignment.target type →
    ∀ {environment : Dynamic.Environment} {initialIndex : ProtectedStateTransition.Index}
      (initial : protocol.State initialIndex),
    head.ReachedErrors functions protocol environment initial faults (registry := registry)

/-- Both operation families use the same genuine receiving authority. -/
structure Ready : Prop where
  assignment : AssignmentReady functions protocol source invalidProjection missingDefault registry faults
  unary : UnaryReady functions protocol source invalidProjection missingDefault registry faults

section Sites
variable {functions protocol source invalidProjection missingDefault registry faults}
  {context : SourceSemantics.Context} {certificate : GenericExpressionMeaning.Certificate}
  {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
  {head : GenericAssignmentStatements.Head values source context certificate scope administrative ambient.definitions assignment operator rhs}
  {catalogFaults : FunctionCalls.FaultRep}
  (site : PreparedBranchingCatalogSites.AssignmentSite invalidProjection missingDefault registry catalogFaults head)
  (semantic : ∀ reason token, catalogFaults reason token → faults reason token)

include site semantic in
theorem operands : AssignmentOperandDiagnostics.OperandsLaw faults operator head.invalid := by
  cases site with
  | existing errors => exact fun previous right invalid => semantic _ _ (errors.operands previous right invalid)
  | projected _ _ _ _ errors => exact fun previous right invalid => semantic _ _ (errors previous right invalid)

include site semantic in
theorem shape_errors
    (ready : Ready functions protocol source invalidProjection missingDefault registry faults)
    (typed : SourceAssignmentHasType source context assignment operator rhs)
    {environment : Dynamic.Environment} {initialIndex : ProtectedStateTransition.Index}
    (initial : protocol.State initialIndex) :
    ProtectedPlaceReachedDiagnostics.ShapeErrors values registry functions protocol source context certificate
      scope administrative environment assignment.target head.prepared operator head.invalid initial faults head.shape := by
  cases site with
  | existing errors =>
    apply ProtectedPlaceReachedDiagnostics.ShapeErrors.of_uniform
    exact ⟨fun fault => semantic _ _ (errors.missing fault),
      fun nonempty location => semantic _ _ (errors.uninitialized nonempty location),
      fun previous right invalid => semantic _ _ (errors.operands previous right invalid)⟩
  | projected origin signatures nonempty retained _ =>
    exact ready.assignment head origin signatures nonempty retained typed initial
end Sites

section UnarySites
variable {functions protocol source invalidProjection missingDefault registry faults}

/-- A genuine unary compiler site is interpreted by the same receiving table. -/
theorem unary_errors
    {context : SourceSemantics.Context} {certificate : GenericExpressionMeaning.Certificate}
    {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {assignment : AssignmentResolution}
    {head : CompatibleProjectedBitNotStatements.Head values source context certificate scope administrative
      ambient.definitions assignment}
    (site : PreparedBranchingCatalogSites.UnarySite invalidProjection missingDefault head)
    (ready : Ready functions protocol source invalidProjection missingDefault registry faults)
    {type : TypeSystem.Ty} (typed : SourcePlaceHasType source context assignment.target type)
    {environment : Dynamic.Environment} {initialIndex : ProtectedStateTransition.Index}
    (initial : protocol.State initialIndex) :
    head.ReachedErrors functions protocol environment initial faults (registry := registry) := by
  cases site with
  | projected origin signatures _ retained =>
    exact ready.unary head origin signatures retained typed initial

end UnarySites
end Solcore.SourceSemantics.CoreLowering.PreparedAssignmentReachedDiagnostics
