import Solcore.SourceSemantics.CoreLowering.GenericAssignmentPreparedOrigins
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicPlaceReachedDiagnostics
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicPlaceUninitializedDiagnostics
import Solcore.SourceSemantics.CoreLowering.ProtectedStateProjectedAssignmentHeads

/-! The same selected head retains its owning Source occurrence and actual
compiler preparation. Its real reached witnesses receive their public table
observations before the caller's explicit fault interpretation is applied. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicPreparedShapeDiagnostics
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleMixedRoute
open SourceCoreCompatibleDataPlaces ProtectedPlaceReachedDiagnostics
universe u v

/-- Both ordered For rows keep their genuine parent statement and site. -/
theorem owning_target {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
    {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    (origin : AssignmentDiagnosticOrigins.Occurs source site assignment operator rhs) :
    ∃ node, .statement node ∈ source.nodes ∧ site = .occurrence node.id.occurrence ∧
      assignment ∈ CompatiblePlaceMissingPreparationCoverage.targets node := by
  cases origin with
  | statement found form =>
    refine ⟨_, (lookupStatement?_sound found).1, ?_, ?_⟩
    · exact (congrArg (fun id : StatementId => SourceCoreElaboration.ErrorSite.occurrence id.occurrence)
        (lookupStatement?_sound found).2).symm
    · simp only [CompatiblePlaceMissingPreparationCoverage.targets, form, List.mem_singleton]
  | header found form member =>
    refine ⟨_, (lookupStatement?_sound found).1, ?_, ?_⟩
    · exact (congrArg (fun id : StatementId => SourceCoreElaboration.ErrorSite.occurrence id.occurrence)
        (lookupStatement?_sound found).2).symm
    · rw [CompatiblePlaceMissingPreparationCoverage.targets, form]
      exact List.mem_filterMap.mpr ⟨_, member, rfl⟩

/-- Missing errors use precise raw table observations. Uninitialized errors
also retain the actual reached witness and its location. These inclusions are
the caller's explicit interpretation of the two decoded errors. -/
structure ReachedTableInterpretation
    (checked : Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) {Records : Type v}
    (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (environment : Dynamic.Environment) (place : PlaceResolution) (prepared : Prepared)
    {initialIndex : ProtectedStateTransition.Index} (initial : protocol.State initialIndex)
    (table : SourceCoreFaultSites.Table) (faults : FunctionCalls.FaultRep) : Prop where
  missing : ∀ {rawValue token diagnostic}, table.diagnostic? token = some diagnostic →
    diagnostic.error = .typeMismatch rawValue none → faults (.missingMappingDefault rawValue) token
  uninitialized : ∀ {reachedIndex} (reached : protocol.State reachedIndex) {location},
    protocol.Relates initial reached →
    UninitializedWitness checked registry functions protocol environment place prepared initial reached location →
    ∀ {diagnostic}, table.diagnostic? prepared.invalidProjection = some diagnostic →
      diagnostic.error = .invalidPlaceProjection → faults (.uninitializedLocation location) prepared.invalidProjection

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
  {context : SourceSemantics.Context} {certificate : GenericExpressionMeaning.Certificate}
  {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {ambient : AmbientDefinitions compiled.compatible.checked.catalog.definitions}
  {functions : FunctionModel compiled.compatible.checked.catalog ambient}
  {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
  (head : GenericAssignmentStatements.Head (.initial compiled.compatible.checked) header.function.source
    context certificate scope administrative ambient.definitions assignment operator rhs)
  {registry : SourceCoreRawMetadata.Registry} {Records : Type v}
  {protocol : ProtectedStateTransition.Protocol.{u, v} Records}
  {environment : Dynamic.Environment} {initialIndex : ProtectedStateTransition.Index}
  (initial : protocol.State initialIndex) {table : SourceCoreFaultSites.Table} {faults : FunctionCalls.FaultRep}

/-- Each contract is proved at its own actual reached state. The retained shape
equality selects the same implicit site and layout as the selected head. -/
theorem shape_errors_at_header
    (receipt : CallableIndexedOwnedPublicPreparedTokenReadyNamedExpressionBounds.PublicReceipt header)
    {diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked)}
    (found : compiled.indexed.base.diagnostics = some diagnostics)
    (projected : assignment.target.projections ≠ [])
    {site : SourceCoreElaboration.ErrorSite}
    (origin : AssignmentDiagnosticOrigins.Occurs header.function.source site assignment operator rhs)
    {fuel : Nat}
    (retained : head.PreparedAt site fuel
      (receipt.original.prepared.diagnostics.placeReason header.named.signature.key site assignment.target.root none)
      (fun rawValue => receipt.original.prepared.diagnostics.placeReason header.named.signature.key
        site assignment.target.root (some rawValue)))
    (typed : SourceAssignmentHasType header.function.source context assignment operator rhs)
    (signatures : context.signatures = compiled.compatible.checked.signatures)
    {extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry}
    (rebuilt : diagnostics.tableForRegistry registry extension = .ok table)
    (interprets : ReachedTableInterpretation compiled.compatible.checked registry functions protocol
      environment assignment.target head.prepared initial table faults) :
    ShapeErrors (.initial compiled.compatible.checked) registry functions protocol header.function.source context
      certificate scope administrative environment assignment.target head.prepared operator head.invalid initial faults head.shape := by
  obtain ⟨node, statement, sameSite, target⟩ := owning_target origin
  subst site
  cases retained with
  | bare empty => exact False.elim (projected empty)
  | projected route layout ordinary shape described preparedBy =>
    rw [shape]
    apply ShapeErrors.projected (layout := layout) (ordinary := ordinary)
    · intro reachedIndex reason token reached related witness
      obtain ⟨rawValue, diagnostic, sameReason, decoded, error⟩ :=
        CallableIndexedOwnedPublicPlaceReachedDiagnostics.missing_at_header header receipt found statement target
          typed described preparedBy head.writable signatures rebuilt witness
      rw [sameReason]
      exact interprets.missing decoded error
    · intro reachedIndex location reached related witness
      obtain ⟨actualWitness, diagnostic, decoded, error⟩ :=
        CallableIndexedOwnedPublicPlaceUninitializedDiagnostics.uninitialized_at_header header receipt found
          statement target described preparedBy rebuilt witness
      exact interprets.uninitialized reached related actualWitness decoded error

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicPreparedShapeDiagnostics
