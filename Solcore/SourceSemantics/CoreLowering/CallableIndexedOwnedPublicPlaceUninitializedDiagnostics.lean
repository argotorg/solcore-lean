import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceProjectionDiagnosticCoverage
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicPlaceMissingDiagnostics
import Solcore.SourceSemantics.CoreLowering.ProtectedPlaceReachedDiagnostics

/-! An actual uninitialized root at a projected target uses the fixed row
emitted for that same accepted description. The public inventory and original
reached witness retain their full states and location. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicPlaceUninitializedDiagnostics
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleMixedRoute
open SourceCoreCompatibleDataPlaces ProtectedPlaceReachedDiagnostics
universe u v
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))

/-- The actual public receipt keeps all place reasons through the callable
root-table replacement. -/
theorem place_reason
    (receipt : CallableIndexedOwnedPublicPreparedTokenReadyNamedExpressionBounds.PublicReceipt header)
    {diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked)}
    (found : compiled.indexed.base.diagnostics = some diagnostics)
    (owner : SourceSpecialization.SpecializationKey) (site : SourceCoreElaboration.ErrorSite)
    (binder : Resolved.LocalId) :
    receipt.original.prepared.diagnostics.placeReason owner site binder none =
      diagnostics.program.placeReason owner site binder none := by
  obtain ⟨actual, actualFound, lowered⟩ := receipt.diagnostic.actual
  have same := Option.some.inj (found.symm.trans actualFound)
  subst actual
  rw [lowered]
  cases compiled.indexed.base.callableContext <;> rfl

/-- The same actual projected root witness receives its own fixed diagnostic.
The location and every reached state remain in the original witness. -/
theorem uninitialized_at_header
    (receipt : CallableIndexedOwnedPublicPreparedTokenReadyNamedExpressionBounds.PublicReceipt header)
    {diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked)}
    (found : compiled.indexed.base.diagnostics = some diagnostics)
    {node : StatementNode} (statement : .statement node ∈ header.function.source.nodes)
    {assignment : AssignmentResolution}
    (target : assignment ∈ CompatiblePlaceMissingPreparationCoverage.targets node)
    {route : Route}
    (described : describe (.initial compiled.compatible.checked) compiled.compatible.checked.signatures
      header.function.source (.occurrence node.id.occurrence) assignment = .ok route)
    {fuel : Nat} {prepared : Prepared}
    (generated : prepare (.initial compiled.compatible.checked) fuel route
      (receipt.original.prepared.diagnostics.placeReason header.named.signature.key
        (.occurrence node.id.occurrence) assignment.target.root none)
      (fun valueType => receipt.original.prepared.diagnostics.placeReason header.named.signature.key
        (.occurrence node.id.occurrence) assignment.target.root (some valueType)) = .ok prepared)
    {registry : SourceCoreRawMetadata.Registry}
    {extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry}
    {table : SourceCoreFaultSites.Table} (rebuilt : diagnostics.tableForRegistry registry extension = .ok table)
    {ambient : AmbientDefinitions compiled.compatible.checked.catalog.definitions}
    {functions : FunctionModel compiled.compatible.checked.catalog ambient} {Records : Type v}
    {protocol : ProtectedStateTransition.Protocol.{u, v} Records}
    {initialIndex reachedIndex : ProtectedStateTransition.Index}
    {initial : protocol.State initialIndex} {reached : protocol.State reachedIndex}
    {environment : Dynamic.Environment} {location : Dynamic.Location}
    (witness : UninitializedWitness compiled.compatible.checked registry functions protocol environment
      assignment.target prepared initial reached location) :
    UninitializedWitness compiled.compatible.checked registry functions protocol environment
      assignment.target prepared initial reached location ∧
    ∃ diagnostic, table.diagnostic? prepared.invalidProjection = some diagnostic ∧
      diagnostic.error = .invalidPlaceProjection := by
  have actual := CompatibleMixedPreparation.of_prepare generated
  have projected : prepared.steps ≠ [] := by
    obtain ⟨_phaseIndex, _phase, _target, _cell, _optional, _sources, _resolved,
      _in, _out, _scope, _canonical, _index, _world, _frame, _lookup, _read,
      _reference, _storeRead, _cellRep, _cellType, _empty, _notMapping, nonempty, _values, _resolvedNonempty⟩ := witness
    exact nonempty
  have nonempty : route.steps ≠ [] := by
    intro empty
    have steps := actual.2.2
    rw [empty] at steps
    have only_nil : ∀ {outputs keys}, CompatibleMixedPreparation.Steps compiled.compatible.checked fuel
        (fun valueType => receipt.original.prepared.diagnostics.placeReason header.named.signature.key
          (.occurrence node.id.occurrence) assignment.target.root (some valueType)) [] 0 outputs keys → outputs = [] := by
      intro outputs keys path
      cases path
      rfl
    exact projected (only_nil steps)
  obtain ⟨root, sources, issued, collected⟩ :=
    CallableIndexedOwnedPublicPlaceMissingDiagnostics.inventory_at_header header found
  have concrete := CompatiblePlaceConcretePreparation.describe_concrete
    (CallableIndexedOwnedPublicCatalogClosedSources.compiled_closed compiled) described
  obtain ⟨entry, member, kind, _first, reason⟩ :=
    CompatiblePlaceProjectionDiagnosticCoverage.prepare_coverage issued collected statement target concrete described nonempty
  obtain ⟨decoded, error⟩ := CompatiblePlaceProjectionDiagnosticPreparation.table_diagnostic issued member kind rebuilt
  have same : prepared.invalidProjection = entry.reason :=
    actual.2.1.trans ((place_reason header receipt found _ _ _).trans reason)
  exact ⟨witness, entry.diagnostic, by simpa only [same] using decoded, error⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicPlaceUninitializedDiagnostics
