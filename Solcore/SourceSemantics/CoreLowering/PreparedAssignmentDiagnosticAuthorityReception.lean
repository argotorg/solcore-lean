import Solcore.SourceSemantics.CoreLowering.PreparedAssignmentDiagnosticAuthority
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedReceivingPreparedShapeInterpretations
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicDecodedStagedCallFaults

/-! An exact original specialization supplies the full diagnostic inventory.
The actual public receiver supplies its rebuilt table and callable append;
no diagnostic interpretation is added as a caller premise. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.PreparedAssignmentDiagnosticAuthority
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleMixedRoute
open SourceCoreCompatibleDataPlaces ProtectedPlaceReachedDiagnostics
open CallableIndexedOwnedPublicFaultReceiverTables
universe u v

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {source : TypedSource}
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}

private theorem SourcePort.collected
    (port : SourcePort compiled source invalidProjection missingDefault) :
    (port.owner, source) ∈ compiled.indexed.base.plan.specializations.map
      (fun specialized => (specialized.key, specialized.function.typedBody)) := by
  suffices result : (port.owner, port.row.function.typedBody) ∈ compiled.indexed.base.plan.specializations.map
      (fun specialized => (specialized.key, specialized.function.typedBody)) by
    simpa only [port.sourceEq] using result
  have selected := port.record
  unfold SourceCompilationPlan.exactSpecialization at selected
  split at selected
  · cases selected
  · next actual found =>
    have same := Except.ok.inj selected
    subst actual
    have member : port.row ∈ compiled.indexed.base.plan.specializations.filter
        (fun specialized => decide (specialized.key = port.owner)) := by
      rw [found]; exact List.mem_singleton_self _
    have keyEq := of_decide_eq_true (List.mem_filter.mp member).2
    exact List.mem_map.mpr ⟨port.row, (List.mem_filter.mp member).1, by rw [keyEq]⟩
  · cases selected

/-- Same original source, same successful preparation, and the actual receiving
registry decode every reached missing/default and uninitialized-place fault. -/
private theorem SourcePort.ready_for
    (port : SourcePort compiled source invalidProjection missingDefault)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
      completion.result.extension completion.result.diagnostics)
    {ambient : AmbientDefinitions compiled.compatible.checked.catalog.definitions}
    (functions : FunctionModel compiled.compatible.checked.catalog ambient)
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    {faults : FunctionCalls.FaultRep}
    (included : ∀ reason token, CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
      completion.result.diagnostics (.semantic reason) token → faults reason token) :
    PreparedAssignmentReachedDiagnostics.Ready (values := .initial compiled.compatible.checked) functions protocol source invalidProjection missingDefault
      completion.result.context.registry faults := by
  intro context certificate scope administrative assignment operator rhs head site fuel origin signatures projected retained typed
    environment initialIndex initial
  obtain ⟨node, statement, sameSite, target⟩ :=
    CallableIndexedOwnedPublicPreparedShapeDiagnostics.owning_target origin
  subst site
  obtain ⟨root, sources, issued⟩ :=
    CallableIndexedOwnedPublicDiagnosticReceipts.compiled_diagnostics compiled port.present
  have collected := List.mem_append_left sources port.collected
  have receiverCopy := receiver
  obtain ⟨table, rebuilt, _tableEq⟩ := receiverCopy
  rw [port.present] at rebuilt
  cases retained with
  | bare empty => exact False.elim (projected empty)
  | projected route layout ordinary _shape described preparedBy =>
    have concrete := CompatiblePlaceConcretePreparation.describe_concrete
      (CallableIndexedOwnedPublicCatalogClosedSources.compiled_closed compiled) described
    have generated : prepare (.initial compiled.compatible.checked) fuel route
        (port.issuer.program.placeReason port.owner (.occurrence node.id.occurrence) assignment.target.root none)
        (fun raw => port.issuer.program.placeReason port.owner (.occurrence node.id.occurrence)
          assignment.target.root (some raw)) = .ok head.prepared := by
      have missingEq : missingDefault (.occurrence node.id.occurrence) assignment.target.root =
          (fun raw => port.issuer.program.placeReason port.owner (.occurrence node.id.occurrence)
            assignment.target.root (some raw)) := funext (port.missingToken _ _)
      simpa only [port.invalidToken, missingEq] using preparedBy
    apply ShapeErrors.projected (layout := layout) (ordinary := ordinary)
    · intro reachedIndex reason token reached related witness
      obtain ⟨type, placeTyped⟩ := CallableIndexedOwnedPlaceAdmission.assignment_target_typed typed
      have projections := CallableIndexedOwnedPublicPlaceReachedDiagnostics.projections_at_root placeTyped head.writable
      obtain ⟨binder, selected, description⟩ := CompatiblePlaceDescription.of_describe described
      have preparedRoute := (CompatibleMixedPreparation.of_prepare generated).1
      have sourceTyped : ∀ actualBinder, rootBinder source assignment.target.root = .ok actualBinder →
          SourceProjectionsHaveType source context actualBinder.scheme.body
            assignment.target.projections assignment.target.type := by
        intro actualBinder binding
        have binders := Except.ok.inj (binding.symm.trans description.binding)
        subst actualBinder
        simpa only [preparedRoute, description.rootSource] using projections
      obtain ⟨phaseIndex, phase, location, locationNative, cell, optional, rootValue, value, path,
        _relatedIn, _relatedOut, _scope, _canonical, _index, _worlds, _frame, _read, rootType, terminal⟩ := witness.terminal
      have rootView : SourceCoreRawMetadata.runtimeType cell.type =
          SourceCoreRawMetadata.runtimeType route.rootSourceType :=
        congrArg SourceCoreRawMetadata.runtimeType (rootType.trans (congrArg Route.rootSourceType preparedRoute))
      obtain ⟨rawValue, diagnostic, sameReason, decoded, error⟩ :=
        CompatiblePlaceMissingTerminalDiagnostics.terminal_diagnostic issued collected statement target concrete
          described generated port.unique signatures sourceTyped rootView rebuilt terminal
      apply included
      apply CallableIndexedOwnedPublicDecodedStagedCallFaults.of_semantic
      apply CallableIndexedOwnedPublicDecodedCallFaults.of_assignment
      apply CallableIndexedOwnedPublicDecodedAssignmentFaults.of_decoded
        (CallableIndexedOwnedReceivingPreparedShapeInterpretations.receiver_lookup compiled receiver port.present rebuilt decoded)
      rw [sameReason, error]
      exact .missing rawValue
    · intro reachedIndex location reached related witness
      have actual := CompatibleMixedPreparation.of_prepare generated
      have nonempty : route.steps ≠ [] := by
        intro empty
        have steps := actual.2.2
        rw [empty] at steps
        have only_nil : ∀ {outputs keys}, CompatibleMixedPreparation.Steps compiled.compatible.checked fuel
            (fun raw => port.issuer.program.placeReason port.owner (.occurrence node.id.occurrence)
              assignment.target.root (some raw)) [] 0 outputs keys → outputs = [] := by
          intro outputs keys path
          cases path
          rfl
        exact layout.nonempty (only_nil steps)
      obtain ⟨entry, member, kind, _first, reason⟩ :=
        CompatiblePlaceProjectionDiagnosticCoverage.prepare_coverage issued collected statement target concrete described nonempty
      obtain ⟨decoded, error⟩ := CompatiblePlaceProjectionDiagnosticPreparation.table_diagnostic issued member kind rebuilt
      have same : head.prepared.invalidProjection = entry.reason := actual.2.1.trans reason
      have received := CallableIndexedOwnedReceivingPreparedShapeInterpretations.receiver_lookup
        compiled receiver port.present rebuilt decoded
      apply included
      apply CallableIndexedOwnedPublicDecodedStagedCallFaults.of_semantic
      apply CallableIndexedOwnedPublicDecodedCallFaults.of_assignment
      apply CallableIndexedOwnedPublicDecodedAssignmentFaults.of_decoded (same.symm ▸ received)
      rw [error]
      exact .projectedUninitialized location

/-- The actual receiver closes both reached diagnostic phases. -/
theorem SourcePort.ready
    (port : SourcePort compiled source invalidProjection missingDefault)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
      completion.result.extension completion.result.diagnostics)
    {ambient : AmbientDefinitions compiled.compatible.checked.catalog.definitions}
    (functions : FunctionModel compiled.compatible.checked.catalog ambient)
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records) :
    PreparedAssignmentReachedDiagnostics.Ready (values := .initial compiled.compatible.checked)
      functions protocol source invalidProjection missingDefault completion.result.context.registry
      (fun reason token => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
        completion.result.diagnostics (.semantic reason) token) :=
  port.ready_for receiver functions protocol (fun _ _ fact => fact)

/-- Generic dynamic callers may include the genuine receiving decoder in
an existing semantic fault relation; the exact reached witnesses are retained. -/
theorem SourcePort.ready_included
    (port : SourcePort compiled source invalidProjection missingDefault)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
      completion.result.extension completion.result.diagnostics)
    {ambient : AmbientDefinitions compiled.compatible.checked.catalog.definitions}
    (functions : FunctionModel compiled.compatible.checked.catalog ambient)
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    {faults : FunctionCalls.FaultRep}
    (included : ∀ reason token, CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
      completion.result.diagnostics (.semantic reason) token → faults reason token) :
    PreparedAssignmentReachedDiagnostics.Ready (values := .initial compiled.compatible.checked) functions protocol source invalidProjection missingDefault
      completion.result.context.registry faults := by
  exact port.ready_for receiver functions protocol included

/-- Every retained source port is interpreted at the actual receiver. -/
theorem interprets
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
      completion.result.extension completion.result.diagnostics) :
    Interprets.{u, v} compiled completion.result.context.registry
      (fun reason token => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
        completion.result.diagnostics (.semantic reason) token) := by
  intro source invalidProjection missingDefault port ambient functions Records protocol
  exact port.ready receiver functions protocol

/-- Existing dynamic fault relations receive only real public decoder facts. -/
theorem interprets_included
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
      completion.result.extension completion.result.diagnostics)
    {faults : FunctionCalls.FaultRep}
    (included : ∀ reason token, CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
      completion.result.diagnostics (.semantic reason) token → faults reason token) :
    Interprets.{u, v} compiled completion.result.context.registry faults := by
  intro source invalidProjection missingDefault port ambient functions Records protocol
  exact port.ready_included receiver functions protocol included

end Solcore.SourceSemantics.CoreLowering.PreparedAssignmentDiagnosticAuthority
