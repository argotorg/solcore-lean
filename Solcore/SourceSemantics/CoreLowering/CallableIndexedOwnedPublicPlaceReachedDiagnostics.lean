import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicPlaceMissingDiagnostics
import Solcore.SourceSemantics.CoreLowering.ProtectedPlaceMissingTerminalReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPlaceAdmission

/-! Genuine Source assignment typing and the actual writable root identify
the same raw projection row. The real reached missing phase then supplies its
own prepared terminal to the public diagnostic inventory and table. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicPlaceReachedDiagnostics
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleMixedRoute
open SourceCoreCompatibleDataPlaces ProtectedPlaceReachedDiagnostics
universe u v

/-- Two real first-match writable receipts identify the same raw root type.
The original Source place judgment supplies its ordered projection typing. -/
theorem projections_at_root {source : TypedSource} {context : SourceSemantics.Context}
    {place : PlaceResolution} {root type : TypeSystem.Ty}
    (typed : SourcePlaceHasType source context place type)
    (writable : WritableLocal context place.root root) :
    SourceProjectionsHaveType source context root place.projections place.type := by
  cases typed with
  | intro originalWritable projections stored =>
    obtain ⟨originalScheme, originalLookup, _, _, originalBody⟩ := originalWritable.scheme
    obtain ⟨scheme, lookup, _, _, body⟩ := writable.scheme
    have schemes := Option.some.inj
      ((Resolved.LocalScope.lookup?_iff.mpr originalLookup).symm.trans
        (Resolved.LocalScope.lookup?_iff.mpr lookup))
    have roots := originalBody.symm.trans ((congrArg TypeSystem.Scheme.body schemes).trans body)
    rw [stored]
    exact roots ▸ projections

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))

/-- This decoder consumes the actual retained phase and prepared compiler
equations. It preserves the same witness, raw metadata token and rebuilt table. -/
theorem missing_at_header
    (receipt : CallableIndexedOwnedPublicPreparedTokenReadyNamedExpressionBounds.PublicReceipt header)
    {diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked)}
    (found : compiled.indexed.base.diagnostics = some diagnostics)
    {node : StatementNode} (statement : .statement node ∈ header.function.source.nodes)
    {assignment : AssignmentResolution}
    (target : assignment ∈ CompatiblePlaceMissingPreparationCoverage.targets node)
    {operator : Syntax.ValueAssignOp} {rhs : ExpressionId} {context : SourceSemantics.Context}
    (typed : SourceAssignmentHasType header.function.source context assignment operator rhs)
    {route : Route}
    (described : describe (.initial compiled.compatible.checked) compiled.compatible.checked.signatures
      header.function.source (.occurrence node.id.occurrence) assignment = .ok route)
    {fuel : Nat} {invalid : Word} {prepared : Prepared}
    (generated : prepare (.initial compiled.compatible.checked) fuel route invalid
      (fun valueType => receipt.original.prepared.diagnostics.placeReason header.named.signature.key
        (.occurrence node.id.occurrence) assignment.target.root (some valueType)) = .ok prepared)
    (writable : WritableLocal context assignment.target.root prepared.route.rootSourceType)
    (signatures : context.signatures = compiled.compatible.checked.signatures)
    {registry : SourceCoreRawMetadata.Registry}
    {extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry}
    {table : SourceCoreFaultSites.Table} (rebuilt : diagnostics.tableForRegistry registry extension = .ok table)
    {ambient : AmbientDefinitions compiled.compatible.checked.catalog.definitions}
    {functions : FunctionModel compiled.compatible.checked.catalog ambient} {Records : Type v}
    {protocol : ProtectedStateTransition.Protocol.{u, v} Records}
    {initialIndex reachedIndex : ProtectedStateTransition.Index}
    {initial : protocol.State initialIndex} {reached : protocol.State reachedIndex}
    {leaf : TypeSystem.Ty} {reason : Dynamic.SemanticFault} {token : Word}
    (witness : MissingWitness compiled.compatible.checked registry functions protocol
      header.function.source (.occurrence node.id.occurrence) assignment.target prepared leaf
      initial reached reason token) :
    ∃ rawValue diagnostic, reason = .missingMappingDefault rawValue ∧
      table.diagnostic? token = some diagnostic ∧ diagnostic.error = .typeMismatch rawValue none := by
  obtain ⟨type, placeTyped⟩ := CallableIndexedOwnedPlaceAdmission.assignment_target_typed typed
  have projections := projections_at_root placeTyped writable
  obtain ⟨binder, selected, description⟩ := CompatiblePlaceDescription.of_describe described
  have preparedRoute := (CompatibleMixedPreparation.of_prepare generated).1
  have sourceTyped : ∀ actualBinder, rootBinder header.function.source assignment.target.root = .ok actualBinder →
      SourceProjectionsHaveType header.function.source context actualBinder.scheme.body
        assignment.target.projections assignment.target.type := by
    intro actualBinder binding
    have binders := Except.ok.inj (binding.symm.trans description.binding)
    subst actualBinder
    simpa only [preparedRoute, description.rootSource] using projections
  obtain ⟨phaseIndex, phase, location, locationNative, cell, optional, root, value, path,
    _relatedIn, _relatedOut, _scope, _canonical, _index, _worlds, _frame, _read, rootType, terminal⟩ := witness.terminal
  have rootView : SourceCoreRawMetadata.runtimeType cell.type =
      SourceCoreRawMetadata.runtimeType route.rootSourceType :=
    congrArg SourceCoreRawMetadata.runtimeType (rootType.trans (congrArg Route.rootSourceType preparedRoute))
  exact CallableIndexedOwnedPublicPlaceMissingDiagnostics.terminal_at_header header receipt found statement target
    described generated signatures sourceTyped rootView rebuilt terminal

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicPlaceReachedDiagnostics
