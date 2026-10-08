import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicPreparedShapeDiagnostics
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicCatalogClosedSources
import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceMissingTerminalDiagnostics
import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceProjectionDiagnosticCoverage
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOrdinaryLambdaSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodLambdaSupport
import Solcore.SourceSemantics.CoreLowering.SourceDiagnosticTypingOrigins

/-! The owning Source and the actual diagnostic preparations remain separate
from a lambda's body context. Reached projected faults use the same prepared
head and table; no Header is reconstructed for the lambda. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaSourceDiagnostics
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleMixedRoute
open SourceCoreCompatibleDataPlaces ProtectedPlaceReachedDiagnostics
universe u v

/-- Both preparations and the complete Source typing concern this literal
owner and Source. Collection membership retains the actual issuer occurrence. -/
structure IssuedSource (compiled : SourceCoreUnifiedCompilation.Compiled)
    (owner : SourceSpecialization.SpecializationKey) (source : TypedSource) where
  first : Nat
  assignments : SourceCoreAssignmentFaultSites.Table
  assignmentsPrepared : SourceCoreAssignmentFaultSites.prepare source first = .ok assignments
  typing : EmittedDiagnosticTokenPlan.UnaryTyped source ∧ AssignmentDiagnosticOrigins.OperandsTyped source
  plan : SourceCoreCompatibleDataPlaceFaultSites.Plan
  root : SourceCoreCompatibleDataPlaceFaultSites.Key
  extra : List (SourceCoreCompatibleDataPlaceFaultSites.Key × TypedSource)
  diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked)
  prepared : SourceCoreCompatibleDataPlaceFaultSites.prepare (.initial compiled.compatible.checked)
    plan root extra = .ok diagnostics
  collected : (owner, source) ∈ plan.specializations.map (fun specialized =>
    (specialized.key, specialized.function.typedBody)) ++ extra

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {owner : SourceSpecialization.SpecializationKey} {source : TypedSource}

/-- The ordinary support stores the genuine owning Header and exact Source. -/
theorem ordinary_typing {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} {registry : SourceCoreRawMetadata.Registry}
    {faults : FunctionCalls.FaultRep}
    {code : CallableIndexedLambdaValues.Code compiled.indexed function scope administrative}
    (support : CallableIndexedOwnedOrdinaryLambdaSupport.Support code registry faults)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    EmittedDiagnosticTokenPlan.UnaryTyped function.source ∧ AssignmentDiagnosticOrigins.OperandsTyped function.source := by
  simpa only [support.source, support.caller.agreement.source, CallableIndexedNamedGeneration.source] using SourceDiagnosticTyping.header_diagnostic_typed support.caller wellFormed

/-- The principal's independent selector authenticates its complete Source. -/
theorem principal_typing {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} {registry : SourceCoreRawMetadata.Registry}
    {faults : FunctionCalls.FaultRep}
    {code : CallableIndexedLambdaValues.Code compiled.indexed function scope administrative}
    (support : CallableIndexedOwnedMethodLambdaSupport.Support code registry faults)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    EmittedDiagnosticTokenPlan.UnaryTyped function.source ∧ AssignmentDiagnosticOrigins.OperandsTyped function.source := by
  simpa only [support.source] using SourceDiagnosticTypingOrigins.principal support.principal wellFormed

namespace IssuedSource
variable (issued : IssuedSource compiled owner source)

def invalidOperand (site : SourceCoreElaboration.ErrorSite) (root : Resolved.LocalId)
    (operator : Syntax.ValueAssignOp) : Word :=
  GenericAssignmentDiagnostics.token issued.assignments site root operator

def invalidUnary (site : SourceCoreElaboration.ErrorSite) (root : Resolved.LocalId) : Word :=
  issued.assignments.reasonAt site root .bitNot

def invalidProjection (site : SourceCoreElaboration.ErrorSite) (root : Resolved.LocalId) : Word :=
  issued.diagnostics.program.placeReason owner site root none

def missingDefault (site : SourceCoreElaboration.ErrorSite) (root : Resolved.LocalId)
    (valueType : TypeSystem.Ty) : Word :=
  issued.diagnostics.program.placeReason owner site root (some valueType)

/-- The real canonical preparation closes only this described target's gate. -/
theorem concrete {site : SourceCoreElaboration.ErrorSite} {assignment : AssignmentResolution} {route : Route}
    (described : describe (.initial compiled.compatible.checked) compiled.compatible.checked.signatures
      source site assignment = .ok route) :
    CompatiblePlaceMissingPreparationCoverage.concrete source assignment = true :=
  CompatiblePlaceConcretePreparation.describe_concrete
    (CallableIndexedOwnedPublicCatalogClosedSources.compiled_closed compiled) described

variable {registry : SourceCoreRawMetadata.Registry}
  {extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry}
  {table : SourceCoreFaultSites.Table}
  (rebuilt : issued.diagnostics.tableForRegistry registry extension = .ok table)
  {ambient : AmbientDefinitions compiled.compatible.checked.catalog.definitions}
  {functions : FunctionModel compiled.compatible.checked.catalog ambient} {Records : Type v}
  {protocol : ProtectedStateTransition.Protocol.{u, v} Records}

include rebuilt in
/-- The reached missing witness supplies its own raw root and terminal. -/
theorem missing {node : StatementNode} (statement : .statement node ∈ source.nodes)
    {assignment : AssignmentResolution}
    (target : assignment ∈ CompatiblePlaceMissingPreparationCoverage.targets node)
    {operator : Syntax.ValueAssignOp} {rhs : ExpressionId} {context : SourceSemantics.Context}
    (typed : SourceAssignmentHasType source context assignment operator rhs)
    {route : Route}
    (described : describe (.initial compiled.compatible.checked) compiled.compatible.checked.signatures source
      (.occurrence node.id.occurrence) assignment = .ok route)
    {fuel : Nat} {invalid : Word} {prepared : Prepared}
    (generated : prepare (.initial compiled.compatible.checked) fuel route invalid
      (issued.missingDefault (.occurrence node.id.occurrence) assignment.target.root) = .ok prepared)
    (writable : WritableLocal context assignment.target.root prepared.route.rootSourceType)
    (unique : NodeOccurrencesUnique source) (signatures : context.signatures = compiled.compatible.checked.signatures)
    {initialIndex reachedIndex : ProtectedStateTransition.Index}
    {initial : protocol.State initialIndex} {reached : protocol.State reachedIndex}
    {leaf : TypeSystem.Ty} {reason : Dynamic.SemanticFault} {token : Word}
    (witness : MissingWitness compiled.compatible.checked registry functions protocol source
      (.occurrence node.id.occurrence) assignment.target prepared leaf initial reached reason token) :
    ∃ rawValue diagnostic, reason = .missingMappingDefault rawValue ∧
      table.diagnostic? token = some diagnostic ∧ diagnostic.error = .typeMismatch rawValue none := by
  obtain ⟨type, placeTyped⟩ := CallableIndexedOwnedPlaceAdmission.assignment_target_typed typed
  have projections := CallableIndexedOwnedPublicPlaceReachedDiagnostics.projections_at_root placeTyped writable
  obtain ⟨binder, selected, description⟩ := CompatiblePlaceDescription.of_describe described
  have preparedRoute := (CompatibleMixedPreparation.of_prepare generated).1
  have sourceTyped : ∀ actualBinder, rootBinder source assignment.target.root = .ok actualBinder →
      SourceProjectionsHaveType source context actualBinder.scheme.body assignment.target.projections assignment.target.type := by
    intro actualBinder binding
    have binders := Except.ok.inj (binding.symm.trans description.binding)
    subst actualBinder
    simpa only [preparedRoute, description.rootSource] using projections
  obtain ⟨phaseIndex, phase, location, locationNative, cell, optional, root, value, path,
    _relatedIn, _relatedOut, _scope, _canonical, _index, _worlds, _frame, _read, rootType, terminal⟩ := witness.terminal
  have rootView : SourceCoreRawMetadata.runtimeType cell.type =
      SourceCoreRawMetadata.runtimeType route.rootSourceType :=
    congrArg SourceCoreRawMetadata.runtimeType (rootType.trans (congrArg Route.rootSourceType preparedRoute))
  exact CompatiblePlaceMissingTerminalDiagnostics.terminal_diagnostic issued.prepared issued.collected
    statement target (concrete described) described generated unique signatures sourceTyped rootView rebuilt terminal

include rebuilt in
/-- An uninitialized projected root retains its actual location and witness.
The fixed diagnostic belongs to the same accepted description. -/
theorem uninitialized {node : StatementNode} (statement : .statement node ∈ source.nodes)
    {assignment : AssignmentResolution}
    (target : assignment ∈ CompatiblePlaceMissingPreparationCoverage.targets node)
    {route : Route}
    (described : describe (.initial compiled.compatible.checked) compiled.compatible.checked.signatures source
      (.occurrence node.id.occurrence) assignment = .ok route)
    {fuel : Nat} {prepared : Prepared}
    (generated : prepare (.initial compiled.compatible.checked) fuel route
      (issued.invalidProjection (.occurrence node.id.occurrence) assignment.target.root)
      (issued.missingDefault (.occurrence node.id.occurrence) assignment.target.root) = .ok prepared)
    {initialIndex reachedIndex : ProtectedStateTransition.Index}
    {initial : protocol.State initialIndex} {reached : protocol.State reachedIndex}
    {environment : Dynamic.Environment} {location : Dynamic.Location}
    (witness : UninitializedWitness compiled.compatible.checked registry functions protocol environment
      assignment.target prepared initial reached location) :
    UninitializedWitness compiled.compatible.checked registry functions protocol environment
      assignment.target prepared initial reached location ∧
    ∃ diagnostic, table.diagnostic? prepared.invalidProjection = some diagnostic ∧ diagnostic.error = .invalidPlaceProjection := by
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
        (issued.missingDefault (.occurrence node.id.occurrence) assignment.target.root) [] 0 outputs keys → outputs = [] := by
      intro outputs keys path
      cases path
      rfl
    exact projected (only_nil steps)
  obtain ⟨entry, member, kind, _first, reason⟩ :=
    CompatiblePlaceProjectionDiagnosticCoverage.prepare_coverage issued.prepared issued.collected
      statement target (concrete described) described nonempty
  obtain ⟨decoded, error⟩ := CompatiblePlaceProjectionDiagnosticPreparation.table_diagnostic
    issued.prepared member kind rebuilt
  have same : prepared.invalidProjection = entry.reason := actual.2.1.trans reason
  exact ⟨witness, entry.diagnostic, by simpa only [same] using decoded, error⟩

include rebuilt in
/-- The interpretation is used after the same head's real table observation. -/
theorem shape_errors {context : SourceSemantics.Context} {certificate : GenericExpressionMeaning.Certificate}
    {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    (head : GenericAssignmentStatements.Head (.initial compiled.compatible.checked) source context
      certificate scope administrative ambient.definitions assignment operator rhs)
    {environment : Dynamic.Environment} {initialIndex : ProtectedStateTransition.Index}
    (initial : protocol.State initialIndex) {faults : FunctionCalls.FaultRep}
    (projected : assignment.target.projections ≠ []) {site : SourceCoreElaboration.ErrorSite}
    (origin : AssignmentDiagnosticOrigins.Occurs source site assignment operator rhs) {fuel : Nat}
    (retained : head.PreparedAt site fuel (issued.invalidProjection site assignment.target.root)
      (issued.missingDefault site assignment.target.root))
    (typed : SourceAssignmentHasType source context assignment operator rhs)
    (unique : NodeOccurrencesUnique source) (signatures : context.signatures = compiled.compatible.checked.signatures)
    (interprets : CallableIndexedOwnedPublicPreparedShapeDiagnostics.ReachedTableInterpretation
      compiled.compatible.checked registry functions protocol environment assignment.target head.prepared initial table faults) :
    ShapeErrors (.initial compiled.compatible.checked) registry functions protocol source context certificate
      scope administrative environment assignment.target head.prepared operator head.invalid initial faults head.shape := by
  obtain ⟨node, statement, sameSite, target⟩ := CallableIndexedOwnedPublicPreparedShapeDiagnostics.owning_target origin
  subst site
  cases retained with
  | bare empty => exact False.elim (projected empty)
  | projected route layout ordinary shape described preparedBy =>
    rw [shape]
    apply ShapeErrors.projected (layout := layout) (ordinary := ordinary)
    · intro reachedIndex reason token reached related witness
      obtain ⟨rawValue, diagnostic, sameReason, decoded, error⟩ :=
        issued.missing rebuilt statement target typed described preparedBy head.writable unique signatures witness
      rw [sameReason]
      exact interprets.missing decoded error
    · intro reachedIndex location reached related witness
      obtain ⟨actualWitness, diagnostic, decoded, error⟩ :=
        issued.uninitialized rebuilt statement target described preparedBy witness
      exact interprets.uninitialized reached related actualWitness decoded error

end IssuedSource
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaSourceDiagnostics
