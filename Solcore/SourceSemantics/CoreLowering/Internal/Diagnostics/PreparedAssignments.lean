import Solcore.SourceSemantics.CoreLowering.Internal.Accepted.PreparedBranching
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.AssignmentHeads
import Solcore.SourceSemantics.CoreLowering.Internal.Diagnostics.EmittedMatches
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.GenericAssignments
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.IndexDiagnostics
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.PublicExpressionBounds
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.RuntimeProfileFactories
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.LambdaReceipts
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.LexicalBodyFaults
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ChosenOrdinaryCalls

/-!
# Prepared assignment diagnostics

Authority, producers and reached diagnostics of prepared assignments.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.PreparedAssignmentReachedDiagnostics
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.PreparedAssignmentDiagnosticAuthority
/-! Assignment tokens retain their exact specialized Source and compiler
inventory. Receiving metadata is supplied by the actual public call. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.PreparedAssignmentDiagnosticAuthority
open Core Frontend SourceInference GeneralHeap CompatiblePayload

structure SourcePort (compiled : SourceCoreUnifiedCompilation.Compiled)
    (source : TypedSource)
    (invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word)
    (missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word) where
  owner : SourceSpecialization.SpecializationKey
  row : SourceSpecialization.SpecializedFunction
  record : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan owner = .ok row
  sourceEq : source = row.function.typedBody
  unique : NodeOccurrencesUnique source
  issuer : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked)
  present : compiled.indexed.base.diagnostics = some issuer
  invalidToken : ∀ site root, invalidProjection site root = issuer.program.placeReason owner site root none
  missingToken : ∀ site root raw, missingDefault site root raw = issuer.program.placeReason owner site root (some raw)

universe u v

/-- The dynamic boundary supplies the receiving table for each retained
compiler origin. Public callers construct this from their actual receiver. -/
def Interprets (compiled : SourceCoreUnifiedCompilation.Compiled)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) : Prop :=
  ∀ {source invalidProjection missingDefault},
    SourcePort compiled source invalidProjection missingDefault →
    ∀ {ambient : AmbientDefinitions compiled.compatible.checked.catalog.definitions}
      (functions : FunctionModel compiled.compatible.checked.catalog ambient)
      {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records),
    PreparedAssignmentReachedDiagnostics.Ready (values := .initial compiled.compatible.checked)
      functions protocol source invalidProjection missingDefault registry faults

end Solcore.SourceSemantics.CoreLowering.PreparedAssignmentDiagnosticAuthority
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.PreparedAssignmentDiagnosticProducers
/-! The actual named and cached diagnostic producers authenticate projected
place tokens for the complete retained Source. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.PreparedAssignmentDiagnosticProducers
open Core Frontend SourceInference
open PreparedAssignmentDiagnosticAuthority

 theorem named {compiled : SourceCoreUnifiedCompilation.Compiled} {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared)
    {instantiation : DeclarationInstantiation}
    {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header) :
    Nonempty (SourcePort compiled header.function.source
      (RecursiveNamedPreparedHeaderPolicies.Prepared.invalidProjection prepared)
      (RecursiveNamedPreparedHeaderPolicies.Prepared.missingDefault prepared)) := by
  obtain ⟨issuer, present, lowered⟩ := diagnostic.actual
  refine ⟨{
    owner := prepared.named.signature.key
    row := prepared.named.specialized
    record := CallableIndexedActualNamedSourceReceipts.cached_record compiled prepared.selected prepared.compilation.hook
    sourceEq := by rw [aligned.function]; rfl
    unique := header.unique
    issuer := issuer
    present := present
    invalidToken := ?_
    missingToken := ?_ }⟩
  · intro site root
    simp only [RecursiveNamedPreparedHeaderPolicies.Prepared.invalidProjection, lowered]
    cases compiled.indexed.base.callableContext <;> rfl
  · intro site root raw
    simp only [RecursiveNamedPreparedHeaderPolicies.Prepared.missingDefault, lowered]
    cases compiled.indexed.base.callableContext <;> rfl

 theorem cached {compiled : SourceCoreUnifiedCompilation.Compiled} {row : SourceSpecialization.SpecializedFunction}
    (cached : CallablePreparedMethodSelection.Cached compiled row)
    (diagnostic : CallableIndexedOwnedPreparedStagedMethodTerminalSupport.DiagnosticAt cached)
    {source : TypedSource} (sourceEq : source = cached.named.specialized.function.typedBody)
    (unique : NodeOccurrencesUnique source) :
    Nonempty (SourcePort compiled source
      (fun site root => cached.diagnostics.placeReason cached.named.signature.key site root none)
      (fun site root raw => cached.diagnostics.placeReason cached.named.signature.key site root (some raw))) := by
  obtain ⟨issuer, present, lowered⟩ := diagnostic.actual
  refine ⟨{
    owner := cached.named.signature.key
    row := cached.named.specialized
    record := CallableIndexedActualNamedSourceReceipts.cached_record compiled cached.selected cached.compilation.hook
    sourceEq := sourceEq
    unique := unique
    issuer := issuer
    present := present
    invalidToken := ?_
    missingToken := ?_ }⟩
  · intro site root
    rw [lowered]
    cases compiled.indexed.base.callableContext <;> rfl
  · intro site root raw
    rw [lowered]
    cases compiled.indexed.base.callableContext <;> rfl

end Solcore.SourceSemantics.CoreLowering.PreparedAssignmentDiagnosticProducers
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.PreparedAssignmentDiagnosticAuthorityReception
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
private theorem SourcePort.assignment_ready_for
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
    PreparedAssignmentReachedDiagnostics.AssignmentReady (values := .initial compiled.compatible.checked) functions protocol source invalidProjection missingDefault
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

private theorem SourcePort.unary_ready_for
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
  PreparedAssignmentReachedDiagnostics.UnaryReady (values := .initial compiled.compatible.checked) functions protocol source invalidProjection missingDefault
    completion.result.context.registry faults := by
  intro context certificate scope administrative assignment head site fuel origin signatures retained type typed
    environment initialIndex initial
  obtain ⟨node, statement, sameSite, target⟩ :=
    ProjectedBitNotDiagnosticOrigins.owning_target origin
  subst site
  obtain ⟨root, sources, issued⟩ :=
    CallableIndexedOwnedPublicDiagnosticReceipts.compiled_diagnostics compiled port.present
  have collected := List.mem_append_left sources port.collected
  have receiverCopy := receiver
  obtain ⟨table, rebuilt, _tableEq⟩ := receiverCopy
  rw [port.present] at rebuilt
  obtain ⟨siteEq, route, described, preparedBy⟩ := retained
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
  constructor
  · intro reachedIndex reason token reached related witness
    have projections := CallableIndexedOwnedPublicPlaceReachedDiagnostics.projections_at_root typed head.writable
    obtain ⟨binder, selected, description⟩ := CompatiblePlaceDescription.of_describe described
    have preparedRoute := (CompatibleMixedPreparation.of_prepare generated).1
    have sourceTyped : ∀ actualBinder, rootBinder source assignment.target.root = .ok actualBinder →
        SourceProjectionsHaveType source context actualBinder.scheme.body
          assignment.target.projections assignment.target.type := by
      intro actualBinder binding
      have binders := Except.ok.inj (binding.symm.trans description.binding)
      subst actualBinder
      simpa only [preparedRoute, description.rootSource] using projections
    simp only [siteEq] at witness
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
      exact head.layout.nonempty (only_nil steps)
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
  exact ⟨port.assignment_ready_for receiver functions protocol included,
    port.unary_ready_for receiver functions protocol included⟩

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
end
