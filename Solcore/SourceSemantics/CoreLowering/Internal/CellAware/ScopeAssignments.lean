import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.StagedForLoops
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.ScopeExpressions
import Solcore.SourceSemantics.CoreLowering.CellAllocationReadiness
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.StagedFlows
import Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeTypedSourceSites
import Solcore.SourceSemantics.CoreLowering.ProtectedCellStagedBareAssignment
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.LiteralReturns
import Solcore.SourceSemantics.CoreLowering.GenericAssignmentStatementHead
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.StagedProjected
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.StatementAdmission
import Solcore.SourceSemantics.CoreLowering.PreparedProjectedDiagnosticFields
import Solcore.SourceSemantics.CoreLowering.ProtectedStateProjectedAssignmentHeads
import Solcore.SourceSemantics.Staging.RecursiveProjectedTargetFacts
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.ScopeStatements
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.ScopedSourceInversion
import Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeStatementSuffixTyping

/-!
# Cell-aware scopes: assignments

Bare and projected assignments on the scope protocol: heads, resolution, both directions and flows, and the `for` initial and post bounds that use them.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareScopeForPostBounds
/-! Actual for-post items retain every reached mixed heap and restore the outer
lexical context before another condition. The real header tree closes these
internal preservation and reflection contracts. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareScopeForPostBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)
open CallableIndexedOwnedAdmittedStagedForPostContracts (restoredOutcome)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {protocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (context : SourceSemantics.Context)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  (model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions)
  (named : SourceCoreGeneralFunctions.Function)
  (producer : ProtectedStateTransition.CellAllocation.Producer (catalog := catalog) protocol compiled.indexed.layouts
    compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)))
  (registry : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
  (faults : RecursiveStageMeaning.FaultRep) (administrative : Core.Context)
  (scope : SourceCoreLocalCell.Scope) (items : List ForItemForm)
  (expected : TypeSystem.Ty) (type : Ty) (code : Expr)

/-- Source and native grades remain independent. Every reached branch keeps
its exact mixed heap and restores the caller's lexical observations. -/
def PreservesAt (size : Nat) : Prop :=
  ∀ {mapping world actualContext environment canonical actual before store embedding},
    DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical compiled.indexed.layouts.definitions →
    GenericHeap.CellHeapRepresents
      (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)) mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree embedding canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions →
    Dynamic.SourceRuntimeValid program context (CallableIndexedNamedGeneration.source named) →
    invocation.evidence.Covers context →
    context.solvedRequirements = (CallableIndexedNamedGeneration.context compiled.indexed named).solvedRequirements →
    (∃ control final, ForItemsHaveType (CallableIndexedNamedGeneration.source named) control context items final) →
    ∀ initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩,
      Admission bridge context initial →
      CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model compiled.indexed)
        named.signature.key [] mapping world before store environment →
    ∀ physical : CellAwareScopePhysical.Physical compiled named context scope canonical mapping world before store environment,
    ∀ owner : CallableIndexedOwnedFunctionValues.OwnedKey keys,
      owner.key.frameLocation = physical.location →
      ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native →
    ∀ {finalContext outcome after},
      Staging.Recursive.Size.ForItems program registry size invocation context environment before
        items finalContext outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename embedding) value finalStore ∧
      Represents model finalMap finalWorld false expected type faults (restoredOutcome environment outcome) value ∧
      GenericHeap.CellHeapRepresents
        (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed))
        finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model compiled.indexed)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : protocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        protocol.Relates initial reached ∧ Post bridge context expected (restoredOutcome environment outcome) reached

/-- Actual native completion reconstructs the chosen Source branch and its
real allocations, failures and control transfers. -/
def ReflectsAt (size : Nat) : Prop :=
  ∀ {mapping world actualContext environment canonical actual before store embedding value finalStore},
    DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical compiled.indexed.layouts.definitions →
    GenericHeap.CellHeapRepresents
      (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)) mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree embedding canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions →
    Dynamic.SourceRuntimeValid program context (CallableIndexedNamedGeneration.source named) →
    invocation.evidence.Covers context →
    context.solvedRequirements = (CallableIndexedNamedGeneration.context compiled.indexed named).solvedRequirements →
    (∃ control final, ForItemsHaveType (CallableIndexedNamedGeneration.source named) control context items final) →
    ∀ initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩,
      Admission bridge context initial →
      CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model compiled.indexed)
        named.signature.key [] mapping world before store environment →
    ∀ physical : CellAwareScopePhysical.Physical compiled named context scope canonical mapping world before store environment,
    ∀ owner : CallableIndexedOwnedFunctionValues.OwnedKey keys,
      owner.key.frameLocation = physical.location →
      ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native →
    EvaluationSize size actual store (code.rename embedding) value finalStore →
    ∃ sourceSize finalContext outcome after finalMap finalWorld,
      Staging.Recursive.Size.ForItems program registry sourceSize invocation context environment before
        items finalContext outcome after ∧
      Represents model finalMap finalWorld false expected type faults (restoredOutcome environment outcome) value ∧
      GenericHeap.CellHeapRepresents
        (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed))
        finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model compiled.indexed)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : protocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        protocol.Relates initial reached ∧ Post bridge context expected (restoredOutcome environment outcome) reached

def PreservesAtMost (budget : Nat) : Prop :=
  ∀ size, size ≤ budget → PreservesAt bridge context model named producer registry invocation faults administrative scope items expected type code size

def PreservesBelow (budget : Nat) : Prop :=
  ∀ size, size < budget → PreservesAt bridge context model named producer registry invocation faults administrative scope items expected type code size

def ReflectsAtMost (budget : Nat) : Prop :=
  ∀ size, size ≤ budget → ReflectsAt bridge context model named producer registry invocation faults administrative scope items expected type code size

def ReflectsBelow (budget : Nat) : Prop :=
  ∀ size, size < budget → ReflectsAt bridge context model named producer registry invocation faults administrative scope items expected type code size

end Solcore.SourceSemantics.CoreLowering.CellAwareScopeForPostBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareScopeBareAssignmentHeads
/-! Actual bare assignment Heads use the same admitted staged RHS and preserve
its exact reached caller. Source assignment typing establishes admission after
the write; failures keep the precise staged tag and the RHS endpoint. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareScopeBareAssignmentHeads
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality CompatibleHeap CoreProof ReadOnly
open SourceCoreCompatibleDataPlaces GenericExpressionMeaning
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CellAwareScopeExpressionBounds
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)

variable
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {named : SourceCoreGeneralFunctions.Function}

section Rhs
variable {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {prepared : Prepared} {place : PlaceResolution} {environment : Dynamic.Environment} {actual : Environment}
  {heap : Dynamic.Heap} {store : Store} {mapping : LocationMap} {world : StoreTyping} {index : Nat}
  {faults : RecursiveStageMeaning.FaultRep} {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr} {ξ : Renaming}
  {scope : Scope} {administrativeContext actualContext : Core.Context} {canonical : Environment}
  {certificate : Certificate}
  (snapshot : CompatibleBareAssignment.Snapshot compiled.compatible.checked registry functions prepared place environment actual heap store mapping world (ξ index))

private theorem rhs_preserves_at (size : Nat)
    (meaning : PreservesAt bridge context (payloadModel compiled.compatible.checked registry functions) named stages invocation certificate faults size)
    (generated : certificate scope id lowered) (found : invocation.source.lookupExpression? id = some node)
    (sourceTyped : ExpressionHasType invocation.source context id node.type)
    (environments : DataHeap.EnvRepresents (definitions := compiled.indexed.layouts.definitions) (storageCatalog compiled.compatible.checked.catalog)
      mapping world administrativeContext scope environment canonical)
    (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel (payloadModel compiled.compatible.checked registry functions) (GeneralizedLocalInstanceValues.model compiled.indexed)) mapping world heap store)
    (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
    (initial : callerProtocol.State ⟨scope, mapping, world, heap, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (authority : CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model compiled.indexed) named.signature.key [] mapping world heap store environment)
    (physical : CellAwareScopePhysical.Physical compiled named context scope canonical mapping world heap store environment)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (sameLocation : owner.key.frameLocation = physical.location)
    {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Expression program stages size invocation context environment heap id outcome after) :
    ∃ value finalStore finalMap finalWorld,
      ProtectedCellStagedBareAssignment.RhsResult (cells := (GeneralizedLocalDescriptorHeap.cellModel (payloadModel compiled.compatible.checked registry functions) (GeneralizedLocalInstanceValues.model compiled.indexed))) (instances := (GeneralizedLocalInstanceValues.model compiled.indexed)) (compilation := (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)) (program := program) (context := context)
        (stages := stages) (invocation := invocation) (faults := faults) (id := id) (node := node) (lowered := lowered)
        snapshot size outcome after value finalStore finalMap finalWorld ∧
      ProtectedStateTransition.Transition callerProtocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata,
      effect, reached, related, post⟩ :=
    meaning generated found sourceTyped environments heaps locals
      (DataPlaceChildExpressions.prefix_agrees agrees
        [snapshot.value, .unit, .cellRef (OptionalCell.cellType prepared.route.rootType) snapshot.target])
      (snapshot.runtimeTyped actualTyped) initial admitted authority physical owner sameLocation trace
  refine ⟨value, finalStore, finalMap, finalWorld,
    ⟨trace, ?_, represented, finalHeaps, maps, worlds, frame, metadata, effect, ?_⟩, reached, related⟩
  · simpa only [DataPlaceChildExpressions.rename_prefix, List.length_cons, List.length_nil,
    List.cons_append, List.nil_append, DataPlaceExecution.snapshotEnvironment,
    DataPlaceExecution.keysEnvironment, DataPlaceExecution.referenceEnvironment,
    SourceCoreDataPlaces.shift, shift, Nat.zero_add] using evaluated
  · intro right same
    cases same
    exact ⟨post.at_value.1, post.at_value.2.heap⟩

private theorem rhs_reflects_at (size : Nat)
    (meaning : ReflectsAt bridge context (payloadModel compiled.compatible.checked registry functions) named stages invocation certificate faults size)
    (generated : certificate scope id lowered) (found : invocation.source.lookupExpression? id = some node)
    (sourceTyped : ExpressionHasType invocation.source context id node.type)
    (environments : DataHeap.EnvRepresents (definitions := compiled.indexed.layouts.definitions) (storageCatalog compiled.compatible.checked.catalog)
      mapping world administrativeContext scope environment canonical)
    (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel (payloadModel compiled.compatible.checked registry functions) (GeneralizedLocalInstanceValues.model compiled.indexed)) mapping world heap store)
    (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
    (initial : callerProtocol.State ⟨scope, mapping, world, heap, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (authority : CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model compiled.indexed) named.signature.key [] mapping world heap store environment)
    (physical : CellAwareScopePhysical.Physical compiled named context scope canonical mapping world heap store environment)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (sameLocation : owner.key.frameLocation = physical.location)
    {value : Value} {finalStore : Store}
    (evaluated : EvaluationSize size
      (DataPlaceExecution.snapshotEnvironment prepared.route.rootType snapshot.target .unit snapshot.value actual)
      store (shift 3 (lowered.expression.rename ξ)) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      ProtectedCellStagedBareAssignment.RhsResult (cells := (GeneralizedLocalDescriptorHeap.cellModel (payloadModel compiled.compatible.checked registry functions) (GeneralizedLocalInstanceValues.model compiled.indexed))) (instances := (GeneralizedLocalInstanceValues.model compiled.indexed)) (compilation := (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)) (program := program) (context := context)
        (stages := stages) (invocation := invocation) (faults := faults) (id := id) (node := node) (lowered := lowered)
        snapshot sourceSize outcome after value finalStore finalMap finalWorld ∧
      ProtectedStateTransition.Transition callerProtocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata,
      effect, reached, related, post⟩ :=
    meaning generated found sourceTyped environments heaps locals
      (DataPlaceChildExpressions.prefix_agrees agrees
        [snapshot.value, .unit, .cellRef (OptionalCell.cellType prepared.route.rootType) snapshot.target])
      (snapshot.runtimeTyped actualTyped) initial admitted authority physical owner sameLocation
      (by simpa only [DataPlaceChildExpressions.rename_prefix, List.length_cons, List.length_nil,
        List.cons_append, List.nil_append, DataPlaceExecution.snapshotEnvironment,
        DataPlaceExecution.keysEnvironment, DataPlaceExecution.referenceEnvironment,
        SourceCoreDataPlaces.shift, shift, Nat.zero_add] using evaluated)
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld,
    ⟨trace, evaluated.sound, represented, finalHeaps, maps, worlds, frame, metadata, effect, by
      intro right same
      cases same
      exact ⟨post.at_value.1, post.at_value.2.heap⟩⟩, reached, related⟩
end Rhs

inductive ResultAt (size : Nat)
    (context : SourceSemantics.Context) (stages : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
    (faults : RecursiveStageMeaning.FaultRep) (scope : Scope) (writtenContext : Core.Context)
    (assignment : AssignmentResolution) (operator : Syntax.ValueAssignOp) (rhs : ExpressionId)
    (environment : Dynamic.Environment) (canonical actual : Environment)
    (before : Dynamic.Heap) (store : Store) (mapping : LocationMap) (world : StoreTyping)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (next : Expr) (output : Ty) (value : Value) (finalStore : Store) : Prop where
  | fault {sourceSize : Nat} {target : Dynamic.ResolvedPlace}
      {failure : Staging.Recursive.Failure} {token : Word} {after : Dynamic.Heap}
      {finalMap : LocationMap} {finalWorld : StoreTyping}
      (snapshot : Staging.Recursive.BareTarget environment before assignment.target target)
      (trace : Staging.Recursive.Size.Expression program stages sourceSize invocation context environment before rhs (.fault failure) after)
      (same : value = .inLeft output (.word token)) (matched : faults failure token)
      (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel (payloadModel compiled.compatible.checked registry functions) (GeneralizedLocalInstanceValues.model compiled.indexed)) finalMap finalWorld after finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap finalStore) (metadata : Dynamic.HeapMetadataExtend before after)
      (effect : CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model compiled.indexed) mapping world before store finalMap finalWorld after finalStore)
      (reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (related : callerProtocol.Relates initial reached) (stable : StableRows (bridge.pool reached)) :
      ResultAt size context stages invocation faults scope writtenContext assignment operator rhs
        environment canonical actual before store mapping world initial next output value finalStore
  | operands {sourceSize : Nat} {target : Dynamic.ResolvedPlace}
      {right : Dynamic.Value} {after : Dynamic.Heap} {current : Dynamic.Cell}
      {initialValue selected : Option Dynamic.Value} {token : Word}
      {finalMap : LocationMap} {finalWorld : StoreTyping}
      (snapshot : Staging.Recursive.BareTarget environment before assignment.target target)
      (trace : Staging.Recursive.Size.Expression program stages sourceSize invocation context environment before rhs (.value right) after)
      (currentRead : Dynamic.Heap.Reads after target.location current)
      (rootType : current.type = target.rootType)
      (initialized : Dynamic.RootInitialValue current initialValue)
      (path : Dynamic.ProjectionsRead initialValue target.projections selected)
      (invalid : Dynamic.AssignmentOperandsInvalid operator target.selected right)
      (same : value = .inLeft output (.word token))
      (matched : faults (.semantic (.invalidAssignmentOperands operator)) token)
      (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel (payloadModel compiled.compatible.checked registry functions) (GeneralizedLocalInstanceValues.model compiled.indexed)) finalMap finalWorld after finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap finalStore) (metadata : Dynamic.HeapMetadataExtend before after)
      (effect : CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model compiled.indexed) mapping world before store finalMap finalWorld after finalStore)
      (reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (related : callerProtocol.Relates initial reached) (stable : StableRows (bridge.pool reached)) :
      ResultAt size context stages invocation faults scope writtenContext assignment operator rhs
        environment canonical actual before store mapping world initial next output value finalStore
  | success {sourceSize remainingSize : Nat} {target : Dynamic.ResolvedPlace}
      {right updated : Dynamic.Value} {middle after : Dynamic.Heap}
      {written : Store} {finalMap : LocationMap} {finalWorld : StoreTyping} {slots : Environment}
      (snapshot : Staging.Recursive.BareTarget environment before assignment.target target)
      (trace : Staging.Recursive.Size.Expression program stages sourceSize invocation context environment before rhs (.value right) middle)
      (write : Dynamic.ResolvedPlaceWrites
        (fun _ replacement => Dynamic.AssignmentValueApplies operator target.selected right replacement)
        middle target updated after)
      (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel (payloadModel compiled.compatible.checked registry functions) (GeneralizedLocalInstanceValues.model compiled.indexed)) finalMap finalWorld after written)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap written) (metadata : Dynamic.HeapMetadataExtend before after)
      (effect : CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model compiled.indexed) mapping world before store finalMap finalWorld after written)
      (count : slots.length = 7)
      (typed : RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) writtenContext compiled.indexed.layouts.definitions)
      (reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, written, canonical⟩)
      (related : callerProtocol.Relates initial reached) (admitted : Admission bridge context reached)
      (bounded : remainingSize < size)
      (remaining : EvaluationSize remainingSize (slots ++ actual) written (shift 7 next) value finalStore) :
      ResultAt size context stages invocation faults scope writtenContext assignment operator rhs
        environment canonical actual before store mapping world initial next output value finalStore

section Heads
variable {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : Certificate} {scope : Scope} {administrative : Core.Context}
  (extension : SourceCoreRawMetadata.Extends ((SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)).registry registry)
  {faults : RecursiveStageMeaning.FaultRep}
  (transport : ProtectedStateTransition.AdministrativeTransport callerProtocol)
  {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
  (head : GenericAssignmentStatements.Head (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) invocation.source context certificate scope administrative compiled.indexed.layouts.definitions assignment operator rhs)
  (bare : assignment.target.projections = [])
  {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment}
  {canonical actual : Environment} {before : Dynamic.Heap} {store : Store} {actualContext : Core.Context} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (definitions := compiled.indexed.layouts.definitions) (storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical)
  (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel (payloadModel compiled.compatible.checked registry functions) (GeneralizedLocalInstanceValues.model compiled.indexed)) mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)
  (authority : CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model compiled.indexed) named.signature.key [] mapping world before store environment)
  (physical : CellAwareScopePhysical.Physical compiled named context scope canonical mapping world before store environment)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (sameLocation : owner.key.frameLocation = physical.location)
  (unique : NodeOccurrencesUnique invocation.source)
  (assignmentTyped : SourceAssignmentHasType invocation.source context assignment operator rhs)

include extension environments heaps locals agrees bare head admitted in
/-- The accepted writable root and actual represented heap determine the
pre-RHS snapshot; no Source assignment execution is assumed. -/
theorem target_snapshot :
    ∃ target, Staging.Recursive.BareTarget environment before assignment.target target := by
  rcases head with ⟨prepared, index, codes, leaf, lowered, node, invalid, shape, slot, writable, found, right, rightView, rightType, profile⟩
  cases shape with
  | projected layout _ =>
    have length := CompatiblePlaceCompilerCertificates.PreparedPath.steps_length layout.path
    rw [bare, List.length_nil] at length
    exact False.elim (layout.nonempty (List.eq_nil_of_length_eq_zero length))
  | bare empty layout =>
    obtain ⟨snapshot, _ordinary⟩ := @CompatibleBareAssignment.snapshot_of_cell_heap
      registry prepared assignment.target environment actual before store mapping world index
      (.initial compiled.compatible.checked) (CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      functions context scope administrative canonical ξ layout extension environments _
      GeneralizedLocalDescriptorHeap.ordinary_cells heaps admitted.heap locals agrees slot writable
    exact ⟨snapshot.resolved, .intro empty snapshot.lookup snapshot.read snapshot.root⟩

include transport extension environments heaps locals agrees actualTyped initial admitted unique assignmentTyped bare authority physical owner sameLocation in
theorem reflects_bounded (budget : Nat)
    (boundedReflection : ReflectsBelow bridge context (payloadModel compiled.compatible.checked registry functions) named stages invocation certificate faults budget)
    (invalidToken : AssignmentOperandDiagnostics.OperandsLaw
      (fun reason token => faults (.semantic reason) token) operator head.invalid)
    {next : Expr} {output : Ty} {value : Value} {finalStore : Store}
    {size : Nat} (completed : EvaluationSize size actual store ((head.emit next output).rename ξ) value finalStore) (bounded : size ≤ budget) :
    ResultAt (registry := registry) bridge functions size context stages invocation faults
      scope (head.writtenContext actualContext) assignment operator rhs environment canonical actual
      before store mapping world initial (next.rename ξ) output value finalStore := by
  rcases head with ⟨prepared, index, codes, leaf, lowered, node, invalid, shape, slot, writable, found, right, rightView, rightType, profile⟩
  cases shape with
  | projected layout _ =>
    have length := CompatiblePlaceCompilerCertificates.PreparedPath.steps_length layout.path
    rw [bare, List.length_nil] at length
    exact False.elim (layout.nonempty (List.eq_nil_of_length_eq_zero length))
  | bare empty layout =>
    have sourceTyped := CallableIndexedOwnedAssignmentAdmission.rhs_typed unique found assignmentTyped
    have result := ProtectedCellStagedBareAssignment.reflects_with_rhs callerProtocol transport budget initial layout empty extension
      (fun snapshot child smaller {_ _} evaluated => rhs_reflects_at bridge functions snapshot child (boundedReflection child smaller)
        right found sourceTyped environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation evaluated)
      rightView rightType (CallableIndexedOwnedBareAssignmentAdmission.source_profile unique found assignmentTyped rightView)
      environments (GeneralizedLocalDescriptorHeap.ordinary_cells) admitted.heap heaps locals agrees actualTyped slot writable invalidToken completed bounded
    cases result with
    | fault snapshot trace same matched finalHeaps maps worlds preservation metadata effect post =>
      obtain ⟨reached, related⟩ := post
      exact .fault snapshot trace same matched finalHeaps maps worlds preservation metadata effect reached related
        (StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) admitted.rows preservation)
    | operands snapshot trace currentRead rootType initialized path invalidOperands same matched finalHeaps maps worlds preservation metadata effect post =>
      obtain ⟨reached, related⟩ := post
      exact .operands snapshot trace currentRead rootType initialized path invalidOperands same matched finalHeaps maps worlds preservation metadata effect reached related
        (StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) admitted.rows preservation)
    | success snapshot trace rightTyped middleTyped write finalHeaps maps worlds preservation metadata effect count typed strict remaining post =>
      obtain ⟨reached, related⟩ := post
      exact .success snapshot trace write finalHeaps maps worlds preservation metadata effect count
        (by simpa [GenericAssignmentStatements.Head.writtenContext, CompatibleRenamedPlaceSuccess.writtenContext, CompatibleBareAssignment.writtenContext,
          Prepared.optionalLeaf, SourceCoreCalls.packArguments, layout.sameType] using typed)
        reached related ⟨CallableIndexedOwnedBareAssignmentAdmission.heap_after_assignment unique found assignmentTyped
          locals snapshot middleTyped rightTyped write,
          StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) admitted.rows preservation⟩ strict remaining
include transport extension environments heaps locals agrees actualTyped initial admitted unique assignmentTyped bare authority physical owner sameLocation in
theorem preserves_value {sourceSize : Nat}
    (meaning : PreservesAt bridge context (payloadModel compiled.compatible.checked registry functions) named stages invocation certificate faults sourceSize)
    {target : Dynamic.ResolvedPlace} {right updated : Dynamic.Value} {middle after : Dynamic.Heap}
    (snapshot : Staging.Recursive.BareTarget environment before assignment.target target)
    (trace : Staging.Recursive.Size.Expression program stages sourceSize invocation context environment before rhs (.value right) middle)
    (write : Dynamic.ResolvedPlaceWrites
      (fun _ replacement => Dynamic.AssignmentValueApplies operator target.selected right replacement)
      middle target updated after) :
    ∃ finalStore finalMap finalWorld slots,
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel (payloadModel compiled.compatible.checked registry functions) (GeneralizedLocalInstanceValues.model compiled.indexed)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model compiled.indexed) mapping world before store finalMap finalWorld after finalStore ∧
      slots.length = 7 ∧ RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) (head.writtenContext actualContext) compiled.indexed.layouts.definitions ∧
      (∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ Admission bridge context reached) ∧
      ∀ next output, ContinuationAgreement actual store ((head.emit next output).rename ξ)
        (slots ++ actual) finalStore (shift 7 (next.rename ξ)) := by
  rcases head with ⟨prepared, index, codes, leaf, lowered, node, invalid, shape, slot, writable, found, generated, rightView, rightType, profile⟩
  cases shape with
  | projected layout _ =>
    have length := CompatiblePlaceCompilerCertificates.PreparedPath.steps_length layout.path
    rw [bare, List.length_nil] at length
    exact False.elim (layout.nonempty (List.eq_nil_of_length_eq_zero length))
  | bare empty layout =>
    have sourceTyped := CallableIndexedOwnedAssignmentAdmission.rhs_typed unique found assignmentTyped
    obtain ⟨finalStore, finalMap, finalWorld, slots, rightTyped, middleTyped, finalHeaps, maps, worlds, frame, metadata, effect, count, typed, post, agreement⟩ :=
      ProtectedCellStagedBareAssignment.preserves_value_with_rhs callerProtocol transport initial layout empty extension snapshot trace write
        (fun snapshot => rhs_preserves_at bridge functions snapshot sourceSize meaning generated found sourceTyped
          environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation trace)
        rightView rightType (CallableIndexedOwnedBareAssignmentAdmission.source_profile unique found assignmentTyped rightView)
        environments (GeneralizedLocalDescriptorHeap.ordinary_cells) admitted.heap heaps locals agrees actualTyped slot writable invalid
    obtain ⟨reached, related⟩ := post
    exact ⟨finalStore, finalMap, finalWorld, slots, finalHeaps, maps, worlds, frame, metadata, effect, count,
      by simpa [GenericAssignmentStatements.Head.writtenContext, CompatibleRenamedPlaceSuccess.writtenContext, CompatibleBareAssignment.writtenContext,
        Prepared.optionalLeaf, SourceCoreCalls.packArguments, layout.sameType] using typed,
      ⟨reached, related, CallableIndexedOwnedBareAssignmentAdmission.heap_after_assignment unique found assignmentTyped
        locals snapshot middleTyped rightTyped write,
        StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) admitted.rows frame⟩,
      agreement⟩

include extension environments heaps locals agrees actualTyped initial admitted unique assignmentTyped bare authority physical owner sameLocation in
theorem preserves_fault {sourceSize : Nat}
    (meaning : PreservesAt bridge context (payloadModel compiled.compatible.checked registry functions) named stages invocation certificate faults sourceSize)
    {failure : Staging.Recursive.Failure} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Expression program stages sourceSize invocation context environment before rhs (.fault failure) after)
    (next : Expr) (output : Ty) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((head.emit next output).rename ξ) (.inLeft output (.word token)) finalStore ∧ faults failure token ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel (payloadModel compiled.compatible.checked registry functions) (GeneralizedLocalInstanceValues.model compiled.indexed)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model compiled.indexed) mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ StableRows (bridge.pool reached) := by
  rcases head with ⟨prepared, index, codes, leaf, lowered, node, invalid, shape, slot, writable, found, generated, rightView, rightType, profile⟩
  cases shape with
  | projected layout _ =>
    have length := CompatiblePlaceCompilerCertificates.PreparedPath.steps_length layout.path
    rw [bare, List.length_nil] at length
    exact False.elim (layout.nonempty (List.eq_nil_of_length_eq_zero length))
  | bare empty layout =>
    have sourceTyped := CallableIndexedOwnedAssignmentAdmission.rhs_typed unique found assignmentTyped
    obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, frame, metadata, effect, post⟩ :=
      ProtectedCellStagedBareAssignment.preserves_fault_with_rhs callerProtocol initial layout extension
        (fun snapshot => rhs_preserves_at bridge functions snapshot sourceSize meaning generated found sourceTyped
          environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation trace)
        environments (GeneralizedLocalDescriptorHeap.ordinary_cells) admitted.heap heaps locals agrees slot writable next output invalid
    obtain ⟨reached, related⟩ := post
    exact ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, frame, metadata, effect,
      reached, related, StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) admitted.rows frame⟩

include extension environments heaps locals agrees actualTyped initial admitted unique assignmentTyped bare authority physical owner sameLocation in
theorem preserves_operands {sourceSize : Nat}
    (meaning : PreservesAt bridge context (payloadModel compiled.compatible.checked registry functions) named stages invocation certificate faults sourceSize)
    {right : Dynamic.Value} {after : Dynamic.Heap} {target : Dynamic.ResolvedPlace}
    (snapshot : Staging.Recursive.BareTarget environment before assignment.target target)
    (invalidOperands : Dynamic.AssignmentOperandsInvalid operator target.selected right)
    (trace : Staging.Recursive.Size.Expression program stages sourceSize invocation context environment before rhs (.value right) after)
    (next : Expr) (output : Ty)
    (invalidToken : AssignmentOperandDiagnostics.OperandsLaw
      (fun reason token => faults (.semantic reason) token) operator head.invalid) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((head.emit next output).rename ξ) (.inLeft output (.word token)) finalStore ∧ faults (.semantic (.invalidAssignmentOperands operator)) token ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel (payloadModel compiled.compatible.checked registry functions) (GeneralizedLocalInstanceValues.model compiled.indexed)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model compiled.indexed) mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ StableRows (bridge.pool reached) := by
  rcases head with ⟨prepared, index, codes, leaf, lowered, node, invalid, shape, slot, writable, found, generated, rightView, rightType, profile⟩
  cases shape with
  | projected layout _ =>
    have length := CompatiblePlaceCompilerCertificates.PreparedPath.steps_length layout.path
    rw [bare, List.length_nil] at length
    exact False.elim (layout.nonempty (List.eq_nil_of_length_eq_zero length))
  | bare empty layout =>
    have sourceTyped := CallableIndexedOwnedAssignmentAdmission.rhs_typed unique found assignmentTyped
    obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, frame, metadata, effect, post⟩ :=
      ProtectedCellStagedBareAssignment.preserves_operands_with_rhs callerProtocol initial layout empty extension snapshot invalidOperands
        (fun snapshot => rhs_preserves_at bridge functions snapshot sourceSize meaning generated found sourceTyped
          environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation trace)
        rightView rightType (CallableIndexedOwnedBareAssignmentAdmission.source_profile unique found assignmentTyped rightView)
        environments (GeneralizedLocalDescriptorHeap.ordinary_cells) admitted.heap heaps locals agrees slot writable next output invalid invalidToken
    obtain ⟨reached, related⟩ := post
    exact ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, frame, metadata, effect,
      reached, related, StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) admitted.rows frame⟩

end Heads
end Solcore.SourceSemantics.CoreLowering.CellAwareScopeBareAssignmentHeads
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareScopeForInitialBounds
/-! Actual initializer prefixes keep their bindings through the finite loop,
then restore the original lexical observations with the reached mixed heap. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareScopeForInitialBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)
open CallableIndexedOwnedAdmittedStagedForHeadContracts (Trace)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {protocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (context : SourceSemantics.Context)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  (model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions)
  (named : SourceCoreGeneralFunctions.Function)
  (producer : ProtectedStateTransition.CellAllocation.Producer (catalog := catalog) protocol compiled.indexed.layouts
    compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)))
  (registry : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
  (faults : RecursiveStageMeaning.FaultRep) (administrative : Core.Context)
  (scope : SourceCoreLocalCell.Scope) (items : List ForItemForm)
  (test : ExpressionId) (postItems : List ForItemForm) (statements : List StatementId)
  (expected : TypeSystem.Ty) (type : Ty) (code : Expr)

/-- Source and native grades remain independent. Every reached branch keeps
its exact mixed heap and restores the caller's lexical observations. -/
def PreservesAt (size : Nat) : Prop :=
  ∀ {mapping world actualContext environment canonical actual before store embedding},
    DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical compiled.indexed.layouts.definitions →
    GenericHeap.CellHeapRepresents
      (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)) mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree embedding canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions →
    Dynamic.SourceRuntimeValid program context (CallableIndexedNamedGeneration.source named) →
    invocation.evidence.Covers context →
    context.solvedRequirements = (CallableIndexedNamedGeneration.context compiled.indexed named).solvedRequirements →
    ∀ initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩,
      Admission bridge context initial →
      CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model compiled.indexed)
        named.signature.key [] mapping world before store environment →
    ∀ physical : CellAwareScopePhysical.Physical compiled named context scope canonical mapping world before store environment,
    ∀ owner : CallableIndexedOwnedFunctionValues.OwnedKey keys,
      owner.key.frameLocation = physical.location →
      ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native →
    ∀ {outcome after},
      Trace program registry invocation context environment before items test postItems statements size outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename embedding) value finalStore ∧
      Represents model finalMap finalWorld false expected type faults outcome value ∧
      GenericHeap.CellHeapRepresents
        (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed))
        finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model compiled.indexed)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : protocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        protocol.Relates initial reached ∧ Post bridge context expected outcome reached

/-- Actual native completion reconstructs the chosen Source branch and its
real allocations, failures and control transfers. -/
def ReflectsAt (size : Nat) : Prop :=
  ∀ {mapping world actualContext environment canonical actual before store embedding value finalStore},
    DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical compiled.indexed.layouts.definitions →
    GenericHeap.CellHeapRepresents
      (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)) mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree embedding canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions →
    Dynamic.SourceRuntimeValid program context (CallableIndexedNamedGeneration.source named) →
    invocation.evidence.Covers context →
    context.solvedRequirements = (CallableIndexedNamedGeneration.context compiled.indexed named).solvedRequirements →
    ∀ initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩,
      Admission bridge context initial →
      CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model compiled.indexed)
        named.signature.key [] mapping world before store environment →
    ∀ physical : CellAwareScopePhysical.Physical compiled named context scope canonical mapping world before store environment,
    ∀ owner : CallableIndexedOwnedFunctionValues.OwnedKey keys,
      owner.key.frameLocation = physical.location →
      ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native →
    EvaluationSize size actual store (code.rename embedding) value finalStore →
    ∃ sourceSize outcome after finalMap finalWorld,
      Trace program registry invocation context environment before items test postItems statements sourceSize outcome after ∧
      Represents model finalMap finalWorld false expected type faults outcome value ∧
      GenericHeap.CellHeapRepresents
        (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed))
        finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model compiled.indexed)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : protocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        protocol.Relates initial reached ∧ Post bridge context expected outcome reached

def PreservesAtMost (budget : Nat) : Prop :=
  ∀ size, size ≤ budget → PreservesAt bridge context model named producer registry invocation faults administrative scope items test postItems statements expected type code size

def PreservesBelow (budget : Nat) : Prop :=
  ∀ size, size < budget → PreservesAt bridge context model named producer registry invocation faults administrative scope items test postItems statements expected type code size

def ReflectsAtMost (budget : Nat) : Prop :=
  ∀ size, size ≤ budget → ReflectsAt bridge context model named producer registry invocation faults administrative scope items test postItems statements expected type code size

def ReflectsBelow (budget : Nat) : Prop :=
  ∀ size, size < budget → ReflectsAt bridge context model named producer registry invocation faults administrative scope items test postItems statements expected type code size

end Solcore.SourceSemantics.CoreLowering.CellAwareScopeForInitialBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareScopeProjectedAssignmentHeads
/-! Projected assignment heads run the ordered staged key row and the RHS at
their actual reached callers. A successful write keeps the saved target path,
the latest root and all compiler temporary slots. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareScopeProjectedAssignmentHeads
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality CompatibleHeap CoreProof ReadOnly
open SourceCoreCompatibleDataPlaces GenericExpressionMeaning
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CellAwareScopeExpressionBounds
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)

variable {functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
  {registry : SourceCoreRawMetadata.Registry} {named : SourceCoreGeneralFunctions.Function}

section Rhs
variable {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {prepared : Prepared} {place : PlaceResolution} {environment : Dynamic.Environment} {actual : Environment}
  {before targetHeap : Dynamic.Heap} {store : Store} {mapping : LocationMap} {world : StoreTyping}
  {faults : RecursiveStageMeaning.FaultRep} {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr} {ξ : Renaming}
  {scope : Scope} {administrativeContext actualContext : Core.Context} {canonical : Environment}
  {certificate : Certificate} {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty}
  {leaf : TypeSystem.Ty} {target : Dynamic.ResolvedPlace}
  (resolution : CompatibleCellPlaceResolution.Execution compiled.compatible.checked registry functions (GeneralizedLocalDescriptorHeap.cellModel (payloadModel compiled.compatible.checked registry functions) (GeneralizedLocalInstanceValues.model compiled.indexed)) (GeneralizedLocalInstanceValues.model compiled.indexed) prepared
    (CompatibleRenamedPlace.renamedCodes codes ξ) sourceTypes place leaf target actual store mapping world before targetHeap)

structure RhsResult (sourceSize : Nat) (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap) (value : Value)
    (finalStore : Store) (finalMap : LocationMap) (finalWorld : StoreTyping) : Prop where
  trace : Staging.Recursive.Size.Expression program stages sourceSize invocation context environment targetHeap id outcome after
  evaluated : Evaluates
    (DataPlaceExecution.snapshotEnvironment prepared.route.rootType resolution.target (DataPatternValues.packValues resolution.values)
      (.inRight .unit resolution.snapshot) actual)
    resolution.store (shift 3 (lowered.expression.rename ξ)) value finalStore
  represented : RecursiveStageMeaning.ResultRepresentsFor (payloadModel compiled.compatible.checked registry functions)
    finalMap finalWorld node.type lowered.type faults outcome value
  heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel (payloadModel compiled.compatible.checked registry functions) (GeneralizedLocalInstanceValues.model compiled.indexed)) finalMap finalWorld after finalStore
  maps : LocationMap.Extends resolution.mapping finalMap
  worlds : WorldExtends resolution.world finalWorld
  frame : AdministrativePreserved resolution.mapping resolution.store finalMap finalStore
  metadata : Dynamic.HeapMetadataExtend targetHeap after
  effect : CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model compiled.indexed) resolution.mapping resolution.world targetHeap resolution.store finalMap finalWorld after finalStore
  sourcePost : ∀ right, outcome = .value right →
    Dynamic.ValueHasType context after right node.type ∧ Dynamic.HeapWellTyped context after

theorem rhs_preserves_at (size : Nat)
    (meaning : PreservesAt bridge context (payloadModel compiled.compatible.checked registry functions) named stages invocation certificate faults size)
    (generated : certificate scope id lowered) (found : invocation.source.lookupExpression? id = some node)
    (sourceTyped : ExpressionHasType invocation.source context id node.type)
    (environments : DataHeap.EnvRepresents (definitions := compiled.indexed.layouts.definitions) (storageCatalog compiled.compatible.checked.catalog)
      resolution.mapping resolution.world administrativeContext scope environment canonical)
    (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel (payloadModel compiled.compatible.checked registry functions) (GeneralizedLocalInstanceValues.model compiled.indexed)) resolution.mapping resolution.world targetHeap resolution.store)
    (locals : Dynamic.EnvironmentAgrees targetHeap context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
    (initial : callerProtocol.State ⟨scope, resolution.mapping, resolution.world, targetHeap, resolution.store, canonical⟩)
    (admitted : Admission bridge context initial)
    (authority : CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model compiled.indexed) named.signature.key [] resolution.mapping resolution.world targetHeap resolution.store environment)
    (physical : CellAwareScopePhysical.Physical compiled named context scope canonical resolution.mapping resolution.world targetHeap resolution.store environment)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (ownerFrame : owner.key.frameLocation = physical.location)
    {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Expression program stages size invocation context environment targetHeap id outcome after) :
    ∃ value finalStore finalMap finalWorld,
      RhsResult (environment := environment) (program := program) (context := context)
        (stages := stages) (invocation := invocation) (faults := faults) (id := id) (node := node) (lowered := lowered)
        resolution size outcome after value finalStore finalMap finalWorld ∧
      ProtectedStateTransition.Transition callerProtocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata,
      effect, reached, related, post⟩ :=
    meaning generated found sourceTyped environments heaps locals
      (DataPlaceChildExpressions.prefix_agrees agrees
        [.inRight .unit resolution.snapshot, DataPatternValues.packValues resolution.values, .cellRef (OptionalCell.cellType prepared.route.rootType) resolution.target])
      (.cons (.inRight resolution.snapshotRelated.runtime_hasType)
        (.cons (CompatiblePlaceResolution.values_typed resolution.keysRelated)
          (.cons (.cellRef resolution.reference.typed) (actualTyped.weaken resolution.worlds)))) initial admitted authority physical owner ownerFrame trace
  refine ⟨value, finalStore, finalMap, finalWorld,
    ⟨trace, ?_, represented, finalHeaps, maps, worlds, frame, metadata, effect, ?_⟩, reached, related⟩
  · simpa only [DataPlaceChildExpressions.rename_prefix, List.length_cons, List.length_nil,
    List.cons_append, List.nil_append, DataPlaceExecution.snapshotEnvironment,
    DataPlaceExecution.keysEnvironment, DataPlaceExecution.referenceEnvironment,
    SourceCoreDataPlaces.shift, shift, Nat.zero_add] using evaluated
  · intro right same
    cases same
    exact ⟨post.at_value.1, post.at_value.2.heap⟩

theorem rhs_reflects_at (size : Nat)
    (meaning : ReflectsAt bridge context (payloadModel compiled.compatible.checked registry functions) named stages invocation certificate faults size)
    (generated : certificate scope id lowered) (found : invocation.source.lookupExpression? id = some node)
    (sourceTyped : ExpressionHasType invocation.source context id node.type)
    (environments : DataHeap.EnvRepresents (definitions := compiled.indexed.layouts.definitions) (storageCatalog compiled.compatible.checked.catalog)
      resolution.mapping resolution.world administrativeContext scope environment canonical)
    (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel (payloadModel compiled.compatible.checked registry functions) (GeneralizedLocalInstanceValues.model compiled.indexed)) resolution.mapping resolution.world targetHeap resolution.store)
    (locals : Dynamic.EnvironmentAgrees targetHeap context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
    (initial : callerProtocol.State ⟨scope, resolution.mapping, resolution.world, targetHeap, resolution.store, canonical⟩)
    (admitted : Admission bridge context initial)
    (authority : CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model compiled.indexed) named.signature.key [] resolution.mapping resolution.world targetHeap resolution.store environment)
    (physical : CellAwareScopePhysical.Physical compiled named context scope canonical resolution.mapping resolution.world targetHeap resolution.store environment)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (ownerFrame : owner.key.frameLocation = physical.location)
    {value : Value} {finalStore : Store}
    (evaluated : EvaluationSize size
      (DataPlaceExecution.snapshotEnvironment prepared.route.rootType resolution.target (DataPatternValues.packValues resolution.values) (.inRight .unit resolution.snapshot) actual)
      resolution.store (shift 3 (lowered.expression.rename ξ)) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RhsResult (environment := environment) (program := program) (context := context)
        (stages := stages) (invocation := invocation) (faults := faults) (id := id) (node := node) (lowered := lowered)
        resolution sourceSize outcome after value finalStore finalMap finalWorld ∧
      ProtectedStateTransition.Transition callerProtocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata,
      effect, reached, related, post⟩ :=
    meaning generated found sourceTyped environments heaps locals
      (DataPlaceChildExpressions.prefix_agrees agrees
        [.inRight .unit resolution.snapshot, DataPatternValues.packValues resolution.values, .cellRef (OptionalCell.cellType prepared.route.rootType) resolution.target])
      (.cons (.inRight resolution.snapshotRelated.runtime_hasType)
        (.cons (CompatiblePlaceResolution.values_typed resolution.keysRelated)
          (.cons (.cellRef resolution.reference.typed) (actualTyped.weaken resolution.worlds)))) initial admitted authority physical owner ownerFrame
      (by simpa only [DataPlaceChildExpressions.rename_prefix, List.length_cons, List.length_nil,
        List.cons_append, List.nil_append, DataPlaceExecution.snapshotEnvironment,
        DataPlaceExecution.keysEnvironment, DataPlaceExecution.referenceEnvironment,
        SourceCoreDataPlaces.shift, shift, Nat.zero_add] using evaluated)
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld,
    ⟨trace, evaluated.sound, represented, finalHeaps, maps, worlds, frame, metadata, effect, by
      intro right same
      cases same
      exact ⟨post.at_value.1, post.at_value.2.heap⟩⟩, reached, related⟩
end Rhs

theorem tree_typed {source : TypedSource} {context : SourceSemantics.Context}
    {certificate : Certificate} {scope : Scope} {ids : List ExpressionId} {types original : List TypeSystem.Ty}
    {codes : List SourceCoreBasic.LoweredExpr}
    (tree : DataExpressionSequence.Tree source certificate scope ids types codes)
    (unique : NodeOccurrencesUnique source) (typed : ExpressionsHaveTypes source context ids original) :
    ExpressionsHaveTypes source context ids types := by
  have members : ∀ id, id ∈ ids → ∀ node, source.lookupExpression? id = some node → ExpressionHasType source context id node.type :=
    fun _ member _ found => CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique typed member found
  clear typed
  induction tree with
  | nil => exact .nil _
  | single found _ => exact .cons (members _ (by simp) _ found) (.nil _)
  | cons found _ _ ih =>
      exact .cons (members _ (by simp) _ found) (ih (fun id member => members id (List.mem_cons_of_mem _ member)))

inductive ResultAt (size : Nat)
    (context : SourceSemantics.Context) (stages : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
    (faults : RecursiveStageMeaning.FaultRep) (scope : Scope) (writtenContext : Core.Context)
    (assignment : AssignmentResolution) (operator : Syntax.ValueAssignOp) (rhs : ExpressionId)
    (environment : Dynamic.Environment) (canonical actual : Environment)
    (before : Dynamic.Heap) (store : Store) (mapping : LocationMap) (world : StoreTyping)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (next : Expr) (output : Ty) (value : Value) (finalStore : Store) : Prop where
  | keyFault {keySize : Nat} {failure : Staging.Recursive.Failure} {token : Word} {after : Dynamic.Heap}
      {finalMap : LocationMap} {finalWorld : StoreTyping}
      (ready : Staging.Recursive.ProjectedTarget.RootReady environment before assignment.target)
      (trace : Staging.Recursive.Size.Expressions program stages keySize invocation context environment before
        (Staging.Recursive.ProjectedTarget.keys assignment.target.projections) (.fault failure) after)
      (same : value = .inLeft output (.word token)) (matched : faults failure token)
      (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel (payloadModel compiled.compatible.checked registry functions) (GeneralizedLocalInstanceValues.model compiled.indexed)) finalMap finalWorld after finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap finalStore) (metadata : Dynamic.HeapMetadataExtend before after)
      (effect : CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model compiled.indexed) mapping world before store finalMap finalWorld after finalStore)
      (reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (related : callerProtocol.Relates initial reached) (stable : StableRows (bridge.pool reached)) :
      ResultAt size context stages invocation faults scope writtenContext assignment operator rhs
        environment canonical actual before store mapping world initial next output value finalStore
  | getterFault {keySize : Nat} {sources : List Dynamic.Value} {reason : Dynamic.SemanticFault} {token : Word} {after : Dynamic.Heap}
      {finalMap : LocationMap} {finalWorld : StoreTyping}
      (trace : Staging.Recursive.Size.Expressions program stages keySize invocation context environment before
        (Staging.Recursive.ProjectedTarget.keys assignment.target.projections) (.values sources) after)
      (failed : Staging.Recursive.ProjectedTarget.GetterFault environment before after assignment.target sources reason)
      (same : value = .inLeft output (.word token)) (matched : faults (.semantic reason) token)
      (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel (payloadModel compiled.compatible.checked registry functions) (GeneralizedLocalInstanceValues.model compiled.indexed)) finalMap finalWorld after finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap finalStore) (metadata : Dynamic.HeapMetadataExtend before after)
      (effect : CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model compiled.indexed) mapping world before store finalMap finalWorld after finalStore)
      (reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (related : callerProtocol.Relates initial reached) (stable : StableRows (bridge.pool reached)) :
      ResultAt size context stages invocation faults scope writtenContext assignment operator rhs
        environment canonical actual before store mapping world initial next output value finalStore
  | rhsFault {keySize sourceSize : Nat} {target : Dynamic.ResolvedPlace}
      {failure : Staging.Recursive.Failure} {token : Word} {after : Dynamic.Heap}
      {finalMap : LocationMap} {finalWorld : StoreTyping}
      {sources : List Dynamic.Value} {targetHeap : Dynamic.Heap}
      (keys : Staging.Recursive.Size.Expressions program stages keySize invocation context environment before
        (Staging.Recursive.ProjectedTarget.keys assignment.target.projections) (.values sources) targetHeap)
      (snapshot : Staging.Recursive.ProjectedTarget.Snapshot environment before targetHeap assignment.target sources target)
      (trace : Staging.Recursive.Size.Expression program stages sourceSize invocation context environment targetHeap rhs (.fault failure) after)
      (same : value = .inLeft output (.word token)) (matched : faults failure token)
      (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel (payloadModel compiled.compatible.checked registry functions) (GeneralizedLocalInstanceValues.model compiled.indexed)) finalMap finalWorld after finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap finalStore) (metadata : Dynamic.HeapMetadataExtend before after)
      (effect : CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model compiled.indexed) mapping world before store finalMap finalWorld after finalStore)
      (reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (related : callerProtocol.Relates initial reached) (stable : StableRows (bridge.pool reached)) :
      ResultAt size context stages invocation faults scope writtenContext assignment operator rhs
        environment canonical actual before store mapping world initial next output value finalStore
  | writeFault {keySize sourceSize : Nat} {target : Dynamic.ResolvedPlace}
      {right : Dynamic.Value} {after : Dynamic.Heap}
      {token : Word}
      {finalMap : LocationMap} {finalWorld : StoreTyping}
      {sources : List Dynamic.Value} {targetHeap : Dynamic.Heap}
      (keys : Staging.Recursive.Size.Expressions program stages keySize invocation context environment before
        (Staging.Recursive.ProjectedTarget.keys assignment.target.projections) (.values sources) targetHeap)
      (snapshot : Staging.Recursive.ProjectedTarget.Snapshot environment before targetHeap assignment.target sources target)
      (trace : Staging.Recursive.Size.Expression program stages sourceSize invocation context environment targetHeap rhs (.value right) after)
      {reason : Dynamic.SemanticFault}
      (failed : Staging.Recursive.ProjectedTarget.WriteFault operator target right after reason)
      (same : value = .inLeft output (.word token)) (matched : faults (.semantic reason) token)
      (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel (payloadModel compiled.compatible.checked registry functions) (GeneralizedLocalInstanceValues.model compiled.indexed)) finalMap finalWorld after finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap finalStore) (metadata : Dynamic.HeapMetadataExtend before after)
      (effect : CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model compiled.indexed) mapping world before store finalMap finalWorld after finalStore)
      (reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (related : callerProtocol.Relates initial reached) (stable : StableRows (bridge.pool reached)) :
      ResultAt size context stages invocation faults scope writtenContext assignment operator rhs
        environment canonical actual before store mapping world initial next output value finalStore
  | success {keySize sourceSize remainingSize : Nat} {target : Dynamic.ResolvedPlace}
      {right updated : Dynamic.Value} {middle after : Dynamic.Heap}
      {written : Store} {finalMap : LocationMap} {finalWorld : StoreTyping} {slots : Environment}
      {sources : List Dynamic.Value} {targetHeap : Dynamic.Heap}
      (keys : Staging.Recursive.Size.Expressions program stages keySize invocation context environment before
        (Staging.Recursive.ProjectedTarget.keys assignment.target.projections) (.values sources) targetHeap)
      (snapshot : Staging.Recursive.ProjectedTarget.Snapshot environment before targetHeap assignment.target sources target)
      (trace : Staging.Recursive.Size.Expression program stages sourceSize invocation context environment targetHeap rhs (.value right) middle)
      (write : Dynamic.ResolvedPlaceWrites
        (fun _ replacement => Dynamic.AssignmentValueApplies operator target.selected right replacement)
        middle target updated after)
      (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel (payloadModel compiled.compatible.checked registry functions) (GeneralizedLocalInstanceValues.model compiled.indexed)) finalMap finalWorld after written)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap written) (metadata : Dynamic.HeapMetadataExtend before after)
      (effect : CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model compiled.indexed) mapping world before store finalMap finalWorld after written)
      (count : slots.length = 7)
      (typed : RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) writtenContext compiled.indexed.layouts.definitions)
      (reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, written, canonical⟩)
      (related : callerProtocol.Relates initial reached) (admitted : Admission bridge context reached)
      (bounded : remainingSize < size)
      (remaining : EvaluationSize remainingSize (slots ++ actual) written (shift 7 next) value finalStore) :
      ResultAt size context stages invocation faults scope writtenContext assignment operator rhs
        environment canonical actual before store mapping world initial next output value finalStore

end Solcore.SourceSemantics.CoreLowering.CellAwareScopeProjectedAssignmentHeads
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareScopeProjectedAssignmentResolution
/-! The actual staged key row and RHS produce the physical write and its
reached admission. Structural faults retain their actual diagnostic phase. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareScopeProjectedAssignmentHeads
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality CompatibleHeap CoreProof ReadOnly
open SourceCoreCompatibleDataPlaces GenericExpressionMeaning CompatibleRenamedPlace DataPatternValues DataPlaceExecution
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CellAwareScopeExpressionBounds
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)

section Rhs
variable {registry : SourceCoreRawMetadata.Registry} {named : SourceCoreGeneralFunctions.Function}
  {functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {prepared : Prepared} {place : PlaceResolution} {environment : Dynamic.Environment} {actual : Environment}
  {before targetHeap : Dynamic.Heap} {store : Store} {mapping : LocationMap} {world : StoreTyping}
  {faults : RecursiveStageMeaning.FaultRep} {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr} {ξ : Renaming}
  {scope : Scope} {administrativeContext actualContext : Core.Context} {canonical : Environment}
  {certificate : Certificate} {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty}
  {leaf : TypeSystem.Ty} {target : Dynamic.ResolvedPlace}
  (resolution : CompatibleCellPlaceResolution.Execution compiled.compatible.checked registry functions (GeneralizedLocalDescriptorHeap.cellModel (payloadModel compiled.compatible.checked registry functions) (GeneralizedLocalInstanceValues.model compiled.indexed)) (GeneralizedLocalInstanceValues.model compiled.indexed) prepared
    (CompatibleRenamedPlace.renamedCodes codes ξ) sourceTypes place leaf target actual store mapping world before targetHeap)


/-- Only an actual successful staged RHS is erased to the ordinary suffix
receipt. Its current root is read from the actual represented RHS heap. -/
theorem RhsResult.to_ordinary_value {size : Nat} {right : Dynamic.Value} {after : Dynamic.Heap}
    {native : Value} {finalStore : Store} {finalMap : LocationMap} {finalWorld : StoreTyping}
    (result : RhsResult (program := program) (context := context) (stages := stages)
      (invocation := invocation) (faults := faults) (id := id) (node := node) (lowered := lowered)
      (environment := environment) resolution size (.value right) after native finalStore finalMap finalWorld) :
    CompatibleCellPlaceRhs.Result (program := program) (context := context)
      (evidence := invocation.evidence) (source := invocation.source)
      (faults := fun reason token => faults (.semantic reason) token)
      resolution id node (renamed lowered ξ) environment (.value right) after native finalStore finalMap finalWorld := by
  refine ⟨.value result.trace.sound.value_plain, result.evaluated, ?_, result.heaps,
    result.maps, result.worlds, result.frame, result.metadata, result.effect, ?_⟩
  · cases result.represented with
    | value related => exact .value related
  · exact CompatibleCellPlaceRhs.latest_of_heap resolution GeneralizedLocalDescriptorHeap.ordinary_cells
      result.heaps result.maps result.worlds result.metadata
end Rhs

section Resolution
variable {registry : SourceCoreRawMetadata.Registry} {named : SourceCoreGeneralFunctions.Function}
  {functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : Certificate} {faults : RecursiveStageMeaning.FaultRep} {scope : Scope}
  {site : SourceCoreElaboration.ErrorSite} {place : PlaceResolution} {prepared : Prepared}
  {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
  {rhsType : Core.Ty} {administrative actualContext : Core.Context} {ξ : Renaming}
  {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment}
  {canonical actual : Environment} {before getter : Dynamic.Heap} {store : Store} {index : Nat}
  {target : Dynamic.ResolvedPlace} {sources : List Dynamic.Value}

/-- The independent ordered key trace determines the getter state before any
RHS execution. The original key value types and deep heap typing are retained. -/
theorem preserves_keys (budget : Nat)
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := compiled.indexed.layouts.definitions) (.initial compiled.compatible.checked) invocation.source
      certificate scope site place prepared codes sourceTypes leaf administrative rhsType)
    (environments : DataHeap.EnvRepresents (definitions := compiled.indexed.layouts.definitions) (storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical)
    (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel (payloadModel compiled.compatible.checked registry functions) (GeneralizedLocalInstanceValues.model compiled.indexed)) mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (authority : CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model compiled.indexed) named.signature.key [] mapping world before store environment)
    (physical : CellAwareScopePhysical.Physical compiled named context scope canonical mapping world before store environment)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (ownerFrame : owner.key.frameLocation = physical.location)
    (unique : NodeOccurrencesUnique invocation.source)
    {originalTypes : List TypeSystem.Ty}
    (originalKeyTyped : ExpressionsHaveTypes invocation.source context (DataPlaceKeyOrder.sourceKeys place.projections) originalTypes)
    (meaning : PreservesBelow bridge context (payloadModel compiled.compatible.checked registry functions) named stages invocation certificate faults budget)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (writable : WritableLocal context place.root prepared.route.rootSourceType)
    {keySize : Nat}
    (keyTrace : Staging.Recursive.Size.Expressions program stages keySize invocation context environment before
      (Staging.Recursive.ProjectedTarget.keys place.projections) (.values sources) getter)
    (keyBound : keySize ≤ budget)
    {location : Dynamic.Location} {initialCell : Dynamic.Cell} {resolved : List Dynamic.EvaluatedProjection}
    (lookup : Dynamic.Environment.LooksUp environment place.root location)
    (initialRead : Dynamic.Heap.Reads before location initialCell)
    (ordered : Staging.Recursive.ProjectedTarget.Values place.projections sources resolved) :
    ∃ execution : CompatibleCellPlaceTargetKeys.Execution compiled.compatible.checked registry functions (GeneralizedLocalDescriptorHeap.cellModel (payloadModel compiled.compatible.checked registry functions) (GeneralizedLocalInstanceValues.model compiled.indexed)) (GeneralizedLocalInstanceValues.model compiled.indexed) prepared place
      (renamedCodes codes ξ) sourceTypes location resolved actual before getter store mapping world (ξ index),
      Dynamic.ValuesHaveTypes context getter sources sourceTypes ∧ Dynamic.HeapWellTyped context getter ∧
      ∃ reached : callerProtocol.State ⟨scope, execution.keyMap, execution.keyWorld, getter, execution.keyStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ Admission bridge context reached := by
  obtain ⟨target, selected, reference⟩ := environments.lookup_visible lookup slot
  obtain ⟨native, keyStore, keyMap, keyWorld, evaluated, represented, keyHeaps,
    maps, worlds, frame, metadata, effect, typed, reached, related, post⟩ :=
    CellAwareScopeTypedExpressionSequence.preserves_values bridge budget
      layout.children unique originalKeyTyped meaning environments heaps locals
      (DataPlaceChildExpressions.prefix_agrees agrees [.cellRef (OptionalCell.cellType prepared.route.rootType) target])
      (.cons (.cellRef reference.typed) actualTyped) initial admitted authority physical owner ownerFrame
      (by simpa only [Staging.Recursive.ProjectedTarget.keys_eq_sourceKeys] using keyTrace) keyBound
  obtain ⟨scheme, staticLookup, _wellFormed, monomorphic, bodyEq⟩ := writable.scheme
  obtain ⟨staticLocation, staticCell, staticLookupRuntime, staticRead, staticCellType, _⟩ := locals.lookup staticLookup
  cases lookup.functional staticLookupRuntime
  cases initialRead.functional staticRead
  obtain ⟨cell, read, sameType, _⟩ := metadata _ _ initialRead
  refine ⟨⟨target, sources, native, keyStore, keyMap, keyWorld, cell, read,
    (locals.mono metadata).descriptor_empty_of_monomorphic post.at_values.heap staticLookup lookup read monomorphic,
    sameType.trans (staticCellType.trans bodyEq), reference.extend maps worlds, agrees selected,
    ordered.to_data, ?_, ?_, keyHeaps, maps, worlds, frame, metadata, effect⟩,
    typed, post.at_values.heap, reached, related, post.at_values⟩
  · simpa only [DataPlaceChildExpressions.rename_prefix, packed_renamed_expression, List.length_cons, List.length_nil,
      List.cons_append, List.nil_append, referenceEnvironment, SourceCoreDataPlaces.shift, shift, Nat.zero_add] using evaluated
  · simpa only [renamedCodes_types, CallableIndexedAmbient.ambientDefinitions] using represented

theorem preserves_resolution (budget : Nat)
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := compiled.indexed.layouts.definitions) (.initial compiled.compatible.checked) invocation.source
      certificate scope site place prepared codes sourceTypes leaf administrative rhsType)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
    (transport : ProtectedStateTransition.AdministrativeTransport callerProtocol)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compiled.compatible.checked.catalog functions identities)
    (environments : DataHeap.EnvRepresents (definitions := compiled.indexed.layouts.definitions) (storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical)
    (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel (payloadModel compiled.compatible.checked registry functions) (GeneralizedLocalInstanceValues.model compiled.indexed)) mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (authority : CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model compiled.indexed) named.signature.key [] mapping world before store environment)
    (physical : CellAwareScopePhysical.Physical compiled named context scope canonical mapping world before store environment)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (ownerFrame : owner.key.frameLocation = physical.location)
    (unique : NodeOccurrencesUnique invocation.source)
    {originalTypes : List TypeSystem.Ty}
    (originalKeyTyped : ExpressionsHaveTypes invocation.source context (DataPlaceKeyOrder.sourceKeys place.projections) originalTypes)
    (meaning : PreservesBelow bridge context (payloadModel compiled.compatible.checked registry functions) named stages invocation certificate faults budget)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (writable : WritableLocal context place.root prepared.route.rootSourceType)
    {keySize : Nat}
    (keyTrace : Staging.Recursive.Size.Expressions program stages keySize invocation context environment before
      (Staging.Recursive.ProjectedTarget.keys place.projections) (.values sources) getter)
    (keyBound : keySize ≤ budget)
    (snapshot : Staging.Recursive.ProjectedTarget.Snapshot environment before getter place sources target) :
    ∃ resolution : CompatibleCellPlaceResolution.Execution compiled.compatible.checked registry functions (GeneralizedLocalDescriptorHeap.cellModel (payloadModel compiled.compatible.checked registry functions) (GeneralizedLocalInstanceValues.model compiled.indexed)) (GeneralizedLocalInstanceValues.model compiled.indexed) prepared
      (renamedCodes codes ξ) sourceTypes place leaf target actual store mapping world before getter,
      resolution.sources = sources ∧ Dynamic.ValuesHaveTypes context getter sources sourceTypes ∧
      Dynamic.HeapWellTyped context getter ∧
      actual[ξ index]? = some (.cellRef (OptionalCell.cellType prepared.route.rootType) resolution.target) ∧
      ∃ reached : callerProtocol.State ⟨scope, resolution.mapping, resolution.world, getter, resolution.store, canonical⟩,
        callerProtocol.Relates initial reached ∧ Admission bridge context reached := by
  obtain ⟨resolution, sameSources, keyValues, keyHeap, coreLookup, reached, related⟩ :=
    CellAwareStagedProjectedResolution.preserves GeneralizedLocalDescriptorHeap.ordinary_cells layout.path layout.views layout.keyTypes layout.leafProjected
      layout.virtual extension layout.nonempty
      (CompatibleRenamedPlace.getter_typed layout (CompatibleRenamedPlace.virtual_closed layout ordinary)
        (CompatibleRenamedPlace.environment_respects environments.runtime_hasTypes actualTyped agrees))
      callerProtocol transport faithful observations environments locals agrees actualTyped initial
      (fun target _ hiddenTyped => by
        obtain ⟨native, keyStore, keyMap, keyWorld, evaluated, represented, keyHeaps,
          maps, worlds, frame, metadata, effect, typed, reached, related, post⟩ :=
          CellAwareScopeTypedExpressionSequence.preserves_values bridge budget
            layout.children unique originalKeyTyped meaning environments heaps locals
            (DataPlaceChildExpressions.prefix_agrees agrees [.cellRef (OptionalCell.cellType prepared.route.rootType) target])
            hiddenTyped initial admitted authority physical owner ownerFrame
            (by simpa only [Staging.Recursive.ProjectedTarget.keys_eq_sourceKeys] using keyTrace) keyBound
        exact ⟨native, keyStore, keyMap, keyWorld, evaluated, represented, keyHeaps, maps, worlds,
          frame, metadata, typed, post.at_values.heap, effect, reached, related⟩)
      slot writable snapshot
  exact ⟨resolution, sameSources, keyValues, keyHeap, coreLookup, reached, related, keyHeap,
    StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) admitted.rows resolution.frame⟩
end Resolution

end Solcore.SourceSemantics.CoreLowering.CellAwareScopeProjectedAssignmentHeads
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareScopeProjectedAssignmentPreservation
/-! The actual staged key row and RHS produce the physical write and its
reached admission. Structural faults retain their actual diagnostic phase. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareScopeProjectedAssignmentHeads
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality CompatibleHeap CoreProof ReadOnly
open SourceCoreCompatibleDataPlaces GenericExpressionMeaning CompatibleRenamedPlace DataPatternValues DataPlaceExecution
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CellAwareScopeExpressionBounds
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)

section Heads
variable {named : SourceCoreGeneralFunctions.Function}
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : Certificate} {scope : Scope} {administrative : Core.Context}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {faults : RecursiveStageMeaning.FaultRep}
  (transport : ProtectedStateTransition.AdministrativeTransport callerProtocol)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : FunctionObservations compiled.compatible.checked.catalog functions identities)
  {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
  (head : GenericAssignmentStatements.Head (.initial compiled.compatible.checked) invocation.source context certificate scope administrative compiled.indexed.layouts.definitions assignment operator rhs)
  (projected : assignment.target.projections ≠ [])
  {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment}
  {canonical actual : Environment} {before : Dynamic.Heap} {store : Store} {actualContext : Core.Context} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (definitions := compiled.indexed.layouts.definitions) (storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical)
  (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel (payloadModel compiled.compatible.checked registry functions) (GeneralizedLocalInstanceValues.model compiled.indexed)) mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)
  (authority : CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model compiled.indexed) named.signature.key [] mapping world before store environment)
  (physical : CellAwareScopePhysical.Physical compiled named context scope canonical mapping world before store environment)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (ownerFrame : owner.key.frameLocation = physical.location)
  (unique : NodeOccurrencesUnique invocation.source)
  (assignmentTyped : SourceAssignmentHasType invocation.source context assignment operator rhs)


include transport extension environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame unique assignmentTyped projected faithful observations in
theorem preserves_value (budget : Nat)
    (meaning : PreservesBelow bridge context (payloadModel compiled.compatible.checked registry functions) named stages invocation certificate faults budget)
    {keySize rhsSize : Nat} {sources : List Dynamic.Value}
    {target : Dynamic.ResolvedPlace} {right updated : Dynamic.Value} {getter middle after : Dynamic.Heap}
    (keyTrace : Staging.Recursive.Size.Expressions program stages keySize invocation context environment before
      (Staging.Recursive.ProjectedTarget.keys assignment.target.projections) (.values sources) getter)
    (keyBound : keySize ≤ budget)
    (snapshot : Staging.Recursive.ProjectedTarget.Snapshot environment before getter assignment.target sources target)
    (trace : Staging.Recursive.Size.Expression program stages rhsSize invocation context environment getter rhs (.value right) middle)
    (rhsBound : rhsSize < budget)
    (write : Dynamic.ResolvedPlaceWrites
      (fun _ replacement => Dynamic.AssignmentValueApplies operator target.selected right replacement)
      middle target updated after) :
    ∃ finalStore finalMap finalWorld slots,
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel (payloadModel compiled.compatible.checked registry functions) (GeneralizedLocalInstanceValues.model compiled.indexed)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model compiled.indexed) mapping world before store finalMap finalWorld after finalStore ∧
      slots.length = 7 ∧ RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) (head.writtenContext actualContext) compiled.indexed.layouts.definitions ∧
      (∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ Admission bridge context reached) ∧
      ∀ next output, ContinuationAgreement actual store ((head.emit next output).rename ξ)
        (slots ++ actual) finalStore (shift 7 (next.rename ξ)) := by
  rcases head with ⟨prepared, index, codes, leaf, lowered, node, invalid, shape, slot, writable, found, generated, rightView, rightType, profile⟩
  cases shape with
  | bare empty _ => exact (projected empty).elim
  | projected layout ordinary =>
    have sourceTyped := CallableIndexedOwnedAssignmentAdmission.rhs_typed unique found assignmentTyped
    obtain ⟨type, targetTyped⟩ := CallableIndexedOwnedPlaceAdmission.assignment_target_typed assignmentTyped
    obtain ⟨originalTypes, originalKeyTyped⟩ := CallableIndexedOwnedPlaceAdmission.place_keys_typed targetTyped
    have keyTyped := tree_typed layout.children unique originalKeyTyped
    obtain ⟨resolution, sameSources, keyValues, keyHeap, coreLookup, resolutionState, resolutionRelated, resolutionAdmission⟩ :=
      preserves_resolution bridge budget layout ordinary extension transport faithful observations
        environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame unique originalKeyTyped meaning
        slot writable keyTrace keyBound snapshot
    obtain ⟨native, rhsStore, rhsMap, rhsWorld, rhsResult, rhsPost⟩ :=
      rhs_preserves_at bridge resolution rhsSize (meaning rhsSize rhsBound) generated found sourceTyped
        (environments.extend resolution.maps resolution.worlds) resolution.heaps (locals.mono resolution.metadata)
        agrees actualTyped resolutionState resolutionAdmission (authority.transport resolution.effect)
          (physical.transport resolution.effect resolution.frame) owner ownerFrame trace
    cases represented : rhsResult.represented with
    | value payload =>
      have ordinaryRhs := rhsResult.to_ordinary_value
      obtain ⟨updatedValue, finalStore, finalMap, finalWorld, _root, finalHeaps, maps, worlds, frame, metadata, effect,
          slots, count, typed, agreement, reached, related⟩ :=
        CellAwareStagedProjectedCommit.preserves GeneralizedLocalDescriptorHeap.ordinary_cells layout ordinary extension callerProtocol transport faithful observations
          generated found rightView rightType profile environments heaps agrees actualTyped initial resolution coreLookup
          resolutionState resolutionRelated ordinaryRhs rhsPost write invalid
      refine ⟨finalStore, finalMap, finalWorld, slots, finalHeaps, maps, worlds, frame, metadata, effect,
        count, ?_, ⟨reached, related, ?_, ?_⟩, agreement⟩
      · simpa only [GenericAssignmentStatements.Head.writtenContext, CompatibleRenamedPlaceSuccess.writtenContext,
          ProtectedPlaceAssignmentSuccess.writtenContext, CallableIndexedAmbient.ambientDefinitions] using typed
      · exact CallableIndexedOwnedStagedProjectedAssignmentAdmission.heap_after_assignment unique found assignmentTyped
          locals (by simpa only [Staging.Recursive.ProjectedTarget.keys_eq_sourceKeys] using keyTyped)
          keyValues keyHeap resolution.metadata snapshot (rhsResult.sourcePost _ rfl).2
          (rhsResult.sourcePost _ rfl).1 rhsResult.metadata write
      · exact StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) admitted.rows frame

include environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame unique assignmentTyped projected in
/-- A failed key row stops before the getter and RHS. -/
theorem preserves_key_fault (budget : Nat)
    (meaning : PreservesBelow bridge context (payloadModel compiled.compatible.checked registry functions) named stages invocation certificate faults budget)
    {keySize : Nat} {failure : Staging.Recursive.Failure} {after : Dynamic.Heap}
    (ready : Staging.Recursive.ProjectedTarget.RootReady environment before assignment.target)
    (trace : Staging.Recursive.Size.Expressions program stages keySize invocation context environment before
      (Staging.Recursive.ProjectedTarget.keys assignment.target.projections) (.fault failure) after)
    (bounded : keySize ≤ budget) (next : Expr) (output : Ty) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((head.emit next output).rename ξ) (.inLeft output (.word token)) finalStore ∧ faults failure token ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel (payloadModel compiled.compatible.checked registry functions) (GeneralizedLocalInstanceValues.model compiled.indexed)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model compiled.indexed) mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ StableRows (bridge.pool reached) := by
  rcases head with ⟨prepared, index, codes, leaf, lowered, node, invalid, shape, slot, writable, found, generated, rightView, rightType, profile⟩
  cases shape with
  | bare empty _ => exact (projected empty).elim
  | projected layout ordinary =>
    obtain ⟨type, targetTyped⟩ := CallableIndexedOwnedPlaceAdmission.assignment_target_typed assignmentTyped
    obtain ⟨originalTypes, originalKeyTyped⟩ := CallableIndexedOwnedPlaceAdmission.place_keys_typed targetTyped
    cases ready with
    | intro lookup read =>
      obtain ⟨target, selected, reference⟩ := environments.lookup_visible lookup slot
      obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps,
        maps, worlds, frame, metadata, effect, reached, related, post⟩ :=
        CellAwareScopeExpressionSequence.preserves_fault bridge budget layout.children unique originalKeyTyped
          meaning environments heaps locals
          (DataPlaceChildExpressions.prefix_agrees agrees [.cellRef (OptionalCell.cellType prepared.route.rootType) target])
          (.cons (.cellRef reference.typed) actualTyped) initial admitted authority physical owner ownerFrame
          (by simpa only [Staging.Recursive.ProjectedTarget.keys_eq_sourceKeys] using trace) bounded
      refine ⟨token, finalStore, finalMap, finalWorld, ?_, matched, finalHeaps, maps, worlds, frame, metadata, effect,
        reached, related, post.rows⟩
      change Evaluates actual store ((execute prepared (.var index) (SourceCoreCalls.packArguments codes) lowered.expression
        next output (binaryOperator (prepared.route.leafType = .integer) operator) false invalid).rename ξ) _ _
      rw [execute_rename layout.path (virtual_closed layout ordinary)]
      simp only [renamed_packed, Expr.rename]
      unfold execute
      simp only [packed_renamed_type]
      apply Evaluates.letE (.var (agrees selected))
      apply LanguageResult.bind_failure
      simpa only [DataPlaceChildExpressions.rename_prefix, packed_renamed_expression, List.length_cons, List.length_nil,
        List.cons_append, List.nil_append, referenceEnvironment, SourceCoreDataPlaces.shift, shift, Nat.zero_add] using evaluated

include transport extension environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame unique assignmentTyped projected faithful observations in
/-- A successful key row and getter precede the actual staged RHS fault. -/
theorem preserves_fault (budget : Nat)
    (meaning : PreservesBelow bridge context (payloadModel compiled.compatible.checked registry functions) named stages invocation certificate faults budget)
    {keySize rhsSize : Nat} {sources : List Dynamic.Value} {target : Dynamic.ResolvedPlace}
    {failure : Staging.Recursive.Failure} {getter after : Dynamic.Heap}
    (keyTrace : Staging.Recursive.Size.Expressions program stages keySize invocation context environment before
      (Staging.Recursive.ProjectedTarget.keys assignment.target.projections) (.values sources) getter)
    (keyBound : keySize ≤ budget)
    (snapshot : Staging.Recursive.ProjectedTarget.Snapshot environment before getter assignment.target sources target)
    (trace : Staging.Recursive.Size.Expression program stages rhsSize invocation context environment getter rhs (.fault failure) after)
    (rhsBound : rhsSize < budget) (next : Expr) (output : Ty) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((head.emit next output).rename ξ) (.inLeft output (.word token)) finalStore ∧ faults failure token ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel (payloadModel compiled.compatible.checked registry functions) (GeneralizedLocalInstanceValues.model compiled.indexed)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model compiled.indexed) mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ StableRows (bridge.pool reached) := by
  rcases head with ⟨prepared, index, codes, leaf, lowered, node, invalid, shape, slot, writable, found, generated, rightView, rightType, profile⟩
  cases shape with
  | bare empty _ => exact (projected empty).elim
  | projected layout ordinary =>
    have sourceTyped := CallableIndexedOwnedAssignmentAdmission.rhs_typed unique found assignmentTyped
    obtain ⟨type, targetTyped⟩ := CallableIndexedOwnedPlaceAdmission.assignment_target_typed assignmentTyped
    obtain ⟨originalTypes, originalKeyTyped⟩ := CallableIndexedOwnedPlaceAdmission.place_keys_typed targetTyped
    obtain ⟨resolution, sameSources, keyValues, keyHeap, coreLookup, resolutionState, resolutionRelated, resolutionAdmission⟩ :=
      preserves_resolution bridge budget layout ordinary extension transport faithful observations
        environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame unique originalKeyTyped meaning
        slot writable keyTrace keyBound snapshot
    obtain ⟨native, rhsStore, rhsMap, rhsWorld, rhsResult, rhsState, rhsRelated⟩ :=
      rhs_preserves_at bridge resolution rhsSize (meaning rhsSize rhsBound) generated found sourceTyped
        (environments.extend resolution.maps resolution.worlds) resolution.heaps (locals.mono resolution.metadata)
        agrees actualTyped resolutionState resolutionAdmission (authority.transport resolution.effect)
          (physical.transport resolution.effect resolution.frame) owner ownerFrame trace
    cases represented : rhsResult.represented with
    | fault matched =>
      refine ⟨_, rhsStore, rhsMap, rhsWorld, ?_, matched, rhsResult.heaps,
        resolution.maps.trans rhsResult.maps, resolution.worlds.trans rhsResult.worlds,
        resolution.frame.trans rhsResult.frame, resolution.metadata.trans rhsResult.metadata,
        resolution.effect.trans rhsResult.effect,
        rhsState, callerProtocol.trans resolutionRelated rhsRelated,
        StableRows.after_administrative (bridge.pool initial) (bridge.pool rhsState) admitted.rows (resolution.frame.trans rhsResult.frame)⟩
      change Evaluates actual store ((execute prepared (.var index) (SourceCoreCalls.packArguments codes) lowered.expression
        next output (binaryOperator (prepared.route.leafType = .integer) operator) false invalid).rename ξ) _ _
      rw [execute_rename layout.path (virtual_closed layout ordinary)]
      simp only [renamed_packed, Expr.rename]
      unfold execute
      simp only [packed_renamed_type]
      have snapshotEvaluated := resolution.snapshotEvaluated
      simp only [packed_renamed_type] at snapshotEvaluated
      exact .letE (.var coreLookup) (LanguageResult.bind_success _ resolution.keysEvaluated
        (LanguageResult.bind_success _ snapshotEvaluated (LanguageResult.bind_failure _ rhsResult.evaluated)))


include transport extension environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame unique assignmentTyped projected faithful observations in
/-- Getter faults preserve the original reached diagnostic witness. -/
theorem preserves_getter_fault (budget : Nat)
    (meaning : PreservesBelow bridge context (payloadModel compiled.compatible.checked registry functions) named stages invocation certificate faults budget)
    (errors : ProtectedPlaceReachedDiagnostics.ShapeErrors (.initial compiled.compatible.checked) registry functions callerProtocol invocation.source context certificate
      scope administrative environment assignment.target head.prepared operator head.invalid initial
      (fun reason token => faults (.semantic reason) token) head.shape)
    {keySize : Nat} {sources : List Dynamic.Value} {reason : Dynamic.SemanticFault} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Expressions program stages keySize invocation context environment before
      (Staging.Recursive.ProjectedTarget.keys assignment.target.projections) (.values sources) after)
    (bounded : keySize ≤ budget)
    (failed : Staging.Recursive.ProjectedTarget.GetterFault environment before after assignment.target sources reason)
    (next : Expr) (output : Ty) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((head.emit next output).rename ξ) (.inLeft output (.word token)) finalStore ∧ faults (.semantic reason) token ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel (payloadModel compiled.compatible.checked registry functions) (GeneralizedLocalInstanceValues.model compiled.indexed)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model compiled.indexed) mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ StableRows (bridge.pool reached) := by
  rcases head with ⟨prepared, index, codes, leaf, lowered, node, invalid, shape, slot, writable, found, generated, rightView, rightType, profile⟩
  change ProtectedPlaceReachedDiagnostics.ShapeErrors (.initial compiled.compatible.checked) registry functions callerProtocol invocation.source context certificate
    scope administrative environment assignment.target prepared operator invalid initial
    (fun reason token => faults (.semantic reason) token) shape at errors
  obtain ⟨sourceTypes, site, layout, ordinary, missing, uninitialized⟩ :=
    PreparedProjectedDiagnosticFields.projected errors projected
  obtain ⟨type, targetTyped⟩ := CallableIndexedOwnedPlaceAdmission.assignment_target_typed assignmentTyped
  obtain ⟨originalTypes, originalKeyTyped⟩ := CallableIndexedOwnedPlaceAdmission.place_keys_typed targetTyped
  cases failed with
  | dangling lookup initialRead ordered absent =>
    obtain ⟨execution, _, _, reached, related, post⟩ := preserves_keys bridge budget layout
      environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame unique originalKeyTyped meaning
      slot writable trace bounded lookup initialRead ordered
    exact (absent.excludes_read execution.read).elim
  | projection lookup initialRead ordered currentRead initialValue fault =>
    obtain ⟨execution, _, _, keyState, keyRelated, _post⟩ := preserves_keys bridge budget layout
      environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame unique originalKeyTyped meaning
      slot writable trace bounded lookup initialRead ordered
    obtain ⟨token, count, root, finalStore, finalMap, finalWorld, _sourceFault, _initial, _receipt,
        evaluated, finalHeaps, maps, worlds, frame, metadata, effect, reached, related, diagnostic⟩ :=
      CellAwareStagedProjectedFaults.preserves_projection GeneralizedLocalDescriptorHeap.ordinary_cells layout ordinary callerProtocol transport
        environments agrees actualTyped initial execution ⟨keyState, keyRelated⟩ lookup initialRead
        (ordered.evaluates (ProtectedStagedProjectedPrefix.values_plain trace)) currentRead extension faithful observations
        initialValue fault operator rhs (lowered.expression.rename ξ) (next.rename ξ) output invalid
    refine ⟨token, finalStore, finalMap, finalWorld, ?_, missing reached related diagnostic,
      finalHeaps, maps, worlds, frame, metadata, effect, reached, related,
      StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) admitted.rows frame⟩
    change Evaluates actual store ((execute prepared (.var index) (SourceCoreCalls.packArguments codes) lowered.expression
      next output (binaryOperator (prepared.route.leafType = .integer) operator) false invalid).rename ξ) _ _
    simpa only [execute_rename layout.path (virtual_closed layout ordinary), renamed_packed, Expr.rename] using evaluated
  | uninitialized lookup initialRead ordered currentRead empty notMapping nonempty =>
    obtain ⟨execution, _, _, keyState, keyRelated, _post⟩ := preserves_keys bridge budget layout
      environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame unique originalKeyTyped meaning
      slot writable trace bounded lookup initialRead ordered
    obtain ⟨finalStore, finalMap, finalWorld, _sourceFault, evaluated, finalHeaps, maps, worlds,
        frame, metadata, effect, reached, related, diagnostic⟩ :=
      CellAwareStagedProjectedFaults.preserves_uninitialized GeneralizedLocalDescriptorHeap.ordinary_cells layout callerProtocol initial execution ⟨keyState, keyRelated⟩
        lookup initialRead (ordered.evaluates (ProtectedStagedProjectedPrefix.values_plain trace)) currentRead
        ordinary empty notMapping nonempty operator rhs (lowered.expression.rename ξ) (next.rename ξ) output invalid
    refine ⟨prepared.invalidProjection, finalStore, finalMap, finalWorld, ?_, uninitialized reached related diagnostic,
      finalHeaps, maps, worlds, frame, metadata, effect, reached, related,
      StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) admitted.rows frame⟩
    change Evaluates actual store ((execute prepared (.var index) (SourceCoreCalls.packArguments codes) lowered.expression
      next output (binaryOperator (prepared.route.leafType = .integer) operator) false invalid).rename ξ) _ _
    simpa only [execute_rename layout.path (virtual_closed layout ordinary), renamed_packed, Expr.rename] using evaluated


include transport extension environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame unique assignmentTyped projected faithful observations in
/-- Structural write failure is checked against the latest root after the
successful RHS. Represented initialized scalar operands cannot create an
additional operand fault in this projected profile. -/
theorem preserves_write_fault (budget : Nat)
    (meaning : PreservesBelow bridge context (payloadModel compiled.compatible.checked registry functions) named stages invocation certificate faults budget)
    (errors : ProtectedPlaceReachedDiagnostics.ShapeErrors (.initial compiled.compatible.checked) registry functions callerProtocol invocation.source context certificate
      scope administrative environment assignment.target head.prepared operator head.invalid initial
      (fun reason token => faults (.semantic reason) token) head.shape)
    {keySize rhsSize : Nat} {sources : List Dynamic.Value} {target : Dynamic.ResolvedPlace}
    {right : Dynamic.Value} {reason : Dynamic.SemanticFault} {getter after : Dynamic.Heap}
    (keyTrace : Staging.Recursive.Size.Expressions program stages keySize invocation context environment before
      (Staging.Recursive.ProjectedTarget.keys assignment.target.projections) (.values sources) getter)
    (keyBound : keySize ≤ budget)
    (snapshot : Staging.Recursive.ProjectedTarget.Snapshot environment before getter assignment.target sources target)
    (trace : Staging.Recursive.Size.Expression program stages rhsSize invocation context environment getter rhs (.value right) after)
    (rhsBound : rhsSize < budget)
    (failed : Staging.Recursive.ProjectedTarget.WriteFault operator target right after reason)
    (next : Expr) (output : Ty) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((head.emit next output).rename ξ) (.inLeft output (.word token)) finalStore ∧ faults (.semantic reason) token ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel (payloadModel compiled.compatible.checked registry functions) (GeneralizedLocalInstanceValues.model compiled.indexed)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model compiled.indexed) mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ StableRows (bridge.pool reached) := by
  rcases head with ⟨prepared, index, codes, leaf, lowered, node, invalid, shape, slot, writable, found, generated, rightView, rightType, profile⟩
  change ProtectedPlaceReachedDiagnostics.ShapeErrors (.initial compiled.compatible.checked) registry functions callerProtocol invocation.source context certificate
    scope administrative environment assignment.target prepared operator invalid initial
    (fun reason token => faults (.semantic reason) token) shape at errors
  obtain ⟨sourceTypes, site, layout, ordinary, missing, uninitialized⟩ :=
    PreparedProjectedDiagnosticFields.projected errors projected
  have sourceTyped := CallableIndexedOwnedAssignmentAdmission.rhs_typed unique found assignmentTyped
  obtain ⟨type, targetTyped⟩ := CallableIndexedOwnedPlaceAdmission.assignment_target_typed assignmentTyped
  obtain ⟨originalTypes, originalKeyTyped⟩ := CallableIndexedOwnedPlaceAdmission.place_keys_typed targetTyped
  obtain ⟨resolution, sameSources, keyValues, keyHeap, coreLookup, resolutionState, resolutionRelated, resolutionAdmission⟩ :=
    preserves_resolution bridge budget layout ordinary extension transport faithful observations
      environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame unique originalKeyTyped meaning
      slot writable keyTrace keyBound snapshot
  obtain ⟨native, rhsStore, rhsMap, rhsWorld, rhsResult, rhsPost⟩ :=
    rhs_preserves_at bridge resolution rhsSize (meaning rhsSize rhsBound) generated found sourceTyped
      (environments.extend resolution.maps resolution.worlds) resolution.heaps (locals.mono resolution.metadata)
      agrees actualTyped resolutionState resolutionAdmission (authority.transport resolution.effect)
        (physical.transport resolution.effect resolution.frame) owner ownerFrame trace
  cases represented : rhsResult.represented with
  | @value _ native rightRep =>
    have ordinaryRhs := rhsResult.to_ordinary_value
    cases failed with
    | operands read rootType initialValue pathRead invalidOperands =>
      have rightRep : ValueRep compiled.compatible.checked registry functions rhsMap rhsWorld leaf right native prepared.route.leafType :=
        .compatible rightView (by simpa only [payloadModel, renamed, rightType] using rightRep)
      obtain ⟨replacement, replacementValue, replacementRep, applies, evaluated, valid⟩ :=
        CompatiblePlaceModifier.initialized_success observations profile ordinaryRhs.saved_snapshot rightRep
          (environment := rhsEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
            (.inRight .unit resolution.snapshot) native actual)
          (.var (index := 1) rfl) (.var (index := 0) rfl) rhsStore invalid
      rw [resolution.selectedEq] at invalidOperands
      exact (valid invalidOperands).elim
    | structural read rootType initialValue fault =>
      obtain ⟨token, count, root, finalStore, finalMap, finalWorld, _sourceFault, _initial, _receipt,
          evaluated, finalHeaps, maps, worlds, frame, metadata, effect, reached, related, diagnostic⟩ :=
        CellAwareStagedProjectedFaults.preserves_structural GeneralizedLocalDescriptorHeap.ordinary_cells layout ordinary extension callerProtocol transport faithful observations
          generated found rightView rightType profile environments agrees actualTyped initial resolution coreLookup
          resolutionState resolutionRelated ordinaryRhs rhsPost
          (snapshot.resolves (ProtectedStagedProjectedPrefix.values_plain keyTrace)) trace.sound.value_plain
          read rootType initialValue fault (next.rename ξ) output invalid
      refine ⟨token, finalStore, finalMap, finalWorld, ?_, missing reached related diagnostic,
        finalHeaps, maps, worlds, frame, metadata, effect, reached, related,
        StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) admitted.rows frame⟩
      change Evaluates actual store ((execute prepared (.var index) (SourceCoreCalls.packArguments codes) lowered.expression
        next output (binaryOperator (prepared.route.leafType = .integer) operator) false invalid).rename ξ) _ _
      simpa only [execute_rename layout.path (virtual_closed layout ordinary), renamed_packed, Expr.rename] using evaluated

end Heads
end Solcore.SourceSemantics.CoreLowering.CellAwareScopeProjectedAssignmentHeads
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareScopeProjectedAssignmentReflection
/-! Native projected writes reconstruct the ordered staged key row and RHS
at their actual reached states. Only successful children are erased for the
existing pure setter; staged faults retain their own tag and endpoint. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareScopeProjectedAssignmentHeads
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality CompatibleHeap CoreProof ReadOnly
open SourceCoreCompatibleDataPlaces GenericExpressionMeaning CompatibleRenamedPlace DataPlaceExecution DataPatternValues
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CellAwareScopeExpressionBounds
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)

section Heads
variable {named : SourceCoreGeneralFunctions.Function}
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : Certificate} {scope : Scope} {administrative : Core.Context}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {faults : RecursiveStageMeaning.FaultRep}
  (transport : ProtectedStateTransition.AdministrativeTransport callerProtocol)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : FunctionObservations compiled.compatible.checked.catalog functions identities)
  {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
  (head : GenericAssignmentStatements.Head (.initial compiled.compatible.checked) invocation.source context certificate scope administrative compiled.indexed.layouts.definitions assignment operator rhs)
  (projected : assignment.target.projections ≠ [])
  {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment}
  {canonical actual : Environment} {before : Dynamic.Heap} {store : Store} {actualContext : Core.Context} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (definitions := compiled.indexed.layouts.definitions) (storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical)
  (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel (payloadModel compiled.compatible.checked registry functions) (GeneralizedLocalInstanceValues.model compiled.indexed)) mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)
  (authority : CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model compiled.indexed) named.signature.key [] mapping world before store environment)
  (physical : CellAwareScopePhysical.Physical compiled named context scope canonical mapping world before store environment)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (ownerFrame : owner.key.frameLocation = physical.location)
  (unique : NodeOccurrencesUnique invocation.source)
  (assignmentTyped : SourceAssignmentHasType invocation.source context assignment operator rhs)

include transport extension environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame unique assignmentTyped projected observations faithful in
theorem reflects_bounded (budget : Nat)
    (boundedReflection : ReflectsBelow bridge context (payloadModel compiled.compatible.checked registry functions) named stages invocation certificate faults budget)
    (functionTypes : FunctionRuntimeViews functions)
    (errors : ProtectedPlaceReachedDiagnostics.ShapeErrors (.initial compiled.compatible.checked) registry functions callerProtocol invocation.source context certificate
      scope administrative environment assignment.target head.prepared operator head.invalid initial
      (fun reason token => faults (.semantic reason) token) head.shape)
    {next : Expr} {output : Ty} {value : Value} {finalStore : Store}
    {size : Nat} (completed : EvaluationSize size actual store ((head.emit next output).rename ξ) value finalStore) (bounded : size ≤ budget) :
    ResultAt bridge (functions := functions) (registry := registry) size context stages invocation faults
      scope (head.writtenContext actualContext) assignment operator rhs environment canonical actual
      before store mapping world initial (next.rename ξ) output value finalStore := by
  rcases head with ⟨prepared, index, codes, leaf, lowered, node, invalid, shape, slot, writable, found, generated, rightView, rightType, profile⟩
  change ProtectedPlaceReachedDiagnostics.ShapeErrors (.initial compiled.compatible.checked) registry functions callerProtocol invocation.source context certificate
    scope administrative environment assignment.target prepared operator invalid initial
    (fun reason token => faults (.semantic reason) token) shape at errors
  obtain ⟨sourceTypes, site, layout, ordinary, missing, uninitialized⟩ :=
    PreparedProjectedDiagnosticFields.projected errors projected
  have sourceTyped := CallableIndexedOwnedAssignmentAdmission.rhs_typed unique found assignmentTyped
  obtain ⟨type, targetTyped⟩ := CallableIndexedOwnedPlaceAdmission.assignment_target_typed assignmentTyped
  obtain ⟨originalTypes, keyTyped⟩ := CallableIndexedOwnedPlaceAdmission.place_keys_typed targetTyped
  have keyRow : ExpressionsHaveTypes invocation.source context
      (Staging.Recursive.ProjectedTarget.keys assignment.target.projections) sourceTypes := by
    simpa only [Staging.Recursive.ProjectedTarget.keys_eq_sourceKeys] using tree_typed layout.children unique keyTyped
  have nativeCompleted := completed
  change EvaluationSize size actual store
    ((execute prepared (.var index) (SourceCoreCalls.packArguments codes) lowered.expression next output
      (binaryOperator (prepared.route.leafType = .integer) operator) false invalid).rename ξ) value finalStore at nativeCompleted
  rw [execute_rename layout.path (virtual_closed layout ordinary)] at nativeCompleted
  simp only [renamed_packed, Expr.rename] at nativeCompleted
  have prefixResult := CellAwareStagedProjectedPrefix.reflects_getter budget GeneralizedLocalDescriptorHeap.ordinary_cells layout ordinary extension
    callerProtocol transport functionTypes faithful observations environments heaps locals agrees actualTyped initial missing uninitialized
    (by
      intro target _ hiddenTyped keySize keyValue keyStore evaluated smaller
      obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds,
          frame, metadata, effect, typedValues, reached, related, post⟩ :=
        CellAwareScopeTypedExpressionSequence.reflects bridge budget layout.children unique keyTyped
          boundedReflection environments heaps locals
          (DataPlaceChildExpressions.prefix_agrees agrees [.cellRef (OptionalCell.cellType prepared.route.rootType) target])
          hiddenTyped initial admitted authority physical owner ownerFrame evaluated smaller
      refine ⟨sourceSize, outcome, after, finalMap, finalWorld, ?_, represented, finalHeaps, maps, worlds,
        frame, metadata, effect, ?_, reached, related⟩
      · simpa only [Staging.Recursive.ProjectedTarget.keys_eq_sourceKeys] using trace
      · intro sources same
        exact ⟨typedValues sources same, (post.successful sources same).heap⟩)
    slot writable nativeCompleted bounded
  cases prefixResult with
  | keyFault ready trace same matched finalHeaps maps worlds frame metadata effect post =>
    obtain ⟨reached, related⟩ := post
    exact .keyFault ready trace same matched finalHeaps maps worlds frame metadata effect reached related
      (StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) admitted.rows frame)
  | getterFault trace failed same matched finalHeaps maps worlds frame metadata effect post =>
    obtain ⟨reached, related⟩ := post
    exact .getterFault trace failed same matched finalHeaps maps worlds frame metadata effect reached related
      (StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) admitted.rows frame)
  | resolved resolution keyTrace snapshot keyValues getterHeap prefixBound remaining prefixPost =>
    obtain ⟨getterState, getterRelated⟩ := prefixPost
    have getterAdmission : Admission bridge context getterState :=
      ⟨getterHeap, StableRows.after_administrative (bridge.pool initial) (bridge.pool getterState) admitted.rows resolution.frame⟩
    have reflectRhs := fun {child : Nat} {value : Value} {finalStore : Store}
        (evaluated : EvaluationSize child
          (snapshotEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
            (.inRight .unit resolution.snapshot) actual) resolution.store (shift 3 (lowered.expression.rename ξ)) value finalStore)
        (smaller : child < budget) =>
      rhs_reflects_at bridge resolution child (boundedReflection child smaller) generated found sourceTyped
        (environments.extend resolution.maps resolution.worlds) resolution.heaps (locals.mono resolution.metadata)
        agrees actualTyped getterState getterAdmission (authority.transport resolution.effect)
          (physical.transport resolution.effect resolution.frame) owner ownerFrame evaluated
    cases remaining with
    | caseLeft evaluated failed =>
      obtain ⟨rhsSize, outcome, after, finalMap, finalWorld, result, rhsPost⟩ := reflectRhs evaluated (by omega)
      cases represented : result.represented with
      | fault matched =>
        cases failed with
        | inLeft valueEvaluated =>
          cases valueEvaluated with
          | var foundValue =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at foundValue
            subst_vars
            obtain ⟨reached, related⟩ := rhsPost
            exact .rhsFault keyTrace snapshot result.trace rfl matched result.heaps
              (resolution.maps.trans result.maps) (resolution.worlds.trans result.worlds)
              (resolution.frame.trans result.frame) (resolution.metadata.trans result.metadata)
              (resolution.effect.trans result.effect) reached
              (callerProtocol.trans getterRelated related)
              (StableRows.after_administrative (bridge.pool getterState) (bridge.pool reached) getterAdmission.rows result.frame)
    | caseRight evaluated continuation =>
      rename_i rhsStore rightValue
      obtain ⟨rhsSize, outcome, after, finalMap, finalWorld, result, rhsPost⟩ := reflectRhs evaluated (by omega)
      cases represented : result.represented with
      | @value right _ payload =>
        obtain ⟨rhsState, rhsRelated⟩ := rhsPost
        obtain ⟨rightTyped, middleTyped⟩ := result.sourcePost _ rfl
        have plainRhs := result.to_ordinary_value
        have rightRep : CompatiblePayload.ValueRep compiled.compatible.checked registry functions finalMap finalWorld leaf right rightValue prepared.route.leafType :=
          .compatible rightView (by simpa only [payloadModel, rightType] using payload)
        let rightExecution : CompatibleCellPlaceRhsReflection.Execution compiled.compatible.checked registry functions (GeneralizedLocalDescriptorHeap.cellModel (payloadModel compiled.compatible.checked registry functions) (GeneralizedLocalInstanceValues.model compiled.indexed)) (GeneralizedLocalInstanceValues.model compiled.indexed) program context
            invocation.evidence invocation.source (fun reason token => faults (.semantic reason) token) environment
            prepared (renamedCodes codes ξ) sourceTypes assignment.target leaf _ actual store mapping world before _
            resolution rhs node (renamed lowered ξ) :=
          ⟨right, rightValue, after, _, finalMap, finalWorld, plainRhs, rightRep⟩
        obtain ⟨resolveSize, resolve⟩ := SourceExecutionSize.SourcePlaceResolves.has_size
          (snapshot.resolves (CellAwareStagedProjectedPrefix.values_plain keyTrace))
        obtain ⟨plainRhsSize, plainRhsTrace⟩ := SourceExecutionSize.ExpressionEvaluates.has_size result.trace.sound.value_plain
        simp only [packed_renamed_type] at continuation
        have tail := CellAwareStagedProjectedTail.reflects GeneralizedLocalDescriptorHeap.ordinary_cells callerProtocol transport layout ordinary extension functionTypes faithful observations
          profile environments agrees actualTyped resolve resolution rightExecution plainRhsTrace initial rhsState
          (callerProtocol.trans getterRelated rhsRelated) missing continuation
        cases tail with
        | fault failed same matched finalHeaps maps worlds frame metadata effect post =>
          obtain ⟨reached, related⟩ := post
          exact .writeFault keyTrace snapshot result.trace failed same matched finalHeaps maps worlds frame metadata effect reached related
            (StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) admitted.rows frame)
        | committed write finalHeaps maps worlds frame metadata effect count typed post strict continuation =>
          obtain ⟨reached, related⟩ := post
          exact .success keyTrace snapshot result.trace write finalHeaps maps worlds frame metadata effect count
            (by simpa only [GenericAssignmentStatements.Head.writtenContext, CallableIndexedAmbient.ambientDefinitions] using typed)
            reached related
            ⟨CallableIndexedOwnedStagedProjectedAssignmentAdmission.heap_after_assignment unique found assignmentTyped locals
              keyRow keyValues getterHeap resolution.metadata snapshot middleTyped rightTyped result.metadata write,
              StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) admitted.rows frame⟩
            (by omega) continuation

end Heads
end Solcore.SourceSemantics.CoreLowering.CellAwareScopeProjectedAssignmentHeads
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareScopeProjectedAssignmentFlow
/-! Projected assignment sequences retain the reached key, getter, RHS and
write states before continuing through the same mixed scope. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareScopeProjectedAssignmentFlow
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CompatibleEquality CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)
open CallableIndexedOwnedAdmittedStagedImperativeFlow (fault_post)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {protocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (transport : ProtectedStateTransition.AdministrativeTransport protocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {named : SourceCoreGeneralFunctions.Function}
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}
  {administrative : Core.Context} {scope : SourceCoreLocalCell.Scope} {mode : Bool}
  {expected : TypeSystem.Ty} {type : Ty} {id : StatementId} {node : StatementNode}
  {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
  {rest : List StatementId} {body : Expr}
variable
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) protocol compiled.indexed.layouts
    compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) (GeneralizedLocalInstanceValues.model compiled.indexed)))
  (sourceEq : invocation.source = CallableIndexedNamedGeneration.source named)
  (unique : NodeOccurrencesUnique invocation.source)
  (found : invocation.source.lookupStatement? id = some node)
  (form : node.form = .assignValue assignment operator rhs)
  (head : GenericAssignmentStatements.Head (.initial compiled.compatible.checked) invocation.source context certificate
    scope administrative compiled.indexed.layouts.definitions assignment operator rhs)
  (projected : assignment.target.projections ≠ [])
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : FunctionObservations compiled.compatible.checked.catalog functions identities)
  (diagnostics : SourceAssignmentHasType invocation.source context assignment operator rhs →
    ∀ {environment : Dynamic.Environment} {initialIndex : ProtectedStateTransition.Index}
      (initial : protocol.State initialIndex),
      ProtectedPlaceReachedDiagnostics.ShapeErrors (.initial compiled.compatible.checked) registry functions protocol
        invocation.source context certificate scope administrative environment assignment.target head.prepared operator head.invalid
        initial (fun reason token => faults (.semantic reason) token) head.shape)

include transport sourceEq unique found form projected extension faithful observations diagnostics in
theorem preserves (budget : Nat)
    (children : CellAwareScopeExpressionBounds.PreservesBelow bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) named stages invocation certificate faults budget)
    (tail : CellAwareScopeFlowBounds.PreservesAtMost bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) named producer stages invocation faults
      administrative scope mode rest expected type body budget) :
    ∀ size, size ≤ budget → CellAwareScopeFlowBounds.PreservesAt bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) named producer stages invocation faults
      administrative scope mode (id :: rest) expected type (head.emit body (LocalLoop.controlType type)) size := by
  intro size within mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
    initial admitted authority physical owner sameLocation ready finalContext outcome after trace
  have assignmentTyped := ProtectedStateImperativeTypedSourceSites.assignment unique
    (sourceEq.symm ▸ ProtectedStateImperativeTypedSourceSites.head sourceTyped) found form
  have suffix := ProtectedStateImperativeStatementSuffixTyping.assignment
    (sourceEq ▸ unique) sourceTyped (sourceEq ▸ found) form
  have splitTrace := CallableIndexedOwnedPreparedStagedScopedProjectedAssignmentSourceInversion.child_and_tail
    unique found form projected trace
  cases splitTrace with
  | rootFault failed => exact False.elim (failed.excluded head.writable locals)
  | keysFault ready keyTrace =>
      obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds,
          preservation, metadata, effect, reached, related, stable⟩ :=
        CellAwareScopeProjectedAssignmentHeads.preserves_key_fault
          (compiled := compiled)
          (invocation := invocation)
          (context := context) (scope := scope) (administrative := administrative)
          bridge functions
          head projected environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation unique assignmentTyped
          budget children ready keyTrace (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within; omega) body (LocalLoop.controlType type)
      exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds,
        preservation, metadata, effect, reached, related, CallableIndexedOwnedAdmittedStagedImperativeFlow.fault_post bridge reached stable⟩
  | getterFault keyTrace failed =>
      obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds,
          preservation, metadata, effect, reached, related, stable⟩ :=
        CellAwareScopeProjectedAssignmentHeads.preserves_getter_fault
          (compiled := compiled)
          (invocation := invocation)
          (context := context) (scope := scope) (administrative := administrative)
          bridge functions extension transport faithful observations
          head projected environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation unique assignmentTyped
          budget children (diagnostics assignmentTyped initial)
          keyTrace (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within; omega) failed body (LocalLoop.controlType type)
      exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds,
        preservation, metadata, effect, reached, related, CallableIndexedOwnedAdmittedStagedImperativeFlow.fault_post bridge (context := context) (expected := expected) (failure := .semantic _) reached stable⟩
  | rhsFault keyTrace snapshot childTrace =>
      obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds,
          preservation, metadata, effect, reached, related, stable⟩ :=
        CellAwareScopeProjectedAssignmentHeads.preserves_fault
          (compiled := compiled)
          (invocation := invocation)
          (context := context) (scope := scope) (administrative := administrative)
          bridge functions extension transport faithful observations
          head projected environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation unique assignmentTyped
          budget children keyTrace (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within; omega) snapshot childTrace (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within; omega) body (LocalLoop.controlType type)
      exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds,
        preservation, metadata, effect, reached, related, CallableIndexedOwnedAdmittedStagedImperativeFlow.fault_post bridge reached stable⟩
  | writeFault keyTrace snapshot childTrace failed =>
      obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds,
          preservation, metadata, effect, reached, related, stable⟩ :=
        CellAwareScopeProjectedAssignmentHeads.preserves_write_fault
          (compiled := compiled)
          (invocation := invocation)
          (context := context) (scope := scope) (administrative := administrative)
          bridge functions extension transport faithful observations
          head projected environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation unique assignmentTyped
          budget children (diagnostics assignmentTyped initial)
          keyTrace (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within; omega) snapshot childTrace (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within; omega) failed body (LocalLoop.controlType type)
      exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds,
        preservation, metadata, effect, reached, related, CallableIndexedOwnedAdmittedStagedImperativeFlow.fault_post bridge (context := context) (expected := expected) (failure := .semantic _) reached stable⟩
  | success keyTrace snapshot childTrace write remainingTrace =>
      obtain ⟨middleStore, middleMap, middleWorld, slots, middleHeaps, maps, worlds, preservation, metadata,
          effect, count, typed, ⟨reached, related, nextAdmitted⟩, continuation⟩ :=
        CellAwareScopeProjectedAssignmentHeads.preserves_value
          (compiled := compiled)
          (invocation := invocation)
          (context := context) (scope := scope) (administrative := administrative)
          bridge functions extension transport faithful observations
          head projected environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation unique assignmentTyped
          budget children keyTrace (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within; omega) snapshot childTrace (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within; omega) write
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented,
          finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, finalEffect, last, lastRelated, post⟩ :=
        tail _ (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within; omega) (environments.extend maps worlds) middleHeaps (locals.mono metadata)
          (DataPlaceChildExpressions.prefix_agrees agrees slots) typed runtime covers sameLedger suffix
          reached nextAdmitted (authority.transport effect) (physical.transport effect preservation) owner sameLocation ready remainingTrace
      have native := (continuation body (LocalLoop.controlType type)).wrap (by
        simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreCompatibleDataPlaces.shift,
          SourceCoreDataPlaces.shift] using evaluated)
      exact ⟨value, finalStore, finalMap, finalWorld, native, represented, finalHeaps,
        maps.trans finalMaps, worlds.trans finalWorlds, preservation.trans finalFrame, metadata.trans finalMetadata,
        effect.trans finalEffect, last, protocol.trans related lastRelated, post⟩

include transport sourceEq unique found form projected extension faithful observations diagnostics in
theorem reflects (functionTypes : FunctionRuntimeViews functions) (budget : Nat)
    (children : CellAwareScopeExpressionBounds.ReflectsBelow bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) named stages invocation certificate faults budget)
    (tail : CellAwareScopeFlowBounds.ReflectsAtMost bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) named producer stages invocation faults
      administrative scope mode rest expected type body budget) :
    ∀ size, size ≤ budget → CellAwareScopeFlowBounds.ReflectsAt bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) named producer stages invocation faults
      administrative scope mode (id :: rest) expected type (head.emit body (LocalLoop.controlType type)) size := by
  intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
    initial admitted authority physical owner sameLocation ready completed
  have assignmentTyped := ProtectedStateImperativeTypedSourceSites.assignment unique
    (sourceEq.symm ▸ ProtectedStateImperativeTypedSourceSites.head sourceTyped) found form
  have suffix := ProtectedStateImperativeStatementSuffixTyping.assignment
    (sourceEq ▸ unique) sourceTyped (sourceEq ▸ found) form
  have result := CellAwareScopeProjectedAssignmentHeads.reflects_bounded (compiled := compiled)
    (invocation := invocation)
    (context := context) (scope := scope) (administrative := administrative) bridge functions extension transport faithful observations
    head projected environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation unique assignmentTyped
    budget children functionTypes
      (diagnostics assignmentTyped initial) completed within
  cases result with
  | keyFault ready keyTrace same matched finalHeaps maps worlds preservation metadata effect reached related stable =>
      cases same
      refine ⟨Staging.Recursive.Size.stepSize [_], context, _, _, _, _,
        .assignProjectedKeysFault (lookupStatement?_sound found) form projected ready keyTrace, .fault matched,
        finalHeaps, maps, worlds, preservation, metadata, effect, reached, related, ?_⟩
      exact fault_post bridge reached stable
  | getterFault keyTrace failed same matched finalHeaps maps worlds preservation metadata effect reached related stable =>
      cases same
      refine ⟨Staging.Recursive.Size.stepSize [_], context, _, _, _, _,
        .assignProjectedGetterFault (lookupStatement?_sound found) form projected keyTrace failed, .fault matched,
        finalHeaps, maps, worlds, preservation, metadata, effect, reached, related, ?_⟩
      exact fault_post bridge (context := context) (expected := expected) (failure := .semantic _) reached stable
  | rhsFault keyTrace snapshot childTrace same matched finalHeaps maps worlds preservation metadata effect reached related stable =>
      cases same
      refine ⟨Staging.Recursive.Size.stepSize [_, _], context, _, _, _, _,
        .assignProjectedRhsFault (lookupStatement?_sound found) form projected keyTrace snapshot childTrace, .fault matched,
        finalHeaps, maps, worlds, preservation, metadata, effect, reached, related, ?_⟩
      exact fault_post bridge reached stable
  | writeFault keyTrace snapshot childTrace failed same matched finalHeaps maps worlds preservation metadata effect reached related stable =>
      cases same
      refine ⟨Staging.Recursive.Size.stepSize [_, _], context, _, _, _, _,
        .assignProjectedWriteFault (lookupStatement?_sound found) form projected keyTrace snapshot childTrace failed, .fault matched,
        finalHeaps, maps, worlds, preservation, metadata, effect, reached, related, ?_⟩
      exact fault_post bridge (context := context) (expected := expected) (failure := .semantic _) reached stable
  | success keyTrace snapshot childTrace write middleHeaps maps worlds preservation metadata effect count typed reached related nextAdmitted strict remaining =>
      obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented,
          finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, finalEffect, last, lastRelated, post⟩ :=
        tail _ (Nat.le_trans (Nat.le_of_lt strict) within)
          (environments.extend maps worlds) middleHeaps (locals.mono metadata)
          (DataPlaceChildExpressions.prefix_agrees agrees _) typed runtime covers sameLedger suffix
          reached nextAdmitted (authority.transport effect) (physical.transport effect preservation) owner sameLocation ready
          (by simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreCompatibleDataPlaces.shift, SourceCoreDataPlaces.shift] using remaining)
      exact ⟨Staging.Recursive.Size.stepSize [_, _, sourceSize], finalContext, outcome, after, finalMap, finalWorld,
        .assignProjected (lookupStatement?_sound found) form projected keyTrace snapshot childTrace write trace, represented,
        finalHeaps, maps.trans finalMaps, worlds.trans finalWorlds, preservation.trans finalFrame,
        metadata.trans finalMetadata, effect.trans finalEffect, last, protocol.trans related lastRelated, post⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareScopeProjectedAssignmentFlow
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareScopeBareAssignmentFlow
/-! Mixed bare assignments execute the real target snapshot, RHS, modifier
and write before the remaining statements. Every reached descriptor survives
both successful updates and genuine failures. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareScopeBareAssignmentFlow
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)
open CallableIndexedOwnedAdmittedStagedImperativeFlow (fault_post)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {protocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (transport : ProtectedStateTransition.AdministrativeTransport protocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {named : SourceCoreGeneralFunctions.Function}
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}
  {administrative : Core.Context} {scope : SourceCoreLocalCell.Scope} {mode : Bool}
  {expected : TypeSystem.Ty} {type : Ty} {id : StatementId} {node : StatementNode}
  {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
  {rest : List StatementId} {body : Expr}
variable
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) protocol compiled.indexed.layouts
    compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) (GeneralizedLocalInstanceValues.model compiled.indexed)))
  (sourceEq : invocation.source = CallableIndexedNamedGeneration.source named)
  (unique : NodeOccurrencesUnique invocation.source)
  (found : invocation.source.lookupStatement? id = some node)
  (form : node.form = .assignValue assignment operator rhs)
  (head : GenericAssignmentStatements.Head (.initial compiled.compatible.checked) invocation.source context certificate
    scope administrative compiled.indexed.layouts.definitions assignment operator rhs)
  (bare : assignment.target.projections = [])
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  (invalidToken : AssignmentOperandDiagnostics.OperandsLaw
    (fun reason token => faults (.semantic reason) token) operator head.invalid)

include transport sourceEq unique found form bare extension invalidToken in
theorem preserves (budget : Nat)
    (children : CellAwareScopeExpressionBounds.PreservesBelow bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) named stages invocation certificate faults budget)
    (tail : CellAwareScopeFlowBounds.PreservesAtMost bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) named producer stages invocation faults
      administrative scope mode rest expected type body budget) :
    ∀ size, size ≤ budget → CellAwareScopeFlowBounds.PreservesAt bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) named producer stages invocation faults
      administrative scope mode (id :: rest) expected type (head.emit body (LocalLoop.controlType type)) size := by
  intro size within mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
    initial admitted authority physical owner sameLocation ready finalContext outcome after trace
  have assignmentTyped := ProtectedStateImperativeTypedSourceSites.assignment unique
    (sourceEq.symm ▸ ProtectedStateImperativeTypedSourceSites.head sourceTyped) found form
  have suffix := ProtectedStateImperativeStatementSuffixTyping.assignment
    (sourceEq ▸ unique) sourceTyped (sourceEq ▸ found) form
  obtain ⟨target, snapshot⟩ := CellAwareScopeBareAssignmentHeads.target_snapshot
    (invocation := invocation) bridge functions extension head bare environments heaps locals agrees initial admitted
  rcases CallableIndexedOwnedPreparedStagedScopedBareAssignmentSourceInversion.child_and_tail unique found form snapshot trace with
    ⟨childSize, failure, sameSize, contextEq, outcomeEq, childTrace⟩ |
    ⟨childSize, right, currentCell, initialValue, currentSelected, sameSize, contextEq, outcomeEq, childTrace,
      currentRead, rootType, initialized, path, invalid⟩ |
    ⟨childSize, tailSize, right, middle, written, updated, sameSize, childTrace, write, remainingTrace⟩
  · subst finalContext
    subst outcome
    have childStrict : childSize < budget := Nat.lt_of_lt_of_le (by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp)) within
    obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds,
        preservation, metadata, effect, reached, related, stable⟩ :=
      CellAwareScopeBareAssignmentHeads.preserves_fault bridge functions extension head bare
        environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation unique assignmentTyped
        (children childSize childStrict) childTrace body (LocalLoop.controlType type)
    exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds,
      preservation, metadata, effect, reached, related, fault_post bridge reached stable⟩
  · subst finalContext
    subst outcome
    have childStrict : childSize < budget := Nat.lt_of_lt_of_le (by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp)) within
    obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds,
        preservation, metadata, effect, reached, related, stable⟩ :=
      CellAwareScopeBareAssignmentHeads.preserves_operands bridge functions extension head bare
        environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation unique assignmentTyped
        (children childSize childStrict) snapshot invalid childTrace body (LocalLoop.controlType type) invalidToken
    exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds,
      preservation, metadata, effect, reached, related,
      fault_post bridge (context := context) (expected := expected) (failure := .semantic _) reached stable⟩
  · have childStrict : childSize < budget := Nat.lt_of_lt_of_le (by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp)) within
    have tailWithin : tailSize ≤ budget := Nat.le_trans (Nat.le_of_lt (by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))) within
    obtain ⟨middleStore, middleMap, middleWorld, slots, middleHeaps, maps, worlds, preservation, metadata,
        effect, count, typed, ⟨reached, related, nextAdmitted⟩, continuation⟩ :=
      CellAwareScopeBareAssignmentHeads.preserves_value bridge functions extension transport head bare
        environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation unique assignmentTyped
        (children childSize childStrict) snapshot childTrace write
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented,
        finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, finalEffect, last, lastRelated, post⟩ :=
      tail tailSize tailWithin (environments.extend maps worlds) middleHeaps (locals.mono metadata)
        (DataPlaceChildExpressions.prefix_agrees agrees slots) typed runtime covers sameLedger suffix
        reached nextAdmitted (authority.transport effect) (physical.transport effect preservation) owner sameLocation ready remainingTrace
    have native := (continuation body (LocalLoop.controlType type)).wrap (by
      simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreCompatibleDataPlaces.shift,
        SourceCoreDataPlaces.shift] using evaluated)
    exact ⟨value, finalStore, finalMap, finalWorld, native, represented, finalHeaps,
      maps.trans finalMaps, worlds.trans finalWorlds, preservation.trans finalFrame, metadata.trans finalMetadata,
      effect.trans finalEffect, last, protocol.trans related lastRelated, post⟩

include transport sourceEq unique found form bare extension invalidToken in
theorem reflects (budget : Nat)
    (children : CellAwareScopeExpressionBounds.ReflectsBelow bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) named stages invocation certificate faults budget)
    (tail : CellAwareScopeFlowBounds.ReflectsAtMost bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) named producer stages invocation faults
      administrative scope mode rest expected type body budget) :
    ∀ size, size ≤ budget → CellAwareScopeFlowBounds.ReflectsAt bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) named producer stages invocation faults
      administrative scope mode (id :: rest) expected type (head.emit body (LocalLoop.controlType type)) size := by
  intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
    initial admitted authority physical owner sameLocation ready completed
  have assignmentTyped := ProtectedStateImperativeTypedSourceSites.assignment unique
    (sourceEq.symm ▸ ProtectedStateImperativeTypedSourceSites.head sourceTyped) found form
  have suffix := ProtectedStateImperativeStatementSuffixTyping.assignment
    (sourceEq ▸ unique) sourceTyped (sourceEq ▸ found) form
  have result := CellAwareScopeBareAssignmentHeads.reflects_bounded bridge functions extension transport
    head bare environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation unique assignmentTyped
    budget children invalidToken completed within
  cases result with
  | fault snapshot trace same matched finalHeaps maps worlds preservation metadata effect reached related stable =>
    cases same
    exact ⟨Staging.Recursive.Size.stepSize [_], context, _, _, _, _,
      .assignBareFault (lookupStatement?_sound found) form snapshot trace, .fault matched,
      finalHeaps, maps, worlds, preservation, metadata, effect, reached, related, fault_post bridge reached stable⟩
  | operands snapshot trace currentRead rootType initialized path invalid same matched finalHeaps maps worlds preservation metadata effect reached related stable =>
    cases same
    exact ⟨Staging.Recursive.Size.stepSize [_], context, _, _, _, _,
      .assignBareOperands (lookupStatement?_sound found) form snapshot trace currentRead rootType initialized path invalid,
      .fault matched, finalHeaps, maps, worlds, preservation, metadata, effect, reached, related,
      fault_post bridge (context := context) (expected := expected) (failure := .semantic _) reached stable⟩
  | success snapshot childTrace write middleHeaps maps worlds preservation metadata effect count typed reached related nextAdmitted strict remaining =>
    obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented,
        finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, finalEffect, last, lastRelated, post⟩ :=
      tail _ (Nat.le_trans (Nat.le_of_lt strict) within) (environments.extend maps worlds) middleHeaps (locals.mono metadata)
        (DataPlaceChildExpressions.prefix_agrees agrees _) typed runtime covers sameLedger suffix
        reached nextAdmitted (authority.transport effect) (physical.transport effect preservation) owner sameLocation ready
        (by simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreCompatibleDataPlaces.shift,
          SourceCoreDataPlaces.shift] using remaining)
    exact ⟨Staging.Recursive.Size.stepSize [_, sourceSize], finalContext, outcome, after, finalMap, finalWorld,
      .assignBare (lookupStatement?_sound found) form snapshot childTrace write trace, represented,
      finalHeaps, maps.trans finalMaps, worlds.trans finalWorlds, preservation.trans finalFrame,
      metadata.trans finalMetadata, effect.trans finalEffect, last, protocol.trans related lastRelated, post⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareScopeBareAssignmentFlow
end
