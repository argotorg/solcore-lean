import Solcore.SourceSemantics.CoreLowering.Internal.Protected.StateExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.Paths
import Solcore.SourceSemantics.CoreLowering.Internal.Data.PlaceMappings
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.AssignmentContracts
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.BareAssignments
import Solcore.SourceSemantics.CoreLowering.Internal.Diagnostics.ReachedExpressionFaults
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.CoercionMethods

/-!
# Protected contracts: state and place assignments

Place assignments on the protected state, their contracts, and reached place diagnostics.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedPlaceReachedDiagnostics
/-! Place diagnostics are selected at the actual reached state. The phase
receipt retains the prepared raw path, ordered represented keys and live root.
Helper effects relate that same phase to the actual fault post. These receipts
contain no assignment execution law and use the existing fault-tree producer. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedPlaceReachedDiagnostics
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleMixedRoute
open SourceCoreCompatibleDataPlaces CompatiblePlaceLiveRoot CompatibleMapping CompatibleMapping.MixedPaths
universe u v
variable {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions}
  {functions : FunctionModel checked.catalog ambient} {Records : Type v}
  {protocol : ProtectedStateTransition.Protocol.{u, v} Records}
  {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
  {place : PlaceResolution} {prepared : Prepared} {leaf : TypeSystem.Ty}
  {environment : Dynamic.Environment}
  {initialIndex reachedIndex : ProtectedStateTransition.Index}
  {initial : protocol.State initialIndex} {reached : protocol.State reachedIndex}
  {reason : Dynamic.SemanticFault} {token : Word}

def MissingWitness (checked : Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient)
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (source : TypedSource) (site : SourceCoreElaboration.ErrorSite) (place : PlaceResolution)
    (prepared : Prepared) (leaf : TypeSystem.Ty)
    {initialIndex reachedIndex : ProtectedStateTransition.Index}
    (initial : protocol.State initialIndex) (reached : protocol.State reachedIndex)
    (reason : Dynamic.SemanticFault) (token : Word) : Prop :=
  ∃ (phaseIndex : ProtectedStateTransition.Index) (phase : protocol.State phaseIndex)
    (location : Dynamic.Location) (target : Location) (cell : Dynamic.Cell)
    (optional : Value) (root : Dynamic.Value) (value : Value) (keys : List Value)
    (resolved : List Dynamic.EvaluatedProjection) (count : Nat)
    (path : PreparedPath checked source site cell.type place.projections 0 prepared.steps prepared.keys leaf),
    protocol.Relates initial phase ∧ protocol.Relates phase reached ∧
    phaseIndex.scope = initialIndex.scope ∧ phaseIndex.canonical = initialIndex.canonical ∧
    reachedIndex = phaseIndex.extend phaseIndex.mapping reachedIndex.world phaseIndex.heap reachedIndex.store ∧
    WorldExtends phaseIndex.world reachedIndex.world ∧
    AdministrativePreserved phaseIndex.mapping phaseIndex.store phaseIndex.mapping reachedIndex.store ∧
    RootRead checked registry functions phaseIndex.mapping phaseIndex.world prepared phaseIndex.heap phaseIndex.store
      location target cell optional root value ∧
    cell.type = prepared.route.rootSourceType ∧
    Arguments checked registry functions phaseIndex.mapping phaseIndex.world source site keys path resolved ∧
    Dynamic.ProjectionsFaults (some root) resolved reason ∧
    FaultToken checked registry root prepared.steps resolved reason token count ∧
    FaultTree checked registry functions phaseIndex.mapping phaseIndex.world prepared keys root value
      prepared.route.rootType prepared.steps resolved reason token count

def UninitializedWitness (checked : Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient)
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (environment : Dynamic.Environment) (place : PlaceResolution) (prepared : Prepared)
    {initialIndex reachedIndex : ProtectedStateTransition.Index}
    (initial : protocol.State initialIndex) (reached : protocol.State reachedIndex)
    (location : Dynamic.Location) : Prop :=
  ∃ (phaseIndex : ProtectedStateTransition.Index) (phase : protocol.State phaseIndex)
    (target : Location) (cell : Dynamic.Cell) (optional : Value)
    (sources : List Dynamic.Value) (resolved : List Dynamic.EvaluatedProjection),
    protocol.Relates initial phase ∧ protocol.Relates phase reached ∧
    phaseIndex.scope = initialIndex.scope ∧ phaseIndex.canonical = initialIndex.canonical ∧
    reachedIndex = phaseIndex.extend phaseIndex.mapping reachedIndex.world phaseIndex.heap reachedIndex.store ∧
    WorldExtends phaseIndex.world reachedIndex.world ∧
    AdministrativePreserved phaseIndex.mapping phaseIndex.store phaseIndex.mapping reachedIndex.store ∧
    Dynamic.Environment.LooksUp environment place.root location ∧
    Dynamic.Heap.Reads phaseIndex.heap location cell ∧
    ReferenceRepresents phaseIndex.mapping phaseIndex.world location target prepared.route.rootType ∧
    phaseIndex.store.read? target = some optional ∧
    GenericHeap.CellRepresents (CompatibleAmbientHeap.payloadModel checked registry functions)
      phaseIndex.mapping phaseIndex.world cell optional prepared.route.rootType ∧
    cell.type = prepared.route.rootSourceType ∧ cell.value = none ∧
    (¬ ∃ key value, cell.type = .mapping key value) ∧ prepared.steps ≠ [] ∧
    DataPlaceKeyOrder.Values place.projections sources resolved ∧ resolved ≠ []

def MissingPost (checked : Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions} (functions : FunctionModel checked.catalog ambient)
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (source : TypedSource) (site : SourceCoreElaboration.ErrorSite) (place : PlaceResolution)
    (prepared : Prepared) (leaf : TypeSystem.Ty) {initialIndex : ProtectedStateTransition.Index}
    (initial : protocol.State initialIndex) (reachedIndex : ProtectedStateTransition.Index)
    (reason : Dynamic.SemanticFault) (token : Word) : Prop :=
  ∃ reached : protocol.State reachedIndex, protocol.Relates initial reached ∧
    MissingWitness checked registry functions protocol source site place prepared leaf initial reached reason token

def UninitializedPost (checked : Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions} (functions : FunctionModel checked.catalog ambient)
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (environment : Dynamic.Environment) (place : PlaceResolution) (prepared : Prepared)
    {initialIndex : ProtectedStateTransition.Index} (initial : protocol.State initialIndex)
    (reachedIndex : ProtectedStateTransition.Index) (location : Dynamic.Location) : Prop :=
  ∃ reached : protocol.State reachedIndex, protocol.Relates initial reached ∧
    UninitializedWitness checked registry functions protocol environment place prepared initial reached location

theorem MissingPost.forget
    (post : MissingPost checked registry functions protocol source site place prepared leaf initial reachedIndex reason token) :
    ProtectedStateTransition.Transition protocol initial reachedIndex := by
  obtain ⟨reached, related, _⟩ := post
  exact ⟨reached, related⟩

theorem UninitializedPost.forget {location : Dynamic.Location}
    (post : UninitializedPost checked registry functions protocol environment place prepared initial reachedIndex location) :
    ProtectedStateTransition.Transition protocol initial reachedIndex := by
  obtain ⟨reached, related, _⟩ := post
  exact ⟨reached, related⟩

def MissingFor (checked : Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions} (functions : FunctionModel checked.catalog ambient)
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (source : TypedSource) (site : SourceCoreElaboration.ErrorSite) (place : PlaceResolution)
    (prepared : Prepared) (leaf : TypeSystem.Ty) {initialIndex : ProtectedStateTransition.Index}
    (initial : protocol.State initialIndex) (faults : FunctionCalls.FaultRep) : Prop :=
  ∀ {reachedIndex reason token} (reached : protocol.State reachedIndex), protocol.Relates initial reached →
    MissingWitness checked registry functions protocol source site place prepared leaf initial reached reason token →
    faults reason token

def UninitializedFor (checked : Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions} (functions : FunctionModel checked.catalog ambient)
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (environment : Dynamic.Environment) (place : PlaceResolution) (prepared : Prepared)
    {initialIndex : ProtectedStateTransition.Index} (initial : protocol.State initialIndex)
    (faults : FunctionCalls.FaultRep) : Prop :=
  ∀ {reachedIndex location} (reached : protocol.State reachedIndex), protocol.Relates initial reached →
    UninitializedWitness checked registry functions protocol environment place prepared initial reached location →
    faults (.uninitializedLocation location) prepared.invalidProjection

theorem MissingFor.of_uniform {faults : FunctionCalls.FaultRep}
    (law : ∀ {root resolved reason token count},
      FaultToken checked registry root prepared.steps resolved reason token count → faults reason token) :
    MissingFor checked registry functions protocol source site place prepared leaf initial faults := by
  intro _ _ _ _ _ witness
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, receipt, _⟩ := witness
  exact law receipt

theorem UninitializedFor.of_uniform {faults : FunctionCalls.FaultRep}
    [FunctionCalls.FaultTokens faults] (law : ∀ location, faults (.uninitializedLocation location) prepared.invalidProjection) :
    UninitializedFor checked registry functions protocol environment place prepared initial faults := by
  intro _ location _ _ _
  exact law location

/-- The independent Source initial-root receipt selects the actual heap payload. -/
theorem root_of_initial {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient} {mapping : LocationMap} {world : StoreTyping}
    {prepared : Prepared} {heap : Dynamic.Heap} {store : Store} {location : Dynamic.Location} {target : Location}
    {cell : Dynamic.Cell} {sourceRoot : Dynamic.Value}
    (heaps : CompatibleHeap.HeapRepresents compilation.checked registry functions mapping world heap store)
    (reference : ReferenceRepresents mapping world location target prepared.route.rootType)
    (read : Dynamic.Heap.Reads heap location cell)
    (initial : Dynamic.RootInitialValue cell (some sourceRoot))
    (virtual : ∀ key value, cell.type = .mapping key value → VirtualRoot.Generated compilation prepared.route key value)
    (extension : SourceCoreRawMetadata.Extends compilation.registry registry) :
    ∃ optional rootValue, RootRead compilation.checked registry functions mapping world prepared heap store
      location target cell optional sourceRoot rootValue := by
  cases initial with
  | initialized =>
    obtain ⟨value, root⟩ := CompatibleHeap.HeapRepresents.initialized_root heaps reference read
    exact ⟨_, value, root⟩
  | emptyMapping key value =>
    obtain ⟨native, root⟩ := CompatibleHeap.HeapRepresents.virtual_root heaps reference read
      (virtual key value rfl) extension
    exact ⟨_, native, root⟩

end Solcore.SourceSemantics.CoreLowering.ProtectedPlaceReachedDiagnostics
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedStatePlaceAssignment
/-! Actual projected assignment phases share measured expression and sequence
contracts. Compatibility is a proof-only observer of the original Entry. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedStatePlaceAssignment
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open ProtectedStateTransition

def legacyProtocol (guarded : ProtectedExpressionMeaning.Entry) : Protocol Unit where
  State index := PLift (guarded index.scope index.mapping index.world index.heap index.store index.canonical)
  records _ := ()
  Relates _ _ := True
  refl _ := trivial
  trans _ _ := trivial

def legacyTransport {guarded : ProtectedExpressionMeaning.Entry}
    (transport : ProtectedExpressionMeaning.Transport guarded) : AdministrativeTransport (legacyProtocol guarded) where
  extend := fun {_initial} state {_mapping _world _heap _store} maps worlds frame metadata =>
    ⟨transport.extend state.down maps worlds frame metadata⟩
  related := fun {_initial} _state {_mapping _world _heap _store} _maps _worlds _frame _metadata => trivial
  records_eq := fun {_initial} _state {_mapping _world _heap _store} _maps _worlds _frame _metadata => rfl

variable {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
  {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {source : TypedSource} {certificate : GenericExpressionMeaning.Certificate}
  {faults : GenericExpressionMeaning.FaultRep} {entry : ProtectedExpressionMeaning.Entry}

/-- Only the old observer derives its lifted post through proved effects. -/
theorem legacy_preserves (transport : ProtectedExpressionMeaning.Transport entry) {size : Nat}
    (meaning : RecursiveNamedBoundedContracts.PreservesAt size model program context evidence source certificate faults entry) :
    PreservesAt (legacyProtocol entry) model program context evidence source certificate faults size := by
  intro scope id lowered certified node found mapping world administrative environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees typed initial trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
    meaning certified found environments heaps locals agrees typed initial.down trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata,
    ⟨⟨transport.extend initial.down maps worlds frame metadata⟩, trivial⟩⟩

theorem legacy_reflects (transport : ProtectedExpressionMeaning.Transport entry) {size : Nat}
    (meaning : RecursiveNamedBoundedContracts.ReflectsAt size model program context evidence source certificate faults entry) :
    ReflectsAt (legacyProtocol entry) model program context evidence source certificate faults size := by
  intro scope id lowered certified node found mapping world administrative environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees typed initial evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
    meaning certified found environments heaps locals agrees typed initial.down evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata,
    ⟨⟨transport.extend initial.down maps worlds frame metadata⟩, trivial⟩⟩

end Solcore.SourceSemantics.CoreLowering.ProtectedStatePlaceAssignment
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedStatePlaceAssignmentContracts
/-! Actual assignment phases retain source measurements and the original strict
native continuation grades, together with each concrete reached state.
Completed write receipts keep all seven typed temporary slots. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedStatePlaceAssignmentContracts
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning CoreProof
open CompatiblePayload CompatibleEquality CompatibleHeap SourceCoreCompatibleDataPlaces DataPlaceExecution
universe u v

inductive KeyResultAt {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records) (size : Nat) (checked : Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (faults : FaultRep)
    (prepared : Prepared) (codes : List SourceCoreBasic.LoweredExpr) (sourceTypes : List TypeSystem.Ty)
    (place : PlaceResolution) (environment : Dynamic.Environment) (coreEnvironment : Environment)
    (before : Dynamic.Heap) (store : Store) (mapping : LocationMap) (world : StoreTyping)
    (scope : SourceCoreLocalCell.Scope) (canonical : Environment)
    (initialState : protocol.State ⟨scope, mapping, world, before, store, canonical⟩) (index : Nat)
    (rhs next : Expr) (outputType : Ty) (operator : Option Frontend.SourceCoreDataPlaces.Modifier) (bitNot : Bool) (invalid : Word)
    (result : Value) (finalStore : Store) : Prop where
  | fault {sourceSize : Nat} {reason : Dynamic.SemanticFault} {token : Word} {after : Dynamic.Heap}
      {finalMap : LocationMap} {finalWorld : StoreTyping}
      (sourceFault : SourceExecutionSize.SourcePlaceFaults program sourceSize context evidence source environment before place reason after)
      (resultEq : result = .inLeft outputType (.word token)) (tokenRep : faults reason token)
      (heaps : HeapRepresents checked registry functions finalMap finalWorld after finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap finalStore) (metadata : Dynamic.HeapMetadataExtend before after)
      (post : ProtectedStateTransition.Transition protocol initialState ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩) :
      KeyResultAt protocol size checked registry functions program context evidence source faults prepared codes sourceTypes place environment
        coreEnvironment before store mapping world scope canonical initialState index rhs next outputType operator bitNot invalid result finalStore
  | keys {sourceSize remainingSize : Nat} {location : Dynamic.Location} {resolved : List Dynamic.EvaluatedProjection} {after : Dynamic.Heap}
      (lookup : Dynamic.Environment.LooksUp environment place.root location)
      (trace : SourceExecutionSize.SourceProjectionsEvaluate program sourceSize context evidence source environment before place.projections resolved after)
      (execution : CompatiblePlaceTargetKeys.Execution checked registry functions prepared place codes sourceTypes location resolved
        coreEnvironment before after store mapping world index)
      (bounded : remainingSize < size)
      (continuation : EvaluationSize remainingSize (keysEnvironment prepared.route.rootType execution.target (packValues execution.values) coreEnvironment)
        execution.keyStore (CompatiblePlaceKeyReflection.remainder prepared (SourceCoreCalls.packArguments codes).type rhs next outputType operator bitNot invalid) result finalStore)
      (post : ProtectedStateTransition.Transition protocol initialState ⟨scope, execution.keyMap, execution.keyWorld, after, execution.keyStore, canonical⟩) :
      KeyResultAt protocol size checked registry functions program context evidence source faults prepared codes sourceTypes place environment
        coreEnvironment before store mapping world scope canonical initialState index rhs next outputType operator bitNot invalid result finalStore


theorem KeyResultAt.forget {Records : Type v} {protocol : ProtectedStateTransition.Protocol.{u, v} Records} {size : Nat} {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {faults : FaultRep}
    {prepared : Prepared} {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty}
    {place : PlaceResolution} {environment : Dynamic.Environment} {coreEnvironment : Environment}
    {before : Dynamic.Heap} {store : Store} {mapping : LocationMap} {world : StoreTyping}
    {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
    {initialState : protocol.State ⟨scope, mapping, world, before, store, canonical⟩} {index : Nat}
    {rhs next : Expr} {outputType : Ty} {operator : Option Frontend.SourceCoreDataPlaces.Modifier} {bitNot : Bool} {invalid : Word}
    {result : Value} {finalStore : Store}
    (receipt : KeyResultAt protocol size checked registry functions program context evidence source faults prepared codes sourceTypes place environment
        coreEnvironment before store mapping world scope canonical initialState index rhs next outputType operator bitNot invalid result finalStore) :
    RecursiveNamedPlaceAssignmentContracts.KeyResultAt size checked registry functions program context evidence source faults prepared codes sourceTypes place environment
        coreEnvironment before store mapping world index rhs next outputType operator bitNot invalid result finalStore := by
  cases receipt with
  | fault trace same represented heaps maps worlds frame metadata _ =>
    exact .fault trace same represented heaps maps worlds frame metadata
  | keys lookup trace execution bounded remaining _ =>
    exact .keys lookup trace execution bounded remaining
inductive PrefixResultAt {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records) (size : Nat) (checked : Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (faults : FaultRep)
    (prepared : Prepared) (codes : List SourceCoreBasic.LoweredExpr) (sourceTypes : List TypeSystem.Ty)
    (place : PlaceResolution) (leaf : TypeSystem.Ty) (environment : Dynamic.Environment) (coreEnvironment : Environment)
    (before : Dynamic.Heap) (store : Store) (mapping : LocationMap) (world : StoreTyping)
    (scope : SourceCoreLocalCell.Scope) (canonical : Environment)
    (initialState : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (rhs next : Expr) (outputType : Ty) (operator : Option Frontend.SourceCoreDataPlaces.Modifier) (bitNot : Bool) (invalid : Word)
    (result : Value) (finalStore : Store) : Prop where
  | fault {sourceSize : Nat} {reason : Dynamic.SemanticFault} {token : Word} {after : Dynamic.Heap}
      {finalMap : LocationMap} {finalWorld : StoreTyping}
      (sourceFault : SourceExecutionSize.SourcePlaceFaults program sourceSize context evidence source environment before place reason after)
      (resultEq : result = .inLeft outputType (.word token)) (tokenRep : faults reason token)
      (heaps : HeapRepresents checked registry functions finalMap finalWorld after finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap finalStore) (metadata : Dynamic.HeapMetadataExtend before after)
      (post : ProtectedStateTransition.Transition protocol initialState ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩) :
      PrefixResultAt protocol size checked registry functions program context evidence source faults prepared codes sourceTypes place leaf environment
        coreEnvironment before store mapping world scope canonical initialState rhs next outputType operator bitNot invalid result finalStore
  | resolved {sourceSize remainingSize : Nat} {target : Dynamic.ResolvedPlace} {after : Dynamic.Heap}
      (sourceTrace : SourceExecutionSize.SourcePlaceResolves program sourceSize context evidence source environment before place target after)
      (execution : CompatiblePlaceResolution.Execution checked registry functions prepared codes sourceTypes place leaf target
        coreEnvironment store mapping world before after)
      (bounded : remainingSize < size)
      (continuation : EvaluationSize remainingSize (snapshotEnvironment prepared.route.rootType execution.target (packValues execution.values)
        (.inRight .unit execution.snapshot) coreEnvironment) execution.store
        (CompatiblePlacePrefixReflection.remainder prepared (SourceCoreCalls.packArguments codes).type rhs next outputType operator bitNot invalid) result finalStore)
      (post : ProtectedStateTransition.Transition protocol initialState ⟨scope, execution.mapping, execution.world, after, execution.store, canonical⟩) :
      PrefixResultAt protocol size checked registry functions program context evidence source faults prepared codes sourceTypes place leaf environment
        coreEnvironment before store mapping world scope canonical initialState rhs next outputType operator bitNot invalid result finalStore

theorem PrefixResultAt.forget {Records : Type v} {protocol : ProtectedStateTransition.Protocol.{u, v} Records} {size : Nat} {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {faults : FaultRep}
    {prepared : Prepared} {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty}
    {place : PlaceResolution} {leaf : TypeSystem.Ty} {environment : Dynamic.Environment} {coreEnvironment : Environment}
    {before : Dynamic.Heap} {store : Store} {mapping : LocationMap} {world : StoreTyping}
    {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
    {initialState : protocol.State ⟨scope, mapping, world, before, store, canonical⟩}
    {rhs next : Expr} {outputType : Ty} {operator : Option Frontend.SourceCoreDataPlaces.Modifier} {bitNot : Bool} {invalid : Word}
    {result : Value} {finalStore : Store}
    (receipt : PrefixResultAt protocol size checked registry functions program context evidence source faults prepared codes sourceTypes place leaf environment
        coreEnvironment before store mapping world scope canonical initialState rhs next outputType operator bitNot invalid result finalStore) :
    RecursiveNamedPlaceAssignmentContracts.PrefixResultAt size checked registry functions program context evidence source faults prepared codes sourceTypes place leaf environment
      coreEnvironment before store mapping world rhs next outputType operator bitNot invalid result finalStore := by
  cases receipt with
  | fault trace same represented heaps maps worlds frame metadata _ =>
    exact .fault trace same represented heaps maps worlds frame metadata
  | resolved trace execution bound remaining _ =>
    exact .resolved trace execution bound remaining

inductive RhsResultAt {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records) (size : Nat) (checked : Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (faults : FaultRep)
    (prepared : Prepared) (codes : List SourceCoreBasic.LoweredExpr) (sourceTypes : List TypeSystem.Ty)
    (place : PlaceResolution) (leaf : TypeSystem.Ty) (environment : Dynamic.Environment) (coreEnvironment : Environment)
    (before : Dynamic.Heap) (store : Store) (mapping : LocationMap) (world : StoreTyping)
    (scope : SourceCoreLocalCell.Scope) (canonical : Environment)
    (initialState : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (rhs : ExpressionId) (node : ExpressionNode) (lowered : SourceCoreBasic.LoweredExpr) (next : Expr) (outputType : Ty)
    (operator : Syntax.ValueAssignOp) (invalid : Word) (result : Value) (finalStore : Store) : Prop where
  | fault {sourceSize : Nat} {reason : Dynamic.SemanticFault} {token : Word} {after : Dynamic.Heap}
      {finalMap : LocationMap} {finalWorld : StoreTyping}
      (sourceFault : SourceExecutionSize.SourcePlaceAssignmentFaults program sourceSize context evidence source environment before place operator rhs reason after)
      (resultEq : result = .inLeft outputType (.word token)) (tokenRep : faults reason token)
      (heaps : HeapRepresents checked registry functions finalMap finalWorld after finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap finalStore) (metadata : Dynamic.HeapMetadataExtend before after)
      (post : ProtectedStateTransition.Transition protocol initialState ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩) :
      RhsResultAt protocol size checked registry functions program context evidence source faults prepared codes sourceTypes place leaf environment
        coreEnvironment before store mapping world scope canonical initialState rhs node lowered next outputType operator invalid result finalStore
  | ready {sourceSize remainingSize : Nat} {target : Dynamic.ResolvedPlace} {targetHeap : Dynamic.Heap}
      (sourceTrace : SourceExecutionSize.SourcePlaceResolves program sourceSize context evidence source environment before place target targetHeap)
      (resolution : CompatiblePlaceResolution.Execution checked registry functions prepared codes sourceTypes place leaf target
        coreEnvironment store mapping world before targetHeap)
      (right : CompatiblePlaceRhsReflection.Execution checked registry functions program context evidence source faults environment prepared codes sourceTypes place leaf target
        coreEnvironment store mapping world before targetHeap resolution rhs node lowered)
      {rhsSize : Nat}
      (rhsTrace : SourceExecutionSize.ExpressionEvaluates program rhsSize context evidence source environment targetHeap rhs right.right right.heap)
      (bounded : remainingSize < size)
      (continuation : EvaluationSize remainingSize (rhsEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
        (.inRight .unit resolution.snapshot) right.value coreEnvironment) right.store
        (CompatiblePlaceRhsReflection.remainder prepared (SourceCoreCalls.packArguments codes).type next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) invalid) result finalStore)
      (post : ProtectedStateTransition.Transition protocol initialState ⟨scope, right.mapping, right.world, right.heap, right.store, canonical⟩) :
      RhsResultAt protocol size checked registry functions program context evidence source faults prepared codes sourceTypes place leaf environment
        coreEnvironment before store mapping world scope canonical initialState rhs node lowered next outputType operator invalid result finalStore

theorem RhsResultAt.forget {Records : Type v} {protocol : ProtectedStateTransition.Protocol.{u, v} Records} {size : Nat} {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {faults : FaultRep}
    {prepared : Prepared} {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty}
    {place : PlaceResolution} {leaf : TypeSystem.Ty} {environment : Dynamic.Environment} {coreEnvironment : Environment}
    {before : Dynamic.Heap} {store : Store} {mapping : LocationMap} {world : StoreTyping}
    {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
    {initialState : protocol.State ⟨scope, mapping, world, before, store, canonical⟩}
    {rhs : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr} {next : Expr} {outputType : Ty}
    {operator : Syntax.ValueAssignOp} {invalid : Word} {result : Value} {finalStore : Store}
    (receipt : RhsResultAt protocol size checked registry functions program context evidence source faults prepared codes sourceTypes place leaf environment
        coreEnvironment before store mapping world scope canonical initialState rhs node lowered next outputType operator invalid result finalStore) :
    RecursiveNamedPlaceAssignmentContracts.RhsResultAt size checked registry functions program context evidence source faults prepared codes sourceTypes place leaf environment
      coreEnvironment before store mapping world rhs node lowered next outputType operator invalid result finalStore := by
  cases receipt with
  | fault trace same represented heaps maps worlds frame metadata _ =>
    exact .fault trace same represented heaps maps worlds frame metadata
  | ready trace execution right rhsTrace bound remaining _ =>
    exact .ready trace execution right rhsTrace bound remaining

inductive ResultAt {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records) (size : Nat) (checked : Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (faults : FaultRep)
    (prepared : Prepared) (keyType : Ty) (actualContext : Core.Context)
    (place : PlaceResolution) (operator : Syntax.ValueAssignOp) (rhs : ExpressionId)
    (environment : Dynamic.Environment) (coreEnvironment : Environment)
    (before : Dynamic.Heap) (store : Store) (mapping : LocationMap) (world : StoreTyping)
    (scope : SourceCoreLocalCell.Scope) (canonical : Environment)
    (initialState : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (next : Expr) (outputType : Ty) (result : Value) (finalStore : Store) : Prop where
  | fault {sourceSize : Nat} {reason : Dynamic.SemanticFault} {token : Word} {after : Dynamic.Heap}
      {finalMap : LocationMap} {finalWorld : StoreTyping}
      (trace : SourceExecutionSize.SourcePlaceAssignmentFaults program sourceSize context evidence source environment before place operator rhs reason after)
      (resultEq : result = .inLeft outputType (.word token)) (tokenRep : faults reason token)
      (heaps : HeapRepresents checked registry functions finalMap finalWorld after finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap finalStore) (metadata : Dynamic.HeapMetadataExtend before after)
      (post : ProtectedStateTransition.Transition protocol initialState ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩) :
      ResultAt protocol size checked registry functions program context evidence source faults prepared keyType actualContext place operator rhs environment coreEnvironment
        before store mapping world scope canonical initialState next outputType result finalStore
  | committed {sourceSize remainingSize : Nat} {updated : Dynamic.Value} {after : Dynamic.Heap} {written : Store}
      {finalMap : LocationMap} {finalWorld : StoreTyping} {slots : Environment}
      (trace : SourceExecutionSize.SourcePlaceAssignment program sourceSize context evidence source (Dynamic.AssignmentValueApplies operator)
        environment before place rhs updated after)
      (heaps : HeapRepresents checked registry functions finalMap finalWorld after written)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap written) (metadata : Dynamic.HeapMetadataExtend before after)
      (length : slots.length = 7)
      (typed : RuntimeEnvironmentHasTypes finalWorld (slots ++ coreEnvironment)
        (CompatibleRenamedPlaceSuccess.writtenContext prepared keyType actualContext) ambient.definitions)
      (post : ProtectedStateTransition.Transition protocol initialState ⟨scope, finalMap, finalWorld, after, written, canonical⟩)
      (bounded : remainingSize < size)
      (continuation : EvaluationSize remainingSize (slots ++ coreEnvironment) written (shift 7 next) result finalStore) :
      ResultAt protocol size checked registry functions program context evidence source faults prepared keyType actualContext place operator rhs environment coreEnvironment
        before store mapping world scope canonical initialState next outputType result finalStore

theorem ResultAt.forget {Records : Type v} {protocol : ProtectedStateTransition.Protocol.{u, v} Records} {size : Nat} {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {faults : FaultRep}
    {prepared : Prepared} {keyType : Ty} {actualContext : Core.Context} {place : PlaceResolution}
    {operator : Syntax.ValueAssignOp} {rhs : ExpressionId} {environment : Dynamic.Environment} {actual : Environment}
    {before : Dynamic.Heap} {store : Store} {mapping : LocationMap} {world : StoreTyping}
    {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
    {initialState : protocol.State ⟨scope, mapping, world, before, store, canonical⟩} {next : Expr} {output : Ty} {value : Value} {finalStore : Store}
    (result : ResultAt protocol size checked registry functions program context evidence source faults prepared keyType actualContext place operator rhs
      environment actual before store mapping world scope canonical initialState next output value finalStore) :
    RecursiveNamedPlaceAssignmentContracts.ResultAt size checked registry functions program context evidence source faults prepared keyType actualContext place operator rhs environment actual
      before store mapping world next output value finalStore := by
  cases result with
  | fault trace same represented heaps maps worlds frame metadata _ =>
    exact .fault trace same represented heaps maps worlds frame metadata
  | committed trace heaps maps worlds frame metadata count typed _ bound remaining =>
    exact .committed trace heaps maps worlds frame metadata count typed bound remaining

theorem ResultAt.weaken_bound {Records : Type v} {protocol : ProtectedStateTransition.Protocol.{u, v} Records} {size larger : Nat} {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {faults : FaultRep}
    {prepared : Prepared} {keyType : Ty} {actualContext : Core.Context} {place : PlaceResolution}
    {operator : Syntax.ValueAssignOp} {rhs : ExpressionId} {environment : Dynamic.Environment} {actual : Environment}
    {before : Dynamic.Heap} {store : Store} {mapping : LocationMap} {world : StoreTyping}
    {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
    {initialState : protocol.State ⟨scope, mapping, world, before, store, canonical⟩} {next : Expr} {output : Ty} {value : Value} {finalStore : Store}
    (result : ResultAt protocol size checked registry functions program context evidence source faults prepared keyType actualContext place operator rhs
      environment actual before store mapping world scope canonical initialState next output value finalStore) (bound : size ≤ larger) :
    ResultAt protocol larger checked registry functions program context evidence source faults prepared keyType actualContext place operator rhs
      environment actual before store mapping world scope canonical initialState next output value finalStore := by
  cases result with
  | fault trace same represented heaps maps worlds frame metadata post =>
    exact .fault trace same represented heaps maps worlds frame metadata post
  | committed trace heaps maps worlds frame metadata count typed post smaller remaining =>
    exact .committed trace heaps maps worlds frame metadata count typed post (Nat.lt_of_lt_of_le smaller bound) remaining

end Solcore.SourceSemantics.CoreLowering.ProtectedStatePlaceAssignmentContracts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedStateBareAssignment
/-! Actual bare-assignment prefix endpoints retain the expression-produced state
and the real seven-slot continuation. Grades come from the existing Source and
Core derivations. Compatibility uses a constant proof witness. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedStateBareAssignment
open Core Frontend SourceInference GeneralHeap ReadOnly CoreProof
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleBareAssignment
open SourceCoreCompatibleDataPlaces DataPlaceExecution
open GenericExpressionMeaning (FaultRep)
open ProtectedStateTransition
universe u v

def unitProtocol : Protocol Unit where
  State _ := Unit
  records _ := ()
  Relates _ _ := True
  refl _ := trivial
  trans _ _ := trivial

def unitTransport : AdministrativeTransport unitProtocol where
  extend := fun {_} _ {_ _ _ _} _ _ _ _ => ()
  related := by intros; trivial
  records_eq := by intros; rfl

inductive ResultAt {Records : Type v} (protocol : Protocol.{u, v} Records) (size : Nat) (compilation : SourceCoreCompatibleDataPlaces.Context) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions compilation.checked.catalog.definitions} (functions : FunctionModel compilation.checked.catalog ambient)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource)
    (faults : FaultRep) (prepared : Prepared) (place : PlaceResolution) (operator : Syntax.ValueAssignOp)
    (scope : Scope) (canonical : Environment)
    (environment : Dynamic.Environment) (before : Dynamic.Heap) (store : Store) (mapping : LocationMap) (world : StoreTyping)
    (rhs : ExpressionId) (actual : Environment) (actualContext : Core.Context) (ξ : Renaming)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (next : Expr) (outputType : Ty) (value : Value) (finalStore : Store) : Prop where
  | fault {sourceSize : Nat} {reason : Dynamic.SemanticFault} {token : Word} {after : Dynamic.Heap} {finalMap : LocationMap} {finalWorld : StoreTyping}
      (trace : SourceExecutionSize.SourcePlaceAssignmentFaults program sourceSize context evidence source environment before place operator rhs reason after)
      (result : value = .inLeft outputType (.word token)) (represented : faults reason token)
      (heaps : HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap finalStore) (metadata : Dynamic.HeapMetadataExtend before after)
      (post : Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩) :
      ResultAt protocol size compilation registry functions program context evidence source faults prepared place operator scope canonical environment before store mapping world
        rhs actual actualContext ξ initial next outputType value finalStore
  | success {sourceSize remainingSize : Nat} {updated : Dynamic.Value} {updatedValue : Value} {after : Dynamic.Heap} {commitStore : Store}
      {finalMap : LocationMap} {finalWorld : StoreTyping} {slots : Environment}
      (trace : SourceExecutionSize.SourcePlaceAssignment program sourceSize context evidence source (Dynamic.AssignmentValueApplies operator)
        environment before place rhs updated after)
      (represented : ValueRep compilation.checked registry functions finalMap finalWorld prepared.route.rootSourceType updated updatedValue prepared.route.rootType)
      (heaps : HeapRepresents compilation.checked registry functions finalMap finalWorld after commitStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap commitStore) (metadata : Dynamic.HeapMetadataExtend before after)
      (count : slots.length = 7)
      (typed : RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) (writtenContext prepared actualContext) ambient.definitions)
      (bounded : remainingSize < size)
      (continuation : EvaluationSize remainingSize (slots ++ actual) commitStore (shift 7 (next.rename ξ)) value finalStore)
      (post : Transition protocol initial ⟨scope, finalMap, finalWorld, after, commitStore, canonical⟩) :
      ResultAt protocol size compilation registry functions program context evidence source faults prepared place operator scope canonical environment before store mapping world
        rhs actual actualContext ξ initial next outputType value finalStore


theorem ResultAt.forget {Records : Type v} {protocol : Protocol.{u, v} Records}
    {size : Nat} {compilation : SourceCoreCompatibleDataPlaces.Context} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {faults : FaultRep} {prepared : Prepared} {place : PlaceResolution} {operator : Syntax.ValueAssignOp}
    {scope : Scope} {canonical : Environment} {environment : Dynamic.Environment} {before : Dynamic.Heap}
    {store : Store} {mapping : LocationMap} {world : StoreTyping} {rhs : ExpressionId}
    {actual : Environment} {actualContext : Core.Context} {ξ : Renaming}
    {initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩}
    {next : Expr} {outputType : Ty} {value : Value} {finalStore : Store}
    (result : ResultAt protocol size compilation registry functions program context evidence source faults prepared place operator
      scope canonical environment before store mapping world rhs actual actualContext ξ initial next outputType value finalStore) :
    RecursiveNamedBareAssignmentContracts.ResultAt size compilation registry functions program context evidence source faults prepared place operator
      environment before store mapping world rhs actual actualContext ξ next outputType value finalStore := by
  cases result with
  | fault trace same represented heaps maps worlds frame metadata _ =>
    exact .fault trace same represented heaps maps worlds frame metadata
  | success trace represented heaps maps worlds frame metadata count typed bounded continuation _ =>
    exact .success trace represented heaps maps worlds frame metadata count typed bounded continuation

end Solcore.SourceSemantics.CoreLowering.ProtectedStateBareAssignment
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedBareAssignmentRhs
/-! Guarded RHS transport uses the actual three saved native values and their
typing. The canonical installed entry remains unchanged; only actual variable
indices are shifted. The original snapshot/latest/RHS receipts are reused. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedBareAssignment
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap SourceCoreCompatibleDataPlaces DataPlaceExecution
open CompatibleBareAssignment

variable {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
  {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
  {prepared : Prepared} {place : PlaceResolution} {environment : Dynamic.Environment} {actual : Environment}
  {heap : Dynamic.Heap} {store : Store} {mapping : LocationMap} {world : StoreTyping} {index : Nat}
  {faults : FaultRep} {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr} {ξ : Renaming}

variable (snapshot : Snapshot checked registry functions prepared place environment actual heap store mapping world (ξ index))

private theorem latest_of_heap {nextMap : LocationMap} {nextWorld : StoreTyping} {after : Dynamic.Heap} {finalStore : Store}
    (heaps : HeapRepresents checked registry functions nextMap nextWorld after finalStore)
    (maps : LocationMap.Extends mapping nextMap) (worlds : WorldExtends world nextWorld)
    (metadata : Dynamic.HeapMetadataExtend heap after) :
    Nonempty (CompatiblePlaceRhs.Latest checked registry functions nextMap nextWorld prepared snapshot.resolved snapshot.target after finalStore) := by
  obtain ⟨cell, read, sameType, _⟩ := metadata _ _ snapshot.read
  have reference := snapshot.reference.extend maps worlds
  obtain ⟨optional, nativeRead, represented⟩ := heaps.read_at reference read
  exact ⟨⟨cell, optional, read, sameType.trans snapshot.type, reference, nativeRead, represented⟩⟩

universe u v

variable {scope : Scope} {administrativeContext actualContext : Core.Context} {canonical : Environment}
  {certificate : Certificate} {entry : ProtectedExpressionMeaning.Entry}

/-- Assemble the original native RHS receipt and its actual protected post. -/
theorem rhs_of_expression {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (initial : protocol.State ⟨scope, mapping, world, heap, store, canonical⟩)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap} {value : Value}
    {finalStore : Store} {finalMap : LocationMap} {finalWorld : StoreTyping}
    (trace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment heap id outcome after)
    (evaluated : Evaluates (snapshotEnvironment prepared.route.rootType snapshot.target .unit snapshot.value actual)
      store (shift 3 (lowered.expression.rename ξ)) value finalStore)
    (represented : ResultRepresents (payloadModel checked registry functions) finalMap finalWorld node.type lowered.type faults outcome value)
    (heaps : HeapRepresents checked registry functions finalMap finalWorld after finalStore)
    (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
    (frame : AdministrativePreserved mapping store finalMap finalStore) (metadata : Dynamic.HeapMetadataExtend heap after)
    (post : ProtectedStateTransition.Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩) :
    RhsResult (program := program) (context := context) (evidence := evidence) (source := source)
      (faults := faults) (id := id) (node := node) (lowered := lowered) snapshot outcome after value finalStore finalMap finalWorld ∧
      ProtectedStateTransition.Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ :=
  ⟨⟨trace, evaluated, represented, heaps, maps, worlds, frame, metadata,
    latest_of_heap snapshot heaps maps worlds metadata⟩, post⟩

namespace Stateful
variable {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)

theorem rhs_preserves_at (size : Nat)
    (meaning : ProtectedStateTransition.PreservesAt protocol (payloadModel checked registry functions) program context evidence source certificate faults size)
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog)
      mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents checked registry functions mapping world heap store)
    (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (initial : protocol.State ⟨scope, mapping, world, heap, store, canonical⟩)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment heap id outcome after) :
    ∃ value finalStore finalMap finalWorld,
      RhsResult (program := program) (context := context) (evidence := evidence) (source := source)
        (faults := faults) (id := id) (node := node) (lowered := lowered) snapshot outcome after value finalStore finalMap finalWorld ∧
      ProtectedStateTransition.Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds, frame, metadata, post⟩ :=
    meaning generated found environments heaps locals
      (DataPlaceChildExpressions.prefix_agrees agrees
        [snapshot.value, .unit, .cellRef (OptionalCell.cellType prepared.route.rootType) snapshot.target])
      (snapshot.runtimeTyped actualTyped) initial trace
  refine ⟨value, finalStore, finalMap, finalWorld, rhs_of_expression snapshot protocol initial trace.sound ?_ represented heaps maps worlds frame metadata post⟩
  simpa only [DataPlaceChildExpressions.rename_prefix, List.length_cons, List.length_nil,
    List.cons_append, List.nil_append, snapshotEnvironment, keysEnvironment, referenceEnvironment,
    SourceCoreDataPlaces.shift, shift, Nat.zero_add] using evaluated

theorem rhs_reflects_at (size : Nat)
    (meaning : ProtectedStateTransition.ReflectsAt protocol (payloadModel checked registry functions) program context evidence source certificate faults size)
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog)
      mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents checked registry functions mapping world heap store)
    (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (initial : protocol.State ⟨scope, mapping, world, heap, store, canonical⟩)
    {value : Value} {finalStore : Store}
    (evaluated : CoreProof.EvaluationSize size (snapshotEnvironment prepared.route.rootType snapshot.target .unit snapshot.value actual)
      store (shift 3 (lowered.expression.rename ξ)) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome program sourceSize context evidence source environment heap id outcome after ∧
      RhsResult (program := program) (context := context) (evidence := evidence) (source := source)
        (faults := faults) (id := id) (node := node) (lowered := lowered) snapshot outcome after value finalStore finalMap finalWorld ∧
      ProtectedStateTransition.Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds, frame, metadata, post⟩ :=
    meaning generated found environments heaps locals
      (DataPlaceChildExpressions.prefix_agrees agrees
        [snapshot.value, .unit, .cellRef (OptionalCell.cellType prepared.route.rootType) snapshot.target])
      (snapshot.runtimeTyped actualTyped) initial
      (by simpa only [DataPlaceChildExpressions.rename_prefix, List.length_cons, List.length_nil,
        List.cons_append, List.nil_append, snapshotEnvironment, keysEnvironment, referenceEnvironment,
        SourceCoreDataPlaces.shift, shift, Nat.zero_add] using evaluated)
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace,
    rhs_of_expression snapshot protocol initial trace.sound evaluated.sound represented heaps maps worlds frame metadata post⟩

end Stateful

theorem rhs_preserves_at (size : Nat)
    (meaning : RecursiveNamedBoundedContracts.PreservesAt size (payloadModel checked registry functions) program context evidence source certificate faults entry)
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog)
      mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents checked registry functions mapping world heap store)
    (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (installed : entry scope mapping world heap store canonical)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment heap id outcome after) :
    ∃ value finalStore finalMap finalWorld,
      RhsResult (program := program) (context := context) (evidence := evidence) (source := source)
        (faults := faults) (id := id) (node := node) (lowered := lowered) snapshot outcome after value finalStore finalMap finalWorld := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds, frame, metadata⟩ :=
    meaning generated found environments heaps locals
      (DataPlaceChildExpressions.prefix_agrees agrees
        [snapshot.value, .unit, .cellRef (OptionalCell.cellType prepared.route.rootType) snapshot.target])
      (snapshot.runtimeTyped actualTyped) installed trace
  have receipt := rhs_of_expression (scope := scope) (canonical := canonical) snapshot ProtectedStateBareAssignment.unitProtocol () trace.sound
    (by simpa only [DataPlaceChildExpressions.rename_prefix, List.length_cons, List.length_nil,
      List.cons_append, List.nil_append, snapshotEnvironment, keysEnvironment, referenceEnvironment,
      SourceCoreDataPlaces.shift, shift, Nat.zero_add] using evaluated)
    represented heaps maps worlds frame metadata (show ProtectedStateTransition.Transition ProtectedStateBareAssignment.unitProtocol (initial := ⟨scope, mapping, world, heap, store, canonical⟩) () ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ from ⟨(), trivial⟩)
  exact ⟨value, finalStore, finalMap, finalWorld, receipt.1⟩

theorem rhs_reflects_at (size : Nat)
    (meaning : RecursiveNamedBoundedContracts.ReflectsAt size (payloadModel checked registry functions) program context evidence source certificate faults entry)
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog)
      mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents checked registry functions mapping world heap store)
    (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (installed : entry scope mapping world heap store canonical)
    {value : Value} {finalStore : Store}
    (evaluated : CoreProof.EvaluationSize size (snapshotEnvironment prepared.route.rootType snapshot.target .unit snapshot.value actual)
      store (shift 3 (lowered.expression.rename ξ)) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome program sourceSize context evidence source environment heap id outcome after ∧
      RhsResult (program := program) (context := context) (evidence := evidence) (source := source)
        (faults := faults) (id := id) (node := node) (lowered := lowered) snapshot outcome after value finalStore finalMap finalWorld := by
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds, frame, metadata⟩ :=
    meaning generated found environments heaps locals
      (DataPlaceChildExpressions.prefix_agrees agrees
        [snapshot.value, .unit, .cellRef (OptionalCell.cellType prepared.route.rootType) snapshot.target])
      (snapshot.runtimeTyped actualTyped) installed
      (by simpa only [DataPlaceChildExpressions.rename_prefix, List.length_cons, List.length_nil,
        List.cons_append, List.nil_append, snapshotEnvironment, keysEnvironment, referenceEnvironment,
        SourceCoreDataPlaces.shift, shift, Nat.zero_add] using evaluated)
  have receipt := rhs_of_expression (scope := scope) (canonical := canonical) snapshot ProtectedStateBareAssignment.unitProtocol () trace.sound evaluated.sound
    represented heaps maps worlds frame metadata (show ProtectedStateTransition.Transition ProtectedStateBareAssignment.unitProtocol (initial := ⟨scope, mapping, world, heap, store, canonical⟩) () ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ from ⟨(), trivial⟩)
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, receipt.1⟩

theorem rhs_preserves
    (meaning : ProtectedExpressionMeaning.Preserves (payloadModel checked registry functions) program context evidence source certificate faults entry)
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog)
      mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents checked registry functions mapping world heap store)
    (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (installed : entry scope mapping world heap store canonical)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment heap id outcome after) :
    ∃ value finalStore finalMap finalWorld,
      RhsResult (program := program) (context := context) (evidence := evidence) (source := source)
        (faults := faults) (id := id) (node := node) (lowered := lowered) snapshot outcome after value finalStore finalMap finalWorld := by
  obtain ⟨size, sized⟩ := RecursiveNamedCallBounds.ExpressionOutcome.has_size trace
  exact rhs_preserves_at snapshot size (RecursiveNamedBoundedContracts.preserves_at_of_unbounded meaning size)
    generated found environments heaps locals agrees actualTyped installed sized

theorem rhs_reflects
    (meaning : ProtectedExpressionMeaning.Reflects (payloadModel checked registry functions) program context evidence source certificate faults entry)
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog)
      mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents checked registry functions mapping world heap store)
    (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (installed : entry scope mapping world heap store canonical)
    {value : Value} {finalStore : Store}
    (evaluated : Evaluates (snapshotEnvironment prepared.route.rootType snapshot.target .unit snapshot.value actual)
      store (shift 3 (lowered.expression.rename ξ)) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      RhsResult (program := program) (context := context) (evidence := evidence) (source := source)
        (faults := faults) (id := id) (node := node) (lowered := lowered) snapshot outcome after value finalStore finalMap finalWorld := by
  obtain ⟨size, sized⟩ := CoreProof.evaluation_has_size evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, _, result⟩ :=
    rhs_reflects_at snapshot size (RecursiveNamedBoundedContracts.reflects_at_of_unbounded meaning size)
      generated found environments heaps locals agrees actualTyped installed sized
  exact ⟨outcome, after, finalMap, finalWorld, result⟩



end Solcore.SourceSemantics.CoreLowering.ProtectedBareAssignment
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedStateAssignmentHeadContracts
/-! Sized assignment heads return the state of their actual fault or written
prefix. Successful continuation values and their original native grade remain
separate from the prefix state. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedStateAssignmentHeadContracts
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality CompatibleHeap CoreProof
open SourceCoreCompatibleDataPlaces GenericExpressionMeaning ProtectedStateTransition
universe u v

inductive ResultAt {Records : Type v} (protocol : Protocol.{u, v} Records) (size : Nat) (checked : Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions} (functions : FunctionModel checked.catalog ambient)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource)
    (faults : FunctionCalls.FaultRep) (scope : Scope) (writtenContext : Core.Context)
    (place : PlaceResolution) (operator : Syntax.ValueAssignOp) (rhs : ExpressionId)
    (environment : Dynamic.Environment) (canonical actual : Environment)
    (before : Dynamic.Heap) (store : Store) (mapping : LocationMap) (world : StoreTyping)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (next : Expr) (output : Ty) (value : Value) (finalStore : Store) : Prop where
  | fault {sourceSize : Nat} {reason : Dynamic.SemanticFault} {token : Word} {after : Dynamic.Heap}
      {finalMap : LocationMap} {finalWorld : StoreTyping}
      (trace : SourceExecutionSize.SourcePlaceAssignmentFaults program sourceSize context evidence source environment before place operator rhs reason after)
      (same : value = .inLeft output (.word token)) (matched : faults reason token)
      (heaps : HeapRepresents checked registry functions finalMap finalWorld after finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap finalStore) (metadata : Dynamic.HeapMetadataExtend before after)
      (post : Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩) :
      ResultAt protocol size checked registry functions program context evidence source faults scope writtenContext place operator rhs
        environment canonical actual before store mapping world initial next output value finalStore
  | success {sourceSize remainingSize : Nat} {updated : Dynamic.Value} {after : Dynamic.Heap}
      {written : Store} {finalMap : LocationMap} {finalWorld : StoreTyping} {slots : Environment}
      (trace : SourceExecutionSize.SourcePlaceAssignment program sourceSize context evidence source (Dynamic.AssignmentValueApplies operator)
        environment before place rhs updated after)
      (heaps : HeapRepresents checked registry functions finalMap finalWorld after written)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap written) (metadata : Dynamic.HeapMetadataExtend before after)
      (count : slots.length = 7)
      (typed : RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) writtenContext ambient.definitions)
      (post : Transition protocol initial ⟨scope, finalMap, finalWorld, after, written, canonical⟩)
      (bounded : remainingSize < size)
      (remaining : EvaluationSize remainingSize (slots ++ actual) written (shift 7 next) value finalStore) :
      ResultAt protocol size checked registry functions program context evidence source faults scope writtenContext place operator rhs
        environment canonical actual before store mapping world initial next output value finalStore

end Solcore.SourceSemantics.CoreLowering.ProtectedStateAssignmentHeadContracts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedBareAssignmentPreservation
/-! Forward finite meaning of bare assignments. These laws preserve the exact
independent source trace, including a fault after RHS effects. The returned
continuation runs in its real renamed seven-slot environment. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedBareAssignment
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap SourceCoreCompatibleDataPlaces DataPlaceExecution CoreProof
open CompatibleBareAssignment
universe u v

variable {compilation : SourceCoreCompatibleDataPlaces.Context} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions compilation.checked.catalog.definitions} {functions : FunctionModel compilation.checked.catalog ambient}
  {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
  {prepared : Prepared} {place : PlaceResolution} {environment : Dynamic.Environment} {canonical actual : Environment}
  {before : Dynamic.Heap} {store : Store} {mapping : LocationMap} {world : StoreTyping} {index : Nat} {ξ : Renaming}
  {scope : Scope} {administrativeContext actualContext : Core.Context} {certificate : Certificate} {faults : FaultRep}
  {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
  {operator : Syntax.ValueAssignOp} {identities : Dynamic.Value → Word → Prop}
  {entry : ProtectedExpressionMeaning.Entry}

private theorem writes_functional {heap left right : Dynamic.Heap} {location : Dynamic.Location} {value : Option Dynamic.Value}
    (first : Dynamic.Heap.Writes heap location value left) (second : Dynamic.Heap.Writes heap location value right) : left = right := by
  have cells : ∀ {before first second : List Dynamic.Cell} {index : Nat} {value : Dynamic.Cell},
      Dynamic.Heap.CellsWrite before index value first → Dynamic.Heap.CellsWrite before index value second → first = second := by
    intro before first second index value left
    induction left generalizing second with
    | head => intro right; cases right; rfl
    | tail _ ih => intro right; cases right with | tail rest => exact congrArg (List.cons _) (ih rest)
  cases first with
  | intro firstRead firstWrite =>
    cases second with
    | intro secondRead secondWrite =>
      have same := firstRead.functional secondRead
      cases same
      exact congrArg Dynamic.Heap.mk (cells firstWrite secondWrite)

namespace Stateful
variable {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
  (transport : ProtectedStateTransition.AdministrativeTransport protocol)

include transport in
theorem preserves_prefix_bounded_with_rhs (budget : Nat)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (layout : Layout compilation prepared) (bare : place.projections = [])
    (extension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (rhsMeaning : ∀ (snapshot : Snapshot compilation.checked registry functions prepared place environment actual before store mapping world (ξ index))
      (child : Nat), child < budget → ∀ {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap},
      RecursiveNamedCallBounds.ExpressionOutcome program child context evidence source environment before id outcome after →
      ∃ value finalStore finalMap finalWorld,
        RhsResult (program := program) (context := context) (evidence := evidence) (source := source)
          (faults := faults) (id := id) (node := node) (lowered := lowered) snapshot outcome after value finalStore finalMap finalWorld ∧
        ProtectedStateTransition.Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    (_generated : certificate scope id lowered) (_found : source.lookupExpression? id = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCore : lowered.type = prepared.route.leafType)
    (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .word ∨
      SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .integer ∧ operator.wordOnly = false)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog)
      mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {updated : Dynamic.Value} {after : Dynamic.Heap}
    {size : Nat} (trace : SourceExecutionSize.SourcePlaceAssignment program size context evidence source (Dynamic.AssignmentValueApplies operator)
      environment before place id updated after) (bounded : size ≤ budget) (invalid : Word) :
    ∃ updatedValue finalStore finalMap finalWorld slots,
      ValueRep compilation.checked registry functions finalMap finalWorld prepared.route.rootSourceType updated updatedValue prepared.route.rootType ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      slots.length = 7 ∧ RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) (writtenContext prepared actualContext) ambient.definitions ∧
      (∀ next outputType, ContinuationAgreement actual store
        ((execute prepared (.var index) (SourceCoreCalls.packArguments []) lowered.expression next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalid).rename ξ)
        (slots ++ actual) finalStore (shift 7 (next.rename ξ))) ∧
      ProtectedStateTransition.Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨snapshot⟩ := snapshot_of_heap layout extension environments heaps locals agrees slot rootTyped
  cases trace with
  | intro resolved evaluated written =>
    obtain ⟨rfl, rfl⟩ := snapshot.resolve_unique bare resolved.sound
    obtain ⟨value, rhsStore, rhsMap, rhsWorld, result, rhsPost⟩ :=
      rhsMeaning snapshot _
        (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded) (.value evaluated)
    cases related : result.represented with
    | @value _ rightValue payload =>
      have rightRep : ValueRep compilation.checked registry functions rhsMap rhsWorld prepared.route.rootSourceType _ rightValue prepared.route.rootType :=
        .compatible rhsView (by simpa only [payloadModel, rhsCore, ← layout.sameType] using payload)
      have saved := snapshot.represented.extend result.maps result.worlds
      cases written with
      | intro read sameType initial update written =>
        cases update with
        | leaf applied =>
          rcases modifier_total observations profile saved rightRep
            (environment := rhsEnvironment prepared.route.rootType snapshot.target .unit snapshot.value rightValue actual)
            (.var (index := 1) rfl) (.var (index := 0) rfl) rhsStore invalid with
            ⟨invalidOperands, _⟩ | ⟨replacement, updatedValue, replacementRep, outcome, modified⟩
          · exact (DataPlaceModifier.assignment_excludes_invalid applied invalidOperands).elim
          · rcases outcome with generatedApply | ⟨_, _, _, panics⟩
            case inr => exact (CompatiblePlaceModifier.panic_excludes_applies panics applied).elim
            have same := DataPlaceModifier.assignment_functional generatedApply applied
            subst replacement
            have passes := CompatiblePlaceModifier.passes_of_applies observations profile rightRep applied
              (prepared.route.leafType = .integer)
            obtain ⟨generatedHeap, finalStore, _, generatedWrite, finalHeaps, frame, metadata, typed, writeFrame, writeMetadata, agreement⟩ :=
              commit_with_write layout snapshot bare result rightRep replacementRep applied (by simpa only [layout.sameType] using modified)
                passes actualTyped
            have same := writes_functional generatedWrite written
            subst generatedHeap
            obtain ⟨rhsState, rhsRelated⟩ := rhsPost
            exact ⟨updatedValue, finalStore, rhsMap, rhsWorld,
              [.unit, updatedValue, updatedValue, rightValue, snapshot.value, .unit,
                .cellRef (OptionalCell.cellType prepared.route.rootType) snapshot.target],
              replacementRep, finalHeaps, result.maps, result.worlds, frame, metadata, rfl, typed, agreement,
              transport.extend rhsState (.refl _) (.refl _) writeFrame writeMetadata,
              protocol.trans rhsRelated (transport.related rhsState (.refl _) (.refl _) writeFrame writeMetadata)⟩

include transport in
theorem preserves_prefix_bounded (budget : Nat)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (layout : Layout compilation prepared) (bare : place.projections = [])
    (extension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun size =>
      ProtectedStateTransition.PreservesAt protocol (payloadModel compilation.checked registry functions) program context evidence source certificate faults size))
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCore : lowered.type = prepared.route.leafType)
    (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .word ∨
      SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .integer ∧ operator.wordOnly = false)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog)
      mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {updated : Dynamic.Value} {after : Dynamic.Heap}
    {size : Nat} (trace : SourceExecutionSize.SourcePlaceAssignment program size context evidence source (Dynamic.AssignmentValueApplies operator)
      environment before place id updated after) (bounded : size ≤ budget) (invalid : Word) :
    ∃ updatedValue finalStore finalMap finalWorld slots,
      ValueRep compilation.checked registry functions finalMap finalWorld prepared.route.rootSourceType updated updatedValue prepared.route.rootType ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      slots.length = 7 ∧ RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) (writtenContext prepared actualContext) ambient.definitions ∧
      (∀ next outputType, ContinuationAgreement actual store
        ((execute prepared (.var index) (SourceCoreCalls.packArguments []) lowered.expression next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalid).rename ξ)
        (slots ++ actual) finalStore (shift 7 (next.rename ξ))) ∧
      ProtectedStateTransition.Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  exact preserves_prefix_bounded_with_rhs protocol transport budget initial layout bare extension
    (fun snapshot child smaller {_ _} expressionTrace =>
      Stateful.rhs_preserves_at snapshot protocol child (meaning child smaller) generated found
        environments heaps locals agrees actualTyped initial expressionTrace) observations generated found rhsView rhsCore profile environments heaps locals agrees actualTyped slot rootTyped trace bounded invalid

end Stateful

theorem preserves_prefix_bounded (budget : Nat)
    (layout : Layout compilation prepared) (bare : place.projections = [])
    (extension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun size =>
      RecursiveNamedBoundedContracts.PreservesAt size (payloadModel compilation.checked registry functions) program context evidence source certificate faults entry))
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCore : lowered.type = prepared.route.leafType)
    (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .word ∨
      SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .integer ∧ operator.wordOnly = false)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog)
      mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (installed : entry scope mapping world before store canonical)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {updated : Dynamic.Value} {after : Dynamic.Heap}
    {size : Nat} (trace : SourceExecutionSize.SourcePlaceAssignment program size context evidence source (Dynamic.AssignmentValueApplies operator)
      environment before place id updated after) (bounded : size ≤ budget) (invalid : Word) :
    ∃ updatedValue finalStore finalMap finalWorld slots,
      ValueRep compilation.checked registry functions finalMap finalWorld prepared.route.rootSourceType updated updatedValue prepared.route.rootType ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      slots.length = 7 ∧ RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) (writtenContext prepared actualContext) ambient.definitions ∧
      ∀ next outputType, ContinuationAgreement actual store
        ((execute prepared (.var index) (SourceCoreCalls.packArguments []) lowered.expression next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalid).rename ξ)
        (slots ++ actual) finalStore (shift 7 (next.rename ξ)) := by
  obtain ⟨updatedValue, finalStore, finalMap, finalWorld, slots, represented, finalHeaps, maps, worlds, frame, metadata, count, typed, agreement, _⟩ :=
    Stateful.preserves_prefix_bounded_with_rhs (scope := scope) (canonical := canonical) ProtectedStateBareAssignment.unitProtocol ProtectedStateBareAssignment.unitTransport budget () layout bare extension
    (fun snapshot child smaller {_ _} expressionTrace => by
      obtain ⟨value, rhsStore, rhsMap, rhsWorld, result⟩ := rhs_preserves_at snapshot child (meaning child smaller)
        generated found environments heaps locals agrees actualTyped installed expressionTrace
      exact ⟨value, rhsStore, rhsMap, rhsWorld, result, (), trivial⟩) observations generated found rhsView rhsCore profile environments heaps locals agrees actualTyped slot rootTyped trace bounded invalid
  exact ⟨updatedValue, finalStore, finalMap, finalWorld, slots, represented, finalHeaps, maps, worlds, frame, metadata, count, typed, agreement⟩

theorem preserves_prefix
    (layout : Layout compilation prepared) (bare : place.projections = [])
    (extension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (meaning : ProtectedExpressionMeaning.Preserves (payloadModel compilation.checked registry functions) program context evidence source certificate faults entry)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCore : lowered.type = prepared.route.leafType)
    (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .word ∨
      SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .integer ∧ operator.wordOnly = false)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog)
      mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (installed : entry scope mapping world before store canonical)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {updated : Dynamic.Value} {after : Dynamic.Heap}
    (trace : Dynamic.SourcePlaceAssignment program context evidence source (Dynamic.AssignmentValueApplies operator)
      environment before place id updated after) (invalid : Word) :
    ∃ updatedValue finalStore finalMap finalWorld slots,
      ValueRep compilation.checked registry functions finalMap finalWorld prepared.route.rootSourceType updated updatedValue prepared.route.rootType ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      slots.length = 7 ∧ RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) (writtenContext prepared actualContext) ambient.definitions ∧
      ∀ next outputType, ContinuationAgreement actual store
        ((execute prepared (.var index) (SourceCoreCalls.packArguments []) lowered.expression next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalid).rename ξ)
        (slots ++ actual) finalStore (shift 7 (next.rename ξ)) := by
  obtain ⟨size, sized⟩ := SourceExecutionSize.SourcePlaceAssignment.has_size trace
  exact preserves_prefix_bounded size layout bare extension
    (RecursiveNamedBoundedContracts.preserves_below_of_unbounded meaning size) observations generated found rhsView rhsCore profile
    environments heaps locals agrees actualTyped installed slot rootTyped sized (Nat.le_refl size) invalid

private theorem no_target_fault
    (snapshot : Snapshot compilation.checked registry functions prepared place environment actual before store mapping world (ξ index))
    (bare : place.projections = []) {reason : Dynamic.SemanticFault} {after : Dynamic.Heap}
    (fault : Dynamic.SourcePlaceFaults program context evidence source environment before place reason after) : False := by
  cases fault with
  | unbound missing => exact missing.excludes_lookup snapshot.lookup
  | dangling lookup missing =>
    have same := lookup.functional snapshot.lookup
    cases same
    exact missing.excludes_read snapshot.read
  | projectionExpression _ _ fault => rw [bare] at fault; cases fault
  | danglingAfterProjections lookup _ evaluated missing =>
    rw [bare] at evaluated
    cases evaluated
    have same := lookup.functional snapshot.lookup
    cases same
    exact missing.excludes_read snapshot.read
  | projectionRead _ _ evaluated _ _ fault =>
    rw [bare] at evaluated
    cases evaluated
    cases fault
  | uninitialized _ _ evaluated _ _ _ nonempty =>
    rw [bare] at evaluated
    cases evaluated
    exact nonempty rfl

/- All independently specified bare assignment faults retain RHS prefix
state. A target fault or structural traversal fault contradicts the empty
path and live lexical reference, rather than being silently reclassified. -/
namespace Stateful
variable {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
  (transport : ProtectedStateTransition.AdministrativeTransport protocol)

theorem preserves_fault_reachable_bounded_with_rhs (budget : Nat)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (layout : Layout compilation prepared) (bare : place.projections = [])
    (extension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (rhsMeaning : ∀ (snapshot : Snapshot compilation.checked registry functions prepared place environment actual before store mapping world (ξ index))
      (child : Nat), child < budget → ∀ {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap},
      RecursiveNamedCallBounds.ExpressionOutcome program child context evidence source environment before id outcome after →
      ∃ value finalStore finalMap finalWorld,
        RhsResult (program := program) (context := context) (evidence := evidence) (source := source)
          (faults := faults) (id := id) (node := node) (lowered := lowered) snapshot outcome after value finalStore finalMap finalWorld ∧
        ProtectedStateTransition.Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    (_generated : certificate scope id lowered) (_found : source.lookupExpression? id = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCore : lowered.type = prepared.route.leafType)
    (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .word ∨
      SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .integer ∧ operator.wordOnly = false)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog)
      mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (_actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {reason : Dynamic.SemanticFault} {after : Dynamic.Heap}
    {size : Nat} (trace : SourceExecutionSize.SourcePlaceAssignmentFaults program size context evidence source environment before place operator id reason after) (bounded : size ≤ budget)
    (next : Expr) (outputType : Ty) (invalid : Word)
    [FunctionCalls.FaultTokens faults] (invalidToken : AssignmentOperandDiagnostics.OperandsLaw faults operator invalid) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store
        ((execute prepared (.var index) (SourceCoreCalls.packArguments []) lowered.expression next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalid).rename ξ)
        (.inLeft outputType (.word token)) finalStore ∧ faults reason token ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨snapshot⟩ := snapshot_of_heap layout extension environments heaps locals agrees slot rootTyped
  have phase := snapshot_prefix layout snapshot lowered.expression next outputType
    (binaryOperator (prepared.route.leafType = .integer) operator) invalid
  cases trace with
  | target fault => exact (no_target_fault snapshot bare fault.sound).elim
  | rhs resolve fault =>
    obtain ⟨rfl, rfl⟩ := snapshot.resolve_unique bare resolve.sound
    obtain ⟨value, rhsStore, rhsMap, rhsWorld, result, rhsPost⟩ :=
      rhsMeaning snapshot _
        (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded) (.fault fault)
    cases represented : result.represented with
    | fault token =>
      exact ⟨_, rhsStore, rhsMap, rhsWorld, phase.wrap (LanguageResult.bind_failure outputType result.evaluated), token,
        result.heaps, result.maps, result.worlds, result.frame, result.metadata, rhsPost⟩
  | operands resolve evaluated _ _ _ _ invalidOperands =>
    obtain ⟨rfl, rfl⟩ := snapshot.resolve_unique bare resolve.sound
    obtain ⟨value, rhsStore, rhsMap, rhsWorld, result, rhsPost⟩ :=
      rhsMeaning snapshot _
        (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded) (.value evaluated)
    cases represented : result.represented with
    | @value _ rightValue payload =>
      have rightRep : ValueRep compilation.checked registry functions rhsMap rhsWorld prepared.route.rootSourceType _ rightValue prepared.route.rootType :=
        .compatible rhsView (by simpa only [payloadModel, rhsCore, ← layout.sameType] using payload)
      rcases modifier_total observations profile (snapshot.represented.extend result.maps result.worlds) rightRep
        (environment := rhsEnvironment prepared.route.rootType snapshot.target .unit snapshot.value rightValue actual)
        (.var (index := 1) rfl) (.var (index := 0) rfl) rhsStore invalid with
          ⟨_, failed⟩ | ⟨_, _, _, outcome, _⟩
      · have failed : Evaluates (rhsEnvironment prepared.route.rootType snapshot.target .unit snapshot.value rightValue actual) rhsStore
            (modified prepared.route.leafType (binaryOperator (prepared.route.leafType = .integer) operator) false (.var 1) (.var 0) invalid)
            (.inLeft prepared.route.leafType (.word invalid)) rhsStore := by simpa only [layout.sameType] using failed
        exact ⟨invalid, rhsStore, rhsMap, rhsWorld,
          phase.wrap (LanguageResult.bind_success outputType result.evaluated (LanguageResult.bind_failure outputType failed)),
          invalidToken _ _ invalidOperands, result.heaps, result.maps, result.worlds, result.frame, result.metadata, rhsPost⟩
      · rcases outcome with applied | ⟨_, _, _, panics⟩
        · exact (DataPlaceModifier.assignment_excludes_invalid applied invalidOperands).elim
        · exact (DataPlaceModifier.panic_excludes_invalid panics invalidOperands).elim
  | panic resolve evaluated _ _ _ _ panics =>
    obtain ⟨rfl, rfl⟩ := snapshot.resolve_unique bare resolve.sound
    obtain ⟨value, rhsStore, rhsMap, rhsWorld, result, rhsPost⟩ :=
      rhsMeaning snapshot _
        (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded) (.value evaluated)
    cases represented : result.represented with
    | @value _ rightValue payload =>
      have rightRep : ValueRep compilation.checked registry functions rhsMap rhsWorld prepared.route.rootSourceType _ rightValue prepared.route.rootType :=
        .compatible rhsView (by simpa only [payloadModel, rhsCore, ← layout.sameType] using payload)
      rcases modifier_total observations profile (snapshot.represented.extend result.maps result.worlds) rightRep
        (environment := rhsEnvironment prepared.route.rootType snapshot.target .unit snapshot.value rightValue actual)
        (.var (index := 1) rfl) (.var (index := 0) rfl) rhsStore invalid with
          ⟨invalidOperands, _⟩ | ⟨_, updatedValue, _, outcome, modified⟩
      · exact (DataPlaceModifier.panic_excludes_invalid panics invalidOperands).elim
      · rcases outcome with applied | ⟨operation, selected, zero, other⟩
        · exact (CompatiblePlaceModifier.panic_excludes_applies panics applied).elim
        · -- The setter runs and the check fails before the write.
          have sameCode := CompatiblePlaceModifier.panic_functional panics other
          subst sameCode zero
          have selected : binaryOperator (prepared.route.leafType = .integer) operator = some ⟨operation, true⟩ := by
            simpa only [layout.sameType] using selected
          have nativeModified : Evaluates (rhsEnvironment prepared.route.rootType snapshot.target .unit snapshot.value
              (.word Word.zero) actual) rhsStore
              (SourceCoreCompatibleDataPlaces.modified prepared.route.leafType (binaryOperator (prepared.route.leafType = .integer) operator) false
                (.var 1) (.var 0) invalid) (.inRight .word updatedValue) rhsStore := by
            simpa only [layout.sameType] using modified
          obtain ⟨latest⟩ := result.latest
          exact ⟨_, rhsStore, rhsMap, rhsWorld,
            phase.wrap (LanguageResult.bind_success outputType result.evaluated
              (LanguageResult.bind_success outputType nativeModified
                (LanguageResult.bind_success outputType
                  (setter_evaluates layout snapshot.value (.word Word.zero) updatedValue latest.nativeRead)
                  (DataPlaceGuard.panic_of_selected selected)))),
            FunctionCalls.FaultTokens.panic _, result.heaps, result.maps, result.worlds, result.frame, result.metadata, rhsPost⟩
  | structuralUpdate resolve _ _ _ _ fault =>
    obtain ⟨rfl, rfl⟩ := snapshot.resolve_unique bare resolve.sound
    cases fault

theorem preserves_fault_reachable_bounded (budget : Nat)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (layout : Layout compilation prepared) (bare : place.projections = [])
    (extension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun size =>
      ProtectedStateTransition.PreservesAt protocol (payloadModel compilation.checked registry functions) program context evidence source certificate faults size))
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCore : lowered.type = prepared.route.leafType)
    (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .word ∨
      SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .integer ∧ operator.wordOnly = false)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog)
      mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {reason : Dynamic.SemanticFault} {after : Dynamic.Heap}
    {size : Nat} (trace : SourceExecutionSize.SourcePlaceAssignmentFaults program size context evidence source environment before place operator id reason after) (bounded : size ≤ budget)
    (next : Expr) (outputType : Ty) (invalid : Word)
    [FunctionCalls.FaultTokens faults] (invalidToken : AssignmentOperandDiagnostics.OperandsLaw faults operator invalid) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store
        ((execute prepared (.var index) (SourceCoreCalls.packArguments []) lowered.expression next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalid).rename ξ)
        (.inLeft outputType (.word token)) finalStore ∧ faults reason token ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  exact preserves_fault_reachable_bounded_with_rhs protocol budget initial layout bare extension
    (fun snapshot child smaller {_ _} expressionTrace =>
      Stateful.rhs_preserves_at snapshot protocol child (meaning child smaller) generated found
        environments heaps locals agrees actualTyped initial expressionTrace) observations generated found rhsView rhsCore profile environments heaps locals agrees actualTyped slot rootTyped trace bounded next outputType invalid invalidToken

end Stateful

theorem preserves_fault_reachable_bounded (budget : Nat)
    (layout : Layout compilation prepared) (bare : place.projections = [])
    (extension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun size =>
      RecursiveNamedBoundedContracts.PreservesAt size (payloadModel compilation.checked registry functions) program context evidence source certificate faults entry))
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCore : lowered.type = prepared.route.leafType)
    (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .word ∨
      SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .integer ∧ operator.wordOnly = false)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog)
      mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (installed : entry scope mapping world before store canonical)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {reason : Dynamic.SemanticFault} {after : Dynamic.Heap}
    {size : Nat} (trace : SourceExecutionSize.SourcePlaceAssignmentFaults program size context evidence source environment before place operator id reason after) (bounded : size ≤ budget)
    (next : Expr) (outputType : Ty) (invalid : Word)
    [FunctionCalls.FaultTokens faults] (invalidToken : AssignmentOperandDiagnostics.OperandsLaw faults operator invalid) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store
        ((execute prepared (.var index) (SourceCoreCalls.packArguments []) lowered.expression next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalid).rename ξ)
        (.inLeft outputType (.word token)) finalStore ∧ faults reason token ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, frame, metadata, _⟩ :=
    Stateful.preserves_fault_reachable_bounded_with_rhs (scope := scope) (canonical := canonical) ProtectedStateBareAssignment.unitProtocol budget () layout bare extension
    (fun snapshot child smaller {_ _} expressionTrace => by
      obtain ⟨value, rhsStore, rhsMap, rhsWorld, result⟩ := rhs_preserves_at snapshot child (meaning child smaller)
        generated found environments heaps locals agrees actualTyped installed expressionTrace
      exact ⟨value, rhsStore, rhsMap, rhsWorld, result, (), trivial⟩) observations generated found rhsView rhsCore profile environments heaps locals agrees actualTyped slot rootTyped trace bounded next outputType invalid invalidToken
  exact ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, frame, metadata⟩

theorem preserves_fault_reachable
    (layout : Layout compilation prepared) (bare : place.projections = [])
    (extension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (meaning : ProtectedExpressionMeaning.Preserves (payloadModel compilation.checked registry functions) program context evidence source certificate faults entry)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCore : lowered.type = prepared.route.leafType)
    (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .word ∨
      SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .integer ∧ operator.wordOnly = false)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog)
      mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (installed : entry scope mapping world before store canonical)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {reason : Dynamic.SemanticFault} {after : Dynamic.Heap}
    (trace : Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator id reason after)
    (next : Expr) (outputType : Ty) (invalid : Word)
    [FunctionCalls.FaultTokens faults] (invalidToken : AssignmentOperandDiagnostics.OperandsLaw faults operator invalid) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store
        ((execute prepared (.var index) (SourceCoreCalls.packArguments []) lowered.expression next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalid).rename ξ)
        (.inLeft outputType (.word token)) finalStore ∧ faults reason token ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨size, sized⟩ := SourceExecutionSize.SourcePlaceAssignmentFaults.has_size trace
  exact preserves_fault_reachable_bounded size layout bare extension
    (RecursiveNamedBoundedContracts.preserves_below_of_unbounded meaning size) observations generated found rhsView rhsCore profile
    environments heaps locals agrees actualTyped installed slot rootTyped sized (Nat.le_refl size) next outputType invalid invalidToken

/-- Compatibility entry point retaining the original operand-token premise. -/
theorem preserves_fault
    (layout : Layout compilation prepared) (bare : place.projections = [])
    (extension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (meaning : ProtectedExpressionMeaning.Preserves (payloadModel compilation.checked registry functions) program context evidence source certificate faults entry)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCore : lowered.type = prepared.route.leafType)
    (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .word ∨
      SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .integer ∧ operator.wordOnly = false)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog)
      mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (installed : entry scope mapping world before store canonical)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {reason : Dynamic.SemanticFault} {after : Dynamic.Heap}
    (trace : Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator id reason after)
    (next : Expr) (outputType : Ty) (invalid : Word)
    [FunctionCalls.FaultTokens faults] (invalidToken : faults (.invalidAssignmentOperands operator) invalid) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store
        ((execute prepared (.var index) (SourceCoreCalls.packArguments []) lowered.expression next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalid).rename ξ)
        (.inLeft outputType (.word token)) finalStore ∧ faults reason token ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  exact preserves_fault_reachable layout bare extension meaning observations generated found rhsView rhsCore profile
    environments heaps locals agrees actualTyped installed slot rootTyped trace next outputType invalid
    (AssignmentOperandDiagnostics.of_unconditional invalidToken)

end Solcore.SourceSemantics.CoreLowering.ProtectedBareAssignment
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedPlaceMissingTerminalReceipts
/-! The actual missing-default phase yields its own terminal receipt using
 the existing ordered-key fault producer. The phase State, live root read,
 original raw root type and same emitted token remain together. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedPlaceReachedDiagnostics
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleMixedRoute
open SourceCoreCompatibleDataPlaces CompatiblePlaceLiveRoot
universe u v
variable {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions}
  {functions : FunctionModel checked.catalog ambient} {Records : Type v}
  {protocol : ProtectedStateTransition.Protocol.{u, v} Records}
  {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
  {place : PlaceResolution} {prepared : Prepared} {leaf : TypeSystem.Ty}
  {initialIndex reachedIndex : ProtectedStateTransition.Index}
  {initial : protocol.State initialIndex} {reached : protocol.State reachedIndex}
  {reason : Dynamic.SemanticFault} {token : Word}

/-- This is the same genuine phase and root read retained by MissingWitness,
 with the existing terminal receipt at that exact phase mapping and world. -/
def MissingTerminalPhase (checked : Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient)
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (source : TypedSource) (site : SourceCoreElaboration.ErrorSite) (place : PlaceResolution)
    (prepared : Prepared) (leaf : TypeSystem.Ty)
    {initialIndex reachedIndex : ProtectedStateTransition.Index}
    (initial : protocol.State initialIndex) (reached : protocol.State reachedIndex)
    (reason : Dynamic.SemanticFault) (token : Word) : Prop :=
  ∃ (phaseIndex : ProtectedStateTransition.Index) (phase : protocol.State phaseIndex)
    (location : Dynamic.Location) (target : Location) (cell : Dynamic.Cell)
    (optional : Value) (root : Dynamic.Value) (value : Value)
    (path : PreparedPath checked source site cell.type place.projections
      0 prepared.steps prepared.keys leaf),
    protocol.Relates initial phase ∧ protocol.Relates phase reached ∧
    phaseIndex.scope = initialIndex.scope ∧ phaseIndex.canonical = initialIndex.canonical ∧
    reachedIndex = phaseIndex.extend phaseIndex.mapping reachedIndex.world phaseIndex.heap reachedIndex.store ∧
    WorldExtends phaseIndex.world reachedIndex.world ∧
    AdministrativePreserved phaseIndex.mapping phaseIndex.store phaseIndex.mapping reachedIndex.store ∧
    RootRead checked registry functions phaseIndex.mapping phaseIndex.world prepared phaseIndex.heap phaseIndex.store
      location target cell optional root value ∧
    cell.type = prepared.route.rootSourceType ∧
    MissingTerminal (registry := registry) functions phaseIndex.mapping phaseIndex.world path reason token

/-- Token functionality identifies the terminal produced from these actual
 ordered keys with the original getter or setter fault token. -/
theorem MissingWitness.terminal
    (witness : MissingWitness checked registry functions protocol source site place prepared leaf
      initial reached reason token) :
    MissingTerminalPhase checked registry functions protocol source site place prepared leaf
      initial reached reason token := by
  obtain ⟨phaseIndex, phase, location, target, cell, optional, root, value, keys,
    resolved, count, path, relatedIn, relatedOut, sameScope, sameCanonical,
    sameIndex, worlds, frame, read, rootType, arguments, sourceFault, receipt, _tree⟩ := witness
  obtain ⟨otherToken, otherCount, otherReceipt, _otherTree, terminal⟩ :=
    arguments.faultTree_with_terminal read.payload sourceFault prepared
  obtain ⟨sameToken, _sameCount⟩ := receipt.functional otherReceipt
  exact ⟨phaseIndex, phase, location, target, cell, optional, root, value, path,
    relatedIn, relatedOut, sameScope, sameCanonical, sameIndex, worlds, frame, read, rootType,
    sameToken.symm ▸ terminal⟩

end Solcore.SourceSemantics.CoreLowering.ProtectedPlaceReachedDiagnostics
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedCoercionPathMeaning
/-! Ordered coercion methods consume the actual reached protocol state.
The original Source/native path folds compose its relation through every
method and keep the final method's actual post, including faults. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedCoercionPathMeaning
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableCoercionPathMeaning
universe v
variable {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{0, v} Records)
  (scope : SourceCoreLocalCell.Scope) (canonical : Environment)

/-- Each actual path state keeps the caller's original scope and captures. -/
abbrev states (mapping : LocationMap) (world : StoreTyping) (heap : Dynamic.Heap) (store : Store) :=
  protocol.State ⟨scope, mapping, world, heap, store, canonical⟩

/-- The relation is the protocol's original relation at the actual indices. -/
def relation : StateRelation (states protocol scope canonical) :=
  fun {_mapping _nextMap _world _nextWorld _before _after _store _finalStore} first last =>
    protocol.Relates first last

variable {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {α : Type} {row : α → Row}
  (functions : FunctionModel values.checked.catalog ambient) (program : Program)
  {caller : Environment} {reason : Word}

/-- The one-method interface retains the actual post and its full relation. -/
abbrev StepPreserves (methods : List α) :=
  StepPreservesForWithState row (states protocol scope canonical) (relation protocol scope canonical)
    functions registry faults program caller reason methods

/-- Native rows retain original completion receipts for their chosen invocation. -/
abbrev StepReflects (invocation : CallableCoercionSpine.Call → Store → Value → Value → Store → Prop)
    (methods : List α) :=
  StepReflectsForWithState row (states protocol scope canonical) (relation protocol scope canonical)
    functions registry faults program invocation methods

/-- The same ordered Source fold forwards every method's real reached state. -/
theorem preserves
    {source target : TypeSystem.Ty} {inputType outputType : Ty} {methods : List α}
    (step : StepPreserves (row := row) (registry := registry) (faults := faults) (caller := caller) (reason := reason)
      protocol scope canonical functions program methods)
    (chain : ChainFor row source inputType methods target outputType)
    {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap} {store : Store}
    {input : Dynamic.Value} {native : Value} {outcome : Dynamic.ExpressionOutcome}
    (entry : states protocol scope canonical mapping world before store)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (represented : ValueRep values.checked registry functions mapping world source input native inputType)
    (trace : SelectedTraceFor row program methods before input outcome after) :
    ∃ value finalStore finalMap finalWorld,
      CallableCoercionSpine.Runs caller reason store (.inRight .word native) (methods.map (fun method => (row method).call)) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        target outputType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition protocol entry
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  exact preserves_for_with_state (functions := functions)
    (relation := relation protocol scope canonical)
    (fun state => protocol.refl state) (fun first second => protocol.trans first second)
    step chain entry heaps represented trace

/-- Native completion uses the original path inversion and actual post.
The Source result is independent of the native invocation's measurement. -/
theorem reflects
    {invocation : CallableCoercionSpine.Call → Store → Value → Value → Store → Prop}
    (forget : ∀ {call before input result after}, invocation call before input result after →
      CallableCoercionSpine.Invoke caller reason call before input result after)
    {source target : TypeSystem.Ty} {inputType outputType : Ty} {methods : List α}
    (step : StepReflects (row := row) (registry := registry) (faults := faults)
      protocol scope canonical functions program invocation methods)
    (chain : ChainFor row source inputType methods target outputType)
    {mapping : LocationMap} {world : StoreTyping}
    {before : Dynamic.Heap} {store finalStore : Store} {input : Dynamic.Value} {native value : Value}
    (entry : states protocol scope canonical mapping world before store)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (represented : ValueRep values.checked registry functions mapping world source input native inputType)
    (runs : CallableCoercionSpine.RunsFor invocation store (.inRight .word native) (methods.map (fun method => (row method).call)) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      SelectedTraceFor row program methods before input outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        target outputType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition protocol entry
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  exact reflects_for_with_state (functions := functions)
    (relation := relation protocol scope canonical) forget
    (fun state => protocol.refl state) (fun first second => protocol.trans first second)
    step chain entry heaps represented runs

end Solcore.SourceSemantics.CoreLowering.ProtectedCoercionPathMeaning
end
