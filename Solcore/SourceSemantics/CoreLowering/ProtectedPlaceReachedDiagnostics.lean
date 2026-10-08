import Solcore.SourceSemantics.CoreLowering.ProtectedStateTransition
import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceLiveRoot
import Solcore.SourceSemantics.CoreLowering.DataPlaceKeyOrder

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
    (law : ∀ location, faults (.uninitializedLocation location) prepared.invalidProjection) :
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
