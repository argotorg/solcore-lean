import Solcore.SourceSemantics.CoreLowering.CellAwareLoopAllocation
import Solcore.SourceSemantics.CoreLowering.CellAwareScopeFlowBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedWhileReadiness

/-! A live loop carries its actual self closure, the mixed Source heap and the
same caller frame. Child computation keeps its reached protocol state while
transporting every generalized descriptor through its concrete effect. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareLoopState
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open TypedLexicalWhile (installedStore installedWorld)

variable {whole : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
    projects whole.indexed.layouts.definitions}
  {named : SourceCoreGeneralFunctions.Function}
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
    whole.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed)))

structure State (context : SourceSemantics.Context) (scope : SourceCoreLocalCell.Scope)
    (administrative actualContext : Core.Context) (environment : Dynamic.Environment)
    (canonical actual : Environment) (location : Location) (type : Ty)
    (condition body : Expr) (reason : Word)
    (mapping : LocationMap) (world : StoreTyping) (heap : Dynamic.Heap) (store : Store) where
  environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
    mapping world administrative scope environment canonical whole.indexed.layouts.definitions
  heaps : GenericHeap.CellHeapRepresents
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed)) mapping world heap store
  locals : Dynamic.EnvironmentAgrees heap context.locals environment
  actualTyped : RuntimeEnvironmentHasTypes world actual actualContext whole.indexed.layouts.definitions
  authority : CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model whole.indexed)
    named.signature.key [] mapping world heap store environment
  physical : CellAwareScopePhysical.Physical whole named context scope canonical mapping world heap store environment
  owner : CallableIndexedOwnedFunctionValues.OwnedKey keys
  ownerAt : owner.key.frameLocation = physical.location
  ready : ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native
  selfTyped : world[location]? = some (OptionalCell.cellType (LocalLoop.functionType type))
  selfRead : store.read? location = some (.inRight .unit
    (LocalLoop.installedClosure type condition body (LocalLoop.fallthrough type) reason location actual))
  selfUnmapped : location ∉ mapping
  retained : protocol.State ⟨scope,mapping,world,heap,store,canonical⟩

variable {producer} {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
  {canonical actual : Environment} {location : Location} {type : Ty}
  {condition body : Expr} {reason : Word}
  {mapping nextMap : LocationMap} {world nextWorld : StoreTyping}
  {heap after : Dynamic.Heap} {store finalStore : Store}

/-- Retain the exact child post-state, rather than reconstructing an unrelated
state with the same heap. The loop's recursive closure remains unchanged. -/
def State.reach
    (state : State (named := named) producer context scope administrative actualContext environment canonical actual
      location type condition body reason mapping world heap store)
    (heaps : GenericHeap.CellHeapRepresents
      (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed)) nextMap nextWorld after finalStore)
    (effect : CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model whole.indexed)
      mapping world heap store nextMap nextWorld after finalStore)
    (frame : AdministrativePreserved mapping store nextMap finalStore)
    (reached : protocol.State ⟨scope,nextMap,nextWorld,after,finalStore,canonical⟩) :
    State (named := named) producer context scope administrative actualContext environment canonical actual
      location type condition body reason nextMap nextWorld after finalStore :=
  { environments := state.environments.extend effect.maps effect.worlds,
    heaps := heaps, locals := state.locals.mono effect.metadata, actualTyped := state.actualTyped.weaken effect.worlds,
    authority := state.authority.transport effect, physical := state.physical.transport effect frame,
    owner := state.owner, ownerAt := state.ownerAt, ready := state.ready,
    selfTyped := effect.worlds.lookup state.selfTyped,
    selfRead := (TypedLexicalWhile.retain state.selfUnmapped state.selfRead frame).2,
    selfUnmapped := (TypedLexicalWhile.retain state.selfUnmapped state.selfRead frame).1,
    retained := reached }

variable (transport : ProtectedStateTransition.AdministrativeTransport protocol)
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
    mapping world administrative scope environment canonical whole.indexed.layouts.definitions)
  (heaps : GenericHeap.CellHeapRepresents
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed)) mapping world heap store)
  (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
  (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext whole.indexed.layouts.definitions)
  (authority : CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model whole.indexed)
    named.signature.key [] mapping world heap store environment)
  (physical : CellAwareScopePhysical.Physical whole named context scope canonical mapping world heap store environment)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (ownerAt : owner.key.frameLocation = physical.location)
  (ready : ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native)
  (typed : HasType actualContext (LocalLoop.whileLoop type condition body reason)
    (LocalLoop.resultType type) whole.indexed.layouts.definitions)
  (initial : protocol.State ⟨scope,mapping,world,heap,store,canonical⟩)

/-- Installing the real while self cell changes only administrative storage. -/
def install : State (named := named) producer context scope administrative actualContext environment canonical actual
    store.length type condition body reason mapping (installedWorld world type) heap
    (installedStore store type condition body (LocalLoop.fallthrough type) reason actual) := by
  have allocation := CellAwareLoopAllocation.install reason heaps actualTyped typed
  have worlds := allocation.2.1
  have frame := allocation.2.2.2.2.2.1
  have effect := allocation.2.2.2.2.2.2
  exact {
    environments := environments.extend (.refl mapping) worlds,
    heaps := allocation.1, locals := locals, actualTyped := actualTyped.weaken worlds,
    authority := authority.transport effect, physical := physical.transport effect frame,
    owner := owner, ownerAt := ownerAt, ready := ready,
    selfTyped := allocation.2.2.2.1, selfRead := allocation.2.2.2.2.1,
    selfUnmapped := allocation.2.2.1,
    retained := transport.extend initial (.refl mapping) worlds frame (.refl heap) }

theorem install_related : protocol.Relates initial
    (install transport environments heaps locals actualTyped authority physical owner ownerAt ready typed initial).retained := by
  unfold install
  apply transport.related

theorem install_records : protocol.records
    (install transport environments heaps locals actualTyped authority physical owner ownerAt ready typed initial).retained =
    protocol.records initial := by
  unfold install
  apply transport.records_eq

end Solcore.SourceSemantics.CoreLowering.CellAwareLoopState
