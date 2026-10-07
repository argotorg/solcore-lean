import Solcore.SourceSemantics.CoreLowering.ProtectedWhileState
import Solcore.SourceSemantics.CoreLowering.ProtectedState

/-! The live loop activation and its actual protected state have separate
fields. Child transitions retain their reached state; installing the hidden
self cell is an administrative operation with an unchanged record observation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedStateTransition.While
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open TypedLexicalWhile (Scope ValuesContext LoopState Progress installedStore installedWorld)
universe u v
variable {Records : Type v}

structure State (protocol : Protocol.{u, v} Records)
    (values : ValuesContext) {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (registry : SourceCoreRawMetadata.Registry) (functions : FunctionModel values.checked.catalog ambient)
    (context : SourceSemantics.Context) (scope : Scope) (administrative actualContext : Core.Context)
    (frameLayout : SourceCoreCallableIndexedFrames.Layout)
    (environment : Dynamic.Environment) (canonical actual : Environment)
    (contextLocation location : Location) (type : Ty) (condition body : Expr) (reason : Word)
    (mapping : LocationMap) (world : StoreTyping) (heap : Dynamic.Heap) (store : Store) where
  live : LoopState values registry functions context scope administrative actualContext frameLayout environment canonical actual
    contextLocation location type condition body reason mapping world heap store
  retained : protocol.State ⟨scope, mapping, world, heap, store, canonical⟩

variable {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {registry : SourceCoreRawMetadata.Registry} {functions : FunctionModel values.checked.catalog ambient}
  {context : SourceSemantics.Context} {scope : Scope} {administrative actualContext : Core.Context}
  {frameLayout : SourceCoreCallableIndexedFrames.Layout}
  {environment : Dynamic.Environment} {canonical actual : Environment}
  {contextLocation location : Location} {type : Ty} {condition body : Expr} {reason : Word}
  {mapping futureMap : LocationMap} {world futureWorld : StoreTyping}
  {before after : Dynamic.Heap} {store futureStore : Store}
  {Records : Type v} {protocol : Protocol.{u, v} Records}

/-- Keep the actual child post-witness while transporting the live loop frame. -/
theorem State.reach
    (state : State protocol values registry functions context scope administrative actualContext frameLayout
      environment canonical actual contextLocation location type condition body reason mapping world before store)
    (progress : Progress values registry functions before after mapping futureMap world futureWorld store futureStore)
    (transition : Transition protocol state.retained
      ⟨scope, futureMap, futureWorld, after, futureStore, canonical⟩) :
    ∃ reached : State protocol values registry functions context scope administrative actualContext frameLayout
      environment canonical actual contextLocation location type condition body reason futureMap futureWorld after futureStore,
      protocol.Relates state.retained reached.retained := by
  obtain ⟨final, related⟩ := transition
  exact ⟨⟨state.live.progress progress, final⟩, related⟩

/-- Install the real self cell, retaining the exact input records. -/
def install (transport : AdministrativeTransport protocol)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (typed : HasType actualContext (LocalLoop.whileLoop type condition body reason)
      (LocalLoop.resultType type) ambient.definitions)
    {native : CallableIndexedHistory.NativeFrame}
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩) :
    State protocol values registry functions context scope administrative actualContext frameLayout
      environment canonical actual contextLocation store.length type condition body reason mapping
      (installedWorld world type) before
      (installedStore store type condition body (LocalLoop.fallthrough type) reason actual) := by
  have facts := TypedLexicalWhile.install reason heaps actualTyped typed
  refine ⟨?_, transport.extend initial (.refl mapping) facts.2.1 facts.2.2.2.2.2
    (Dynamic.HeapMetadataExtend.refl before)⟩
  obtain ⟨finalHeaps, worlds, selfUnmapped, selfTyped, selfRead, preserved⟩ := facts
  obtain ⟨contextUnmapped, contextRead⟩ := TypedLexicalWhile.retain unmapped read preserved
  exact ⟨environments.extend (.refl mapping) worlds, finalHeaps, locals, actualTyped.weaken worlds,
    ⟨native, contextRead⟩, contextUnmapped, selfTyped, selfRead, selfUnmapped⟩


theorem install_related (transport : AdministrativeTransport protocol)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (typed : HasType actualContext (LocalLoop.whileLoop type condition body reason)
      (LocalLoop.resultType type) ambient.definitions)
    {native : CallableIndexedHistory.NativeFrame}
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩) :
    protocol.Relates initial (install transport environments heaps locals actualTyped typed read unmapped initial).retained := by
  dsimp only [install]
  apply transport.related

theorem install_records (transport : AdministrativeTransport protocol)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (typed : HasType actualContext (LocalLoop.whileLoop type condition body reason)
      (LocalLoop.resultType type) ambient.definitions)
    {native : CallableIndexedHistory.NativeFrame}
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩) :
    protocol.records (install transport environments heaps locals actualTyped typed read unmapped initial).retained = protocol.records initial := by
  dsimp only [install]
  apply transport.records_eq

end Solcore.SourceSemantics.CoreLowering.ProtectedStateTransition.While
