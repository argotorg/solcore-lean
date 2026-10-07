import Solcore.SourceSemantics.CoreLowering.TypedImperativeForEndpoint
import Solcore.SourceSemantics.CoreLowering.ProtectedState

/-! The real for activation, including its post code, and its protected state have separate
fields. Child transitions retain their reached state; installing the hidden
self cell is an administrative operation with an unchanged record observation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedStateTransition.For
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open TypedLexicalWhile (Scope ValuesContext installedStore installedWorld)
open TypedImperativeFor (LoopState Progress)
universe u v
variable {Records : Type v}

structure State (protocol : Protocol.{u, v} Records)
    (values : ValuesContext) {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (registry : SourceCoreRawMetadata.Registry) (functions : FunctionModel values.checked.catalog ambient)
    (context : SourceSemantics.Context) (scope : Scope) (administrative actualContext : Core.Context)
    (frameLayout : SourceCoreCallableIndexedFrames.Layout)
    (environment : Dynamic.Environment) (canonical actual : Environment)
    (contextLocation location : Location) (type : Ty) (condition body post : Expr) (reason : Word)
    (mapping : LocationMap) (world : StoreTyping) (heap : Dynamic.Heap) (store : Store) where
  live : LoopState values registry functions context scope administrative actualContext frameLayout environment canonical actual
    contextLocation location type condition body post reason mapping world heap store
  retained : protocol.State ⟨scope, mapping, world, heap, store, canonical⟩

variable {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {registry : SourceCoreRawMetadata.Registry} {functions : FunctionModel values.checked.catalog ambient}
  {context : SourceSemantics.Context} {scope : Scope} {administrative actualContext : Core.Context}
  {frameLayout : SourceCoreCallableIndexedFrames.Layout}
  {environment : Dynamic.Environment} {canonical actual : Environment}
  {contextLocation location : Location} {type : Ty} {condition body post : Expr} {reason : Word}
  {mapping futureMap : LocationMap} {world futureWorld : StoreTyping}
  {before after : Dynamic.Heap} {store futureStore : Store}
  {Records : Type v} {protocol : Protocol.{u, v} Records}

/-- Keep the actual child post-witness while transporting the live loop frame. -/
theorem State.reach
    (state : State protocol values registry functions context scope administrative actualContext frameLayout
      environment canonical actual contextLocation location type condition body post reason mapping world before store)
    (progress : Progress values registry functions before after mapping futureMap world futureWorld store futureStore)
    (transition : Transition protocol state.retained
      ⟨scope, futureMap, futureWorld, after, futureStore, canonical⟩) :
    ∃ reached : State protocol values registry functions context scope administrative actualContext frameLayout
      environment canonical actual contextLocation location type condition body post reason futureMap futureWorld after futureStore,
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
    (typed : HasType actualContext (LocalLoop.iterate type condition body post reason)
      (LocalLoop.resultType type) ambient.definitions)
    {native : CallableIndexedHistory.NativeFrame}
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩) :
    State protocol values registry functions context scope administrative actualContext frameLayout
      environment canonical actual contextLocation store.length type condition body post reason mapping
      (installedWorld world type) before
      (installedStore store type condition body post reason actual) := by
  have facts := TypedImperativeFor.install reason heaps actualTyped typed
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
    (typed : HasType actualContext (LocalLoop.iterate type condition body post reason)
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
    (typed : HasType actualContext (LocalLoop.iterate type condition body post reason)
      (LocalLoop.resultType type) ambient.definitions)
    {native : CallableIndexedHistory.NativeFrame}
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩) :
    protocol.records (install transport environments heaps locals actualTyped typed read unmapped initial).retained = protocol.records initial := by
  dsimp only [install]
  apply transport.records_eq

/-- Source typing installs the actual renamed for closure and returns its
complete administrative progress, input relation, and exact record equality. -/
theorem initial_state (transport : AdministrativeTransport protocol)
    {conditionCode bodyCode postCode : Expr} {ξ : Renaming}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {native : CallableIndexedHistory.NativeFrame}
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.iterate type conditionCode bodyCode postCode reason) (LocalLoop.resultType type) ambient.definitions)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩) :
    ∃ state : State protocol values registry functions context scope administrative actualContext frameLayout
      environment canonical actual contextLocation store.length type (conditionCode.rename ξ) (bodyCode.rename ξ)
      (postCode.rename ξ) reason mapping (installedWorld world type) before
      (installedStore store type (conditionCode.rename ξ) (bodyCode.rename ξ) (postCode.rename ξ) reason actual),
      Progress values registry functions before before mapping mapping world (installedWorld world type) store
        (installedStore store type (conditionCode.rename ξ) (bodyCode.rename ξ) (postCode.rename ξ) reason actual) ∧
      protocol.Relates initial state.retained ∧ protocol.records state.retained = protocol.records initial := by
  have actualCode := typed.rename
    (TypedLexicalWhile.environment_respects environments.runtime_hasTypes actualTyped agrees)
  rw [LoopRenaming.iterate] at actualCode
  let state := install transport environments heaps locals actualTyped actualCode read unmapped initial
  have facts := TypedImperativeFor.install reason heaps actualTyped actualCode
  exact ⟨state, ⟨state.live.heaps, .refl _, facts.2.1, facts.2.2.2.2.2, .refl _⟩,
    install_related transport environments heaps locals actualTyped actualCode read unmapped initial,
    install_records transport environments heaps locals actualTyped actualCode read unmapped initial⟩

end Solcore.SourceSemantics.CoreLowering.ProtectedStateTransition.For
