import Solcore.SourceSemantics.CoreLowering.ProtectedExpressionBindings
import Solcore.SourceSemantics.CoreLowering.TypedLexicalWhileIteration

/-! A protected while activation retains the actual self closure and the
authenticated named-call entry. Hidden loop slots affect the actual environment
and renaming only; the canonical caller environment remains fixed. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedWhile
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open TypedLexicalWhile (Scope ValuesContext LoopState Progress installedStore installedWorld)

/-- The existing live native activation and a separate authority receipt.
Neither environment typing nor a source heap relation creates the entry. -/
def State (entry : ProtectedExpressionMeaning.Entry)
    (values : ValuesContext) {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (registry : SourceCoreRawMetadata.Registry) (functions : FunctionModel values.checked.catalog ambient)
    (context : SourceSemantics.Context) (scope : Scope) (administrative actualContext : Core.Context)
    (frameLayout : SourceCoreCallableIndexedFrames.Layout)
    (environment : Dynamic.Environment) (canonical actual : Environment)
    (contextLocation location : Location) (type : Ty) (condition body : Expr) (reason : Word)
    (mapping : LocationMap) (world : StoreTyping) (heap : Dynamic.Heap) (store : Store) : Prop :=
  LoopState values registry functions context scope administrative actualContext frameLayout environment canonical actual
    contextLocation location type condition body reason mapping world heap store ∧
  entry scope mapping world heap store canonical

variable {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {registry : SourceCoreRawMetadata.Registry} {functions : FunctionModel values.checked.catalog ambient}
  {context : SourceSemantics.Context} {scope : Scope} {administrative actualContext : Core.Context}
  {frameLayout : SourceCoreCallableIndexedFrames.Layout}
  {environment : Dynamic.Environment} {canonical actual : Environment}
  {contextLocation location : Location} {type : Ty} {condition body : Expr} {reason : Word}
  {mapping futureMap : LocationMap} {world futureWorld : StoreTyping}
  {before after : Dynamic.Heap} {store futureStore : Store}
  {entry : ProtectedExpressionMeaning.Entry}

/-- Progress transports the same installed code, captures and histories
through the actual protected administrative cells. -/
theorem State.advance (transport : ProtectedExpressionMeaning.Transport entry)
    (state : State entry values registry functions context scope administrative actualContext frameLayout
      environment canonical actual contextLocation location type condition body reason mapping world before store)
    (progress : Progress values registry functions before after mapping futureMap world futureWorld store futureStore) :
    State entry values registry functions context scope administrative actualContext frameLayout
      environment canonical actual contextLocation location type condition body reason futureMap futureWorld after futureStore :=
  ⟨state.1.progress progress,
    transport.extend state.2 progress.2.1 progress.2.2.1 progress.2.2.2.1 progress.2.2.2.2⟩

/-- The real generated self-cell installation preserves the original entry.
Its world entry and closure captures come from the actual native typing receipt;
the source map and canonical environment do not gain a loop binder. -/
theorem install (transport : ProtectedExpressionMeaning.Transport entry)
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
    (installed : entry scope mapping world before store canonical) :
    State entry values registry functions context scope administrative actualContext frameLayout
      environment canonical actual contextLocation store.length type condition body reason mapping
      (installedWorld world type) before
      (installedStore store type condition body (LocalLoop.fallthrough type) reason actual) := by
  obtain ⟨finalHeaps, worlds, selfUnmapped, selfTyped, selfRead, preserved⟩ :=
    TypedLexicalWhile.install reason heaps actualTyped typed
  obtain ⟨contextUnmapped, contextRead⟩ := TypedLexicalWhile.retain unmapped read preserved
  exact ⟨⟨environments.extend (.refl mapping) worlds, finalHeaps, locals, actualTyped.weaken worlds,
    ⟨native, contextRead⟩, contextUnmapped, selfTyped, selfRead, selfUnmapped⟩,
    transport.extend installed (.refl mapping) worlds preserved (Dynamic.HeapMetadataExtend.refl before)⟩

end Solcore.SourceSemantics.CoreLowering.ProtectedWhile
