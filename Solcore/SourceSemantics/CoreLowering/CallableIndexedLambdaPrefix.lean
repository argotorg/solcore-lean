import Solcore.SourceSemantics.CoreLowering.FunctionCallBody
import Solcore.SourceSemantics.CoreLowering.CompatibleAmbientHeap
import Solcore.SourceSemantics.CoreLowering.CallableIndexedParameterTyped
import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaViewPrefix

/-! A closure's entry copies its captured cells and then installs its
parameters, reaching the actual monomorphic call context. Its
finite continuation agreement comes from the production allocation receipts;
body correspondence comes from the extracted mixed lexical certificate. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaPrefix
open Core Frontend SourceInference GeneralHeap CoreProof ReadOnly CompatiblePayload
open CallableIndexedParameterCertificates CallableIndexedParameterMeaning

structure Entry (layout : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (contextLocation : Location) (native : SourceCoreCallableIndexedFrames.Frame) (values : SourceCoreCompatibleValues.Context)
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) (registry : SourceCoreRawMetadata.Registry)
    (function : Dynamic.Closure) (context : SourceSemantics.Context) (scope : Scope) (bindings : List Binding)
    (arguments : List Dynamic.Value) (before : Dynamic.Heap) (initialStore : Store)
    (initialMap : LocationMap) (initialWorld : StoreTyping) (administrative actualContext : Core.Context)
    (actual : Environment) (ξ : Renaming) (parameterCode body : Expr) where private mk ::
  copies : Dynamic.Environment
  copiedHeap : Dynamic.Heap
  copiedContext : Core.Context
  environment : Dynamic.Environment
  heap : Dynamic.Heap
  canonical : Environment
  actualBody : Environment
  store : Store
  mapping : LocationMap
  world : StoreTyping
  embedding : Renaming
  copy : Dynamic.EnvironmentCopies function.source function.captured before copies copiedHeap
  allocation : Dynamic.BindersAllocate copies copiedHeap function.parameters arguments environment heap
  environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
    administrative
    (bindings.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope) environment canonical ambient.definitions
  heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world heap store
  locals : Dynamic.EnvironmentAgrees heap context.locals environment
  maps : LocationMap.Extends initialMap mapping
  worlds : WorldExtends initialWorld world
  frame : AdministrativePreserved initialMap initialStore mapping store
  metadata : Dynamic.HeapMetadataExtend before heap
  lookups : EnvironmentsAgree embedding canonical actualBody
  actualTyped : RuntimeEnvironmentHasTypes world actualBody
    (CallableIndexedParameterTyped.prefixContext bindings copiedContext) ambient.definitions
  reference : canonical[(bindings.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope).length + 1 + globals]? =
    some (.cellRef layout.type contextLocation)
  read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native)
  unmapped : contextLocation ∉ mapping
  agreement : ContinuationAgreement actual initialStore (parameterCode.rename ξ) actualBody store (body.rename embedding)

/-- Actual prefix receipts copy the captured cells and construct parameter
allocation, the typed body environment and the surviving context-reference
slot. Its read and unmapped status follow from allocation preservation. No
final body facts are assumed. -/
theorem entry_of_accepted
    {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    {function : Dynamic.Closure} {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
    {scope : Scope} {bindings : List Binding} {output : Ty} {body allocatedCode parameterCode : Expr}
    (accepted : SourceCoreSourceCells.bindParameters
      (SourceCoreCallableIndexedAllocationFrames.allocator layout globals (layouts.allocatorAt owner active onError))
      function.source scope bindings output SourceCoreFunctions.argumentProjection (body.weakenAt bindings.length) = .ok allocatedCode)
    (copied : SourceCoreSourceCells.copyScope
      (some (SourceCoreCallableIndexedAllocationFrames.allocator layout globals (layouts.allocatorAt owner active onError)))
      function.source scope (· + 1) allocatedCode = .ok parameterCode)
    (parameters : function.parameters = bindings.map Prod.fst)
    (kinds : ∀ binding ∈ bindings, function.source.inputs.any (fun input => decide (input.id = binding.1.id)) = false)
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
    (definitions : layouts.definitions = ambient.definitions) (registered : layout.Registered ambient.definitions)
    {mapping : LocationMap} {world : StoreTyping} {arguments : List Dynamic.Value} {nativeArguments : List Value}
    (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      mapping world bindings arguments nativeArguments)
    {administrative actualContext : Core.Context} {canonical actual : Environment} {before : Dynamic.Heap} {store : Store}
    {ξ : Renaming} {contextLocation : Location} {native : SourceCoreCallableIndexedFrames.Frame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      administrative scope function.captured canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (initialLocals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
    (actualLayout : EnvironmentsAgree ξ (DataPatternValues.packValues nativeArguments :: canonical) actual)
    (types : Renaming.Respects ξ (SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) ::
      (SourceCoreLocalCell.coreContext scope ++ administrative)) actualContext)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef layout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native))
    (unmapped : contextLocation ∉ mapping) :
    Nonempty (Entry layout globals contextLocation native values functions registry function context scope bindings arguments before store mapping world
      administrative actualContext actual ξ parameterCode body) := by
  obtain ⟨entry⟩ := CallableIndexedLambdaViewPrefix.entry_of_accepted functions onError
    (LambdaMetadataViews.MetadataView.refl function.source) accepted copied parameters kinds extended definitions
    registered represented environments heaps initialLocals actualLayout types actualTyped reference read unmapped
  exact ⟨⟨entry.copies, entry.copiedHeap, entry.copiedContext, entry.environment, entry.heap, entry.canonical,
    entry.actualBody, entry.store, entry.mapping, entry.world, entry.embedding, entry.copy, entry.allocation,
    entry.environments, entry.heaps, entry.locals, entry.maps, entry.worlds, entry.frame, entry.metadata,
    entry.lookups, entry.actualTyped, entry.reference, entry.read, entry.unmapped, entry.agreement⟩⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaPrefix
