import Solcore.SourceSemantics.CoreLowering.CompatibleNamedParameterCertificates
import Solcore.SourceSemantics.CoreLowering.CallableIndexedParameters
import Solcore.SourceSemantics.CoreLowering.CompatibleNamedBodyMeaning

/-! Parameter installation reaches the actual monomorphic call context. Its
finite continuation agreement comes from the production allocation receipts;
body correspondence comes from the extracted fixed-context certificate. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleNamedParameters
open Core Frontend SourceInference GeneralHeap CoreProof ReadOnly CompatiblePayload
open CallableIndexedParameterCertificates CallableIndexedParameterMeaning

structure Entry (values : SourceCoreCompatibleValues.Context)
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) (registry : SourceCoreRawMetadata.Registry)
    (function : Dynamic.Closure) (context : SourceSemantics.Context) (bindings : List Binding)
    (arguments : List Dynamic.Value) (before : Dynamic.Heap) (initialStore : Store)
    (initialMap : LocationMap) (initialWorld : StoreTyping) (administrative : Core.Context)
    (actual : Environment) (ξ : Renaming) (parameterCode body : Expr) where private mk ::
  environment : Dynamic.Environment
  heap : Dynamic.Heap
  canonical : Environment
  actualBody : Environment
  store : Store
  mapping : LocationMap
  world : StoreTyping
  embedding : Renaming
  allocation : Dynamic.BindersAllocate [] before function.parameters arguments environment heap
  environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
    (SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) :: administrative)
    (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) environment canonical ambient.definitions
  heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world heap store
  locals : Dynamic.EnvironmentAgrees heap context.locals environment
  maps : LocationMap.Extends initialMap mapping
  worlds : WorldExtends initialWorld world
  frame : AdministrativePreserved initialMap initialStore mapping store
  metadata : Dynamic.HeapMetadataExtend before heap
  lookups : EnvironmentsAgree embedding canonical actualBody
  agreement : ContinuationAgreement actual initialStore (parameterCode.rename ξ) actualBody store (body.rename embedding)

/-- Every source/native parameter fact is constructed before running the body.
The call context is fixed by the independent monomorphic binder extension. -/
theorem entry_of_accepted
    {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    {function : Dynamic.Closure} {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
    {bindings : List Binding} {output : Ty} {body parameterCode : Expr}
    (accepted : SourceCoreSourceCells.bindParameters
      (SourceCoreCallableIndexedAllocationFrames.allocator layout globals (layouts.allocatorAt owner active onError))
      function.source [] bindings output SourceCoreFunctions.argumentProjection body = .ok parameterCode)
    (parameters : function.parameters = bindings.map Prod.fst)
    (inputs : function.source.inputs = bindings.map Prod.fst)
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
    (definitions : layouts.definitions = ambient.definitions) (registered : layout.Registered ambient.definitions)
    {mapping : LocationMap} {world : StoreTyping} {arguments : List Dynamic.Value} {nativeArguments : List Value}
    (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      mapping world bindings arguments nativeArguments)
    {administrative : Core.Context} {canonical actual : Environment} {before : Dynamic.Heap} {store : Store}
    {ξ : Renaming} {contextLocation : Location} {native : SourceCoreCallableIndexedFrames.Frame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      administrative [] [] canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (initialLocals : Dynamic.EnvironmentAgrees before function.context.locals [])
    (actualLayout : EnvironmentsAgree ξ (DataPatternValues.packValues nativeArguments :: canonical) actual)
    (reference : canonical[globals]? = some (.cellRef layout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native))
    (unmapped : contextLocation ∉ mapping) :
    Nonempty (Entry values functions registry function context bindings arguments before store mapping world
      administrative actual ξ parameterCode body) := by
  obtain ⟨environment, heap, finalCanonical, finalActual, finalStore, finalMap, finalWorld, embedding,
      allocated, finalEnvironments, finalHeaps, maps, worlds, frame, lookups, agreement⟩ :=
    CallableIndexedParameters.named_prefix onError accepted inputs definitions registered represented environments heaps
      actualLayout reference read unmapped
  rw [← parameters] at allocated
  have mono := FunctionCallBody.mono_binders extended
  exact ⟨⟨environment, heap, finalCanonical, finalActual, finalStore, finalMap, finalWorld, embedding,
    allocated, finalEnvironments, finalHeaps, GenericLexicalContext.binders_agree mono.1 mono.2 initialLocals allocated,
    maps, worlds, frame, GenericLexicalContext.binders_metadata allocated, lookups, agreement⟩⟩

variable {readFuel : Nat} {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends values.registry registry) (program : Program)
  {function : Dynamic.Closure} {context : SourceSemantics.Context} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {bindings : List Binding} {output : Ty}
  {policy : SourceCoreLoops.Policy} {fuel : Nat} {fellThrough escaped : Word} {body parameterCode : Expr}
  (contextValid : CompatibleExpressionLiterals.ContextValid solved context function.evidence)
  (unique : NodeOccurrencesUnique function.source) {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  {arguments : List Dynamic.Value} {before : Dynamic.Heap} {store : Store}
  {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context} {actual : Environment} {ξ : Renaming}

include extension contextValid unique uninitialized in
/-- Finite source body execution completes the actual parameter prefix. The
source allocation is the one retained by the constructed entry. -/
theorem Entry.preserves
    (entry : Entry values functions registry function context bindings arguments before store mapping world
      administrative actual ξ parameterCode body)
    (certificate : CompatibleNamedBody.Certificate readFuel values function.source context solved reasonAt
      (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) function.body function.resultType output
      policy fuel fellThrough escaped body)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : FunctionCallBody.Trace program function context entry.environment entry.heap outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (parameterCode.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds, frame, metadata⟩ :=
    certificate.preserves functions extension program contextValid unique uninitialized entry.environments entry.heaps
      entry.locals entry.lookups trace
  exact ⟨value, finalStore, finalMap, finalWorld, entry.agreement.wrap evaluated, represented, heaps,
    entry.maps.trans maps, entry.worlds.trans worlds, entry.frame.trans frame, entry.metadata.trans metadata⟩

include extension contextValid unique uninitialized in
/-- Completed native prefix execution constructs the independent source trace
at the installed call context, without a universal body reflection premise. -/
theorem Entry.reflects
    (entry : Entry values functions registry function context bindings arguments before store mapping world
      administrative actual ξ parameterCode body)
    (certificate : CompatibleNamedBody.Certificate readFuel values function.source context solved reasonAt
      (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) function.body function.resultType output
      policy fuel fellThrough escaped body)
    {value : Value} {finalStore : Store}
    (evaluated : Evaluates actual store (parameterCode.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      FunctionCallBody.Trace program function context entry.environment entry.heap outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds, frame, metadata⟩ :=
    certificate.reflects functions extension program contextValid unique uninitialized entry.environments entry.heaps
      entry.locals entry.lookups (entry.agreement.unwrap evaluated)
  exact ⟨outcome, after, finalMap, finalWorld, trace, represented, heaps, entry.maps.trans maps,
    entry.worlds.trans worlds, entry.frame.trans frame, entry.metadata.trans metadata⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleNamedParameters
