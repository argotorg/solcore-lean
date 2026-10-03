import Solcore.SourceSemantics.CoreLowering.TypedForHeaderReflection

/-! The post header has an actual constant fallthrough continuation. Closing
that continuation recovers finite post execution and reflection. Source names
introduced by the post can then be forgotten without dropping their cells or
effects, or changing the captured outer native environment. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.TypedForHeader
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory (NativeFrame)

def Fallthrough (type : Ty) (_context : SourceSemantics.Context) (_scope : Scope) (code : Expr) : Prop :=
  code = LocalLoop.fallthrough type

variable {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {registry : SourceCoreRawMetadata.Registry} {functions : FunctionModel values.checked.catalog ambient}
  {source : TypedSource} {solved : List SolvedRequirement} {evidence : Dynamic.EvidenceEnvironment}
  {administrative : Core.Context} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {contextLocation : Location} {native : NativeFrame} {type : Ty}
  {context : SourceSemantics.Context} {environment : Dynamic.Environment} {heap : Dynamic.Heap}

theorem TailFor.fallthrough_evaluates
    {validity : SourceSemantics.Context → Prop}
    (tail : TailFor validity registry functions source solved evidence administrative frame globals contextLocation native
      (Fallthrough type) context environment heap) :
    Evaluates tail.actual tail.store (tail.code.rename tail.embedding) (LocalLoop.fallthroughValue type) tail.store := by
  rw [tail.certificate]
  simpa only [LoopRenaming.fallthrough] using LocalLoop.fallthrough_evaluates type tail.actual tail.store

theorem TailFor.fallthrough_reflects
    {validity : SourceSemantics.Context → Prop}
    (tail : TailFor validity registry functions source solved evidence administrative frame globals contextLocation native
      (Fallthrough type) context environment heap) {value : Value} {store : Store}
    (evaluated : Evaluates tail.actual tail.store (tail.code.rename tail.embedding) value store) :
    value = LocalLoop.fallthroughValue type ∧ store = tail.store :=
  evaluation_deterministic evaluated tail.fallthrough_evaluates

theorem Tail.fallthrough_evaluates
    (tail : Tail registry functions source solved evidence administrative frame globals contextLocation native
      (Fallthrough type) context environment heap) :
    Evaluates tail.actual tail.store (tail.code.rename tail.embedding) (LocalLoop.fallthroughValue type) tail.store :=
  TailFor.fallthrough_evaluates tail

theorem Tail.fallthrough_reflects
    (tail : Tail registry functions source solved evidence administrative frame globals contextLocation native
      (Fallthrough type) context environment heap) {value : Value} {store : Store}
    (evaluated : Evaluates tail.actual tail.store (tail.code.rename tail.embedding) value store) :
    value = LocalLoop.fallthroughValue type ∧ store = tail.store :=
  TailFor.fallthrough_reflects tail evaluated

end Solcore.SourceSemantics.CoreLowering.TypedForHeader

namespace Solcore.SourceSemantics.CoreLowering.TypedForHeader
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory (NativeFrame)

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {readFuel : Nat} {values : ValuesContext} {source : TypedSource} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {administrative : Core.Context}
  {type : Ty} {continuation : SourceSemantics.Context → Scope → Expr → Prop}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)

include definitions registered extension uninitialized missing faithful observations in
theorem Tree.preserves_post {context finalContext : SourceSemantics.Context} {scope : Scope}
    {items : List ForItemForm} {code : Expr}
    (tree : Tree layouts owner active frame globals onError readFuel values source solved reasonAt ambient.definitions administrative type (Fallthrough type)
      context scope items code)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (unique : NodeOccurrencesUnique source)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment finalEnvironment : Dynamic.Environment} {canonical actual : Environment}
    {before after : Dynamic.Heap} {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (trace : Dynamic.ForItemsExecute program context evidence source environment before items finalContext finalEnvironment after) :
    ∃ tail : Tail registry functions source solved evidence administrative frame globals contextLocation native (Fallthrough type) finalContext finalEnvironment after,
      LocationMap.Extends mapping tail.mapping ∧ WorldExtends world tail.world ∧
      AdministrativePreserved mapping store tail.mapping tail.store ∧ Dynamic.HeapMetadataExtend before after ∧
      Evaluates actual store (code.rename ξ) (LocalLoop.fallthroughValue type) tail.store ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
        tail.mapping tail.world administrative scope environment canonical ambient.definitions ∧
      Dynamic.EnvironmentAgrees after context.locals environment ∧
      RuntimeEnvironmentHasTypes tail.world actual actualContext ambient.definitions := by
  obtain ⟨tail, maps, worlds, preservation, metadata, agreement⟩ :=
    tree.preserves_prefix functions definitions registered extension program evidence uninitialized missing faithful observations
      valid unique environments heaps locals agrees actualTyped reference read unmapped trace
  refine ⟨tail, maps, worlds, preservation, metadata, agreement.wrap tail.fallthrough_evaluates,
    environments.extend maps worlds, locals.mono metadata, actualTyped.weaken worlds⟩

include definitions registered extension uninitialized missing faithful observations in
theorem Tree.reflects_post (functionTypes : FunctionRuntimeViews functions)
    {context : SourceSemantics.Context} {scope : Scope} {items : List ForItemForm} {code : Expr}
    (tree : Tree layouts owner active frame globals onError readFuel values source solved reasonAt ambient.definitions administrative type (Fallthrough type)
      context scope items code) (errors : Tree.Errors registry faults tree)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (unique : NodeOccurrencesUnique source)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before : Dynamic.Heap} {store finalStore : Store} {value : Value}
    {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual store (code.rename ξ) value finalStore) :
    (∃ finalContext finalEnvironment after,
      ∃ tail : Tail registry functions source solved evidence administrative frame globals contextLocation native
        (Fallthrough type) finalContext finalEnvironment after,
      Dynamic.ForItemsExecute program context evidence source environment before items finalContext finalEnvironment after ∧
      value = LocalLoop.fallthroughValue type ∧ finalStore = tail.store ∧
      LocationMap.Extends mapping tail.mapping ∧ WorldExtends world tail.world ∧
      AdministrativePreserved mapping store tail.mapping tail.store ∧ Dynamic.HeapMetadataExtend before after ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
        tail.mapping tail.world administrative scope environment canonical ambient.definitions ∧
      Dynamic.EnvironmentAgrees after context.locals environment ∧
      RuntimeEnvironmentHasTypes tail.world actual actualContext ambient.definitions) ∨
    (∃ finalContext reason token after finalMap finalWorld,
      Dynamic.ForItemsFault program context evidence source environment before items finalContext reason after ∧
      value = .inLeft (LocalLoop.controlType type) (.word token) ∧ faults reason token ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after) := by
  have reflected := tree.reflects functions definitions registered extension program evidence uninitialized missing faithful observations
    functionTypes errors valid unique environments heaps locals agrees actualTyped reference read unmapped evaluated
  cases reflected with
  | continues tail trace maps worlds preservation metadata remaining =>
    obtain ⟨same, storeEq⟩ := tail.fallthrough_reflects remaining
    exact .inl ⟨_, _, _, tail, trace, same, storeEq, maps, worlds, preservation, metadata,
      environments.extend maps worlds, locals.mono metadata, actualTyped.weaken worlds⟩
  | fault trace same matched finalHeaps maps worlds preservation metadata =>
    exact .inr ⟨_, _, _, _, _, _, trace, same, matched, finalHeaps, maps, worlds, preservation, metadata⟩

end Solcore.SourceSemantics.CoreLowering.TypedForHeader
