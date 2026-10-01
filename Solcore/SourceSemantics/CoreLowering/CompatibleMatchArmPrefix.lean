import Solcore.SourceSemantics.CoreLowering.CompatibleMatchArmAllocation
import Solcore.SourceSemantics.CoreLowering.CompatiblePatternDecision
import Solcore.SourceSemantics.CoreLowering.CompatibleAmbientHeap

/-! The selected compatible arm reaches the canonical source lexical scope
through its actual marked allocator, skipping both successful bundle and
loaded scrutinee. The continuation agreement has both finite directions and
retains arbitrary captured function values and administrative store cells. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMatchArmPrefix
open Core Frontend SourceInference GeneralHeap DataEquality CoreProof ReadOnly DataPatternValues
open CompatibleMatchArmAllocation
open DataMatchCoreAllocation
open CompatibleMatchArmCertificates (Scope)

/-- The matcher's retained binder records feed the common ordinary payload
allocator without dropping their raw source type or function provenance. -/
theorem bindings_arguments
    {checked : SourceCoreCompatibleCatalog.Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : CompatiblePayload.FunctionModel checked.catalog ambient}
    {mapping : LocationMap} {world : StoreTyping}
    {bindings : List (TypedBinder × Ty)} {sources : List (TypedBinder × Dynamic.Value)} {values : List Value}
    (represented : CompatiblePatternLeaves.BindingsRep checked registry functions mapping world bindings sources values) :
    CallableIndexedParameterMeaning.Arguments (CompatibleAmbientHeap.payloadModel checked registry functions)
      mapping world bindings (sources.map Prod.snd) values := by
  induction represented with
  | nil => exact .nil
  | cons head tail ih => exact .cons head ih

theorem bindings_identical
    {checked : SourceCoreCompatibleCatalog.Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : CompatiblePayload.FunctionModel checked.catalog ambient}
    {mapping : LocationMap} {world : StoreTyping}
    {bindings : List (TypedBinder × Ty)} {sources : List (TypedBinder × Dynamic.Value)} {values : List Value}
    (represented : CompatiblePatternLeaves.BindingsRep checked registry functions mapping world bindings sources values) :
    bindings.map Prod.fst = sources.map Prod.fst := by
  induction represented with
  | nil => rfl
  | cons head tail ih => simp [ih]

private theorem liftMany_twoInsertions (count cutoff : Nat) :
    liftMany count (Renaming.comp (Renaming.insertion cutoff) (Renaming.insertion cutoff)) =
      Renaming.comp (Renaming.insertion (cutoff + count)) (Renaming.insertion (cutoff + count)) := by
  induction count generalizing cutoff with
  | zero => rfl
  | succ count ih =>
    simp only [liftMany, Renaming.lift_comp, Renaming.lift_insertion, ih]
    congr 2 <;> omega

/-- This is the successful branch emitted by compatible match lowering,
including its two hidden lexical slots. The result relates the arm's ordinary lexical scope
to its actual Core environment and transforms the body syntax with the same
embedding. Both finite evaluation directions retain the exact final store. -/
theorem bindArm_prefix {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {source : TypedSource} {context : SourceCoreCompatibleDataMatches.Context}
    {catalog : SourceCoreDataCatalog.Catalog}
    {projects : GenericHeap.Projection} {nativeDefinitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects nativeDefinitions}
    {bindings : List (TypedBinder × Ty)} {sources : List Dynamic.Value} {values : List Value}
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {scope : Scope} {environment : Dynamic.Environment} {canonical actual : Environment}
    {heap : Dynamic.Heap} {store : Store} {ξ : Renaming}
    (represented : CallableIndexedParameterMeaning.Arguments model mapping world bindings sources values)
    {scrutinee : Value} {outputType : Ty} {body code : Expr}
    (definitions : layouts.definitions = nativeDefinitions) (registered : layout.Registered nativeDefinitions)
    (allocator : context.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator layout globals
      (layouts.allocatorAt owner active onError)))
    (accepted : SourceCoreCompatibleDataMatches.bindArmWithAllocator context source scope bindings outputType
      (body.weakenAt bindings.length) = .ok code)
    {named : Bool} {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame}
    (kinds : ∀ binding ∈ bindings, source.inputs.any (fun input => decide (input.id = binding.1.id)) = named)
    (reference : canonical[scope.length + (if named then 0 else 1) + globals]? = some (.cellRef layout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native))
    (unmapped : contextLocation ∉ mapping)
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical nativeDefinitions)
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (actualLayout : EnvironmentsAgree ξ (packValues values :: scrutinee :: canonical) actual) :
    ∃ finalEnvironment finalHeap finalCanonical finalActual finalStore finalMap finalWorld finalEmbedding,
      Dynamic.BindersAllocate environment heap (bindings.map Prod.fst) sources
        finalEnvironment finalHeap ∧
      DataHeap.EnvRepresents catalog finalMap finalWorld administrativeContext
        (bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope)
        finalEnvironment finalCanonical nativeDefinitions ∧
      GenericHeap.HeapRepresents model finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      EnvironmentsAgree finalEmbedding finalCanonical finalActual ∧
      ContinuationAgreement actual store
        (code.rename ξ)
        finalActual finalStore (body.rename finalEmbedding) := by
  let κ := Renaming.comp (Renaming.insertion 0) (Renaming.insertion 0)
  have sourceLayout : EnvironmentsAgree κ canonical (packValues values :: scrutinee :: canonical) := by
    intro index value found
    exact found
  have length : (bindings.map Prod.snd).length = values.length := by
    simpa using represented.length.2
  obtain ⟨finalEnvironment, finalHeap, finalCanonical, finalLogical, finalActual, finalStore, finalMap,
    finalWorld, finalEmbedding, allocated, finalEnv, finalHeapRep, maps, worlds, frame,
    finalSourceLayout, finalActualLayout, _, agreement⟩ :=
    CompatibleMatchArmAllocation.Tree.prefix
      (CompatibleMatchArmCertificates.of_accepted onError allocator accepted) definitions registered represented
      environments heaps sourceLayout actualLayout (start := 0) rfl rfl length
      (fun {_ _} found => by simpa using found) kinds reference read unmapped
  refine ⟨finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore, finalMap,
    finalWorld, Renaming.comp finalEmbedding (liftMany bindings.length κ), allocated, finalEnv,
    finalHeapRep, maps, worlds, frame, ?_, ?_⟩
  · intro index value found
    exact finalActualLayout (finalSourceLayout found)
  · have same : ((body.weakenAt bindings.length).weakenAt bindings.length).rename finalEmbedding =
        body.rename (Renaming.comp finalEmbedding (liftMany bindings.length κ)) := by
      simp only [κ, liftMany_twoInsertions, Nat.zero_add]
      rw [← Expr.rename_insertion, ← Expr.rename_insertion, Expr.rename_comp, Expr.rename_comp]
      rfl
    rw [same] at agreement
    exact agreement


end Solcore.SourceSemantics.CoreLowering.CompatibleMatchArmPrefix
