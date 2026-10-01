import Solcore.SourceSemantics.CoreLowering.CompatibleGeneralIndexLookup

/-! General index decisions retain the source mapping metadata. Callable type
views and identity observations are supplied by the function model, independently
of native type projection. No extra Core instruction is needed. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleGeneralIndex
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CompatibleMapping
open CompatibleExpressionIndices

/-- The final helper creates a source decision and typed administrative suffix.
The key guard follows retained raw types and the authenticated function model. -/
theorem finish {values : ValuesContext} {source : TypedSource} {id base : ExpressionId}
    {node baseNode keyNode : ExpressionNode} {layout : Core.OrderedMapping.Layout}
    {comparison : SourceCoreCompatibleDataEquality.Prepared values.checked} {first second : SourceCoreBasic.LoweredExpr}
    (header : Header values source id base node baseNode layout comparison first second)
    (sourceType : baseNode.type = .mapping keyNode.type node.type)
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    {functions : FunctionModel values.checked.catalog ambient} {mapping : LocationMap} {world : StoreTyping}
    {identities : Dynamic.Value → Word → Prop}
    (faithful : DataEquality.IdentityFaithful identities)
    (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
    (functionTypes : FunctionRuntimeViews functions)
    {baseSource keySource : Dynamic.Value} {baseValue keyValue : Value}
    (baseRep : ValueRep values.checked registry functions mapping world baseNode.type baseSource baseValue first.type)
    (keyRep : ValueRep values.checked registry functions mapping world keyNode.type keySource keyValue second.type)
    {environment : Environment} {context : Core.Context} {heap : Dynamic.Heap} {store : Store}
    (environmentTyped : RuntimeEnvironmentHasTypes world environment context ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world heap store)
    (reason : Word) {faults : FunctionCalls.FaultRep}
    (missing : ∀ key value tag, MetadataRep registry (.mapping key value) tag → faults (.missingMappingDefault value) (reason.add tag)) :
    ∃ outcome result finalStore futureWorld,
      Terminal baseSource keySource outcome ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        mapping futureWorld node.type layout.valueType faults outcome result ∧
      Evaluates (keyValue :: baseValue :: environment) store
        (SourceCoreMappingWithDefault.lookup layout reason comparison.expression (.var 1) (.var 0)) result finalStore ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping futureWorld heap finalStore ∧
      WorldExtends world futureWorld ∧ AdministrativePreserved mapping store mapping finalStore ∧
      (∀ other, Terminal baseSource keySource other → other = outcome) := by
  obtain ⟨rawKey, rawValue, sources, rfl⟩ := source_mapping baseRep (by rw [sourceType]; rfl)
  obtain ⟨tag, nativeEntries, fallback, rfl, keyView, valueView, fields⟩ := header.mapping_fields sourceType baseRep
  have keyTyped : Dynamic.ValueRuntimeTypeMatches keySource rawKey := by
    cases keyRep.source_runtimeView functionTypes with
    | intro typed view =>
      exact .intro typed (view.trans (by simpa only [runtimeType_agrees_metadata] using keyView))
  have nativeKey : Payload registry functions mapping world rawKey layout.keyType keySource keyValue :=
    .compatible keyView.symm (header.keyType ▸ keyRep)
  obtain ⟨result, finalStore, futureWorld, resultMeaning, evaluated, finalHeaps, worlds, frame⟩ :=
    lookup_preserves_heap comparison faithful functionLeaves header.comparisonType fields nativeKey environmentTyped heaps reason
  have outcome : ∃ outcome, Terminal (.mapping rawKey rawValue sources) keySource outcome ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        mapping futureWorld node.type layout.valueType faults outcome result := by
    cases resultMeaning with
    | found located represented => exact ⟨_, .found rfl located, .value (.compatible valueView represented)⟩
    | default absent defaulted represented => exact ⟨_, .default rfl absent defaulted, .value (.compatible valueView represented)⟩
    | missing absent unavailable => exact ⟨_, .unavailable rfl keyTyped absent unavailable, .fault (missing _ _ _ fields.metadata)⟩
  obtain ⟨outcome, terminal, represented⟩ := outcome
  exact ⟨outcome, result, finalStore, futureWorld, terminal, represented, evaluated, finalHeaps, worlds, frame,
    fun _ other => other.functional keyTyped terminal⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleGeneralIndex
