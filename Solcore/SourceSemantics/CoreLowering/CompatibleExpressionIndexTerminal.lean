import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionIndexExecution

/-! The source decision after successful base and key effects is compared with
the real ordered mapping helper. Missing defaults retain the raw source type. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionIndices
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CompatibleMapping

inductive Terminal (base key : Dynamic.Value) : Dynamic.ExpressionOutcome → Prop where
  | found {sourceKey sourceValue entries value} (shape : base = .mapping sourceKey sourceValue entries)
      (located : Dynamic.MappingLookup key entries value) : Terminal base key (.value value)
  | default {sourceKey sourceValue entries value} (shape : base = .mapping sourceKey sourceValue entries)
      (absent : Dynamic.MappingAbsent key entries) (defaulted : Dynamic.DefaultValue sourceValue value) : Terminal base key (.value value)
  | shape (invalid : ¬ Dynamic.MappingValue base) : Terminal base key (.fault .invalidProjection)
  | keyType {sourceKey sourceValue entries actual} (shape : base = .mapping sourceKey sourceValue entries)
      (typed : Dynamic.ValueRuntimeType key actual) (mismatch : Dynamic.runtimeType actual ≠ Dynamic.runtimeType sourceKey) :
      Terminal base key (.fault (.typeMismatch sourceKey (Dynamic.runtimeType actual)))
  | unavailable {sourceKey sourceValue entries} (shape : base = .mapping sourceKey sourceValue entries)
      (typed : Dynamic.ValueRuntimeTypeMatches key sourceKey) (absent : Dynamic.MappingAbsent key entries)
      (missing : ¬ Dynamic.Defaultable sourceValue) : Terminal base key (.fault (.missingMappingDefault sourceValue))

theorem Terminal.functional {sourceKey sourceValue : TypeSystem.Ty} {entries : List (Dynamic.Value × Dynamic.Value)}
    {key : Dynamic.Value} {first second : Dynamic.ExpressionOutcome}
    (typed : Dynamic.ValueRuntimeTypeMatches key sourceKey)
    (left : Terminal (.mapping sourceKey sourceValue entries) key first)
    (right : Terminal (.mapping sourceKey sourceValue entries) key second) : first = second := by
  have mismatchImpossible : ∀ {actual}, Dynamic.ValueRuntimeType key actual →
      Dynamic.runtimeType actual ≠ Dynamic.runtimeType sourceKey → False := by
    intro actual actualTyped mismatch
    cases typed with
    | intro expected same => exact mismatch (actualTyped.functional expected ▸ same)
  cases left with
  | found shape found =>
    cases shape
    cases right with
    | found shape other => cases shape; exact congrArg Dynamic.ExpressionOutcome.value (found.functional other)
    | default shape absent _ | unavailable shape _ absent _ => cases shape; exact (absent.excludes_lookup found).elim
    | shape invalid => exact (invalid .intro).elim
    | keyType shape actual mismatch => cases shape; exact (mismatchImpossible actual mismatch).elim
  | default shape absent defaulted =>
    cases shape
    cases right with
    | found shape found => cases shape; exact (absent.excludes_lookup found).elim
    | default shape _ other => cases shape; exact congrArg Dynamic.ExpressionOutcome.value (defaulted.functional other)
    | unavailable shape _ _ missing => cases shape; exact (missing defaulted.defaultable).elim
    | shape invalid => exact (invalid .intro).elim
    | keyType shape actual mismatch => cases shape; exact (mismatchImpossible actual mismatch).elim
  | unavailable shape _ absent missing =>
    cases shape
    cases right with
    | found shape found => cases shape; exact (absent.excludes_lookup found).elim
    | default shape _ defaulted => cases shape; exact (missing defaulted.defaultable).elim
    | unavailable shape _ _ _ => cases shape; rfl
    | shape invalid => exact (invalid .intro).elim
    | keyType shape actual mismatch => cases shape; exact (mismatchImpossible actual mismatch).elim
  | shape invalid => exact (invalid .intro).elim
  | keyType shape actual mismatch => cases shape; exact (mismatchImpossible actual mismatch).elim

theorem SourceIndex.split {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap} {base key : ExpressionId}
    {outcome : Dynamic.ExpressionOutcome}
    (trace : SourceIndex program context evidence source environment before base key outcome after) :
    (∃ reason, outcome = .fault reason ∧ Dynamic.ExpressionFaults program context evidence source environment before base reason after) ∨
    (∃ baseValue middle, Dynamic.ExpressionEvaluates program context evidence source environment before base baseValue middle ∧
      ((∃ reason, outcome = .fault reason ∧ Dynamic.ExpressionFaults program context evidence source environment middle key reason after) ∨
       (∃ keyValue, Dynamic.ExpressionEvaluates program context evidence source environment middle key keyValue after ∧ Terminal baseValue keyValue outcome))) := by
  cases trace with
  | baseFailure failed => exact .inl ⟨_, rfl, failed⟩
  | keyFailure base failed => exact .inr ⟨_, _, base, .inl ⟨_, rfl, failed⟩⟩
  | found base key found => exact .inr ⟨_, _, base, .inr ⟨_, key, .found rfl found⟩⟩
  | default base key absent defaulted => exact .inr ⟨_, _, base, .inr ⟨_, key, .default rfl absent defaulted⟩⟩
  | shape base key invalid => exact .inr ⟨_, _, base, .inr ⟨_, key, .shape invalid⟩⟩
  | keyType base key typed mismatch => exact .inr ⟨_, _, base, .inr ⟨_, key, .keyType rfl typed mismatch⟩⟩
  | unavailable base key typed absent missing => exact .inr ⟨_, _, base, .inr ⟨_, key, .unavailable rfl typed absent missing⟩⟩

theorem Terminal.trace {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before middle after : Dynamic.Heap} {base key : ExpressionId}
    {baseValue keyValue : Dynamic.Value} {outcome : Dynamic.ExpressionOutcome}
    (baseTrace : Dynamic.ExpressionEvaluates program context evidence source environment before base baseValue middle)
    (keyTrace : Dynamic.ExpressionEvaluates program context evidence source environment middle key keyValue after)
    (terminal : Terminal baseValue keyValue outcome) :
    SourceIndex program context evidence source environment before base key outcome after := by
  cases terminal with
  | found shape found => cases shape; exact .found baseTrace keyTrace found
  | default shape absent defaulted => cases shape; exact .default baseTrace keyTrace absent defaulted
  | shape invalid => exact .shape baseTrace keyTrace invalid
  | keyType shape typed mismatch => cases shape; exact .keyType baseTrace keyTrace typed mismatch
  | unavailable shape typed absent missing => cases shape; exact .unavailable baseTrace keyTrace typed absent missing

/-- The final helper creates a source decision and typed administrative suffix.
The key guard follows retained raw types and the explicit scalar source profile. -/
theorem Header.finish {values : ValuesContext} {source : TypedSource} {id base : ExpressionId}
    {node baseNode keyNode : ExpressionNode} {layout : Core.OrderedMapping.Layout}
    {comparison : SourceCoreCompatibleDataEquality.Prepared values.checked} {first second : SourceCoreBasic.LoweredExpr}
    (header : Header values source id base node baseNode layout comparison first second)
    (sourceType : baseNode.type = .mapping keyNode.type node.type) (scalar : SourceScalar keyNode.type)
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    {functions : FunctionModel values.checked.catalog ambient} {mapping : LocationMap} {world : StoreTyping}
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
  have keyTyped := scalar.runtime_matches keyRep keyView
  have nativeKey : Payload registry functions mapping world rawKey layout.keyType keySource keyValue :=
    .compatible keyView.symm (header.keyType ▸ keyRep)
  obtain ⟨result, finalStore, futureWorld, resultMeaning, evaluated, finalHeaps, worlds, frame⟩ :=
    lookup_preserves_heap comparison (header.scalar sourceType scalar) header.comparisonType fields nativeKey environmentTyped heaps reason
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

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionIndices
