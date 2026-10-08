import Solcore.SourceSemantics.CoreLowering.ReachedExpressionExtendedFaultPaths

/-! These ports start after the actual ordered base and key children succeeded.
They compose the existing suffix and preserve the same returned tuple. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ReachedIndexSuccessOutcomePorts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CompatibleMapping
open CompatibleExpressionIndices ExpressionFailurePostContracts
open GenericExpressionMeaning (rename_prefix)

private theorem index_completed_at_header {values : ValuesContext} {source : TypedSource} {id base : ExpressionId}
    {node baseNode : ExpressionNode} {layout : Core.OrderedMapping.Layout}
    {comparison : SourceCoreCompatibleDataEquality.Prepared values.checked} {first second : SourceCoreBasic.LoweredExpr}
    (header : Header values source id base node baseNode layout comparison first second)
    {environment : Environment} {store middleStore keyStore finalStore : Store}
    {baseValue keyValue result : Value} {ξ : Renaming} {reason : Word}
    (firstEval : Evaluates environment store (first.expression.rename ξ) (.inRight .word baseValue) middleStore)
    (secondEval : Evaluates (baseValue :: environment) middleStore (second.expression.rename ((Renaming.insertion 0).comp ξ)) (.inRight .word keyValue) keyStore)
    (lookup : Evaluates (keyValue :: baseValue :: environment) keyStore
      (SourceCoreMappingWithDefault.lookup layout reason comparison.expression (.var 1) (.var 0)) result finalStore) :
    Evaluates environment store
      ((SourceCoreCompatibleDataExpressions.index layout comparison.expression first.expression second.expression reason).rename ξ)
      result finalStore := by
  rw [index_rename comparison header.registered header.comparisonType]
  rw [rename_prefix] at secondEval
  apply SourceCoreCompatibleDataExpressions.index_completed layout reason firstEval secondEval
  simpa only [Transport.expression_weaken] using lookup

theorem index_after_values {values : ValuesContext} {source : TypedSource} {id base key : ExpressionId}
    {node baseNode keyNode : ExpressionNode} {layout : Core.OrderedMapping.Layout}
    {comparison : SourceCoreCompatibleDataEquality.Prepared values.checked} {first second : SourceCoreBasic.LoweredExpr}
    (header : Header values source id base node baseNode layout comparison first second)
    (sourceType : baseNode.type = .mapping keyNode.type node.type)
    (scalar : SourceScalar keyNode.type)
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    {functions : FunctionModel values.checked.catalog ambient}
    {initialMap middleMap keyMap : LocationMap} {initialWorld middleWorld keyWorld : StoreTyping}
    {baseSource keySource : Dynamic.Value} {baseValue keyValue : Value}
    (baseRep : ValueRep values.checked registry functions middleMap middleWorld baseNode.type baseSource baseValue first.type)
    (keyRep : ValueRep values.checked registry functions keyMap keyWorld keyNode.type keySource keyValue second.type)
    {environment : Environment} {nativeContext : Core.Context} {store middleStore keyStore : Store} {ξ : Renaming}
    (actualTyped : RuntimeEnvironmentHasTypes initialWorld environment nativeContext ambient.definitions)
    (firstEval : Evaluates environment store (first.expression.rename ξ) (.inRight .word baseValue) middleStore)
    (secondEval : Evaluates (baseValue :: environment) middleStore (second.expression.rename ((Renaming.insertion 0).comp ξ)) (.inRight .word keyValue) keyStore)
    (firstMaps : LocationMap.Extends initialMap middleMap) (keyMaps : LocationMap.Extends middleMap keyMap)
    (firstWorlds : WorldExtends initialWorld middleWorld) (keyWorlds : WorldExtends middleWorld keyWorld)
    (firstFrame : AdministrativePreserved initialMap store middleMap middleStore)
    (keyFrame : AdministrativePreserved middleMap middleStore keyMap keyStore)
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {sourceEnvironment : Dynamic.Environment} {before middle keyHeap : Dynamic.Heap}
    (keyFound : source.lookupExpression? key = some keyNode) (form : node.form = .index base key)
    (baseTrace : Dynamic.ExpressionEvaluates program context evidence source sourceEnvironment before base baseSource middle)
    (keyTrace : Dynamic.ExpressionEvaluates program context evidence source sourceEnvironment middle key keySource keyHeap)
    (firstMetadata : Dynamic.HeapMetadataExtend before middle) (keyMetadata : Dynamic.HeapMetadataExtend middle keyHeap)
    (keyHeaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions keyMap keyWorld keyHeap keyStore)
    (reasonAt : ExpressionId → Word) {faults : FunctionCalls.FaultRep}
    (missing : MissingPolicy (keyNode := keyNode) (registry := registry) header functions keyMap keyWorld
      baseSource keySource baseValue (reasonAt id) faults) :
    ∃ outcome result finalStore futureWorld,
      Terminal baseSource keySource outcome ∧
      Dynamic.ExpressionEvaluatesOutcome program context evidence source sourceEnvironment before id outcome keyHeap ∧
      Evaluates environment store
        ((SourceCoreCompatibleDataExpressions.index layout comparison.expression first.expression second.expression (reasonAt id)).rename ξ)
        result finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        keyMap futureWorld node.type layout.valueType faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions keyMap futureWorld keyHeap finalStore ∧
      LocationMap.Extends initialMap keyMap ∧ WorldExtends initialWorld futureWorld ∧
      AdministrativePreserved initialMap store keyMap finalStore ∧ Dynamic.HeapMetadataExtend before keyHeap ∧
      (∀ other, Terminal baseSource keySource other → other = outcome) ∧
      OutcomePost (ReachedExpressionExtendedFaultPaths.model_expressionPost values.checked functions registry)
        program context evidence source sourceEnvironment before id layout.valueType outcome keyHeap result keyMap futureWorld finalStore := by
  obtain ⟨outcome, result, finalStore, futureWorld, terminal, represented, lookup, finalHeaps, worlds,
    frame, functional, trace, post⟩ :=
    ReachedExpressionPrimitiveOutcomeProviders.index_finish header sourceType scalar (baseRep.extend (.refl _) keyMaps keyWorlds) keyRep
      (actualTyped.weaken (firstWorlds.trans keyWorlds)) keyHeaps keyFound form baseTrace keyTrace (reasonAt id) missing
  exact ⟨outcome, result, finalStore, futureWorld, terminal, trace,
    index_completed_at_header header firstEval secondEval lookup, represented, finalHeaps,
    firstMaps.trans keyMaps, (firstWorlds.trans keyWorlds).trans worlds,
    (firstFrame.trans keyFrame).trans frame, firstMetadata.trans keyMetadata, functional,
    ReachedExpressionExtendedFaultPaths.prior_outcomePost post⟩

theorem general_index_after_values {values : ValuesContext} {source : TypedSource} {id base key : ExpressionId}
    {node baseNode keyNode : ExpressionNode} {layout : Core.OrderedMapping.Layout}
    {comparison : SourceCoreCompatibleDataEquality.Prepared values.checked} {first second : SourceCoreBasic.LoweredExpr}
    (header : Header values source id base node baseNode layout comparison first second)
    (sourceType : baseNode.type = .mapping keyNode.type node.type)
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    {functions : FunctionModel values.checked.catalog ambient}
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
    (functionTypes : FunctionRuntimeViews functions)
    {initialMap middleMap keyMap : LocationMap} {initialWorld middleWorld keyWorld : StoreTyping}
    {baseSource keySource : Dynamic.Value} {baseValue keyValue : Value}
    (baseRep : ValueRep values.checked registry functions middleMap middleWorld baseNode.type baseSource baseValue first.type)
    (keyRep : ValueRep values.checked registry functions keyMap keyWorld keyNode.type keySource keyValue second.type)
    {environment : Environment} {nativeContext : Core.Context} {store middleStore keyStore : Store} {ξ : Renaming}
    (actualTyped : RuntimeEnvironmentHasTypes initialWorld environment nativeContext ambient.definitions)
    (firstEval : Evaluates environment store (first.expression.rename ξ) (.inRight .word baseValue) middleStore)
    (secondEval : Evaluates (baseValue :: environment) middleStore (second.expression.rename ((Renaming.insertion 0).comp ξ)) (.inRight .word keyValue) keyStore)
    (firstMaps : LocationMap.Extends initialMap middleMap) (keyMaps : LocationMap.Extends middleMap keyMap)
    (firstWorlds : WorldExtends initialWorld middleWorld) (keyWorlds : WorldExtends middleWorld keyWorld)
    (firstFrame : AdministrativePreserved initialMap store middleMap middleStore)
    (keyFrame : AdministrativePreserved middleMap middleStore keyMap keyStore)
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {sourceEnvironment : Dynamic.Environment} {before middle keyHeap : Dynamic.Heap}
    (keyFound : source.lookupExpression? key = some keyNode) (form : node.form = .index base key)
    (baseTrace : Dynamic.ExpressionEvaluates program context evidence source sourceEnvironment before base baseSource middle)
    (keyTrace : Dynamic.ExpressionEvaluates program context evidence source sourceEnvironment middle key keySource keyHeap)
    (firstMetadata : Dynamic.HeapMetadataExtend before middle) (keyMetadata : Dynamic.HeapMetadataExtend middle keyHeap)
    (keyHeaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions keyMap keyWorld keyHeap keyStore)
    (reasonAt : ExpressionId → Word) {faults : FunctionCalls.FaultRep}
    (missing : MissingPolicy (keyNode := keyNode) (registry := registry) header functions keyMap keyWorld
      baseSource keySource baseValue (reasonAt id) faults) :
    ∃ outcome result finalStore futureWorld,
      Terminal baseSource keySource outcome ∧
      Dynamic.ExpressionEvaluatesOutcome program context evidence source sourceEnvironment before id outcome keyHeap ∧
      Evaluates environment store
        ((SourceCoreCompatibleDataExpressions.index layout comparison.expression first.expression second.expression (reasonAt id)).rename ξ)
        result finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        keyMap futureWorld node.type layout.valueType faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions keyMap futureWorld keyHeap finalStore ∧
      LocationMap.Extends initialMap keyMap ∧ WorldExtends initialWorld futureWorld ∧
      AdministrativePreserved initialMap store keyMap finalStore ∧ Dynamic.HeapMetadataExtend before keyHeap ∧
      (∀ other, Terminal baseSource keySource other → other = outcome) ∧
      OutcomePost (ReachedExpressionExtendedFaultPaths.model_expressionPost values.checked functions registry)
        program context evidence source sourceEnvironment before id layout.valueType outcome keyHeap result keyMap futureWorld finalStore := by
  obtain ⟨outcome, result, finalStore, futureWorld, terminal, represented, lookup, finalHeaps, worlds,
    frame, functional, trace, post⟩ :=
    ReachedExpressionPrimitiveOutcomeProviders.general_index_finish header sourceType faithful functionLeaves functionTypes (baseRep.extend (.refl _) keyMaps keyWorlds) keyRep
      (actualTyped.weaken (firstWorlds.trans keyWorlds)) keyHeaps keyFound form baseTrace keyTrace (reasonAt id) missing
  exact ⟨outcome, result, finalStore, futureWorld, terminal, trace,
    index_completed_at_header header firstEval secondEval lookup, represented, finalHeaps,
    firstMaps.trans keyMaps, (firstWorlds.trans keyWorlds).trans worlds,
    (firstFrame.trans keyFrame).trans frame, firstMetadata.trans keyMetadata, functional,
    ReachedExpressionExtendedFaultPaths.prior_outcomePost post⟩

end Solcore.SourceSemantics.CoreLowering.ReachedIndexSuccessOutcomePorts
