import Solcore.SourceSemantics.CoreLowering.ReachedLoweredReadOutcomePorts

/-! The original index fold consumes only genuine fragment, finite terminal
and static Source join receipts. The actual returned fields remain indexed. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.IndexFaultPostContracts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CompatibleMapping
open CompatibleExpressionIndices ExpressionFailurePostContracts

structure IndexJoins (post : ExpressionFaultPost) (values : ValuesContext)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) : Prop where
  base : ∀ {id base key : ExpressionId} {node baseNode keyNode : ExpressionNode} {layout : Core.OrderedMapping.Layout}
      {comparison : SourceCoreCompatibleDataEquality.Prepared values.checked} {first second : SourceCoreBasic.LoweredExpr}
      (_header : Header values source id base node baseNode layout comparison first second)
      (_keyFound : source.lookupExpression? key = some keyNode) (_form : node.form = .index base key)
      (_sourceType : baseNode.type = .mapping keyNode.type node.type),
    ∀ {environment before after reason token mapping world store},
      Dynamic.ExpressionFaults program context evidence source environment before base reason after →
      post program context evidence source environment before base reason after token mapping world store →
      post program context evidence source environment before id reason after token mapping world store
  key : ∀ {id base key : ExpressionId} {node baseNode keyNode : ExpressionNode} {layout : Core.OrderedMapping.Layout}
      {comparison : SourceCoreCompatibleDataEquality.Prepared values.checked} {first second : SourceCoreBasic.LoweredExpr}
      (_header : Header values source id base node baseNode layout comparison first second)
      (_keyFound : source.lookupExpression? key = some keyNode) (_form : node.form = .index base key)
      (_sourceType : baseNode.type = .mapping keyNode.type node.type),
    ∀ {environment before middle after baseSource reason token mapping world store},
      Dynamic.ExpressionEvaluates program context evidence source environment before base baseSource middle →
      Dynamic.ExpressionFaults program context evidence source environment middle key reason after →
      post program context evidence source environment middle key reason after token mapping world store →
      post program context evidence source environment before id reason after token mapping world store

def TerminalProvider (values : ValuesContext) (source : TypedSource)
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) (registry : SourceCoreRawMetadata.Registry)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (reasonAt : ExpressionId → Word) (keyPolicy : TypeSystem.Ty → Prop)
    (faults : FunctionCalls.FaultRep) (post : ExpressionFaultPost) : Prop :=
  ∀ {id base key node baseNode keyNode layout comparison first second}
    (_header : Header values source id base node baseNode layout comparison first second),
    baseNode.type = .mapping keyNode.type node.type → keyPolicy keyNode.type →
    ∀ {mapping world baseSource keySource baseValue keyValue},
    ValueRep values.checked registry functions mapping world baseNode.type baseSource baseValue first.type →
    ValueRep values.checked registry functions mapping world keyNode.type keySource keyValue second.type →
    ∀ {environment nativeContext heap store},
    RuntimeEnvironmentHasTypes world environment nativeContext ambient.definitions →
    CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world heap store →
    ∀ {sourceEnvironment before middle},
    source.lookupExpression? key = some keyNode → node.form = .index base key →
    Dynamic.ExpressionEvaluates program context evidence source sourceEnvironment before base baseSource middle →
    Dynamic.ExpressionEvaluates program context evidence source sourceEnvironment middle key keySource heap →
    ∃ outcome result finalStore futureWorld,
      Terminal baseSource keySource outcome ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        mapping futureWorld node.type layout.valueType faults outcome result ∧
      Evaluates (keyValue :: baseValue :: environment) store
        (SourceCoreMappingWithDefault.lookup layout (reasonAt id) comparison.expression (.var 1) (.var 0)) result finalStore ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping futureWorld heap finalStore ∧
      WorldExtends world futureWorld ∧ AdministrativePreserved mapping store mapping finalStore ∧
      (∀ other, Terminal baseSource keySource other → other = outcome) ∧
      Dynamic.ExpressionEvaluatesOutcome program context evidence source sourceEnvironment before id outcome heap ∧
      OutcomePost post program context evidence source sourceEnvironment before id layout.valueType
        outcome heap result mapping futureWorld finalStore

theorem trivial_index_joins (values : ValuesContext) (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) :
    IndexJoins TrivialExpressionPost values program context evidence source where
  base := by intros; trivial
  key := by intros; trivial

theorem IndexJoins.base_outcome {post : ExpressionFaultPost} {values : ValuesContext}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    (joins : IndexJoins post values program context evidence source)
    {id base key : ExpressionId} {node baseNode keyNode : ExpressionNode} {layout : Core.OrderedMapping.Layout}
    {comparison : SourceCoreCompatibleDataEquality.Prepared values.checked} {first second : SourceCoreBasic.LoweredExpr}
    (header : Header values source id base node baseNode layout comparison first second)
    (keyFound : source.lookupExpression? key = some keyNode) (form : node.form = .index base key)
    (sourceType : baseNode.type = .mapping keyNode.type node.type)
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {reason : Dynamic.SemanticFault} {token : Word} {mapping : LocationMap} {world : StoreTyping} {store : Store}
    {childType parentType : Ty}
    (failed : Dynamic.ExpressionFaults program context evidence source environment before base reason after)
    (retained : OutcomePost post program context evidence source environment before base childType (.fault reason)
      after (.inLeft childType (.word token)) mapping world store) :
    OutcomePost post program context evidence source environment before id parentType (.fault reason)
      after (.inLeft parentType (.word token)) mapping world store :=
  ⟨token, rfl, joins.base header keyFound form sourceType failed (OutcomePost.fault retained)⟩

theorem IndexJoins.key_outcome {post : ExpressionFaultPost} {values : ValuesContext}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    (joins : IndexJoins post values program context evidence source)
    {id base key : ExpressionId} {node baseNode keyNode : ExpressionNode} {layout : Core.OrderedMapping.Layout}
    {comparison : SourceCoreCompatibleDataEquality.Prepared values.checked} {first second : SourceCoreBasic.LoweredExpr}
    (header : Header values source id base node baseNode layout comparison first second)
    (keyFound : source.lookupExpression? key = some keyNode) (form : node.form = .index base key)
    (sourceType : baseNode.type = .mapping keyNode.type node.type)
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {middle : Dynamic.Heap} {baseSource : Dynamic.Value}
    {reason : Dynamic.SemanticFault} {token : Word} {mapping : LocationMap} {world : StoreTyping} {store : Store}
    {childType parentType : Ty}
    (baseTrace : Dynamic.ExpressionEvaluates program context evidence source environment before base baseSource middle)
    (failed : Dynamic.ExpressionFaults program context evidence source environment middle key reason after)
    (retained : OutcomePost post program context evidence source environment middle key childType (.fault reason)
      after (.inLeft childType (.word token)) mapping world store) :
    OutcomePost post program context evidence source environment before id parentType (.fault reason)
      after (.inLeft parentType (.word token)) mapping world store :=
  ⟨token, rfl, joins.key header keyFound form sourceType baseTrace failed (OutcomePost.fault retained)⟩

theorem trivial_scalar_terminal {values : ValuesContext} {source : TypedSource}
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) (registry : SourceCoreRawMetadata.Registry)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (reasonAt : ExpressionId → Word) {faults : FunctionCalls.FaultRep}
    (missing : ∀ id rawKey rawValue tag, MetadataRep registry (.mapping rawKey rawValue) tag →
      faults (.missingMappingDefault rawValue) ((reasonAt id).add tag)) :
    TerminalProvider values source functions registry program context evidence reasonAt SourceScalar faults TrivialExpressionPost := by
  intro id base key node baseNode keyNode layout comparison first second header sourceType profile
    mapping world baseSource keySource baseValue keyValue baseRep keyRep environment nativeContext heap store
    actualTyped heaps sourceEnvironment before middle keyFound form baseTrace keyTrace
  obtain ⟨outcome, result, finalStore, futureWorld, terminal, represented, lookup, finalHeaps, worlds, frame, functional⟩ :=
    header.finish sourceType profile baseRep keyRep actualTyped heaps (reasonAt id) (missing id)
  exact ⟨outcome, result, finalStore, futureWorld, terminal, represented, lookup, finalHeaps, worlds, frame, functional,
    index_intro header.metadata form (terminal.trace baseTrace keyTrace), OutcomePost.of_trivial represented⟩

theorem trivial_general_terminal {values : ValuesContext} {source : TypedSource}
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) (registry : SourceCoreRawMetadata.Registry)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (reasonAt : ExpressionId → Word) {faults : FunctionCalls.FaultRep}
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
    (functionTypes : FunctionRuntimeViews functions)
    (missing : ∀ id rawKey rawValue tag, MetadataRep registry (.mapping rawKey rawValue) tag →
      faults (.missingMappingDefault rawValue) ((reasonAt id).add tag)) :
    TerminalProvider values source functions registry program context evidence reasonAt (fun _ => True) faults TrivialExpressionPost := by
  intro id base key node baseNode keyNode layout comparison first second header sourceType profile
    mapping world baseSource keySource baseValue keyValue baseRep keyRep environment nativeContext heap store
    actualTyped heaps sourceEnvironment before middle keyFound form baseTrace keyTrace
  obtain ⟨outcome, result, finalStore, futureWorld, terminal, represented, lookup, finalHeaps, worlds, frame, functional⟩ :=
    CompatibleGeneralIndex.finish header sourceType faithful functionLeaves functionTypes baseRep keyRep actualTyped heaps (reasonAt id) (missing id)
  exact ⟨outcome, result, finalStore, futureWorld, terminal, represented, lookup, finalHeaps, worlds, frame, functional,
    index_intro header.metadata form (terminal.trace baseTrace keyTrace), OutcomePost.of_trivial represented⟩

/-- The callback is selected only at this actual Header, owning key/form and
ordered Source prefixes, then only at its invoked MissingWitness. -/
def MissingPolicies (values : ValuesContext) (source : TypedSource)
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) (registry : SourceCoreRawMetadata.Registry)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (reasonAt : ExpressionId → Word) (faults : FunctionCalls.FaultRep) : Prop :=
  ∀ {id base key node baseNode keyNode layout comparison first second}
    (header : Header values source id base node baseNode layout comparison first second)
    {mapping world baseSource keySource baseValue sourceEnvironment before middle heap},
    source.lookupExpression? key = some keyNode → node.form = .index base key →
    Dynamic.ExpressionEvaluates program context evidence source sourceEnvironment before base baseSource middle →
    Dynamic.ExpressionEvaluates program context evidence source sourceEnvironment middle key keySource heap →
    MissingPolicy (keyNode := keyNode) (registry := registry) header functions mapping world
      baseSource keySource baseValue (reasonAt id) faults

theorem model_scalar_terminal {values : ValuesContext} {source : TypedSource}
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) (registry : SourceCoreRawMetadata.Registry)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (reasonAt : ExpressionId → Word) {faults : FunctionCalls.FaultRep}
    (policies : MissingPolicies values source functions registry program context evidence reasonAt faults) :
    TerminalProvider values source functions registry program context evidence reasonAt SourceScalar faults
      (ReachedExpressionExtendedFaultPaths.model_expressionPost values.checked functions registry) := by
  intro id base key node baseNode keyNode layout comparison first second header sourceType profile
    mapping world baseSource keySource baseValue keyValue baseRep keyRep environment nativeContext heap store
    actualTyped heaps sourceEnvironment before middle keyFound form baseTrace keyTrace
  obtain ⟨outcome, result, finalStore, futureWorld, terminal, represented, lookup, finalHeaps, worlds, frame, functional, trace, post⟩ :=
    ReachedExpressionPrimitiveOutcomeProviders.index_finish header sourceType profile baseRep keyRep
      actualTyped heaps keyFound form baseTrace keyTrace (reasonAt id) (policies header keyFound form baseTrace keyTrace)
  exact ⟨outcome, result, finalStore, futureWorld, terminal, represented, lookup, finalHeaps, worlds, frame, functional, trace,
    ReachedExpressionExtendedFaultPaths.prior_outcomePost post⟩

theorem model_general_terminal {values : ValuesContext} {source : TypedSource}
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) (registry : SourceCoreRawMetadata.Registry)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (reasonAt : ExpressionId → Word) {faults : FunctionCalls.FaultRep}
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
    (functionTypes : FunctionRuntimeViews functions)
    (policies : MissingPolicies values source functions registry program context evidence reasonAt faults) :
    TerminalProvider values source functions registry program context evidence reasonAt (fun _ => True) faults
      (ReachedExpressionExtendedFaultPaths.model_expressionPost values.checked functions registry) := by
  intro id base key node baseNode keyNode layout comparison first second header sourceType profile
    mapping world baseSource keySource baseValue keyValue baseRep keyRep environment nativeContext heap store
    actualTyped heaps sourceEnvironment before middle keyFound form baseTrace keyTrace
  obtain ⟨outcome, result, finalStore, futureWorld, terminal, represented, lookup, finalHeaps, worlds, frame, functional, trace, post⟩ :=
    ReachedExpressionPrimitiveOutcomeProviders.general_index_finish header sourceType faithful functionLeaves functionTypes baseRep keyRep
      actualTyped heaps keyFound form baseTrace keyTrace (reasonAt id) (policies header keyFound form baseTrace keyTrace)
  exact ⟨outcome, result, finalStore, futureWorld, terminal, represented, lookup, finalHeaps, worlds, frame, functional, trace,
    ReachedExpressionExtendedFaultPaths.prior_outcomePost post⟩

theorem model_index_joins {values : ValuesContext} {source : TypedSource}
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) (registry : SourceCoreRawMetadata.Registry)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) :
    IndexJoins (ReachedExpressionExtendedFaultPaths.model_expressionPost values.checked functions registry)
      values program context evidence source where
  base := by
    intro id base key node baseNode keyNode layout comparison first second header keyFound form sourceType
      environment before after reason token mapping world store failed post
    exact ReachedExpressionExtendedFaultPaths.index_base header keyFound form sourceType failed post
  key := by
    intro id base key node baseNode keyNode layout comparison first second header keyFound form sourceType
      environment before middle after baseSource reason token mapping world store baseTrace failed post
    exact ReachedExpressionExtendedFaultPaths.index_key header keyFound form sourceType baseTrace failed post

end Solcore.SourceSemantics.CoreLowering.IndexFaultPostContracts
