import Solcore.SourceSemantics.CoreLowering.ReachedExpressionPrimitiveOutcomeProviders

/-! Static index joins retain the same primitive packet. Ordinary joins reuse
their original Source links. No expression or execution is traversed here. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ReachedExpressionExtendedFaultPaths
open Core Frontend SourceInference GeneralHeap CompatiblePayload
open ExpressionFailurePostContracts
open ReachedExpressionFaultOrigins (PrimitiveOrigin NativeTransport)
open ReachedExpressionPrimitiveOutcomeProviders (ModelAssociation)

mutual
  inductive ExpressionPath : {heap : Dynamic.Heap} → {reason : Dynamic.SemanticFault} → {token : Word} →
      PrimitiveOrigin heap reason token → Program → SourceSemantics.Context → Dynamic.EvidenceEnvironment →
      TypedSource → Dynamic.Environment → Dynamic.Heap → ExpressionId → Prop where
    | prior {heap : Dynamic.Heap} {reason : Dynamic.SemanticFault} {token : Word}
        {origin : PrimitiveOrigin heap reason token} {program : Program} {context : SourceSemantics.Context}
        {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
        {before : Dynamic.Heap} {id : ExpressionId}
        (path : ReachedExpressionFaultOrigins.ExpressionPath origin program context evidence source environment before id) :
        ExpressionPath origin program context evidence source environment before id
    | indexBase {heap : Dynamic.Heap} {reason : Dynamic.SemanticFault} {token : Word}
        {origin : PrimitiveOrigin heap reason token} {program : Program} {context : SourceSemantics.Context}
        {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
        {before : Dynamic.Heap} {values : SourceCoreCompatibleValues.Context} {id base key : ExpressionId}
        {node baseNode keyNode : ExpressionNode} {layout : Core.OrderedMapping.Layout}
        {comparison : SourceCoreCompatibleDataEquality.Prepared values.checked} {first second : SourceCoreBasic.LoweredExpr}
        (header : CompatibleExpressionIndices.Header values source id base node baseNode layout comparison first second)
        (keyFound : source.lookupExpression? key = some keyNode) (form : node.form = .index base key)
        (sourceType : baseNode.type = .mapping keyNode.type node.type)
        (failed : Dynamic.ExpressionFaults program context evidence source environment before base reason heap)
        (child : ExpressionPath origin program context evidence source environment before base) :
        ExpressionPath origin program context evidence source environment before id
    | indexKey {heap : Dynamic.Heap} {reason : Dynamic.SemanticFault} {token : Word}
        {origin : PrimitiveOrigin heap reason token} {program : Program} {context : SourceSemantics.Context}
        {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
        {before middle : Dynamic.Heap} {baseSource : Dynamic.Value}
        {values : SourceCoreCompatibleValues.Context} {id base key : ExpressionId}
        {node baseNode keyNode : ExpressionNode} {layout : Core.OrderedMapping.Layout}
        {comparison : SourceCoreCompatibleDataEquality.Prepared values.checked} {first second : SourceCoreBasic.LoweredExpr}
        (header : CompatibleExpressionIndices.Header values source id base node baseNode layout comparison first second)
        (keyFound : source.lookupExpression? key = some keyNode) (form : node.form = .index base key)
        (sourceType : baseNode.type = .mapping keyNode.type node.type)
        (baseTrace : Dynamic.ExpressionEvaluates program context evidence source environment before base baseSource middle)
        (failed : Dynamic.ExpressionFaults program context evidence source environment middle key reason heap)
        (child : ExpressionPath origin program context evidence source environment middle key) :
        ExpressionPath origin program context evidence source environment before id
    | expression {heap : Dynamic.Heap} {reason : Dynamic.SemanticFault} {token : Word}
        {origin : PrimitiveOrigin heap reason token} {program : Program} {context : SourceSemantics.Context}
        {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
        {before middle : Dynamic.Heap} {id childId : ExpressionId}
        (link : ExpressionLink program context evidence source environment before id middle childId)
        (child : ExpressionPath origin program context evidence source environment middle childId) :
        ExpressionPath origin program context evidence source environment before id
    | expressions {heap : Dynamic.Heap} {reason : Dynamic.SemanticFault} {token : Word}
        {origin : PrimitiveOrigin heap reason token} {program : Program} {context : SourceSemantics.Context}
        {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
        {before : Dynamic.Heap} {id : ExpressionId} {ids : List ExpressionId}
        (link : ExpressionsLink source id ids)
        (children : ExpressionsPath origin program context evidence source environment before ids) :
        ExpressionPath origin program context evidence source environment before id

  inductive ExpressionsPath : {heap : Dynamic.Heap} → {reason : Dynamic.SemanticFault} → {token : Word} →
      PrimitiveOrigin heap reason token → Program → SourceSemantics.Context → Dynamic.EvidenceEnvironment →
      TypedSource → Dynamic.Environment → Dynamic.Heap → List ExpressionId → Prop where
    | prior {heap : Dynamic.Heap} {reason : Dynamic.SemanticFault} {token : Word}
        {origin : PrimitiveOrigin heap reason token} {program : Program} {context : SourceSemantics.Context}
        {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
        {before : Dynamic.Heap} {ids : List ExpressionId}
        (path : ReachedExpressionFaultOrigins.ExpressionsPath origin program context evidence source environment before ids) :
        ExpressionsPath origin program context evidence source environment before ids
    | head {heap : Dynamic.Heap} {reason : Dynamic.SemanticFault} {token : Word}
        {origin : PrimitiveOrigin heap reason token} {program : Program} {context : SourceSemantics.Context}
        {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
        {before : Dynamic.Heap} {id : ExpressionId} {ids : List ExpressionId}
        (child : ExpressionPath origin program context evidence source environment before id) :
        ExpressionsPath origin program context evidence source environment before (id :: ids)
    | tail {heap : Dynamic.Heap} {reason : Dynamic.SemanticFault} {token : Word}
        {origin : PrimitiveOrigin heap reason token} {program : Program} {context : SourceSemantics.Context}
        {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
        {before middle : Dynamic.Heap} {id : ExpressionId} {ids : List ExpressionId} {value : Dynamic.Value}
        (head : Dynamic.ExpressionEvaluates program context evidence source environment before id value middle)
        (child : ExpressionsPath origin program context evidence source environment middle ids) :
        ExpressionsPath origin program context evidence source environment before (id :: ids)
end

def model_expressionPost (checked : SourceCoreCompatibleCatalog.Checked)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) (registry : SourceCoreRawMetadata.Registry) :
    ExpressionFaultPost :=
  fun program context evidence source environment before id reason after token mapping world _store =>
    ∃ origin : PrimitiveOrigin after reason token,
      ExpressionPath origin program context evidence source environment before id ∧
      NativeTransport origin registry mapping world ∧ ModelAssociation checked functions origin

def model_expressionsPost (checked : SourceCoreCompatibleCatalog.Checked)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) (registry : SourceCoreRawMetadata.Registry) :
    ExpressionsFaultPost :=
  fun program context evidence source environment before ids reason after token mapping world _store =>
    ∃ origin : PrimitiveOrigin after reason token,
      ExpressionsPath origin program context evidence source environment before ids ∧
      NativeTransport origin registry mapping world ∧ ModelAssociation checked functions origin

theorem prior_expressionPost {checked : SourceCoreCompatibleCatalog.Checked}
    {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
    {registry : SourceCoreRawMetadata.Registry} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : ExpressionId} {reason : Dynamic.SemanticFault} {token : Word}
    {mapping : LocationMap} {world : StoreTyping} {store : Store}
    (post : ReachedExpressionPrimitiveOutcomeProviders.model_expressionPost checked functions registry program context
      evidence source environment before id reason after token mapping world store) :
    model_expressionPost checked functions registry program context evidence source environment before id reason
      after token mapping world store := by
  obtain ⟨origin, path, native, associated⟩ := post
  exact ⟨origin, .prior path, native, associated⟩

theorem prior_outcomePost {checked : SourceCoreCompatibleCatalog.Checked}
    {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
    {registry : SourceCoreRawMetadata.Registry} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : ExpressionId} {type : Ty} {outcome : Dynamic.ExpressionOutcome}
    {value : Value} {mapping : LocationMap} {world : StoreTyping} {store : Store}
    (post : OutcomePost (ReachedExpressionPrimitiveOutcomeProviders.model_expressionPost checked functions registry)
      program context evidence source environment before id type outcome after value mapping world store) :
    OutcomePost (model_expressionPost checked functions registry) program context evidence source environment
      before id type outcome after value mapping world store := by
  cases outcome with
  | value _ => trivial
  | fault _ =>
    obtain ⟨token, same, retained⟩ := post
    exact ⟨token, same, prior_expressionPost retained⟩

theorem sequence_joins (checked : SourceCoreCompatibleCatalog.Checked)
    {ambient : AmbientDefinitions checked.catalog.definitions} (functions : FunctionModel checked.catalog ambient)
    (registry : SourceCoreRawMetadata.Registry) (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) :
    SequenceJoins (model_expressionPost checked functions registry) (model_expressionsPost checked functions registry)
      program context evidence source where
  head := by
    intro environment before id ids reason after token mapping world store _failed post
    obtain ⟨origin, path, native, associated⟩ := post
    exact ⟨origin, .head path, native, associated⟩
  tail := by
    intro environment before middle id ids value reason after token mapping world store firstSource _failed post
    obtain ⟨origin, path, native, associated⟩ := post
    exact ⟨origin, .tail firstSource path, native, associated⟩

theorem composition_joins (checked : SourceCoreCompatibleCatalog.Checked)
    {ambient : AmbientDefinitions checked.catalog.definitions} (functions : FunctionModel checked.catalog ambient)
    (registry : SourceCoreRawMetadata.Registry) (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) :
    CompositionJoins (model_expressionPost checked functions registry) (model_expressionsPost checked functions registry)
      program context evidence source where
  expression := by
    intro environment before id middle child reason after token mapping world store link _failed post
    obtain ⟨origin, path, native, associated⟩ := post
    exact ⟨origin, .expression link path, native, associated⟩
  expressions := by
    intro environment before id ids reason after token mapping world store link _failed post
    obtain ⟨origin, path, native, associated⟩ := post
    exact ⟨origin, .expressions link path, native, associated⟩

theorem index_base {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {id base key : ExpressionId} {node baseNode keyNode : ExpressionNode} {layout : Core.OrderedMapping.Layout}
    {comparison : SourceCoreCompatibleDataEquality.Prepared values.checked} {first second : SourceCoreBasic.LoweredExpr}
    (header : CompatibleExpressionIndices.Header values source id base node baseNode layout comparison first second)
    (keyFound : source.lookupExpression? key = some keyNode) (form : node.form = .index base key)
    (sourceType : baseNode.type = .mapping keyNode.type node.type)
    {ambient : AmbientDefinitions values.checked.catalog.definitions} {functions : FunctionModel values.checked.catalog ambient}
    {registry : SourceCoreRawMetadata.Registry} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {reason : Dynamic.SemanticFault} {token : Word} {mapping : LocationMap} {world : StoreTyping} {store : Store}
    (failed : Dynamic.ExpressionFaults program context evidence source environment before base reason after)
    (post : model_expressionPost values.checked functions registry program context evidence source environment
      before base reason after token mapping world store) :
    model_expressionPost values.checked functions registry program context evidence source environment
      before id reason after token mapping world store := by
  obtain ⟨origin, path, native, associated⟩ := post
  exact ⟨origin, .indexBase header keyFound form sourceType failed path, native, associated⟩

theorem index_key {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {id base key : ExpressionId} {node baseNode keyNode : ExpressionNode} {layout : Core.OrderedMapping.Layout}
    {comparison : SourceCoreCompatibleDataEquality.Prepared values.checked} {first second : SourceCoreBasic.LoweredExpr}
    (header : CompatibleExpressionIndices.Header values source id base node baseNode layout comparison first second)
    (keyFound : source.lookupExpression? key = some keyNode) (form : node.form = .index base key)
    (sourceType : baseNode.type = .mapping keyNode.type node.type)
    {ambient : AmbientDefinitions values.checked.catalog.definitions} {functions : FunctionModel values.checked.catalog ambient}
    {registry : SourceCoreRawMetadata.Registry} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment} {before middle after : Dynamic.Heap}
    {baseSource : Dynamic.Value} {reason : Dynamic.SemanticFault} {token : Word}
    {mapping : LocationMap} {world : StoreTyping} {store : Store}
    (baseTrace : Dynamic.ExpressionEvaluates program context evidence source environment before base baseSource middle)
    (failed : Dynamic.ExpressionFaults program context evidence source environment middle key reason after)
    (post : model_expressionPost values.checked functions registry program context evidence source environment
      middle key reason after token mapping world store) :
    model_expressionPost values.checked functions registry program context evidence source environment
      before id reason after token mapping world store := by
  obtain ⟨origin, path, native, associated⟩ := post
  exact ⟨origin, .indexKey header keyFound form sourceType baseTrace failed path, native, associated⟩

end Solcore.SourceSemantics.CoreLowering.ReachedExpressionExtendedFaultPaths
