import Solcore.SourceSemantics.CoreLowering.ScalarMemberFaultPostContracts
import Solcore.SourceSemantics.CoreLowering.IndexFaultPostContracts

/-! A scalar path carries the same primitive packet through authentic parent
receipts. Ordinary links are reused; no Source or native trace is traversed. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ReachedScalarExpressionFaultPaths
open Core Frontend SourceInference GeneralHeap CompatiblePayload ExpressionFailurePostContracts
open ReachedExpressionFaultOrigins (PrimitiveOrigin NativeTransport)
open ReachedExpressionPrimitiveOutcomeProviders (ModelAssociation)

inductive IndexParentLink (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (environment : Dynamic.Environment) :
    Dynamic.Heap → ExpressionId → Dynamic.Heap → ExpressionId → Prop where
  | base {values : SourceCoreCompatibleValues.Context} {id base key : ExpressionId}
      {node baseNode keyNode : ExpressionNode} {layout : Core.OrderedMapping.Layout}
      {comparison : SourceCoreCompatibleDataEquality.Prepared values.checked} {first second : SourceCoreBasic.LoweredExpr}
      {before : Dynamic.Heap}
      (header : CompatibleExpressionIndices.Header values source id base node baseNode layout comparison first second)
      (keyFound : source.lookupExpression? key = some keyNode) (form : node.form = .index base key)
      (sourceType : baseNode.type = .mapping keyNode.type node.type) :
      IndexParentLink program context evidence source environment before id before base
  | key {values : SourceCoreCompatibleValues.Context} {id base key : ExpressionId}
      {node baseNode keyNode : ExpressionNode} {layout : Core.OrderedMapping.Layout}
      {comparison : SourceCoreCompatibleDataEquality.Prepared values.checked} {first second : SourceCoreBasic.LoweredExpr}
      {before middle : Dynamic.Heap} {baseSource : Dynamic.Value}
      (header : CompatibleExpressionIndices.Header values source id base node baseNode layout comparison first second)
      (keyFound : source.lookupExpression? key = some keyNode) (form : node.form = .index base key)
      (sourceType : baseNode.type = .mapping keyNode.type node.type)
      (baseTrace : Dynamic.ExpressionEvaluates program context evidence source environment before base baseSource middle) :
      IndexParentLink program context evidence source environment before id middle key

mutual
  inductive ExpressionPath : {heap : Dynamic.Heap} → {reason : Dynamic.SemanticFault} → {token : Word} →
      PrimitiveOrigin heap reason token → Program → SourceSemantics.Context → Dynamic.EvidenceEnvironment →
      TypedSource → Dynamic.Environment → Dynamic.Heap → ExpressionId → Prop where
    | prior {heap : Dynamic.Heap} {reason : Dynamic.SemanticFault} {token : Word}
        {origin : PrimitiveOrigin heap reason token} {program : Program} {context : SourceSemantics.Context}
        {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
        {before : Dynamic.Heap} {id : ExpressionId}
        (path : ReachedExpressionExtendedFaultPaths.ExpressionPath origin program context evidence source environment before id) :
        ExpressionPath origin program context evidence source environment before id
    | indexSelected {heap : Dynamic.Heap} {reason : Dynamic.SemanticFault} {token : Word}
        {origin : PrimitiveOrigin heap reason token} {program : Program} {context : SourceSemantics.Context}
        {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
        {before middle : Dynamic.Heap} {id childId : ExpressionId}
        (link : IndexParentLink program context evidence source environment before id middle childId)
        (failed : Dynamic.ExpressionFaults program context evidence source environment middle childId reason heap)
        (child : ExpressionPath origin program context evidence source environment middle childId) :
        ExpressionPath origin program context evidence source environment before id
    | constructorArguments {heap : Dynamic.Heap} {reason : Dynamic.SemanticFault} {token : Word}
        {origin : PrimitiveOrigin heap reason token} {program : Program} {context : SourceSemantics.Context}
        {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
        {before : Dynamic.Heap} {values : SourceCoreCompatibleValues.Context}
        {id : ExpressionId} {node : ExpressionNode} {instantiation : DataConstructorInstantiation}
        {ids : List ExpressionId} {tag : ConstructorId} {header : Word} {codes : List SourceCoreBasic.LoweredExpr}
        (receipt : CompatibleExpressionConstructors.Header values source id node instantiation tag header codes)
        (form : node.form = .constructor instantiation ids)
        (valid : SourceSemantics.DataConstructorInstantiation.Valid context instantiation)
        (count : ids.length = instantiation.payloadTypes.length)
        (nodes : CompatibleExpressionConstructors.Nodes source ids instantiation.payloadTypes codes)
        (failed : Dynamic.ExpressionsFault program context evidence source environment before ids reason heap)
        (children : ExpressionsPath origin program context evidence source environment before ids) :
        ExpressionPath origin program context evidence source environment before id
    | memberBase {heap : Dynamic.Heap} {reason : Dynamic.SemanticFault} {token : Word}
        {origin : PrimitiveOrigin heap reason token} {program : Program} {context : SourceSemantics.Context}
        {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
        {before : Dynamic.Heap} {values : SourceCoreCompatibleValues.Context}
        {id base : ExpressionId} {node baseNode : ExpressionNode} {name : String} {index : Nat}
        {identity : DataTypeId} {branches : List Expr} {result childType : Ty}
        (metadata : CompatibleExpressionReads.Metadata values.checked source id node result)
        (baseMetadata : CompatibleExpressionReads.Metadata values.checked source base baseNode childType)
        (form : node.form = .member base name index)
        (layout : CompatibleExpressionMembers.Layout values.checked (.occurrence id.occurrence)
          baseNode.type node.type index identity branches result)
        (failed : Dynamic.ExpressionFaults program context evidence source environment before base reason heap)
        (child : ExpressionPath origin program context evidence source environment before base) :
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
        (path : ReachedExpressionExtendedFaultPaths.ExpressionsPath origin program context evidence source environment before ids) :
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
    (post : ReachedExpressionExtendedFaultPaths.model_expressionPost checked functions registry program context
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
    (post : OutcomePost (ReachedExpressionExtendedFaultPaths.model_expressionPost checked functions registry)
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

theorem constructor_joins (values : SourceCoreCompatibleValues.Context)
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) (registry : SourceCoreRawMetadata.Registry)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) :
    ScalarConstructorFaultPostContracts.Joins (model_expressionPost values.checked functions registry)
      (model_expressionsPost values.checked functions registry) values program context evidence source where
  arguments := by
    intro id node instantiation ids tag header codes environment before reason after token mapping world store
      receipt form valid count nodes failed post
    obtain ⟨origin, path, native, associated⟩ := post
    exact ⟨origin, .constructorArguments receipt form valid count nodes failed path, native, associated⟩

theorem member_joins (values : SourceCoreCompatibleValues.Context)
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) (registry : SourceCoreRawMetadata.Registry)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) :
    ScalarMemberFaultPostContracts.Joins (model_expressionPost values.checked functions registry)
      values program context evidence source where
  base := by
    intro id node child childNode name index identity branches result childType
      environment before reason after token mapping world store metadata baseMetadata form layout failed post
    obtain ⟨origin, path, native, associated⟩ := post
    exact ⟨origin, .memberBase metadata baseMetadata form layout failed path, native, associated⟩

theorem index_joins (values : SourceCoreCompatibleValues.Context)
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) (registry : SourceCoreRawMetadata.Registry)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) :
    IndexFaultPostContracts.IndexJoins (model_expressionPost values.checked functions registry)
      values program context evidence source where
  base := by
    intro id base key node baseNode keyNode layout comparison first second header keyFound form sourceType
      environment before after reason token mapping world store failed post
    obtain ⟨origin, path, native, associated⟩ := post
    exact ⟨origin, .indexSelected (.base header keyFound form sourceType) failed path, native, associated⟩
  key := by
    intro id base key node baseNode keyNode layout comparison first second header keyFound form sourceType
      environment before middle after baseSource reason token mapping world store baseTrace failed post
    obtain ⟨origin, path, native, associated⟩ := post
    exact ⟨origin, .indexSelected (.key header keyFound form sourceType baseTrace) failed path, native, associated⟩

end Solcore.SourceSemantics.CoreLowering.ReachedScalarExpressionFaultPaths
