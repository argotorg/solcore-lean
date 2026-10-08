import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReadFaultPolicies
import Solcore.SourceSemantics.CoreLowering.CompatibleMappingView
import Solcore.SourceSemantics.CoreLowering.ExpressionFailurePostContracts

/-! The initial concrete sum covers ordinary local
reads and unavailable mapping indices. Later fault families require actual
producer extensions. These packets define no evaluation traversal. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ReachedExpressionFaultOrigins
open Core Frontend SourceInference GeneralHeap CompatiblePayload

/-- The certificate and witness refer to this exact current Source read. -/
structure ReadLeaf where
  program : Program
  context : SourceSemantics.Context
  evidence : Dynamic.EvidenceEnvironment
  source : TypedSource
  environment : Dynamic.Environment
  heap : Dynamic.Heap
  fuel : Nat
  values : SourceCoreCompatibleValues.Context
  scope : SourceCoreLocalCell.Scope
  id : ExpressionId
  reason : Word
  code : Expr
  certificate : CompatibleExpressionReads.Certificate fuel values source scope id reason code
  location : Dynamic.Location
  cell : Dynamic.Cell
  witness : CompatibleExpressionReads.UninitializedWitness certificate context environment heap location cell
  fault : Dynamic.ExpressionFaults program context evidence source environment heap id
    (.uninitializedLocation location) heap

/-- Actual Source index occurrence and raw unavailable mapping fields.
The upper finite converter supplies these from its own Header and MissingWitness.
This packet does not reconstruct that Header or a prepare association. -/
structure IndexLeaf where
  checked : SourceCoreCompatibleCatalog.Checked
  registry : SourceCoreRawMetadata.Registry
  ambient : AmbientDefinitions checked.catalog.definitions
  functions : FunctionModel checked.catalog ambient
  mapping : LocationMap
  world : StoreTyping
  program : Program
  context : SourceSemantics.Context
  evidence : Dynamic.EvidenceEnvironment
  source : TypedSource
  environment : Dynamic.Environment
  before : Dynamic.Heap
  middle : Dynamic.Heap
  heap : Dynamic.Heap
  id : ExpressionId
  base : ExpressionId
  key : ExpressionId
  node : ExpressionNode
  baseNode : ExpressionNode
  keyNode : ExpressionNode
  contains : ContainsExpression source id node
  baseContains : ContainsExpression source base baseNode
  keyFound : source.lookupExpression? key = some keyNode
  form : node.form = .index base key
  sourceType : baseNode.type = .mapping keyNode.type node.type
  baseSource : Dynamic.Value
  keySource : Dynamic.Value
  baseValue : Value
  rawKey : TypeSystem.Ty
  rawValue : TypeSystem.Ty
  sources : List (Dynamic.Value × Dynamic.Value)
  baseShape : baseSource = .mapping rawKey rawValue sources
  keyView : SourceCoreRawMetadata.runtimeType keyNode.type = SourceCoreRawMetadata.runtimeType rawKey
  valueView : SourceCoreRawMetadata.runtimeType node.type = SourceCoreRawMetadata.runtimeType rawValue
  tag : Word
  layout : Core.OrderedMapping.Layout
  entries : Core.OrderedMapping.Entries
  fallback : Option Value
  nativeShape : baseValue = SourceCoreMappingWithDefault.value tag fallback layout entries
  fields : CompatibleMapping.Fields checked registry functions mapping world rawKey rawValue
    sources tag layout entries fallback
  keyTyped : Dynamic.ValueRuntimeTypeMatches keySource rawKey
  absent : Dynamic.MappingAbsent keySource sources
  unavailable : ¬ Dynamic.Defaultable rawValue
  baseTrace : Dynamic.ExpressionEvaluates program context evidence source environment
    before base baseSource middle
  keyTrace : Dynamic.ExpressionEvaluates program context evidence source environment
    middle key keySource heap
  reason : Word
  fault : Dynamic.ExpressionFaults program context evidence source environment before id
    (.missingMappingDefault rawValue) heap

/-- No arbitrary predicate branch stands in for an actual primitive origin. -/
inductive PrimitiveOrigin : Dynamic.Heap → Dynamic.SemanticFault → Word → Type where
  | read (leaf : ReadLeaf) : PrimitiveOrigin leaf.heap (.uninitializedLocation leaf.location) leaf.reason
  | index (leaf : IndexLeaf) : PrimitiveOrigin leaf.heap (.missingMappingDefault leaf.rawValue)
      (leaf.reason.add leaf.tag)

/- The leaf packet is an index. Each join keeps its exact final Source heap.
Only the first sequence/composition seam is represented here; later original
semantic branches add their own concrete constructors. -/
mutual
  inductive ExpressionPath : {heap : Dynamic.Heap} → {reason : Dynamic.SemanticFault} → {token : Word} →
      PrimitiveOrigin heap reason token → Program → SourceSemantics.Context → Dynamic.EvidenceEnvironment →
      TypedSource → Dynamic.Environment → Dynamic.Heap → ExpressionId → Prop where
    | read (leaf : ReadLeaf) : ExpressionPath (.read leaf) leaf.program leaf.context leaf.evidence
        leaf.source leaf.environment leaf.heap leaf.id
    | index (leaf : IndexLeaf) : ExpressionPath (.index leaf) leaf.program leaf.context leaf.evidence
        leaf.source leaf.environment leaf.before leaf.id
    | expression {heap : Dynamic.Heap} {reason : Dynamic.SemanticFault} {token : Word}
        {origin : PrimitiveOrigin heap reason token} {program : Program} {context : SourceSemantics.Context}
        {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
        {before middle : Dynamic.Heap} {id childId : ExpressionId}
        (link : ExpressionFailurePostContracts.ExpressionLink program context evidence source environment
          before id middle childId)
        (child : ExpressionPath origin program context evidence source environment middle childId) :
        ExpressionPath origin program context evidence source environment before id
    | expressions {heap : Dynamic.Heap} {reason : Dynamic.SemanticFault} {token : Word}
        {origin : PrimitiveOrigin heap reason token} {program : Program} {context : SourceSemantics.Context}
        {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
        {before : Dynamic.Heap} {id : ExpressionId} {ids : List ExpressionId}
        (link : ExpressionFailurePostContracts.ExpressionsLink source id ids)
        (children : ExpressionsPath origin program context evidence source environment before ids) :
        ExpressionPath origin program context evidence source environment before id

  inductive ExpressionsPath : {heap : Dynamic.Heap} → {reason : Dynamic.SemanticFault} → {token : Word} →
      PrimitiveOrigin heap reason token → Program → SourceSemantics.Context → Dynamic.EvidenceEnvironment →
      TypedSource → Dynamic.Environment → Dynamic.Heap → List ExpressionId → Prop where
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

/-- Raw headers and compatible field views use only real retained registry,
map and world extensions. The restored native store is a separate result index. -/
def NativeTransport {heap : Dynamic.Heap} {reason : Dynamic.SemanticFault} {token : Word}
    (origin : PrimitiveOrigin heap reason token) (registry : SourceCoreRawMetadata.Registry)
    (mapping : LocationMap) (world : StoreTyping) : Prop :=
  match origin with
  | .read leaf => SourceCoreRawMetadata.Extends leaf.values.registry registry
  | .index leaf => SourceCoreRawMetadata.Extends leaf.registry registry ∧
      LocationMap.Extends leaf.mapping mapping ∧ WorldExtends leaf.world world

/-- The final Source heap is the very heap indexing the selected leaf. The
actual native Store belongs to the original full result tuple and is not equated
with a leaf store or with the Source heap. -/
def expressionPost (registry : SourceCoreRawMetadata.Registry) :
    ExpressionFailurePostContracts.ExpressionFaultPost :=
  fun program context evidence source environment before id reason after token mapping world _store =>
    ∃ origin : PrimitiveOrigin after reason token,
      ExpressionPath origin program context evidence source environment before id ∧
      NativeTransport origin registry mapping world

def expressionsPost (registry : SourceCoreRawMetadata.Registry) :
    ExpressionFailurePostContracts.ExpressionsFaultPost :=
  fun program context evidence source environment before ids reason after token mapping world _store =>
    ∃ origin : PrimitiveOrigin after reason token,
      ExpressionsPath origin program context evidence source environment before ids ∧
      NativeTransport origin registry mapping world

/-- The actual Source list constructor is appended once to the same child packet. -/
theorem sequence_joins (registry : SourceCoreRawMetadata.Registry)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) :
    ExpressionFailurePostContracts.SequenceJoins (expressionPost registry) (expressionsPost registry)
      program context evidence source where
  head := by
    intro environment before id ids reason after token mapping world store _failed post
    obtain ⟨origin, path, native⟩ := post
    exact ⟨origin, .head path, native⟩
  tail := by
    intro environment before middle id ids value reason after token mapping world store firstSource _failed post
    obtain ⟨origin, path, native⟩ := post
    exact ⟨origin, .tail firstSource path, native⟩

/-- The actual Source expression join is appended once, without finding a leaf
or traversing a Source/native execution. -/
theorem composition_joins (registry : SourceCoreRawMetadata.Registry)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) :
    ExpressionFailurePostContracts.CompositionJoins (expressionPost registry) (expressionsPost registry)
      program context evidence source where
  expression := by
    intro environment before id middle child reason after token mapping world store link _failed post
    obtain ⟨origin, path, native⟩ := post
    exact ⟨origin, .expression link path, native⟩
  expressions := by
    intro environment before id ids reason after token mapping world store link _failed post
    obtain ⟨origin, path, native⟩ := post
    exact ⟨origin, .expressions link path, native⟩

end Solcore.SourceSemantics.CoreLowering.ReachedExpressionFaultOrigins
