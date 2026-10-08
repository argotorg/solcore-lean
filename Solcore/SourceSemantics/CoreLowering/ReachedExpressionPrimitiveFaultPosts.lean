import Solcore.SourceSemantics.CoreLowering.ReachedExpressionFaultOrigins
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionIndexFaultPolicies

/-! Finite converters retain the actual primitive read or index witness.
The owning Source trace and key occurrence remain authentic inputs. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ReachedExpressionPrimitiveFaultPosts
open Core Frontend SourceInference GeneralHeap CompatiblePayload
open ReachedExpressionFaultOrigins

/-- A read leaf keeps this exact certificate, lexical cell and Source fault. -/
def read_leaf {fuel : Nat} {values : SourceCoreCompatibleValues.Context}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {reason : Word} {code : Expr}
    (certificate : CompatibleExpressionReads.Certificate fuel values source scope id reason code)
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {location : Dynamic.Location} {cell : Dynamic.Cell}
    (witness : CompatibleExpressionReads.UninitializedWitness certificate context environment heap location cell)
    (failed : Dynamic.ExpressionFaults program context evidence source environment heap id
      (.uninitializedLocation location) heap) : ReadLeaf where
  program := program
  context := context
  evidence := evidence
  source := source
  environment := environment
  heap := heap
  fuel := fuel
  values := values
  scope := scope
  id := id
  reason := reason
  code := code
  certificate := certificate
  location := location
  cell := cell
  witness := witness
  fault := failed

/-- The current represented mapping supplies every raw field; the upper
index constructor supplies its own exact key and ordered Source traces. -/
def index_leaf {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {id base key : ExpressionId} {node baseNode keyNode : ExpressionNode}
    {layout : Core.OrderedMapping.Layout}
    {comparison : SourceCoreCompatibleDataEquality.Prepared values.checked}
    {first second : SourceCoreBasic.LoweredExpr}
    (header : CompatibleExpressionIndices.Header values source id base node baseNode layout comparison first second)
    {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient)
    {mapping : LocationMap} {world : StoreTyping}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before middle after : Dynamic.Heap}
    {baseSource keySource : Dynamic.Value} {baseValue : Value}
    {rawKey rawValue : TypeSystem.Ty} {sources : List (Dynamic.Value × Dynamic.Value)}
    {tag reason : Word} {entries : Core.OrderedMapping.Entries} {fallback : Option Value}
    (witness : CompatibleExpressionIndices.MissingWitness (keyNode := keyNode) (registry := registry)
      header functions mapping world baseSource keySource baseValue rawKey rawValue sources tag entries fallback)
    (keyFound : source.lookupExpression? key = some keyNode)
    (form : node.form = .index base key)
    (baseTrace : Dynamic.ExpressionEvaluates program context evidence source environment before base baseSource middle)
    (keyTrace : Dynamic.ExpressionEvaluates program context evidence source environment middle key keySource after)
    (failed : Dynamic.ExpressionFaults program context evidence source environment before id
      (.missingMappingDefault rawValue) after) : IndexLeaf where
  checked := values.checked
  registry := registry
  ambient := ambient
  functions := functions
  mapping := mapping
  world := world
  program := program
  context := context
  evidence := evidence
  source := source
  environment := environment
  before := before
  middle := middle
  heap := after
  id := id
  base := base
  key := key
  node := node
  baseNode := baseNode
  keyNode := keyNode
  contains := witness.contains
  baseContains := witness.baseContains
  keyFound := keyFound
  form := form
  sourceType := witness.sourceType
  baseSource := baseSource
  keySource := keySource
  baseValue := baseValue
  rawKey := rawKey
  rawValue := rawValue
  sources := sources
  baseShape := witness.baseShape
  keyView := witness.keyView
  valueView := witness.valueView
  tag := tag
  layout := layout
  entries := entries
  fallback := fallback
  nativeShape := witness.nativeShape
  fields := witness.fields
  keyTyped := witness.keyTyped
  absent := witness.absent
  unavailable := witness.unavailable
  baseTrace := baseTrace
  keyTrace := keyTrace
  reason := reason
  fault := failed

/-- Only real registry extension transports the selected read leaf. -/
theorem read_post (leaf : ReadLeaf) {registry : SourceCoreRawMetadata.Registry}
    {mapping : LocationMap} {world : StoreTyping} {store : Store}
    (extended : SourceCoreRawMetadata.Extends leaf.values.registry registry) :
    expressionPost registry leaf.program leaf.context leaf.evidence leaf.source leaf.environment
      leaf.heap leaf.id (.uninitializedLocation leaf.location) leaf.heap leaf.reason mapping world store :=
  ⟨.read leaf, .read leaf, extended⟩

/-- The actual unavailable index keeps the same raw header and fields under
real registry, location-map and store-world extension. -/
theorem index_post (leaf : IndexLeaf) {registry : SourceCoreRawMetadata.Registry}
    {mapping : LocationMap} {world : StoreTyping} {store : Store}
    (registered : SourceCoreRawMetadata.Extends leaf.registry registry)
    (maps : LocationMap.Extends leaf.mapping mapping) (worlds : WorldExtends leaf.world world) :
    expressionPost registry leaf.program leaf.context leaf.evidence leaf.source leaf.environment
      leaf.before leaf.id (.missingMappingDefault leaf.rawValue) leaf.heap
      (leaf.reason.add leaf.tag) mapping world store :=
  ⟨.index leaf, .index leaf, registered, maps, worlds⟩

end Solcore.SourceSemantics.CoreLowering.ReachedExpressionPrimitiveFaultPosts
