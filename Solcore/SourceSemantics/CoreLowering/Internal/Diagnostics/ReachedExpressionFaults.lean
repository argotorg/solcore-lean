import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionReads
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.MappingsAndEquality
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.BasicExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionIndices
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.Statements
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.FunctionCalls
import Solcore.SourceSemantics.Dynamic.Fault
import Solcore.Frontend.SourceCore.Internal.FaultSites

/-!
# Reached expression faults

Fault origins and paths of reached expressions, outcome ports of reads and indices, and the fault table of assignment operands.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ReachedExpressionFaultOrigins
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ReachedExpressionPrimitiveFaultPosts
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ReachedExpressionPrimitiveOutcomeProviders
/-! Primitive fault posts come from the actual finite read or index terminal.
The existing diagnostic core selects its own witness. Public issuer and receiver
table association remain separate authentic inputs. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ReachedExpressionPrimitiveOutcomeProviders
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CompatibleMapping
open ExpressionFailurePostContracts ReachedExpressionFaultOrigins ReachedExpressionPrimitiveFaultPosts

/-- The actual raw mapping leaf uses this same checked catalog and function
model. Read leaves retain their actual checked context independently. -/
def ModelAssociation (checked : SourceCoreCompatibleCatalog.Checked)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient)
    {heap : Dynamic.Heap} {reason : Dynamic.SemanticFault} {token : Word}
    (origin : PrimitiveOrigin heap reason token) : Prop :=
  match origin with
  | .read leaf => leaf.values.checked = checked
  | .index leaf => leaf.checked = checked ∧ HEq leaf.ambient ambient ∧ HEq leaf.functions functions

/-- Model association belongs to this SAME existential origin and path. -/
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

theorem model_expressionPost_forget {checked : SourceCoreCompatibleCatalog.Checked}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {registry : SourceCoreRawMetadata.Registry}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : ExpressionId} {reason : Dynamic.SemanticFault} {token : Word}
    {mapping : LocationMap} {world : StoreTyping} {store : Store}
    (post : model_expressionPost checked functions registry program context evidence source environment
      before id reason after token mapping world store) :
    expressionPost registry program context evidence source environment before id reason after token mapping world store := by
  obtain ⟨origin, path, native, _associated⟩ := post
  exact ⟨origin, path, native⟩

theorem model_expressionsPost_forget {checked : SourceCoreCompatibleCatalog.Checked}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {registry : SourceCoreRawMetadata.Registry}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {ids : List ExpressionId} {reason : Dynamic.SemanticFault} {token : Word}
    {mapping : LocationMap} {world : StoreTyping} {store : Store}
    (post : model_expressionsPost checked functions registry program context evidence source environment
      before ids reason after token mapping world store) :
    expressionsPost registry program context evidence source environment before ids reason after token mapping world store := by
  obtain ⟨origin, path, native, _associated⟩ := post
  exact ⟨origin, path, native⟩

theorem model_sequence_joins (checked : SourceCoreCompatibleCatalog.Checked)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) (registry : SourceCoreRawMetadata.Registry)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) :
    SequenceJoins (model_expressionPost checked functions registry)
      (model_expressionsPost checked functions registry) program context evidence source where
  head := by
    intro environment before id ids reason after token mapping world store _failed post
    obtain ⟨origin, path, native, associated⟩ := post
    exact ⟨origin, .head path, native, associated⟩
  tail := by
    intro environment before middle id ids value reason after token mapping world store firstSource _failed post
    obtain ⟨origin, path, native, associated⟩ := post
    exact ⟨origin, .tail firstSource path, native, associated⟩

theorem model_composition_joins (checked : SourceCoreCompatibleCatalog.Checked)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) (registry : SourceCoreRawMetadata.Registry)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) :
    CompositionJoins (model_expressionPost checked functions registry)
      (model_expressionsPost checked functions registry) program context evidence source where
  expression := by
    intro environment before id middle child reason after token mapping world store link _failed post
    obtain ⟨origin, path, native, associated⟩ := post
    exact ⟨origin, .expression link path, native, associated⟩
  expressions := by
    intro environment before id ids reason after token mapping world store link _failed post
    obtain ⟨origin, path, native, associated⟩ := post
    exact ⟨origin, .expressions link path, native, associated⟩

private theorem original_result {catalog : SourceCoreDataCatalog.Catalog}
    {projects : GenericHeap.Projection} {definitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects definitions}
    {mapping : LocationMap} {world : StoreTyping} {sourceType : TypeSystem.Ty} {type : Ty}
    {faults retained : FunctionCalls.FaultRep} {outcome : Dynamic.ExpressionOutcome} {result : Value}
    (forget : ∀ reason token, retained reason token → faults reason token)
    (represented : FunctionCalls.ResultRepresents model mapping world sourceType type retained outcome result) :
    FunctionCalls.ResultRepresents model mapping world sourceType type faults outcome result := by
  cases represented with
  | value value => exact .value value
  | fault fault => exact .fault (forget _ _ fault)

private def ReadLift {fuel : Nat} {values : SourceCoreCompatibleValues.Context}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {reason : Word} {code : Expr}
    (certificate : CompatibleExpressionReads.Certificate fuel values source scope id reason code)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment) (heap : Dynamic.Heap)
    (faults : FunctionCalls.FaultRep) : FunctionCalls.FaultRep :=
  fun fault token => faults fault token ∧ ∃ location cell,
    CompatibleExpressionReads.UninitializedWitness certificate context environment heap location cell ∧
    fault = .uninitializedLocation location ∧ token = reason

private theorem read_lift {fuel : Nat} {values : SourceCoreCompatibleValues.Context}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {reason : Word} {code : Expr}
    (certificate : CompatibleExpressionReads.Certificate fuel values source scope id reason code)
    {context : SourceSemantics.Context} {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {faults : FunctionCalls.FaultRep}
    (uninitialized : CompatibleExpressionReads.UninitializedPolicy certificate context environment heap faults) :
    CompatibleExpressionReads.UninitializedPolicy certificate context environment heap
      (ReadLift certificate context environment heap faults) := by
  intro location cell witness
  exact ⟨uninitialized location cell witness, location, cell, witness, rfl, rfl⟩

private theorem read_fault {fuel : Nat} {values : SourceCoreCompatibleValues.Context}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {reason : Word} {code : Expr}
    (certificate : CompatibleExpressionReads.Certificate fuel values source scope id reason code)
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {location : Dynamic.Location} {cell : Dynamic.Cell}
    (witness : CompatibleExpressionReads.UninitializedWitness certificate context environment heap location cell) :
    Dynamic.ExpressionFaults program context evidence source environment heap id
      (.uninitializedLocation location) heap := by
  apply Dynamic.ExpressionFaults.form witness.contains
  rw [witness.localReference, certificate.metadata.requirements, certificate.metadata.coercions]
  exact .localUninitialized (owned := []) rfl witness.lookup witness.read
    witness.ordinary witness.empty witness.notMapping

private theorem read_outcome_post {fuel : Nat} {values : SourceCoreCompatibleValues.Context}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {reason : Word} {code : Expr}
    (certificate : CompatibleExpressionReads.Certificate fuel values source scope id reason code)
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    {functions : FunctionModel values.checked.catalog ambient} {registry : SourceCoreRawMetadata.Registry}
    (extension : SourceCoreRawMetadata.Extends values.registry registry)
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {mapping : LocationMap} {world : StoreTyping} {store : Store}
    {faults : FunctionCalls.FaultRep} {outcome : Dynamic.ExpressionOutcome} {result : Value}
    (unique : NodeOccurrencesUnique source)
    (trace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after)
    (represented : FunctionCalls.ResultRepresents
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) mapping world
      certificate.node.type certificate.type (ReadLift certificate context environment before faults) outcome result) :
    OutcomePost (model_expressionPost values.checked functions registry) program context evidence source environment before id
      certificate.type outcome after result mapping world store := by
  cases represented with
  | value value => exact True.intro
  | fault retained =>
    obtain ⟨_original, location, cell, witness, rfl, rfl⟩ := retained
    have failed := read_fault (program := program) (evidence := evidence) certificate witness
    obtain ⟨_sameOutcome, sameHeap⟩ := CompatibleExpressionReads.source_outcome_unique unique
      witness.contains witness.localReference certificate.metadata.coercions witness.lookup witness.read
      witness.ordinary (.fault failed) trace
    cases sameHeap
    let leaf := read_leaf certificate witness failed
    exact ⟨leaf.reason, rfl, .read leaf, .read leaf, extension, rfl⟩

open CompatibleExpressionReads

theorem read_evaluates {fuel : Nat} {context : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {scope : Scope} {id : ExpressionId} {reason : Word} {code : Expr}
    (certificate : Certificate fuel context source scope id reason code)
    {ambient : AmbientDefinitions context.checked.catalog.definitions}
    (functions : FunctionModel context.checked.catalog ambient)
    {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends context.registry registry)
    (program : Program) (sourceContext : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (binding : StaticBinding certificate sourceContext)
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {heap : Dynamic.Heap} {store : Store} {ξ : Renaming}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog context.checked.catalog) mapping world
      administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents context.checked registry functions mapping world heap store)
    (locals : Dynamic.EnvironmentAgrees heap sourceContext.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (unique : NodeOccurrencesUnique source)
    {faults : FunctionCalls.FaultRep} (uninitialized : UninitializedPolicy certificate sourceContext environment heap faults) :
    ∃ outcome after value finalStore,
      Dynamic.ExpressionEvaluatesOutcome program sourceContext evidence source environment heap id outcome after ∧
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel context.checked registry functions)
        mapping world certificate.node.type certificate.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents context.checked registry functions mapping world after finalStore ∧
      AdministrativePreserved mapping store mapping finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
      OutcomePost (model_expressionPost context.checked functions registry) program sourceContext evidence source environment heap id
        certificate.type outcome after value mapping world finalStore := by
  obtain ⟨outcome, after, value, finalStore, trace, evaluated, represented, finalHeaps, frame, metadata⟩ :=
    certificate.evaluates_with_diagnostics functions extension program sourceContext evidence binding
      environments heaps locals agrees (read_lift certificate uninitialized)
  exact ⟨outcome, after, value, finalStore, trace, evaluated,
    original_result (fun _ _ retained => retained.1) represented, finalHeaps, frame, metadata,
    read_outcome_post certificate extension unique trace represented⟩

theorem read_completed {fuel : Nat} {context : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {scope : Scope} {id : ExpressionId} {reason : Word} {code : Expr}
    (certificate : Certificate fuel context source scope id reason code)
    {ambient : AmbientDefinitions context.checked.catalog.definitions}
    (functions : FunctionModel context.checked.catalog ambient)
    {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends context.registry registry)
    (program : Program) (sourceContext : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (binding : StaticBinding certificate sourceContext)
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {heap : Dynamic.Heap} {store : Store} {ξ : Renaming}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog context.checked.catalog) mapping world
      administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents context.checked registry functions mapping world heap store)
    (locals : Dynamic.EnvironmentAgrees heap sourceContext.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (unique : NodeOccurrencesUnique source)
    {faults : FunctionCalls.FaultRep} (uninitialized : UninitializedPolicy certificate sourceContext environment heap faults)
    {value : Value} {finalStore : Store} (evaluation : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ outcome after,
      Dynamic.ExpressionEvaluatesOutcome program sourceContext evidence source environment heap id outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel context.checked registry functions)
        mapping world certificate.node.type certificate.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents context.checked registry functions mapping world after finalStore ∧
      AdministrativePreserved mapping store mapping finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
      OutcomePost (model_expressionPost context.checked functions registry) program sourceContext evidence source environment heap id
        certificate.type outcome after value mapping world finalStore := by
  obtain ⟨outcome, after, trace, represented, finalHeaps, frame, metadata⟩ :=
    certificate.completed_with_diagnostics functions extension program sourceContext evidence binding
      environments heaps locals agrees (read_lift certificate uninitialized) evaluation
  exact ⟨outcome, after, trace, original_result (fun _ _ retained => retained.1) represented,
    finalHeaps, frame, metadata, read_outcome_post certificate extension unique trace represented⟩

theorem read_preserves {fuel : Nat} {context : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {scope : Scope} {id : ExpressionId} {reason : Word} {code : Expr}
    (certificate : Certificate fuel context source scope id reason code)
    {ambient : AmbientDefinitions context.checked.catalog.definitions}
    (functions : FunctionModel context.checked.catalog ambient)
    {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends context.registry registry)
    (program : Program) (sourceContext : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (binding : StaticBinding certificate sourceContext)
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {heap : Dynamic.Heap} {store : Store} {ξ : Renaming}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog context.checked.catalog) mapping world
      administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents context.checked registry functions mapping world heap store)
    (locals : Dynamic.EnvironmentAgrees heap sourceContext.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    {faults : FunctionCalls.FaultRep} (uninitialized : UninitializedPolicy certificate sourceContext environment heap faults)
    (unique : NodeOccurrencesUnique source)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : Dynamic.ExpressionEvaluatesOutcome program sourceContext evidence source environment heap id outcome after) :
    ∃ value finalStore,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel context.checked registry functions)
        mapping world certificate.node.type certificate.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents context.checked registry functions mapping world after finalStore ∧
      AdministrativePreserved mapping store mapping finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
      OutcomePost (model_expressionPost context.checked functions registry) program sourceContext evidence source environment heap id
        certificate.type outcome after value mapping world finalStore := by
  obtain ⟨actualOutcome, actualHeap, value, finalStore, sourceTrace, evaluated, represented, finalHeaps,
    frame, metadata, post⟩ := read_evaluates certificate functions extension program sourceContext evidence
      binding environments heaps locals agrees unique uninitialized
  obtain ⟨location, cell, lookup, read, _, _⟩ := locals.lookup binding.declared
  obtain ⟨_, selected, _, _, _, selectedRead, _, cellRep⟩ :=
    GenericHeap.lookup_visible environments heaps lookup certificate.slot
  have sameCell := read.functional selectedRead
  subst selected
  obtain ⟨rfl, rfl⟩ := source_outcome_unique unique (lookupExpression?_sound certificate.metadata.found)
    certificate.form certificate.metadata.coercions lookup read cellRep.ordinary sourceTrace trace
  exact ⟨value, finalStore, evaluated, represented, finalHeaps, frame, metadata, post⟩


private def IndexLift {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {id base : ExpressionId} {node baseNode keyNode : ExpressionNode}
    {layout : Core.OrderedMapping.Layout}
    {comparison : SourceCoreCompatibleDataEquality.Prepared values.checked}
    {first second : SourceCoreBasic.LoweredExpr}
    (header : CompatibleExpressionIndices.Header values source id base node baseNode layout comparison first second)
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) (mapping : LocationMap) (world : StoreTyping)
    (baseSource keySource : Dynamic.Value) (baseValue : Value) (reason : Word)
    (faults : FunctionCalls.FaultRep) : FunctionCalls.FaultRep :=
  fun fault token => faults fault token ∧ ∃ rawKey rawValue sources tag entries fallback,
    CompatibleExpressionIndices.MissingWitness (keyNode := keyNode) (registry := registry)
      header functions mapping world baseSource keySource baseValue rawKey rawValue sources tag entries fallback ∧
    fault = .missingMappingDefault rawValue ∧ token = reason.add tag

private theorem index_lift {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {id base : ExpressionId} {node baseNode keyNode : ExpressionNode}
    {layout : Core.OrderedMapping.Layout}
    {comparison : SourceCoreCompatibleDataEquality.Prepared values.checked}
    {first second : SourceCoreBasic.LoweredExpr}
    (header : CompatibleExpressionIndices.Header values source id base node baseNode layout comparison first second)
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    {functions : FunctionModel values.checked.catalog ambient} {mapping : LocationMap} {world : StoreTyping}
    {baseSource keySource : Dynamic.Value} {baseValue : Value} {reason : Word}
    {faults : FunctionCalls.FaultRep}
    (missing : CompatibleExpressionIndices.MissingPolicy (keyNode := keyNode) (registry := registry)
      header functions mapping world baseSource keySource baseValue reason faults) :
    CompatibleExpressionIndices.MissingPolicy (keyNode := keyNode) (registry := registry)
      header functions mapping world baseSource keySource baseValue reason
      (IndexLift (keyNode := keyNode) (registry := registry) header functions mapping world baseSource keySource baseValue reason faults) := by
  intro rawKey rawValue sources tag entries fallback witness
  exact ⟨missing rawKey rawValue sources tag entries fallback witness,
    rawKey, rawValue, sources, tag, entries, fallback, witness, rfl, rfl⟩

private theorem index_outcome_post {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {id base key : ExpressionId} {node baseNode keyNode : ExpressionNode}
    {layout : Core.OrderedMapping.Layout}
    {comparison : SourceCoreCompatibleDataEquality.Prepared values.checked}
    {first second : SourceCoreBasic.LoweredExpr}
    (header : CompatibleExpressionIndices.Header values source id base node baseNode layout comparison first second)
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    {functions : FunctionModel values.checked.catalog ambient} {mapping : LocationMap} {world futureWorld : StoreTyping}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before middle after : Dynamic.Heap}
    {baseSource keySource : Dynamic.Value} {baseValue : Value} {reason : Word} {store : Store}
    {faults : FunctionCalls.FaultRep} {outcome : Dynamic.ExpressionOutcome} {result : Value}
    (keyFound : source.lookupExpression? key = some keyNode) (form : node.form = .index base key)
    (baseTrace : Dynamic.ExpressionEvaluates program context evidence source environment before base baseSource middle)
    (keyTrace : Dynamic.ExpressionEvaluates program context evidence source environment middle key keySource after)
    (trace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after)
    (worlds : WorldExtends world futureWorld)
    (represented : FunctionCalls.ResultRepresents
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) mapping futureWorld node.type layout.valueType
      (IndexLift (keyNode := keyNode) (registry := registry) header functions mapping world baseSource keySource baseValue reason faults)
      outcome result) :
    OutcomePost (model_expressionPost values.checked functions registry) program context evidence source environment before id
      layout.valueType outcome after result mapping futureWorld store := by
  cases represented with
  | value value => exact True.intro
  | fault retained =>
    obtain ⟨_original, rawKey, rawValue, sources, tag, entries, fallback, witness, rfl, rfl⟩ := retained
    cases trace with
    | fault failed =>
      let leaf := index_leaf (reason := reason) header functions witness keyFound form baseTrace keyTrace failed
      exact ⟨reason.add tag, rfl, .index leaf, .index leaf,
        ⟨.refl _, .refl _, worlds⟩, rfl, HEq.rfl, HEq.rfl⟩

open CompatibleExpressionIndices

theorem index_finish {values : SourceCoreCompatibleValues.Context} {source : TypedSource} {id base : ExpressionId}
    {key : ExpressionId} {node baseNode keyNode : ExpressionNode} {layout : Core.OrderedMapping.Layout}
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
    {program : Program} {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {sourceEnvironment : Dynamic.Environment} {before middle : Dynamic.Heap}
    (keyFound : source.lookupExpression? key = some keyNode) (form : node.form = .index base key)
    (baseTrace : Dynamic.ExpressionEvaluates program sourceContext evidence source sourceEnvironment before base baseSource middle)
    (keyTrace : Dynamic.ExpressionEvaluates program sourceContext evidence source sourceEnvironment middle key keySource heap)
    (reason : Word) {faults : FunctionCalls.FaultRep}
    (missing : MissingPolicy (keyNode := keyNode) (registry := registry) header functions mapping world
      baseSource keySource baseValue reason faults) :
    ∃ outcome result finalStore futureWorld,
      Terminal baseSource keySource outcome ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        mapping futureWorld node.type layout.valueType faults outcome result ∧
      Evaluates (keyValue :: baseValue :: environment) store
        (SourceCoreMappingWithDefault.lookup layout reason comparison.expression (.var 1) (.var 0)) result finalStore ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping futureWorld heap finalStore ∧
      WorldExtends world futureWorld ∧ AdministrativePreserved mapping store mapping finalStore ∧
      (∀ other, Terminal baseSource keySource other → other = outcome) ∧
      Dynamic.ExpressionEvaluatesOutcome program sourceContext evidence source sourceEnvironment before id outcome heap ∧
      OutcomePost (model_expressionPost values.checked functions registry) program sourceContext evidence source sourceEnvironment before id
        layout.valueType outcome heap result mapping futureWorld finalStore := by
  obtain ⟨outcome, result, finalStore, futureWorld, terminal, represented, evaluated, finalHeaps, worlds, frame, functional⟩ :=
    header.finish_with_diagnostics sourceType scalar baseRep keyRep environmentTyped heaps reason (index_lift header missing)
  have sourceTrace := index_intro header.metadata form (terminal.trace baseTrace keyTrace)
  exact ⟨outcome, result, finalStore, futureWorld, terminal,
    original_result (fun _ _ retained => retained.1) represented, evaluated, finalHeaps, worlds, frame, functional,
    sourceTrace, index_outcome_post header keyFound form baseTrace keyTrace sourceTrace worlds represented⟩

theorem general_index_finish {values : SourceCoreCompatibleValues.Context} {source : TypedSource} {id base : ExpressionId}
    {key : ExpressionId} {node baseNode keyNode : ExpressionNode} {layout : Core.OrderedMapping.Layout}
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
    {program : Program} {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {sourceEnvironment : Dynamic.Environment} {before middle : Dynamic.Heap}
    (keyFound : source.lookupExpression? key = some keyNode) (form : node.form = .index base key)
    (baseTrace : Dynamic.ExpressionEvaluates program sourceContext evidence source sourceEnvironment before base baseSource middle)
    (keyTrace : Dynamic.ExpressionEvaluates program sourceContext evidence source sourceEnvironment middle key keySource heap)
    (reason : Word) {faults : FunctionCalls.FaultRep}
    (missing : MissingPolicy (keyNode := keyNode) (registry := registry) header functions mapping world
      baseSource keySource baseValue reason faults) :
    ∃ outcome result finalStore futureWorld,
      Terminal baseSource keySource outcome ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        mapping futureWorld node.type layout.valueType faults outcome result ∧
      Evaluates (keyValue :: baseValue :: environment) store
        (SourceCoreMappingWithDefault.lookup layout reason comparison.expression (.var 1) (.var 0)) result finalStore ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping futureWorld heap finalStore ∧
      WorldExtends world futureWorld ∧ AdministrativePreserved mapping store mapping finalStore ∧
      (∀ other, Terminal baseSource keySource other → other = outcome) ∧
      Dynamic.ExpressionEvaluatesOutcome program sourceContext evidence source sourceEnvironment before id outcome heap ∧
      OutcomePost (model_expressionPost values.checked functions registry) program sourceContext evidence source sourceEnvironment before id
        layout.valueType outcome heap result mapping futureWorld finalStore := by
  obtain ⟨outcome, result, finalStore, futureWorld, terminal, represented, evaluated, finalHeaps, worlds, frame, functional⟩ :=
    CompatibleGeneralIndex.finish_with_diagnostics header sourceType faithful functionLeaves functionTypes baseRep keyRep environmentTyped heaps reason (index_lift header missing)
  have sourceTrace := index_intro header.metadata form (terminal.trace baseTrace keyTrace)
  exact ⟨outcome, result, finalStore, futureWorld, terminal,
    original_result (fun _ _ retained => retained.1) represented, evaluated, finalHeaps, worlds, frame, functional,
    sourceTrace, index_outcome_post header keyFound form baseTrace keyTrace sourceTrace worlds represented⟩


end Solcore.SourceSemantics.CoreLowering.ReachedExpressionPrimitiveOutcomeProviders
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ReachedExpressionExtendedFaultPaths
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ReachedLoweredReadOutcomePorts
/-! A lowered read port consumes its actual certificate and lexical binding.
The finite primitive producer keeps its own invoked witness and final fields. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ReachedLoweredReadOutcomePorts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CompatibleExpressionReads ExpressionFailurePostContracts

/-- Inclusion is requested only at a real certified, statically bound read and
its actual current cell witness. -/
def ReadPolicies (fuel : Nat) (values : ValuesContext) (source : TypedSource)
    (context : SourceSemantics.Context) (reasonAt : ExpressionId → Word)
    (faults : FunctionCalls.FaultRep) : Prop :=
  ∀ {scope id code} (certificate : Certificate fuel values source scope id (reasonAt id) code),
    StaticBinding certificate context → ∀ environment heap,
      UninitializedPolicy certificate context environment heap faults

theorem lowered_read_preserves_with_post {fuel : Nat} {values : ValuesContext} {source : TypedSource}
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient)
    {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (reasonAt : ExpressionId → Word) {faults : FunctionCalls.FaultRep}
    (policies : ReadPolicies fuel values source context reasonAt faults)
    (unique : NodeOccurrencesUnique source) :
    Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (LoweredRead fuel values source context reasonAt) faults
      (ReachedExpressionExtendedFaultPaths.model_expressionPost values.checked functions registry) := by
  intro scope id lowered receipt node found mapping world administrative environment canonical actual before store ξ outcome after
    environments heaps locals agrees trace
  obtain ⟨certificate, typeEq, binding⟩ := receipt
  have nodeEq := Option.some.inj (certificate.metadata.found.symm.trans found)
  obtain ⟨value, finalStore, evaluated, represented, finalHeaps, frame, metadata, post⟩ :=
    ReachedExpressionPrimitiveOutcomeProviders.read_preserves certificate functions extension program context evidence
      binding environments heaps locals agrees (policies certificate binding environment before) unique trace
  refine ⟨value, finalStore, mapping, world, evaluated, ?_, finalHeaps, .refl _, .refl _, frame, metadata, ?_⟩
  · simpa only [nodeEq, typeEq] using represented
  · simpa only [typeEq] using ReachedExpressionExtendedFaultPaths.prior_outcomePost post

theorem lowered_read_reflects_with_post {fuel : Nat} {values : ValuesContext} {source : TypedSource}
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient)
    {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (reasonAt : ExpressionId → Word) {faults : FunctionCalls.FaultRep}
    (policies : ReadPolicies fuel values source context reasonAt faults)
    (unique : NodeOccurrencesUnique source) :
    Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (LoweredRead fuel values source context reasonAt) faults
      (ReachedExpressionExtendedFaultPaths.model_expressionPost values.checked functions registry) := by
  intro scope id lowered receipt node found mapping world administrative environment canonical actual before store ξ value finalStore
    environments heaps locals agrees evaluated
  obtain ⟨certificate, typeEq, binding⟩ := receipt
  have nodeEq := Option.some.inj (certificate.metadata.found.symm.trans found)
  obtain ⟨outcome, after, trace, represented, finalHeaps, frame, metadata, post⟩ :=
    ReachedExpressionPrimitiveOutcomeProviders.read_completed certificate functions extension program context evidence
      binding environments heaps locals agrees unique (policies certificate binding environment before) evaluated
  refine ⟨outcome, after, mapping, world, trace, ?_, finalHeaps, .refl _, .refl _, frame, metadata, ?_⟩
  · simpa only [nodeEq, typeEq] using represented
  · simpa only [typeEq] using ReachedExpressionExtendedFaultPaths.prior_outcomePost post

/-- Adding the genuine runtime row premise does not change the child result. -/
theorem typed_preserves_of_unrestricted {catalog : SourceCoreDataCatalog.Catalog}
    {projects : GenericHeap.Projection} {definitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects definitions}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {certificate : GenericExpressionMeaning.Certificate}
    {faults : FunctionCalls.FaultRep} {post : ExpressionFaultPost}
    (meaning : Preserves model program context evidence source certificate faults post) :
    TypedPreserves model program context evidence source certificate faults post := by
  intro scope id lowered generated node found mapping world administrative environment canonical actual actualContext before store ξ
    outcome after environments heaps locals agrees _actualTyped trace
  exact meaning generated found environments heaps locals agrees trace

theorem typed_reflects_of_unrestricted {catalog : SourceCoreDataCatalog.Catalog}
    {projects : GenericHeap.Projection} {definitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects definitions}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {certificate : GenericExpressionMeaning.Certificate}
    {faults : FunctionCalls.FaultRep} {post : ExpressionFaultPost}
    (meaning : Reflects model program context evidence source certificate faults post) :
    TypedReflects model program context evidence source certificate faults post := by
  intro scope id lowered generated node found mapping world administrative environment canonical actual actualContext before store ξ
    value finalStore environments heaps locals agrees _actualTyped evaluated
  exact meaning generated found environments heaps locals agrees evaluated

end Solcore.SourceSemantics.CoreLowering.ReachedLoweredReadOutcomePorts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.AssignmentOperandDiagnostics
/-! Assignment operand tokens are required only when the independent source
operand relation can fail. Plain assignment always accepts its RHS, so no
diagnostic entry is needed for its unused native operand token. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.AssignmentOperandDiagnostics
open Core Frontend

def OperandsLaw (faults : FunctionCalls.FaultRep) (operator : Syntax.ValueAssignOp)
    (token : Word) : Prop :=
  ∀ previous right, Dynamic.AssignmentOperandsInvalid operator previous right →
    faults (.invalidAssignmentOperands operator) token

theorem invalid_not_equal {operator : Syntax.ValueAssignOp}
    {previous : Option Dynamic.Value} {right : Dynamic.Value}
    (invalid : Dynamic.AssignmentOperandsInvalid operator previous right) : operator ≠ .equal := by
  cases invalid with
  | uninitialized different => exact different
  | compound corresponds _ => cases corresponds <;> intro same <;> cases same

theorem equal (faults : FunctionCalls.FaultRep) (token : Word) :
    OperandsLaw faults .equal token := by
  intro previous right invalid
  exact (invalid_not_equal invalid rfl).elim

theorem of_unconditional {faults : FunctionCalls.FaultRep} {operator : Syntax.ValueAssignOp}
    {token : Word} (interpreted : faults (.invalidAssignmentOperands operator) token) :
    OperandsLaw faults operator token := by
  intro _ _ _
  exact interpreted

theorem of_not_equal {faults : FunctionCalls.FaultRep} {operator : Syntax.ValueAssignOp}
    {token : Word} (interpreted : operator ≠ .equal → faults (.invalidAssignmentOperands operator) token) :
    OperandsLaw faults operator token := by
  intro previous right invalid
  exact interpreted (invalid_not_equal invalid)

end Solcore.SourceSemantics.CoreLowering.AssignmentOperandDiagnostics
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.AssignmentFaultTableCertificates
/-! Certificates for the actual diagnostic-table fold. A repeated key retains
its first complete entry. Raw target eligibility is explicit; normalized type
equality cannot supply it. A retained entry need not have the metadata of a
later same-key occurrence. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreAssignmentFaultSites.Certificates
open SourceInference Core

abbrev Matches (location : SourceCoreElaboration.ErrorSite) (binder : Resolved.LocalId) (kind : Kind) (site : Site) : Bool :=
  decide (site.site = location ∧ site.binder = binder ∧ site.kind = kind)

def Numbered (first : Nat) (sites : List Site) : Prop :=
  ∀ index site, sites[index]? = some site → site.reason.val = first + index

private theorem bind_ok {α β ε : Type} {value : Except ε α} {next : α → Except ε β} {result : β}
    (accepted : (value >>= next) = .ok result) :
    ∃ middle, value = .ok middle ∧ next middle = .ok result := by
  cases value with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem find_append {sites suffix : List Site} {test : Site → Bool} {site : Site}
    (found : sites.find? test = some site) : (sites ++ suffix).find? test = some site := by
  simp only [List.find?_append, found, Option.or]

private theorem add_shape {owner : Resolved.DeclarationId} {first : Nat} {sites next : List Site}
    {location : SourceCoreElaboration.ErrorSite} {span : Syntax.SourceSpan}
    {assignment : AssignmentResolution} {kind : Kind}
    (accepted : add owner first sites location span assignment kind = .ok next) :
    next = sites ∨ ∃ reason,
      Word.ofNat? (first + sites.length) = some reason ∧
      next = sites ++ [{site := location, binder := assignment.target.root, kind := kind, span := span, reason := reason, rhsType := assignment.target.type}] := by
  by_cases owned : assignment.target.root.owner = owner
  · simp only [add, owned, ne_eq, not_true_eq_false, ↓reduceIte, bind, Except.bind, pure, Except.pure] at accepted
    split at accepted
    · exact .inl (Except.ok.inj accepted).symm
    · split at accepted
      · exact .inl (Except.ok.inj accepted).symm
      · split at accepted
        · rename_i reason generated
          exact .inr ⟨reason, generated, (Except.ok.inj accepted).symm⟩
        · cases accepted
  · simp [add, owned, throw, bind, Except.bind] at accepted

theorem add_preserves_found {owner : Resolved.DeclarationId} {first : Nat} {sites next : List Site}
    {location : SourceCoreElaboration.ErrorSite} {span : Syntax.SourceSpan}
    {assignment : AssignmentResolution} {kind : Kind} {test : Site → Bool} {site : Site}
    (accepted : add owner first sites location span assignment kind = .ok next)
    (found : sites.find? test = some site) : next.find? test = some site := by
  rcases add_shape accepted with rfl | ⟨reason, _, rfl⟩
  · exact found
  · exact find_append found

theorem add_lookup {owner : Resolved.DeclarationId} {first : Nat} {sites next : List Site}
    {location : SourceCoreElaboration.ErrorSite} {span : Syntax.SourceSpan}
    {assignment : AssignmentResolution} {kind : Kind}
    (rawScalar : assignment.target.type = .word ∨ assignment.target.type = .integer)
    (accepted : add owner first sites location span assignment kind = .ok next) :
    ∃ site, next.find? (Matches location assignment.target.root kind) = some site := by
  by_cases owned : assignment.target.root.owner = owner
  · have eligible : ¬ (assignment.target.type ≠ .word ∧ assignment.target.type ≠ .integer) := by
      intro excluded
      exact rawScalar.elim excluded.1 excluded.2
    simp only [add, owned, ne_eq, not_true_eq_false, eligible, ↓reduceIte, bind, Except.bind, pure, Except.pure] at accepted
    split at accepted
    · rename_i present
      obtain ⟨site, member, matched⟩ := List.any_eq_true.mp present
      have hasEntry := (List.find?_isSome (p := Matches location assignment.target.root kind)).mpr ⟨site, member, matched⟩
      cases found : sites.find? (Matches location assignment.target.root kind) with
      | none => simp only [found, Option.isSome_none, Bool.false_eq_true] at hasEntry
      | some result => exact ⟨result, Except.ok.inj accepted ▸ found⟩
    · split at accepted
      · rename_i reason generated
        have nextEq := (Except.ok.inj accepted).symm
        subst next
        cases found : sites.find? (Matches location assignment.target.root kind) with
        | none => exact ⟨{site := location, binder := assignment.target.root, kind := kind, span := span, reason := reason, rhsType := assignment.target.type}, by simp [List.find?_append, found, Matches]⟩
        | some site => exact ⟨site, find_append found⟩
      · cases accepted
  · simp [add, owned, throw, bind, Except.bind] at accepted

private theorem numbered_append {first : Nat} {sites : List Site} {site : Site}
    (numbered : Numbered first sites) (reason : site.reason.val = first + sites.length) :
    Numbered first (sites ++ [site]) := by
  intro index entry found
  by_cases before : index < sites.length
  · have previous : sites[index]? = some entry := by simpa only [List.getElem?_append, before, ↓reduceIte] using found
    exact numbered index entry previous
  · have suffix : [site][index - sites.length]? = some entry := by
      simpa only [List.getElem?_append, before, ↓reduceIte] using found
    have valid : index - sites.length < 1 := by simpa using (List.getElem?_eq_some_iff.mp suffix).1
    have same : index = sites.length := by omega
    subst index
    simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at suffix
    exact suffix ▸ reason

theorem add_numbered {owner : Resolved.DeclarationId} {first : Nat} {sites next : List Site}
    {location : SourceCoreElaboration.ErrorSite} {span : Syntax.SourceSpan}
    {assignment : AssignmentResolution} {kind : Kind}
    (numbered : Numbered first sites)
    (accepted : add owner first sites location span assignment kind = .ok next) : Numbered first next := by
  rcases add_shape accepted with rfl | ⟨reason, generated, rfl⟩
  · exact numbered
  · apply numbered_append numbered
    unfold Word.ofNat? at generated
    split at generated
    · cases generated; rfl
    · cases generated

private theorem fold_invariant {α : Type} {step : List Site → α → Except Error (List Site)}
    {property : List Site → Prop}
    (each : ∀ sites item next, property sites → step sites item = .ok next → property next)
    {items : List α} {sites next : List Site} (initial : property sites)
    (accepted : items.foldlM step sites = .ok next) : property next := by
  induction items generalizing sites with
  | nil => exact Except.ok.inj accepted ▸ initial
  | cons item rest ih =>
    obtain ⟨middle, first, remaining⟩ := bind_ok accepted
    exact ih (each sites item middle initial first) remaining

private theorem fold_contains {α : Type} {step : List Site → α → Except Error (List Site)}
    {property : List Site → Prop}
    (preserve : ∀ sites item next, property sites → step sites item = .ok next → property next)
    {items : List α} {selected : α}
    (obtains : ∀ sites next, step sites selected = .ok next → property next)
    (member : selected ∈ items) {sites next : List Site}
    (accepted : items.foldlM step sites = .ok next) : property next := by
  induction items generalizing sites with
  | nil => cases member
  | cons item rest ih =>
    obtain ⟨middle, first, remaining⟩ := bind_ok accepted
    rcases List.mem_cons.mp member with rfl | member
    · exact fold_invariant preserve (obtains _ _ first) remaining
    · exact ih member remaining

private theorem item_preserves {owner : Resolved.DeclarationId} {first : Nat} {sites next : List Site}
    {location : SourceCoreElaboration.ErrorSite} {span : Syntax.SourceSpan} {item : ForItemForm}
    {test : Site → Bool} {site : Site}
    (accepted : addItem owner first location span sites item = .ok next)
    (found : sites.find? test = some site) : next.find? test = some site := by
  cases item with
  | letDecl | expression => exact Except.ok.inj accepted ▸ found
  | assignBitNot => exact add_preserves_found accepted found
  | assignValue assignment operator rhs =>
    simp only [addItem] at accepted
    split at accepted
    · exact Except.ok.inj accepted ▸ found
    · exact add_preserves_found accepted found

private theorem item_numbered {owner : Resolved.DeclarationId} {first : Nat} {sites next : List Site}
    {location : SourceCoreElaboration.ErrorSite} {span : Syntax.SourceSpan} {item : ForItemForm}
    (numbered : Numbered first sites)
    (accepted : addItem owner first location span sites item = .ok next) : Numbered first next := by
  cases item with
  | letDecl | expression => exact Except.ok.inj accepted ▸ numbered
  | assignBitNot => exact add_numbered numbered accepted
  | assignValue assignment operator rhs =>
    simp only [addItem] at accepted
    split at accepted
    · exact Except.ok.inj accepted ▸ numbered
    · exact add_numbered numbered accepted

private theorem statement_preserves {owner : Resolved.DeclarationId} {first : Nat} {sites next : List Site}
    {node : StatementNode} {test : Site → Bool} {site : Site}
    (accepted : addStatement owner first sites node = .ok next)
    (found : sites.find? test = some site) : next.find? test = some site := by
  by_cases owned : node.id.occurrence.owner = owner
  · simp only [addStatement, owned, ne_eq, not_true_eq_false, ↓reduceIte, pure, Except.pure] at accepted
    cases form : node.form <;> simp only [form] at accepted
    all_goals first | exact Except.ok.inj accepted ▸ found | exact add_preserves_found accepted found | skip
    · split at accepted
      · exact Except.ok.inj accepted ▸ found
      · exact add_preserves_found accepted found
    · exact fold_invariant (fun _ _ _ previous step => item_preserves step previous) found accepted

  · simp [addStatement, owned, throw, bind, Except.bind] at accepted

private theorem statement_numbered {owner : Resolved.DeclarationId} {first : Nat} {sites next : List Site}
    {node : StatementNode} (numbered : Numbered first sites)
    (accepted : addStatement owner first sites node = .ok next) : Numbered first next := by
  by_cases owned : node.id.occurrence.owner = owner
  · simp only [addStatement, owned, ne_eq, not_true_eq_false, ↓reduceIte, pure, Except.pure] at accepted
    cases form : node.form <;> simp only [form] at accepted
    all_goals first | exact Except.ok.inj accepted ▸ numbered | exact add_numbered numbered accepted | skip
    · split at accepted
      · exact Except.ok.inj accepted ▸ numbered
      · exact add_numbered numbered accepted
    · exact fold_invariant (fun _ _ _ previous step => item_numbered previous step) numbered accepted

  · simp [addStatement, owned, throw, bind, Except.bind] at accepted

/-- An operand operation at a statement or inside either ordered for header. -/
inductive OperandAt (node : StatementNode) (assignment : AssignmentResolution)
    (operator : Syntax.ValueAssignOp) : Prop where
  | statement {rhs} : node.form = .assignValue assignment operator rhs → OperandAt node assignment operator
  | header {initializer condition post body rhs} : node.form = .forLoop initializer condition post body →
      .assignValue assignment operator rhs ∈ initializer ++ post → OperandAt node assignment operator

private theorem statement_lookup {owner : Resolved.DeclarationId} {first : Nat} {sites next : List Site}
    {node : StatementNode} {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp}
    (occurs : OperandAt node assignment operator) (different : operator ≠ .equal)
    (rawScalar : assignment.target.type = .word ∨ assignment.target.type = .integer)
    (accepted : addStatement owner first sites node = .ok next) :
    ∃ site, next.find? (Matches (.occurrence node.id.occurrence) assignment.target.root (.value operator)) = some site := by
  by_cases owned : node.id.occurrence.owner = owner
  · simp only [addStatement, owned, ne_eq, not_true_eq_false, ↓reduceIte, pure, Except.pure] at accepted
    cases occurs with
    | statement form =>
      simp only [form, different, ↓reduceIte] at accepted
      exact add_lookup rawScalar accepted
    | header form member =>
      simp only [form] at accepted
      apply fold_contains (selected := ForItemForm.assignValue assignment operator _) (property := fun sites => ∃ site, sites.find? (Matches (.occurrence node.id.occurrence) assignment.target.root (.value operator)) = some site) ?_ ?_ member accepted
      · intro sites item next ⟨site, found⟩ step
        exact ⟨site, item_preserves step found⟩
      · intro sites next step
        simp only [addItem, different, ↓reduceIte] at step
        exact add_lookup rawScalar step

  · simp [addStatement, owned, throw, bind, Except.bind] at accepted

/-- The production fold enumerates successful insertions without wrapping. -/
theorem prepare_numbered {source : TypedSource} {first : Nat} {table : Table}
    (accepted : prepare source first = .ok table) : Numbered first table.sites := by
  unfold prepare at accepted
  obtain ⟨sites, folded, returned⟩ := bind_ok accepted
  cases returned
  exact fold_invariant (fun _ _ _ previous step => statement_numbered previous step)
    (by intro index site found; cases found) folded

/-- Actual eligible occurrences have a lookup after the complete ordered fold.
The result keeps the first entry's metadata, including across header repeats. -/
theorem prepare_lookup {source : TypedSource} {first : Nat} {table : Table}
    {node : StatementNode} {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp}
    (accepted : prepare source first = .ok table)
    (member : Node.statement node ∈ source.nodes)
    (occurs : OperandAt node assignment operator) (different : operator ≠ .equal)
    (rawScalar : assignment.target.type = .word ∨ assignment.target.type = .integer) :
    ∃ site, table.sites.find? (Matches (.occurrence node.id.occurrence) assignment.target.root (.value operator)) = some site := by
  unfold prepare at accepted
  obtain ⟨sites, folded, returned⟩ := bind_ok accepted
  cases returned
  apply fold_contains (selected := node) (property := fun sites => ∃ site, sites.find? (Matches (.occurrence node.id.occurrence) assignment.target.root (.value operator)) = some site) ?_ ?_ ?_ folded
  · intro sites item next ⟨site, found⟩ step
    exact ⟨site, statement_preserves step found⟩
  · intro sites next step
    exact statement_lookup occurs different rawScalar step
  · apply List.mem_mergeSort.mpr
    exact List.mem_filterMap.mpr ⟨.statement node, member, rfl⟩

/-- A successful later header fold preserves the exact first record, including
its span and raw RHS type, even if a later request reuses the lookup key. -/
theorem items_preserve_found {owner : Resolved.DeclarationId} {first : Nat}
    {location : SourceCoreElaboration.ErrorSite} {span : Syntax.SourceSpan}
    {items : List ForItemForm} {sites next : List Site} {test : Site → Bool} {site : Site}
    (accepted : items.foldlM (addItem owner first location span) sites = .ok next)
    (found : sites.find? test = some site) : next.find? test = some site :=
  fold_invariant (fun _ _ _ previous step => item_preserves step previous) found accepted

theorem statements_preserve_found {owner : Resolved.DeclarationId} {first : Nat}
    {nodes : List StatementNode} {sites next : List Site} {test : Site → Bool} {site : Site}
    (accepted : nodes.foldlM (addStatement owner first) sites = .ok next)
    (found : sites.find? test = some site) : next.find? test = some site :=
  fold_invariant (fun _ _ _ previous step => statement_preserves step previous) found accepted

theorem Numbered.reason_unique {first : Nat} {sites : List Site}
    (numbered : Numbered first sites) {left right : Site}
    (leftMem : left ∈ sites) (rightMem : right ∈ sites) (same : left.reason = right.reason) : left = right := by
  obtain ⟨i, leftFound⟩ := List.mem_iff_getElem?.mp leftMem
  obtain ⟨j, rightFound⟩ := List.mem_iff_getElem?.mp rightMem
  have leftIndex := numbered i left leftFound
  have rightIndex := numbered j right rightFound
  have indexEq : i = j := by rw [same] at leftIndex; omega
  subst j
  exact Option.some.inj (leftFound.symm.trans rightFound)

theorem Numbered.diagnostic {first : Nat} {table : Table} {site : Site}
    (numbered : Numbered first table.sites) (member : site ∈ table.sites) :
    table.diagnostic? site.reason = some site.diagnostic := by
  have existsEntry := (List.find?_isSome (p := fun candidate : Site => decide (candidate.reason = site.reason))).mpr
    ⟨site, member, by simp⟩
  cases found : table.sites.find? (fun candidate => decide (candidate.reason = site.reason)) with
  | none => simp only [found, Option.isSome_none, Bool.false_eq_true] at existsEntry
  | some entry =>
    have same : entry.reason = site.reason := by simpa using List.find?_some found
    have identical := numbered.reason_unique (List.mem_of_find?_eq_some found) member same
    subst entry
    exact Table.diagnostic_found found

/-- Lookup and diagnostic decoding agree on the actual first eligible entry.
No equality with a later occurrence's raw metadata is inferred. -/
theorem prepare_operand {source : TypedSource} {first : Nat} {table : Table}
    {node : StatementNode} {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp}
    (accepted : prepare source first = .ok table) (member : Node.statement node ∈ source.nodes)
    (occurs : OperandAt node assignment operator) (different : operator ≠ .equal)
    (rawScalar : assignment.target.type = .word ∨ assignment.target.type = .integer) :
    ∃ site, table.sites.find? (Matches (.occurrence node.id.occurrence) assignment.target.root (.value operator)) = some site ∧
      site.site = .occurrence node.id.occurrence ∧ site.binder = assignment.target.root ∧ site.kind = .value operator ∧
      table.reasonAt (.occurrence node.id.occurrence) assignment.target.root (.value operator) = site.reason ∧
      table.diagnostic? site.reason = some site.diagnostic := by
  obtain ⟨site, found⟩ := prepare_lookup accepted member occurs different rawScalar
  have matched : site.site = .occurrence node.id.occurrence ∧ site.binder = assignment.target.root ∧ site.kind = .value operator :=
    by simpa [Matches] using List.find?_some found
  exact ⟨site, found, matched.1, matched.2.1, matched.2.2,
    Table.reasonAt_found found, (prepare_numbered accepted).diagnostic (List.mem_of_find?_eq_some found)⟩


/-- A unary assignment retains its genuine statement or owning header site. -/
inductive UnaryAt (node : StatementNode) (assignment : AssignmentResolution) : Prop where
  | statement : node.form = .assignBitNot assignment → UnaryAt node assignment
  | header {initializer condition post body} : node.form = .forLoop initializer condition post body →
      .assignBitNot assignment ∈ initializer ++ post → UnaryAt node assignment

private theorem statement_unary_lookup {owner : Resolved.DeclarationId} {first : Nat} {sites next : List Site}
    {node : StatementNode} {assignment : AssignmentResolution}
    (occurs : UnaryAt node assignment)
    (rawScalar : assignment.target.type = .word ∨ assignment.target.type = .integer)
    (accepted : addStatement owner first sites node = .ok next) :
    ∃ site, next.find? (Matches (.occurrence node.id.occurrence) assignment.target.root .bitNot) = some site := by
  by_cases owned : node.id.occurrence.owner = owner
  · simp only [addStatement, owned, ne_eq, not_true_eq_false, ↓reduceIte, pure, Except.pure] at accepted
    cases occurs with
    | statement form =>
      simp only [form] at accepted
      exact add_lookup rawScalar accepted
    | header form member =>
      simp only [form] at accepted
      apply fold_contains (selected := ForItemForm.assignBitNot assignment)
        (property := fun sites => ∃ site, sites.find? (Matches (.occurrence node.id.occurrence) assignment.target.root .bitNot) = some site) ?_ ?_ member accepted
      · intro sites item next ⟨site, found⟩ step
        exact ⟨site, item_preserves step found⟩
      · intro sites next step
        exact add_lookup rawScalar step
  · simp [addStatement, owned, throw, bind, Except.bind] at accepted

/-- The saved original table fold also authenticates actual unary occurrences.
Repeated header requests retain their original first table entry. -/
theorem prepare_unary {source : TypedSource} {first : Nat} {table : Table}
    {node : StatementNode} {assignment : AssignmentResolution}
    (accepted : prepare source first = .ok table) (member : Node.statement node ∈ source.nodes)
    (occurs : UnaryAt node assignment)
    (rawScalar : assignment.target.type = .word ∨ assignment.target.type = .integer) :
    ∃ site, table.sites.find? (Matches (.occurrence node.id.occurrence) assignment.target.root .bitNot) = some site ∧
      site.site = .occurrence node.id.occurrence ∧ site.binder = assignment.target.root ∧ site.kind = .bitNot ∧
      table.reasonAt (.occurrence node.id.occurrence) assignment.target.root .bitNot = site.reason ∧
      table.diagnostic? site.reason = some site.diagnostic := by
  have lookup : ∃ site, table.sites.find? (Matches (.occurrence node.id.occurrence) assignment.target.root .bitNot) = some site := by
    unfold prepare at accepted
    obtain ⟨sites, folded, returned⟩ := bind_ok accepted
    cases returned
    apply fold_contains (selected := node)
      (property := fun sites => ∃ site, sites.find? (Matches (.occurrence node.id.occurrence) assignment.target.root .bitNot) = some site) ?_ ?_ ?_ folded
    · intro sites item next ⟨site, found⟩ step
      exact ⟨site, statement_preserves step found⟩
    · intro sites next step
      exact statement_unary_lookup occurs rawScalar step
    · apply List.mem_mergeSort.mpr
      exact List.mem_filterMap.mpr ⟨.statement node, member, rfl⟩
  obtain ⟨site, found⟩ := lookup
  have matched : site.site = .occurrence node.id.occurrence ∧ site.binder = assignment.target.root ∧ site.kind = .bitNot :=
    by simpa [Matches] using List.find?_some found
  exact ⟨site, found, matched.1, matched.2.1, matched.2.2,
    Table.reasonAt_found found, (prepare_numbered accepted).diagnostic (List.mem_of_find?_eq_some found)⟩

end Solcore.Frontend.SourceCoreAssignmentFaultSites.Certificates
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProgramAssignmentDiagnosticInclusion
/-! Actual program collection allocates disjoint assignment and boundary tokens.
Every assignment diagnostic therefore retains its exact first-match identity in
the combined program table. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.ProgramAssignmentDiagnosticInclusion
open Core Frontend SourceInference SourceCoreProgramFaultSites

private theorem word_value {number : Nat} {word : Word}
    (accepted : Word.ofNat? number = some word) : word.val = number := by
  unfold Word.ofNat? at accepted
  split at accepted
  · cases accepted; rfl
  · cases accepted

private def boundaries (function : Function) : List (Word × SourceCoreFaultSites.Diagnostic) :=
  function.assignments.diagnostics ++ [
    (function.fellThroughReason, {
      error := SourceTypedRuntime.RuntimeError.functionFellThrough function.table.resultType
      site := SourceCoreElaboration.ErrorSite.declaration function.table.owner
      span := none }),
    (function.table.escapedReason, {
      error := SourceTypedRuntime.RuntimeError.controlEscapedFunction
      site := SourceCoreElaboration.ErrorSite.declaration function.table.owner
      span := none })]

private theorem own_ranges {first : Nat} {row : SourceSpecialization.SpecializedFunction} {own : Function}
    (receipt : FunctionIssuance first row own) :
    (∀ pair ∈ boundaries own, first ≤ pair.1.val ∧
      pair.1.val < first + own.table.reads.length + own.assignments.length + 2) ∧
    (∀ left ∈ boundaries own, ∀ right ∈ boundaries own, left.1 = right.1 → left = right) := by
  cases receipt with
  | intro _ _ _ _ assignments fell escaped _ _ _ =>
    obtain ⟨_, assigned, unique⟩ := SourceCoreAssignmentFaultSites.prepare_token_range assignments
    have fellNumber := word_value fell
    have escapedNumber := word_value escaped
    have assignmentUnique : ∀ left ∈ own.assignments.diagnostics,
        ∀ right ∈ own.assignments.diagnostics, left.1 = right.1 → left = right := by
      intro left leftMember right rightMember same
      obtain ⟨a, aMember, rfl⟩ := List.mem_map.mp leftMember
      obtain ⟨b, bMember, rfl⟩ := List.mem_map.mp rightMember
      have equal := unique a aMember b bMember same
      cases equal
      rfl
    constructor
    · intro pair member
      rcases List.mem_append.mp member with member | member
      · have bounds := assigned pair member; exact ⟨by omega, by omega⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl <;> dsimp only <;> omega
    · intro left leftMember right rightMember same
      rcases List.mem_append.mp leftMember with leftMember | leftMember
      · rcases List.mem_append.mp rightMember with rightMember | rightMember
        · exact assignmentUnique left leftMember right rightMember same
        · have bound := assigned left leftMember
          simp only [List.mem_cons, List.not_mem_nil, or_false] at rightMember
          rcases rightMember with rfl | rfl <;>
            have equal := congrArg Fin.val same <;> dsimp only at equal <;> omega
      · rcases List.mem_append.mp rightMember with rightMember | rightMember
        · have bound := assigned right rightMember
          simp only [List.mem_cons, List.not_mem_nil, or_false] at leftMember
          rcases leftMember with rfl | rfl <;>
            have equal := congrArg Fin.val same <;> dsimp only at equal <;> omega
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at leftMember rightMember
          rcases leftMember with rfl | rfl <;> rcases rightMember with rfl | rfl
          · rfl
          · have equal := congrArg Fin.val same; dsimp only at equal; omega
          · have equal := congrArg Fin.val same; dsimp only at equal; omega
          · rfl

private theorem inventory {first : Nat} {rows : List SourceSpecialization.SpecializedFunction}
    {functions : List Function} (receipt : ProgramIssuance first rows functions) :
    (∀ pair ∈ functions.flatMap boundaries, first ≤ pair.1.val) ∧
    (∀ left ∈ functions.flatMap boundaries, ∀ right ∈ functions.flatMap boundaries,
      left.1 = right.1 → left = right) := by
  induction receipt with
  | nil => constructor <;> simp
  | @cons first row rows own functions issued remaining ih =>
    obtain ⟨bounds, unique⟩ := own_ranges issued
    constructor
    · intro pair member
      simp only [List.flatMap_cons, List.mem_append] at member
      rcases member with member | member
      · exact (bounds pair member).1
      · have bound := ih.1 pair member; omega
    · intro left leftMember right rightMember same
      simp only [List.flatMap_cons, List.mem_append] at leftMember rightMember
      rcases leftMember with leftMember | leftMember
      · rcases rightMember with rightMember | rightMember
        · exact unique left leftMember right rightMember same
        · have leftBound := bounds left leftMember
          have rightBound := ih.1 right rightMember
          have equal := congrArg Fin.val same; omega
      · rcases rightMember with rightMember | rightMember
        · have rightBound := bounds right rightMember
          have leftBound := ih.1 left leftMember
          have equal := congrArg Fin.val same; omega
        · exact ih.2 left leftMember right rightMember same

private theorem find_unique {rows : List (Word × SourceCoreFaultSites.Diagnostic)}
    {pair : Word × SourceCoreFaultSites.Diagnostic} (member : pair ∈ rows)
    (unique : ∀ candidate ∈ rows, candidate.1 = pair.1 → candidate = pair) :
    rows.find? (fun candidate => decide (candidate.1 = pair.1)) = some pair := by
  induction rows with
  | nil => simp at member
  | cons head tail ih =>
    by_cases sameKey : head.1 = pair.1
    · have same := unique head List.mem_cons_self sameKey
      simp [same]
    · have tailMember : pair ∈ tail := by
        rcases List.mem_cons.mp member with same | member
        · exact (sameKey (same ▸ rfl)).elim
        · exact member
      simpa only [List.find?_cons, decide_eq_false_iff_not.mpr sameKey,
        Bool.false_eq_true, ↓reduceIte] using
        ih tailMember (fun candidate belongs => unique candidate (List.mem_cons_of_mem head belongs))

/-- The original assignment lookup produces a genuine diagnostic row. -/
theorem assignment_member {table : SourceCoreAssignmentFaultSites.Table}
    {token : Word} {diagnostic : SourceCoreFaultSites.Diagnostic}
    (decoded : table.diagnostic? token = some diagnostic) :
    (token, diagnostic) ∈ table.diagnostics := by
  unfold SourceCoreAssignmentFaultSites.Table.diagnostic? at decoded
  cases found : table.sites.find? (fun site => decide (site.reason = token)) with
  | none => simp only [found, Option.map_none] at decoded; cases decoded
  | some site =>
    simp only [found, Option.map_some, Option.some.injEq] at decoded
    have same := of_decide_eq_true (List.find?_some (p := fun site : SourceCoreAssignmentFaultSites.Site => decide (site.reason = token)) found)
    exact List.mem_map.mpr ⟨site, List.mem_of_find?_eq_some found, by simp only [same, decoded]⟩

/-- Exact program-wide inclusion, including exclusion of the two special
boundary decoder branches. No arbitrary diagnostic-table relation is assumed. -/
theorem prepare_assignment_diagnostic {plan : Plan} {root : Key} {diagnostics : SourceCoreProgramFaultSites.Program}
    (accepted : prepare plan root = .ok diagnostics)
    {own : Function} (member : own ∈ diagnostics.functions)
    {token : Word} {diagnostic : SourceCoreFaultSites.Diagnostic}
    (decoded : own.assignments.diagnostic? token = some diagnostic) :
    token ≠ Word.zero ∧ token ≠ diagnostics.rootTable.escapedReason ∧
    diagnostics.rootTable.additional.find? (fun pair => decide (pair.1 = token)) = some (token, diagnostic) ∧
    diagnostics.rootTable.diagnostic? token = some diagnostic := by
  obtain ⟨selected, collection, selectedFound, table⟩ := prepare_issuance accepted
  have additional : diagnostics.rootTable.additional = diagnostics.functions.flatMap boundaries := congrArg (·.additional) table
  have escaped : diagnostics.rootTable.escapedReason = selected.table.escapedReason := congrArg (·.escapedReason) table
  have actual := assignment_member decoded
  have belongs : (token, diagnostic) ∈ diagnostics.functions.flatMap boundaries :=
    List.mem_flatMap.mpr ⟨own, member, List.mem_append_left _ actual⟩
  have facts := inventory collection
  have positive : token ≠ Word.zero := by
    intro same
    have bound := facts.1 _ belongs
    change 1 ≤ token.val at bound
    have number := congrArg Fin.val same
    change token.val = 0 at number
    omega
  have escapedMember : (selected.table.escapedReason, {
      error := SourceTypedRuntime.RuntimeError.controlEscapedFunction
      site := SourceCoreElaboration.ErrorSite.declaration selected.table.owner
      span := none }) ∈ diagnostics.functions.flatMap boundaries :=
    List.mem_flatMap.mpr ⟨selected, List.mem_of_find?_eq_some selectedFound, by simp [boundaries]⟩
  have ordinary : token ≠ diagnostics.rootTable.escapedReason := by
    intro same
    have equal := facts.2 _ belongs _ escapedMember (same.trans escaped)
    have error := congrArg (fun pair => pair.2.error) equal
    obtain ⟨site, _, row⟩ := List.mem_map.mp actual
    have diag := congrArg Prod.snd row
    rw [← diag] at error
    cases kind : site.kind <;> simp [SourceCoreAssignmentFaultSites.Site.diagnostic, kind] at error
  have found : diagnostics.rootTable.additional.find? (fun pair => decide (pair.1 = token)) = some (token, diagnostic) := by
    rw [additional]
    exact find_unique belongs (fun candidate candidateMember same => facts.2 _ candidateMember _ belongs same)
  refine ⟨positive, ordinary, found, ?_⟩
  simp only [SourceCoreFaultSites.Table.diagnostic?, positive, ordinary, ↓reduceIte, found]

end Solcore.SourceSemantics.CoreLowering.ProgramAssignmentDiagnosticInclusion
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ReachedIndexSuccessOutcomePorts
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
end
