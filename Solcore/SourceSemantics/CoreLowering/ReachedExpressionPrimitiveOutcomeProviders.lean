import Solcore.SourceSemantics.CoreLowering.ReachedExpressionPrimitiveFaultPosts
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReadMeaning
import Solcore.SourceSemantics.CoreLowering.CompatibleGeneralIndexTerminal

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
