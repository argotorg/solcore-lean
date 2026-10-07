import Solcore.SourceSemantics.CoreLowering.RecursiveNamedDataExpressionSourceBounds
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionCallMeaning
import Solcore.SourceSemantics.CoreLowering.ProtectedStatePlaceAssignment
import Solcore.SourceSemantics.CoreLowering.ProtectedStateExpressionReady
import Solcore.SourceSemantics.CoreLowering.ProtectedStateExpressionSequenceProducer
import Solcore.SourceSemantics.CoreLowering.ProtectedStateExpressionOperandTyping

/-! Finite budgets compose the constructor/member/index cases of the existing
static head. Actual child states pass through their real reached effects.
This layer neither changes the expression grammar nor closes its recursive
call/body obligations. Reflected source costs are independent of native costs. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedDataExpressionHeadBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CompatibleExpressionPrimitives
open CompatibleExpressionConditionals CompatibleExpressionConstructors CompatibleExpressionMembers
open CompatibleExpressionIndices CoreProof
open GenericExpressionMeaning (agree_prefix rename_prefix)
open DataPatternValues
open RecursiveNamedCallBounds RecursiveNamedBoundedContracts
open CompatibleExpressionCalls (Head CallHeads)
/-- Only the data cases of the existing head are selected by this layer. -/
inductive Data {calls : CallHeads} {values : SourceCoreCompatibleValues.Context}
    {source : TypedSource} {context : SourceSemantics.Context}
    {reasonAt : ExpressionId → Word} {children : GenericExpressionMeaning.Certificate}
    {scope : SourceCoreLocalCell.Scope} :
    {id : ExpressionId} → {lowered : SourceCoreBasic.LoweredExpr} →
    Head calls values source context reasonAt children scope id lowered → Prop where
  | constructor {id node instantiation ids tag header codes}
      (receipt : CompatibleExpressionConstructors.Header values source id node instantiation tag header codes)
      (form : node.form = .constructor instantiation ids)
      (valid : SourceSemantics.DataConstructorInstantiation.Valid context instantiation)
      (sequence : DataExpressionSequence.Tree source children scope ids instantiation.payloadTypes codes) :
      Data (.constructor receipt form valid sequence)
  | member {id node base baseNode name index identity branches result child}
      (metadata : Metadata values.checked source id node result)
      (baseMetadata : Metadata values.checked source base baseNode child.type)
      (form : node.form = .member base name index)
      (layout : CompatibleExpressionMembers.Layout values.checked (.occurrence id.occurrence) baseNode.type node.type index identity branches result)
      (certified : children scope base child) :
      Data (.member metadata baseMetadata form layout certified)
  | index {id node base key baseNode keyNode layout comparison first second}
      (header : CompatibleExpressionIndices.Header values source id base node baseNode layout comparison first second)
      (keyFound : source.lookupExpression? key = some keyNode)
      (form : node.form = .index base key)
      (sourceType : baseNode.type = .mapping keyNode.type node.type)
      (baseCertified : children scope base first) (keyCertified : children scope key second) :
      Data (.index header keyFound form sourceType baseCertified keyCertified)

def Certificate (calls : CallHeads) (values : SourceCoreCompatibleValues.Context) (source : TypedSource)
    (context : SourceSemantics.Context) (reasonAt : ExpressionId → Word)
    (children : GenericExpressionMeaning.Certificate) : GenericExpressionMeaning.Certificate := fun scope id lowered =>
  ∃ head : Head calls values source context reasonAt children scope id lowered, Data head

private theorem valuesRep {values : SourceCoreCompatibleValues.Context} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions values.checked.catalog.definitions} {functions : FunctionModel values.checked.catalog ambient}
    {mapping : LocationMap} {world : StoreTyping} {types : List TypeSystem.Ty} {natives : List Ty}
    {sources : List Dynamic.Value} {payloads : List Value}
    (represented : DataExpressionSequence.Values (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      mapping world types natives sources payloads) :
    ValuesRep values.checked registry functions mapping world types sources payloads natives := by
  induction represented with
  | nil => exact .nil
  | cons head _ ih => exact .cons head ih

private theorem missing_excludes {values : List Dynamic.Value} {index : Nat} {value : Dynamic.Value}
    (missing : Dynamic.ValueIndexMissing values index) (selected : Dynamic.ValueAt values index value) : False := by
  induction missing with
  | nil => cases selected
  | tail rest ih => cases selected with | tail child => exact ih child

private theorem at_functional {values : List Dynamic.Value} {index : Nat} {first second : Dynamic.Value}
    (left : Dynamic.ValueAt values index first) (right : Dynamic.ValueAt values index second) : first = second := by
  induction left with
  | head => cases right; rfl
  | tail _ ih => cases right with | tail rest => exact ih rest

private def ReflectsRawAt (size : Nat) {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (certificate : GenericExpressionMeaning.Certificate) (faults : FunctionCalls.FaultRep) (entry : ProtectedExpressionMeaning.Entry) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, source.lookupExpression? id = some node →
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext definitions →
    entry scope mapping world before store canonical →
    EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore →
    ∃ outcome after finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after ∧
      FunctionCalls.ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after


variable {fuel : Nat} {values : SourceCoreCompatibleValues.Context} {source : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
  (unique : NodeOccurrencesUnique source) {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))


namespace Stateful
universe u v
variable {calls : CallHeads} {certificate : GenericExpressionMeaning.Certificate}
  {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
  (transport : ProtectedStateTransition.AdministrativeTransport protocol)
private def ReflectsRawAt {Records : Type v} (size : Nat) {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (certificate : GenericExpressionMeaning.Certificate) (faults : FunctionCalls.FaultRep) (protocol : ProtectedStateTransition.Protocol.{u, v} Records) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, source.lookupExpression? id = some node →
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext definitions →
    ∀ initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore →
    ∃ outcome after finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after ∧
      FunctionCalls.ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩


include extension in
/-- The constructor's original Source suffix consumes its actual ordered
sequence receipt and keeps that sequence's exact reached state. -/
theorem constructor_preserves_after_sequence (budget : Nat)
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    {instantiation : DataConstructorInstantiation} {ids : List ExpressionId}
    {tag : ConstructorId} {header : Word} {codes : List SourceCoreBasic.LoweredExpr}
    (receipt : CompatibleExpressionConstructors.Header values source id node instantiation tag header codes)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment}
    {canonical actual : Environment} {before : Dynamic.Heap} {store : Store} {ξ : Renaming}
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (sequence : ProtectedStateExpressionSequenceProducer.Preserves
      (program := program) (context := context) (evidence := evidence) (source := source)
      (environment := environment) (actual := actual) (ξ := ξ) (ids := ids)
      (sourceTypes := instantiation.payloadTypes) (codes := codes) (faults := faults)
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) initial budget)
    {sequenceSize : Nat} {sourceOutcome : DataExpressionSequence.Outcome}
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (sourceTrace : ProtectedDataExpressionSequence.TraceAt program sequenceSize context evidence source environment before ids sourceOutcome after)
    (packed : CompatibleExpressionConstructors.PacksOutcome instantiation sourceOutcome outcome)
    (within : sequenceSize ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCompatibleDataExpressions.construct tag header (SourceCoreCalls.packArguments codes).expression).rename ξ) value finalStore ∧
      GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld node.type (.namedData tag.owner) faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata, transition⟩ :=
    sequence sourceTrace within
  cases represented with
  | @values sources payloadValues payloads =>
    cases packed
    have projected := receipt.metadata.projected
    rw [receipt.sourceType] at projected
    refine ⟨.inRight .word (.constructed tag (.pair (.word header) (packValues payloadValues))), finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps, maps, worlds, frame, heapMetadata, transition⟩
    · rw [CompatibleExpressionConstructors.construct_rename]; exact CompatibleExpressionConstructors.construct_success tag header evaluated
    · rw [receipt.sourceType]
      exact .value (.constructed (receipt.original.extend extension) (extension.signatures.trans values.registryOwner)
        receipt.selected projected receipt.registered (valuesRep payloads))
  | fault matched =>
    cases packed
    exact ⟨_, finalStore, finalMap, finalWorld, by rw [CompatibleExpressionConstructors.construct_rename]; exact CompatibleExpressionConstructors.construct_failure tag header evaluated,
      .fault matched, finalHeaps, maps, worlds, frame, heapMetadata, transition⟩


include extension in
/-- The original measured constructor argument child supplies the same actual
post. Native result determinism retains the original final store. -/
theorem constructor_reflects_after_sequence (budget : Nat)
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    {instantiation : DataConstructorInstantiation} {ids : List ExpressionId}
    {tag : ConstructorId} {header : Word} {codes : List SourceCoreBasic.LoweredExpr}
    (receipt : CompatibleExpressionConstructors.Header values source id node instantiation tag header codes)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment}
    {canonical actual : Environment} {before : Dynamic.Heap} {store : Store} {ξ : Renaming}
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (form : node.form = .constructor instantiation ids)
    (valid : SourceSemantics.DataConstructorInstantiation.Valid context instantiation)
    (sequence : ProtectedStateExpressionSequenceProducer.Reflects
      (program := program) (context := context) (evidence := evidence) (source := source)
      (environment := environment) (actual := actual) (ξ := ξ) (ids := ids)
      (sourceTypes := instantiation.payloadTypes) (codes := codes) (faults := faults)
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) initial budget)
    {sequenceSize : Nat} {childValue value : Value} {childStore finalStore : Store}
    (child : EvaluationSize sequenceSize actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ) childValue childStore)
    (within : sequenceSize < budget)
    (complete : Evaluates actual store (SourceCoreCompatibleDataExpressions.construct tag header ((SourceCoreCalls.packArguments codes).expression.rename ξ)) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld node.type (.namedData tag.owner) faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨sourceSize, sourceOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
      maps, worlds, frame, metadata, transition⟩ := sequence child within
  cases represented with
  | fault matched =>
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete (CompatibleExpressionConstructors.construct_failure tag header child.sound)
    exact ⟨_, after, finalMap, finalWorld, constructor_intro receipt.metadata form valid trace.sound (.fault _),
      .fault matched, finalHeaps, maps, worlds, frame, metadata, transition⟩
  | values payloads =>
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete (CompatibleExpressionConstructors.construct_success tag header child.sound)
    have projected := receipt.metadata.projected
    rw [receipt.sourceType] at projected
    refine ⟨_, after, finalMap, finalWorld, constructor_intro receipt.metadata form valid trace.sound (.values _),
      ?_, finalHeaps, maps, worlds, frame, metadata, transition⟩
    rw [receipt.sourceType]
    exact .value (.constructed (receipt.original.extend extension) (extension.signatures.trans values.registryOwner)
      receipt.selected projected receipt.registered (valuesRep payloads))

namespace WithReady
open ProtectedStateExpressionOperandTyping
variable (ready : ∀ {index : ProtectedStateTransition.Index}, protocol.State index → Prop)

private theorem forget_reached {initial final : ProtectedStateTransition.Index}
    {first : protocol.State initial} {outcome : Dynamic.ExpressionOutcome}
    (post : ProtectedStateTransition.WithReady.Reached protocol ready outcome first final) :
    ProtectedStateTransition.Transition protocol first final := by
  obtain ⟨reached, related, _⟩ := post
  exact ⟨reached, related⟩

/-- Constructor arguments use only the actual parent's ordered operands and
one whole-sequence producer at the genuine caller input. -/
def SequencePreservesFor (budget : Nat) (scope : SourceCoreLocalCell.Scope) (root : ExpressionNode) : Prop :=
  ∀ {ids types codes}, ids = actualOperandIds root.form →
    DataExpressionSequence.Tree source certificate scope ids types codes →
  ∀ {mapping world administrative environment canonical actual actualContext before store ξ},
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions →
    CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual → RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions →
  ∀ initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩, ready initial →
    ProtectedStateExpressionSequenceProducer.Preserves
      (program := program) (context := context) (evidence := evidence) (source := source)
      (environment := environment) (actual := actual) (ξ := ξ) (ids := ids) (sourceTypes := types)
      (codes := codes) (faults := faults) (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      initial (budget + 1)

/-- Constructor arguments use only the actual parent's ordered operands and
one whole-sequence producer at the genuine caller input. -/
def SequenceReflectsFor (budget : Nat) (scope : SourceCoreLocalCell.Scope) (root : ExpressionNode) : Prop :=
  ∀ {ids types codes}, ids = actualOperandIds root.form →
    DataExpressionSequence.Tree source certificate scope ids types codes →
  ∀ {mapping world administrative environment canonical actual actualContext before store ξ},
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions →
    CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual → RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions →
  ∀ initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩, ready initial →
    ProtectedStateExpressionSequenceProducer.Reflects
      (program := program) (context := context) (evidence := evidence) (source := source)
      (environment := environment) (actual := actual) (ξ := ξ) (ids := ids) (sourceTypes := types)
      (codes := codes) (faults := faults) (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      initial (budget + 1)

include transport extension faithful functionLeaves functionTypes unique missing in
theorem Head.preserves_at (budget size : Nat) (bounded : size ≤ budget)
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    {root : ExpressionNode} (certified : Certificate calls values source context reasonAt certificate scope id lowered)
    (found : source.lookupExpression? id = some root)
    (meaning : ∀ childId, childId ∈ actualOperandIds root.form → ∀ childSize, childSize ≤ budget →
      ProtectedStateTransition.WithReady.PreservesAt protocol ready
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source
        (fun current expression code => expression = childId ∧ certificate current expression code) faults childSize)
    (sequences : SequencePreservesFor (values := values) (source := source) (context := context)
      (registry := registry) (faults := faults) (certificate := certificate) functions program evidence protocol ready budget scope root) :
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after},
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world administrativeContext scope environment canonical ambient.definitions →
    CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual → RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions →
  ∀ initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩, ready initial →
    ExpressionOutcome program size context evidence source environment before id outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld root.type lowered.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨head, data⟩ := certified
  cases data with
  | @constructor node instantiation ids tag header codes receipt form valid sequence =>
    intro mapping world administrative environment canonical actual actualContext before store ξ outcome after environments heaps locals agrees actualTyped installedEntry initialReady trace
    have same := Option.some.inj (receipt.metadata.found.symm.trans found)
    subst root
    obtain ⟨sequenceSize, sourceOutcome, sourceTrace, packed, sequenceSmaller⟩ := RecursiveNamedDataExpressionSourceBounds.constructor_inv receipt.metadata form unique valid trace
    exact constructor_preserves_after_sequence functions extension program evidence protocol (budget + 1) receipt installedEntry
      (sequences (by simp only [form, actualOperandIds]) sequence environments heaps locals agrees actualTyped installedEntry initialReady)
      sourceTrace packed (by omega)

  | @member node base baseNode name index identity branches result child metadata baseMetadata form layout childTree =>
    intro mapping world administrative environment canonical actual actualContext before store ξ outcome after environments heaps locals agrees actualTyped installedEntry initialReady trace
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    have ih := fun n (bound : n ≤ budget) => @meaning base (by rw [form]; change base ∈ [base]; simp) n bound _ _ _ ⟨rfl, childTree⟩
    have raw := RecursiveNamedDataExpressionSourceBounds.member_inv metadata form unique trace
    cases raw with
    | value childTrace selected childSmaller =>
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata, transition⟩ :=
        ih _ (Nat.le_trans (Nat.le_of_lt childSmaller) bounded) baseMetadata.found environments heaps locals agrees actualTyped installedEntry initialReady (.value childTrace)
      cases represented with
      | value payload =>
        obtain ⟨actualMetadata, sources, sourceChild, native, shape, sourceAt, related, completed⟩ := member_success layout payload evaluated
        cases shape
        have same := at_functional sourceAt selected
        subst sourceChild
        exact ⟨_, finalStore, finalMap, finalWorld, by rw [member_rename layout]; exact completed,
          .value related, finalHeaps, maps, worlds, frame, heapMetadata, forget_reached protocol ready transition⟩
    | failure childTrace childSmaller =>
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata, transition⟩ :=
        ih _ (Nat.le_trans (Nat.le_of_lt childSmaller) bounded) baseMetadata.found environments heaps locals agrees actualTyped installedEntry initialReady (.fault childTrace)
      cases represented with
      | fault matched =>
        exact ⟨_, finalStore, finalMap, finalWorld, by rw [member_rename layout]; exact LanguageResult.bind_failure _ evaluated,
          .fault matched, finalHeaps, maps, worlds, frame, heapMetadata, forget_reached protocol ready transition⟩
    | shape childTrace invalid childSmaller =>
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, _⟩ :=
        ih _ (Nat.le_trans (Nat.le_of_lt childSmaller) bounded) baseMetadata.found environments heaps locals agrees actualTyped installedEntry initialReady (.value childTrace)
      cases represented with
      | value payload =>
        obtain ⟨_, _, _, _, shape, _⟩ := member_success layout payload evaluated
        subst_vars
        exact False.elim (invalid .intro)
    | position childTrace missing childSmaller =>
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, _⟩ :=
        ih _ (Nat.le_trans (Nat.le_of_lt childSmaller) bounded) baseMetadata.found environments heaps locals agrees actualTyped installedEntry initialReady (.value childTrace)
      cases represented with
      | value payload =>
        obtain ⟨_, _, _, _, shape, selected, _⟩ := member_success layout payload evaluated
        cases shape
        exact False.elim (missing_excludes missing selected)

  | @index node base key baseNode keyNode layout comparison first second header keyFound form sourceType firstTree secondTree =>
    intro mapping world administrative environment canonical actual actualContext before store ξ outcome after
      environments heaps locals agrees actualTyped installedEntry initialReady trace
    have same := Option.some.inj (header.metadata.found.symm.trans found)
    subst root
    have firstIH := fun n (bound : n ≤ budget) => @meaning base (by rw [form]; change base ∈ [base, key]; simp) n bound _ _ _ ⟨rfl, firstTree⟩
    have secondIH := fun n (bound : n ≤ budget) => @meaning key (by rw [form]; change key ∈ [base, key]; simp) n bound _ _ _ ⟨rfl, secondTree⟩
    rcases (RecursiveNamedDataExpressionSourceBounds.index_inv header.metadata form unique trace).split with ⟨reason, baseSize, rfl, failed, baseSmaller⟩ | ⟨baseSource, middle, baseSize, baseTrace, baseSmaller, tail⟩
    · obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, transition⟩ :=
        firstIH _ (Nat.le_trans (Nat.le_of_lt baseSmaller) bounded) header.baseMetadata.found environments heaps locals agrees actualTyped installedEntry initialReady (.fault failed)
      cases represented with
      | fault matched =>
        refine ⟨_, finalStore, finalMap, finalWorld, ?_, .fault matched, finalHeaps, maps, worlds, frame, metadata, forget_reached protocol ready transition⟩
        rw [index_rename comparison header.registered header.comparisonType]
        exact LanguageResult.bind_failure _ evaluated
    · obtain ⟨value, middleStore, middleMap, middleWorld, firstEval, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstTransition⟩ :=
        firstIH _ (Nat.le_trans (Nat.le_of_lt baseSmaller) bounded) header.baseMetadata.found environments heaps locals agrees actualTyped installedEntry initialReady (.value baseTrace)
      cases represented with
      | @value _ baseValue baseRep =>
        obtain ⟨middleState, firstRelated, firstReady⟩ := firstTransition
        have keyEnvironment := RuntimeEnvironmentHasTypes.cons baseRep.runtime_hasType (actualTyped.weaken firstWorlds)
        rcases tail with ⟨reason, keySize, rfl, failed, keySmaller⟩ | ⟨keySource, keySize, keyTrace, keySmaller, terminal⟩
        · obtain ⟨value, finalStore, finalMap, finalWorld, secondEval, represented, finalHeaps, maps, worlds, frame, metadata, transition⟩ :=
            secondIH _ (Nat.le_trans (Nat.le_of_lt keySmaller) bounded) keyFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (agree_prefix agrees _) keyEnvironment middleState (firstReady _ rfl) (.fault failed)
          cases represented with
          | fault matched =>
            obtain ⟨finalState, secondRelated, _⟩ := transition
            refine ⟨_, finalStore, finalMap, finalWorld, ?_, .fault matched, finalHeaps,
              firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata, ⟨finalState, protocol.trans firstRelated secondRelated⟩⟩
            rw [index_rename comparison header.registered header.comparisonType]
            rw [rename_prefix] at secondEval
            exact LanguageResult.bind_success _ firstEval (LanguageResult.bind_failure _ secondEval)
        · obtain ⟨value, keyStore, keyMap, keyWorld, secondEval, represented, keyHeaps, keyMaps, keyWorlds, keyFrame, keyMetadata, keyTransition⟩ :=
            secondIH _ (Nat.le_trans (Nat.le_of_lt keySmaller) bounded) keyFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (agree_prefix agrees _) keyEnvironment middleState (firstReady _ rfl) (.value keyTrace)
          cases represented with
          | @value _ keyValue keyRep =>
            obtain ⟨actualOutcome, result, finalStore, finalWorld, terminal', related, lookup, finalHeaps, worlds, frame, uniqueResult⟩ :=
              CompatibleGeneralIndex.finish header sourceType faithful functionLeaves functionTypes (baseRep.extend (.refl _) keyMaps keyWorlds) keyRep
                (actualTyped.weaken (firstWorlds.trans keyWorlds)) keyHeaps (reasonAt id) (missing id)
            obtain ⟨keyState, keyRelated, _⟩ := keyTransition
            obtain ⟨finalState, terminalRelated⟩ := transport.transition protocol keyState (.refl _) worlds frame (.refl _)
            have same := uniqueResult outcome terminal
            subst actualOutcome
            refine ⟨result, finalStore, keyMap, finalWorld, ?_, related, finalHeaps,
              firstMaps.trans keyMaps, (firstWorlds.trans keyWorlds).trans worlds,
              (firstFrame.trans keyFrame).trans frame, firstMetadata.trans keyMetadata, ⟨finalState, protocol.trans firstRelated (protocol.trans keyRelated terminalRelated)⟩⟩
            rw [index_rename comparison header.registered header.comparisonType]
            rw [rename_prefix] at secondEval
            apply SourceCoreCompatibleDataExpressions.index_completed layout (reasonAt id) firstEval secondEval
            simpa only [CompatibleMapping.Transport.expression_weaken] using lookup



include transport extension faithful functionLeaves functionTypes missing in
theorem Head.reflects_raw_at (budget size : Nat) (bounded : size ≤ budget)
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    {root : ExpressionNode} (certified : Certificate calls values source context reasonAt certificate scope id lowered)
    (found : source.lookupExpression? id = some root)
    (meaning : ∀ childId, childId ∈ actualOperandIds root.form → ∀ childSize, childSize ≤ budget →
      ProtectedStateTransition.WithReady.ReflectsAt protocol ready
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source
        (fun current expression code => expression = childId ∧ certificate current expression code) faults childSize)
    (sequences : SequenceReflectsFor (values := values) (source := source) (context := context)
      (registry := registry) (faults := faults) (certificate := certificate) functions program evidence protocol ready budget scope root) :
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore},
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world administrativeContext scope environment canonical ambient.definitions →
    CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual → RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions →
  ∀ initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩, ready initial →
    EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore →
    ∃ outcome after finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld root.type lowered.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨head, data⟩ := certified
  cases data with
  | @constructor node instantiation ids tag header codes receipt form valid sequence =>
    intro mapping world administrative environment canonical actual actualContext before store ξ value finalStore environments heaps locals agrees actualTyped installedEntry initialReady evaluated
    have same := Option.some.inj (receipt.metadata.found.symm.trans found)
    subst root
    rw [CompatibleExpressionConstructors.construct_rename] at evaluated
    have complete := evaluated.sound
    cases evaluated with
    | caseLeft childEvaluation branch =>
      exact constructor_reflects_after_sequence functions extension program evidence protocol (budget + 1) receipt installedEntry form valid
        (sequences (by simp only [form, actualOperandIds]) sequence environments heaps locals agrees actualTyped installedEntry initialReady)
        childEvaluation (by omega) complete
    | caseRight childEvaluation branch =>
      exact constructor_reflects_after_sequence functions extension program evidence protocol (budget + 1) receipt installedEntry form valid
        (sequences (by simp only [form, actualOperandIds]) sequence environments heaps locals agrees actualTyped installedEntry initialReady)
        childEvaluation (by omega) complete

  | @member node base baseNode name index identity branches result child metadata baseMetadata form layout childTree =>
    intro mapping world administrative environment canonical actual actualContext before store ξ value finalStore environments heaps locals agrees actualTyped installedEntry initialReady evaluated
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    have ih := fun n (bound : n ≤ budget) => @meaning base (by rw [form]; change base ∈ [base]; simp) n bound _ _ _ ⟨rfl, childTree⟩
    rw [member_rename layout] at evaluated
    have complete := evaluated.sound
    cases evaluated with
    | caseLeft baseEvaluation branch =>
      obtain ⟨childSourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata, transition⟩ :=
        ih _ (by omega) baseMetadata.found environments heaps locals agrees actualTyped installedEntry initialReady baseEvaluation
      cases represented with
      | fault matched =>
        have expected := LanguageResult.bind_failure result baseEvaluation.sound (body := .matchData identity (LanguageResult.resultType result) (.var 0) branches)
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete expected
        cases trace with
        | fault failed =>
          exact ⟨_, after, finalMap, finalWorld, member_intro metadata form (.failure failed.sound), .fault matched,
            finalHeaps, maps, worlds, frame, heapMetadata, forget_reached protocol ready transition⟩
    | caseRight baseEvaluation branch =>
      obtain ⟨childSourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata, transition⟩ :=
        ih _ (by omega) baseMetadata.found environments heaps locals agrees actualTyped installedEntry initialReady baseEvaluation
      cases represented with
      | value payload =>
        obtain ⟨actualMetadata, sources, selected, native, shape, sourceAt, related, expected⟩ := member_success layout payload baseEvaluation.sound
        subst_vars
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete expected
        cases trace with
        | value childTrace =>
          exact ⟨_, after, finalMap, finalWorld, member_intro metadata form (.value childTrace.sound sourceAt), .value related,
            finalHeaps, maps, worlds, frame, heapMetadata, forget_reached protocol ready transition⟩

  | @index node base key baseNode keyNode layout comparison first second header keyFound form sourceType firstTree secondTree =>
    intro mapping world administrative environment canonical actual actualContext before store ξ value finalStore
      environments heaps locals agrees actualTyped installedEntry initialReady evaluated
    have same := Option.some.inj (header.metadata.found.symm.trans found)
    subst root
    have firstIH := fun n (bound : n ≤ budget) => @meaning base (by rw [form]; change base ∈ [base, key]; simp) n bound _ _ _ ⟨rfl, firstTree⟩
    have secondIH := fun n (bound : n ≤ budget) => @meaning key (by rw [form]; change key ∈ [base, key]; simp) n bound _ _ _ ⟨rfl, secondTree⟩
    rw [index_rename comparison header.registered header.comparisonType] at evaluated
    have complete := evaluated.sound
    cases evaluated with
    | caseLeft baseEvaluation branch =>
      obtain ⟨childSourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, transition⟩ :=
        firstIH _ (by omega) header.baseMetadata.found environments heaps locals agrees actualTyped installedEntry initialReady baseEvaluation
      cases represented with
      | fault matched =>
        have expected := LanguageResult.bind_failure layout.valueType baseEvaluation.sound (body :=
          LanguageResult.bind layout.valueType ((second.expression.rename ξ).weakenAt 0)
            (SourceCoreMappingWithDefault.lookup layout (reasonAt id) (comparison.expression.weakenAt 0 |>.weakenAt 0) (.var 1) (.var 0)))
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete expected
        cases trace with
        | fault failed => exact ⟨_, after, finalMap, finalWorld, index_intro header.metadata form (.baseFailure failed.sound),
            .fault matched, finalHeaps, maps, worlds, frame, metadata, forget_reached protocol ready transition⟩
    | caseRight baseEvaluation branch =>
      obtain ⟨childSourceSize, outcome, middle, middleMap, middleWorld, trace, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstTransition⟩ :=
        firstIH _ (by omega) header.baseMetadata.found environments heaps locals agrees actualTyped installedEntry initialReady baseEvaluation
      cases represented with
      | @value baseSource baseValue baseRep =>
        cases trace with
        | value baseTrace =>
          obtain ⟨middleState, firstRelated, firstReady⟩ := firstTransition
          have keyEnvironment := RuntimeEnvironmentHasTypes.cons baseRep.runtime_hasType (actualTyped.weaken firstWorlds)
          cases branch with
          | caseLeft keyEvaluation ignored =>
            rw [← rename_prefix] at keyEvaluation
            obtain ⟨childSourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, transition⟩ :=
              secondIH _ (by omega) keyFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                (agree_prefix agrees _) keyEnvironment middleState (firstReady _ rfl) keyEvaluation
            cases represented with
            | fault matched =>
              obtain ⟨finalState, secondRelated, _⟩ := transition
              rw [rename_prefix] at keyEvaluation
              have expected := LanguageResult.bind_success layout.valueType baseEvaluation.sound
                (LanguageResult.bind_failure layout.valueType keyEvaluation.sound (body :=
                  SourceCoreMappingWithDefault.lookup layout (reasonAt id) (comparison.expression.weakenAt 0 |>.weakenAt 0) (.var 1) (.var 0)))
              obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete expected
              cases trace with
              | fault failed => exact ⟨_, after, finalMap, finalWorld, index_intro header.metadata form (.keyFailure baseTrace.sound failed.sound),
                  .fault matched, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata, ⟨finalState, protocol.trans firstRelated secondRelated⟩⟩
          | caseRight keyEvaluation lookupEvaluation =>
            rw [← rename_prefix] at keyEvaluation
            obtain ⟨keySourceSize, outcome, after, keyMap, keyWorld, trace, represented, keyHeaps, keyMaps, keyWorlds, keyFrame, keyMetadata, keyTransition⟩ :=
              secondIH _ (by omega) keyFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                (agree_prefix agrees _) keyEnvironment middleState (firstReady _ rfl) keyEvaluation
            cases represented with
            | @value keySource keyValue keyRep =>
              obtain ⟨outcome, result, endStore, finalWorld, terminal, related, lookup, finalHeaps, worlds, frame, uniqueResult⟩ :=
                CompatibleGeneralIndex.finish header sourceType faithful functionLeaves functionTypes (baseRep.extend (.refl _) keyMaps keyWorlds) keyRep
                  (actualTyped.weaken (firstWorlds.trans keyWorlds)) keyHeaps (reasonAt id) (missing id)
              rw [rename_prefix] at keyEvaluation
              have expected := SourceCoreCompatibleDataExpressions.index_completed (comparison := comparison.expression) layout (reasonAt id) baseEvaluation.sound keyEvaluation.sound
                (by simpa only [CompatibleMapping.Transport.expression_weaken] using lookup)
              obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete expected
              obtain ⟨keyState, keyRelated, _⟩ := keyTransition
              obtain ⟨finalState, terminalRelated⟩ := transport.transition protocol keyState (.refl _) worlds frame (.refl _)
              cases trace with
              | value keyTrace =>
                exact ⟨outcome, after, keyMap, finalWorld, index_intro header.metadata form (terminal.trace baseTrace.sound keyTrace.sound),
                  related, finalHeaps, firstMaps.trans keyMaps, (firstWorlds.trans keyWorlds).trans worlds,
                  (firstFrame.trans keyFrame).trans frame, firstMetadata.trans keyMetadata, ⟨finalState, protocol.trans firstRelated (protocol.trans keyRelated terminalRelated)⟩⟩





end WithReady

include transport extension faithful functionLeaves functionTypes unique missing in
theorem preserves_at (budget size : Nat) (bounded : size ≤ budget)
    (meaning : ∀ childSize, childSize ≤ budget → ProtectedStateTransition.PreservesAt protocol (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source certificate faults childSize)
 :
    ProtectedStateTransition.PreservesAt protocol (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Certificate calls values source context reasonAt certificate) faults size := by
  intro scope id lowered ⟨head, data⟩ root found mapping world administrative environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees actualTyped initial execution
  cases data with
  | @constructor node instantiation ids tag header codes receipt form valid sequence =>
    have same := Option.some.inj (receipt.metadata.found.symm.trans found)
    subst root
    obtain ⟨sequenceSize, sourceOutcome, sourceTrace, packed, sequenceSmaller⟩ := RecursiveNamedDataExpressionSourceBounds.constructor_inv receipt.metadata form unique valid execution
    exact constructor_preserves_after_sequence functions extension program evidence protocol (budget + 1) receipt initial
      (ProtectedStateExpressionSequenceProducer.Preserves.of_uniform initial (budget + 1) sequence
        (fun n bound => ProtectedStateTransition.SequenceBridge.preserves_at protocol (meaning n (by omega)))
        environments heaps locals agrees actualTyped) sourceTrace packed (by omega)
  | member metadata baseMetadata form layout child =>
    have data := Data.member (calls := calls) (context := context) (reasonAt := reasonAt) metadata baseMetadata form layout child
    exact WithReady.Head.preserves_at functions extension faithful functionLeaves functionTypes program evidence unique missing
      protocol transport (fun _ => True) budget size bounded ⟨_, data⟩ found
      (fun child member n bound => ProtectedStateTransition.WithReady.PreservesAt.of_stateful protocol
        (fun {childScope expression code} (entry : expression = child ∧ certificate childScope expression code) => meaning n bound entry.2))
      (fun {ids types codes} same tree {mapping world administrative environment canonical actual actualContext before store ξ}
          env hp lc layout typed state _ =>
        ProtectedStateExpressionSequenceProducer.Preserves.of_uniform state (budget + 1) tree
          (fun n bound => ProtectedStateTransition.SequenceBridge.preserves_at protocol (meaning n (by omega)))
          env hp lc layout typed)
      environments heaps locals agrees actualTyped initial True.intro execution
  | index receipt keyFound form sourceType first second =>
    have data := Data.index (calls := calls) (context := context) (reasonAt := reasonAt) receipt keyFound form sourceType first second
    exact WithReady.Head.preserves_at functions extension faithful functionLeaves functionTypes program evidence unique missing
      protocol transport (fun _ => True) budget size bounded ⟨_, data⟩ found
      (fun child member n bound => ProtectedStateTransition.WithReady.PreservesAt.of_stateful protocol
        (fun {childScope expression code} (entry : expression = child ∧ certificate childScope expression code) => meaning n bound entry.2))
      (fun {ids types codes} same tree {mapping world administrative environment canonical actual actualContext before store ξ}
          env hp lc layout typed state _ =>
        ProtectedStateExpressionSequenceProducer.Preserves.of_uniform state (budget + 1) tree
          (fun n bound => ProtectedStateTransition.SequenceBridge.preserves_at protocol (meaning n (by omega)))
          env hp lc layout typed)
      environments heaps locals agrees actualTyped initial True.intro execution

include transport extension faithful functionLeaves functionTypes missing in
private theorem reflects_raw_at (budget size : Nat) (bounded : size ≤ budget)
    (meaning : ∀ childSize, childSize ≤ budget → ProtectedStateTransition.ReflectsAt protocol (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source certificate faults childSize)
 :
    ReflectsRawAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Certificate calls values source context reasonAt certificate) faults protocol := by
  intro scope id lowered ⟨head, data⟩ root found mapping world administrative environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees actualTyped initial execution
  cases data with
  | @constructor node instantiation ids tag header codes receipt form valid sequence =>
    have same := Option.some.inj (receipt.metadata.found.symm.trans found)
    subst root
    rw [CompatibleExpressionConstructors.construct_rename] at execution
    have complete := execution.sound
    cases execution with
    | caseLeft childEvaluation branch =>
      exact constructor_reflects_after_sequence functions extension program evidence protocol (budget + 1) receipt initial form valid
        (ProtectedStateExpressionSequenceProducer.Reflects.of_uniform initial (budget + 1) sequence
          (fun n bound => ProtectedStateTransition.SequenceBridge.reflects_at protocol (meaning n (by omega)))
          environments heaps locals agrees actualTyped) childEvaluation (by omega) complete
    | caseRight childEvaluation branch =>
      exact constructor_reflects_after_sequence functions extension program evidence protocol (budget + 1) receipt initial form valid
        (ProtectedStateExpressionSequenceProducer.Reflects.of_uniform initial (budget + 1) sequence
          (fun n bound => ProtectedStateTransition.SequenceBridge.reflects_at protocol (meaning n (by omega)))
          environments heaps locals agrees actualTyped) childEvaluation (by omega) complete
  | member metadata baseMetadata form layout child =>
    have data := Data.member (calls := calls) (context := context) (reasonAt := reasonAt) metadata baseMetadata form layout child
    exact WithReady.Head.reflects_raw_at functions extension faithful functionLeaves functionTypes program evidence missing
      protocol transport (fun _ => True) budget size bounded ⟨_, data⟩ found
      (fun child member n bound => ProtectedStateTransition.WithReady.ReflectsAt.of_stateful protocol
        (fun {childScope expression code} (entry : expression = child ∧ certificate childScope expression code) => meaning n bound entry.2))
      (fun {ids types codes} same tree {mapping world administrative environment canonical actual actualContext before store ξ}
          env hp lc layout typed state _ =>
        ProtectedStateExpressionSequenceProducer.Reflects.of_uniform state (budget + 1) tree
          (fun n bound => ProtectedStateTransition.SequenceBridge.reflects_at protocol (meaning n (by omega)))
          env hp lc layout typed)
      environments heaps locals agrees actualTyped initial True.intro execution
  | index receipt keyFound form sourceType first second =>
    have data := Data.index (calls := calls) (context := context) (reasonAt := reasonAt) receipt keyFound form sourceType first second
    exact WithReady.Head.reflects_raw_at functions extension faithful functionLeaves functionTypes program evidence missing
      protocol transport (fun _ => True) budget size bounded ⟨_, data⟩ found
      (fun child member n bound => ProtectedStateTransition.WithReady.ReflectsAt.of_stateful protocol
        (fun {childScope expression code} (entry : expression = child ∧ certificate childScope expression code) => meaning n bound entry.2))
      (fun {ids types codes} same tree {mapping world administrative environment canonical actual actualContext before store ξ}
          env hp lc layout typed state _ =>
        ProtectedStateExpressionSequenceProducer.Reflects.of_uniform state (budget + 1) tree
          (fun n bound => ProtectedStateTransition.SequenceBridge.reflects_at protocol (meaning n (by omega)))
          env hp lc layout typed)
      environments heaps locals agrees actualTyped initial True.intro execution

include transport extension faithful functionLeaves functionTypes missing in
theorem reflects_at (budget size : Nat) (bounded : size ≤ budget)
    (meaning : ∀ childSize, childSize ≤ budget → ProtectedStateTransition.ReflectsAt protocol
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source certificate faults childSize) :
    ProtectedStateTransition.ReflectsAt protocol (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Certificate calls values source context reasonAt certificate) faults size := by
  intro scope id lowered head node found mapping world administrative environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees actualTyped installedEntry completed
  obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, transition⟩ :=
    reflects_raw_at functions extension faithful functionLeaves functionTypes program evidence missing protocol transport budget size bounded meaning head found environments heaps locals agrees actualTyped installedEntry completed
  obtain ⟨sourceSize, sized⟩ := ExpressionOutcome.has_size trace
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, sized, represented, finalHeaps, maps, worlds, frame, metadata, transition⟩

end Stateful

variable {calls : CallHeads} {certificate : GenericExpressionMeaning.Certificate}
  {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)

include transport extension faithful functionLeaves functionTypes unique missing in
theorem preserves_at (budget size : Nat) (bounded : size ≤ budget)
    (meaning : ∀ childSize, childSize ≤ budget → RecursiveNamedBoundedContracts.PreservesAt childSize (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source certificate faults entry)
 :
    RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Certificate calls values source context reasonAt certificate) faults entry := by
  intro scope id lowered head node found mapping world administrative environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees actualTyped installedEntry trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, _⟩ :=
    Stateful.preserves_at functions extension faithful functionLeaves functionTypes program evidence unique missing
      (ProtectedStatePlaceAssignment.legacyProtocol entry) (ProtectedStatePlaceAssignment.legacyTransport transport) budget size bounded
      (fun childSize bound => ProtectedStatePlaceAssignment.legacy_preserves transport (meaning childSize bound))
      head found environments heaps locals agrees actualTyped ⟨installedEntry⟩ trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩

include transport extension faithful functionLeaves functionTypes missing in
theorem reflects_at (budget size : Nat) (bounded : size ≤ budget)
    (meaning : ∀ childSize, childSize ≤ budget → RecursiveNamedBoundedContracts.ReflectsAt childSize
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source certificate faults entry) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Certificate calls values source context reasonAt certificate) faults entry := by
  intro scope id lowered head node found mapping world administrative environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees actualTyped installedEntry completed
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, _⟩ :=
    Stateful.reflects_at functions extension faithful functionLeaves functionTypes program evidence missing
      (ProtectedStatePlaceAssignment.legacyProtocol entry) (ProtectedStatePlaceAssignment.legacyTransport transport) budget size bounded
      (fun childSize bound => ProtectedStatePlaceAssignment.legacy_reflects transport (meaning childSize bound))
      head found environments heaps locals agrees actualTyped ⟨installedEntry⟩ completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedDataExpressionHeadBounds
