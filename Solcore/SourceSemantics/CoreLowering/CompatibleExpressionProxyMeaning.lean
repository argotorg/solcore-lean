import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionProxyCertificates
import Solcore.SourceSemantics.CoreLowering.TypedGenericExpressionMeaning

/-! Ordinary proxy expressions retain their raw inner type, including staging
annotations inside it. A registered Word header carries that metadata while
the native constructor uses its checked nominal layout. Both heaps are unchanged. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionProxies
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CompatibleExpressionPrimitives

variable {values : ValuesContext} {source : TypedSource} {id : ExpressionId} {node : ExpressionNode}
  {inner : TypeSystem.Ty} {owner : DataTypeId} {header : Word}

/-- A leaf has the registered native type under any actual ambient suffix. -/
theorem Header.hasType (receipt : Header values source id node inner owner header)
    (ambient : AmbientDefinitions values.checked.catalog.definitions) (context : Core.Context) :
    HasType context (LanguageResult.success (.construct ⟨owner, 0⟩ (.word header)))
      (LanguageResult.resultType (.namedData owner)) ambient.definitions :=
  .inRight .word (.construct (ambient.basePrefix.constructor_lookup receipt.registered) .word)

theorem Header.source_evaluates (receipt : Header values source id node inner owner header)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (environment : Dynamic.Environment) (heap : Dynamic.Heap) :
    Dynamic.ExpressionEvaluates program context evidence source environment heap id (.proxy inner) heap := by
  apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound receipt.metadata.found)
  · rw [receipt.form, receipt.metadata.requirements, receipt.metadata.coercions]
    exact .proxy rfl
  · rw [receipt.metadata.coercions]; exact .nil

theorem Header.source_outcome (receipt : Header values source id node inner owner header)
    (unique : NodeOccurrencesUnique source)
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}
    (trace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after) :
    outcome = .value (.proxy inner) ∧ after = before := by
  cases trace with
  | value evaluation =>
    have raw := evaluation_raw unique (lookupExpression?_sound receipt.metadata.found)
      (by intros; simp [receipt.form]) receipt.metadata.coercions evaluation
    rw [receipt.form] at raw
    cases raw
    exact ⟨rfl, rfl⟩
  | fault failed =>
    have raw := fault_raw unique (lookupExpression?_sound receipt.metadata.found)
      (by intros; simp [receipt.form]) receipt.metadata.coercions failed
    rw [receipt.form] at raw
    cases raw

theorem Header.represents (receipt : Header values source id node inner owner header)
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
    (extension : SourceCoreRawMetadata.Extends values.registry registry)
    (mapping : LocationMap) (world : StoreTyping) :
    ValueRep values.checked registry functions mapping world node.type (.proxy inner)
      (.constructed ⟨owner, 0⟩ (.word header)) (.namedData owner) := by
  rw [receipt.sourceType]
  exact .proxy (receipt.original.extend extension) receipt.identity receipt.registered

theorem Header.native_evaluates (_receipt : Header values source id node inner owner header)
    (environment : Environment) (store : Store) (ξ : Renaming) :
    Evaluates environment store
      ((LanguageResult.success (.construct ⟨owner, 0⟩ (.word header))).rename ξ)
      (.inRight .word (.constructed ⟨owner, 0⟩ (.word header))) store := .inRight (.construct .word)

/-- Accepted proxy certificates supply their whole expression meaning. No
child semantics, source typing inference or runtime metadata resolver is used. -/
theorem preserves {values : ValuesContext} {source : TypedSource}
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
    (extension : SourceCoreRawMetadata.Extends values.registry registry)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (unique : NodeOccurrencesUnique source) (faults : FunctionCalls.FaultRep) :
    TypedGenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Certificate values source) faults := by
  intro scope id lowered certificate node found mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees actualTyped trace
  cases certificate with
  | @proxy other inner owner header receipt =>
    have same := Option.some.inj (receipt.metadata.found.symm.trans found)
    subst other
    obtain ⟨rfl, rfl⟩ := receipt.source_outcome unique trace
    exact ⟨_, store, mapping, world, receipt.native_evaluates actual store ξ,
      .value (receipt.represents functions extension mapping world), heaps,
      .refl _, .refl _, .refl _ _, .refl _⟩

/-- Every completed proxy evaluation returns the registered raw header and
constructs its independent source trace, with both stores preserved. -/
theorem reflects {values : ValuesContext} {source : TypedSource}
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
    (extension : SourceCoreRawMetadata.Extends values.registry registry)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (faults : FunctionCalls.FaultRep) :
    TypedGenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Certificate values source) faults := by
  intro scope id lowered certificate node found mapping world administrative environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals agrees actualTyped evaluated
  cases certificate with
  | @proxy other inner owner header receipt =>
    have same := Option.some.inj (receipt.metadata.found.symm.trans found)
    subst other
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic (receipt.native_evaluates actual store ξ) evaluated
    exact ⟨.value (.proxy inner), before, mapping, world,
      .value (receipt.source_evaluates program context evidence environment before),
      .value (receipt.represents functions extension mapping world), heaps,
      .refl _, .refl _, .refl _ _, .refl _⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionProxies
