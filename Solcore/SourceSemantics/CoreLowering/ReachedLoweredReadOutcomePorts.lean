import Solcore.SourceSemantics.CoreLowering.ReachedExpressionExtendedFaultPaths

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
