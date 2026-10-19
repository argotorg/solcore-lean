import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalMaterializedCode
import Solcore.SourceSemantics.CoreLowering.EmptySourceSubstitution

/-! In a named lexical context, the actual local read matcher identifies the
complete candidate substitution. The checked candidate's original source and
the allocation's descriptor source then determine the materialized body. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalNamedMaterialization
open Core Frontend SourceInference TypeSystem
open GeneralizedLocalInstanceCompilation (Inputs)
open GeneralizedLocalLambdaCompilation (Packet)

variable {catalog : SourceCoreLocalPolymorphism.Catalog} {caller : SourceCoreLocalPolymorphism.Key}
  {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {reason : Core.Word}
  {lowered : SourceCoreBasic.LoweredExpr}

theorem lookup_eq
    (receipt : GeneralizedLocalReadReceipts.Certificate catalog caller [] source scope id reason lowered)
    {function : Dynamic.GeneralizedClosure} {context : Context}
    {callerEvidence produced : Dynamic.EvidenceEnvironment} {actual : TypeSystem.Ty}
    {requirements : List RequirementId} {semantic : Substitution}
    (instantiation : Dynamic.LocalSchemeRuntimeInstantiation context callerEvidence
      function.binder actual requirements semantic produced)
    (sameScheme : function.binder.scheme = receipt.binding.binder.scheme)
    (sameType : actual = receipt.node.rawType) :
    ∀ metavariable, semantic.lookup? metavariable = receipt.candidate.origin.substitution.lookup? metavariable := by
  have matched := receipt.matched
  simp only [EmptySourceSubstitution.scheme, EmptySourceSubstitution.type] at matched
  have originalType : receipt.original.rawType = receipt.node.rawType := by
    simpa only [EmptySourceSubstitution.type] using receipt.rawType
  have actualMatch : SourceSpecialization.matchClosedSchemeInstance? function.binder.scheme actual =
      some receipt.child := by
    simpa only [sameScheme, sameType, originalType] using matched
  have key : receipt.candidate.origin.substitution = receipt.child := by
    have identity : receipt.child.compose [] = receipt.child := by
      simp [Substitution.compose, List.filter_eq_self]
    exact receipt.candidate_key.trans identity
  intro metavariable
  rw [key]
  exact CallableClosedSchemeSubstitutionAgreement.runtime_instantiation_lookup_eq actualMatch instantiation metavariable

/-- These source identities are supplied by the actual declaration site and
the statically checked catalog row, while the substitution comes from Source. -/
theorem source_eq
    (receipt : GeneralizedLocalReadReceipts.Certificate catalog caller [] source scope id reason lowered)
    {function : Dynamic.GeneralizedClosure} {context : Context}
    {callerEvidence produced : Dynamic.EvidenceEnvironment} {actual : TypeSystem.Ty}
    {requirements : List RequirementId} {semantic : Substitution}
    (instantiation : Dynamic.LocalSchemeRuntimeInstantiation context callerEvidence
      function.binder actual requirements semantic produced)
    (sameScheme : function.binder.scheme = receipt.binding.binder.scheme)
    (sameType : actual = receipt.node.rawType)
    (descriptorSource : function.source = receipt.binding.source)
    (candidateSource : receipt.candidate.origin.source = receipt.binding.source)
    {inputs : Inputs} {raw : Core.Expr}
    (packet : Packet inputs receipt.candidate raw) :
    (function.instantiate semantic (produced ++ callerEvidence.applySubstitution semantic)).source =
      packet.original.emission.prepared.source := by
  change function.source.applySubstitution semantic = _
  rw [GeneralizedLocalLambdaEmissionFacts.Emission.source]
  have same := CallableFlexibleSubstitutionAgreement.typedSource_congr
    (lookup_eq receipt instantiation sameScheme sameType) function.source
  simpa only [descriptorSource, candidateSource] using same

/-- The Source capture occurrence and the accepted emitted lambda determine
the exact parameter, result and statement header of the materialized closure. -/
theorem header
    {function : Dynamic.GeneralizedClosure} {semantic : Substitution} {evidence : Dynamic.EvidenceEnvironment}
    {inputs : Inputs} {candidate : SourceCoreLocalPolymorphism.Instance} {raw : Core.Expr}
    (packet : Packet inputs candidate raw)
    (captures : Dynamic.GeneralizedClosureCaptures function.definitionContext function.source function.captured
      function.binder function.initializer function)
    (unique : NodeOccurrencesUnique function.source)
    (initializer : function.initializer = inputs.initializer)
    (sourceEq : (function.instantiate semantic evidence).source = packet.original.emission.prepared.source) :
    (function.instantiate semantic evidence).parameters = packet.parameters ∧
    (function.instantiate semantic evidence).resultType = packet.result ∧
    (function.instantiate semantic evidence).body = packet.statements := by
  obtain ⟨node, occurrence, form, _⟩ := captures.occurrence
  have found := lookupExpression?_complete unique occurrence
  have substituted := SourceTypedRuntime.TypedSource.lookupExpression?_applySubstitution
    function.source semantic function.initializer node found
  change (function.instantiate semantic evidence).source.lookupExpression? function.initializer = _ at substituted
  simp only [sourceEq, initializer] at substituted
  have sameNode := Option.some.inj (substituted.symm.trans packet.found)
  have sameForm := (congrArg ExpressionNode.form sameNode).trans packet.form
  simp only [ExpressionNode.applySubstitution, form, ExpressionForm.applySubstitution] at sameForm
  exact ExpressionForm.lambda.inj sameForm

/-- The actual named read, its retained capture row and accepted compiler
packet construct ordinary raw Code for the exact materialized Source closure. -/
theorem code_at_read
    (receipt : GeneralizedLocalReadReceipts.Certificate catalog caller [] source scope id reason lowered)
    {function : Dynamic.GeneralizedClosure} {context : Context}
    {callerEvidence produced : Dynamic.EvidenceEnvironment} {actualType : TypeSystem.Ty}
    {requirements : List RequirementId} {semantic : Substitution}
    (instantiation : Dynamic.LocalSchemeRuntimeInstantiation context callerEvidence
      function.binder actualType requirements semantic produced)
    (sameScheme : function.binder.scheme = receipt.binding.binder.scheme)
    (sameType : actualType = receipt.node.rawType)
    (descriptorSource : function.source = receipt.binding.source)
    (candidateSource : receipt.candidate.origin.source = receipt.binding.source)
    {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
    {inputs : Inputs} {raw : Core.Expr}
    (packet : Packet inputs receipt.candidate raw)
    (indexed : GeneralizedLocalLambdaGeneration.Indexed prepared packet)
    (captures : Dynamic.GeneralizedClosureCaptures function.definitionContext function.source function.captured
      function.binder function.initializer function)
    (unique : NodeOccurrencesUnique function.source)
    (initializer : function.initializer = inputs.initializer)
    {mapping : GeneralHeap.LocationMap} {world : StoreTyping} {actual : Core.Environment}
    (captured : CallableIndexedLambdaValues.Captures prepared mapping world inputs.scope function.captured actual)
    (typed : HasType (SourceCoreLocalCell.coreContext inputs.scope ++ captured.administrative)
      raw receipt.candidate.type prepared.layouts.definitions)
    (profile : checked.catalog.callableContracts = true)
    (native : CallableIndexedHistory.NativeFrame) :
    let instantiated := function.instantiate semantic (produced ++ callerEvidence.applySubstitution semantic)
    ∃ code : CallableIndexedLambdaValues.Code prepared instantiated inputs.scope captured.administrative,
      code.compilation = GeneralizedLocalLambdaCompilation.context inputs packet.original.emission.prepared ∧
      code.active = packet.original.emission.prepared.substitution ∧
      code.id = inputs.initializer ∧ code.lowered = packet.original.lowered ∧
      code.policy = GeneralizedLocalLambdaCompilation.policy inputs packet.original.emission.prepared packet.fuel ∧
      code.lowerBody = GeneralizedLocalLambdaCompilation.lowerBody inputs packet.original.emission.prepared ∧
      code.fuel = packet.fuel ∧ code.descriptor.id = indexed.descriptor.id ∧
      HEq code.receipt packet.certificate ∧
      code.view = packet.original.emission.prepared.source ∧
      code.reasonAt = inputs.reasonAt ∧
      CallableIndexedLambdaValues.value code captured.embedding native actual =
        GeneralizedLocalInstanceValues.value indexed captured.embedding native actual := by
  have sourceEq := source_eq receipt instantiation sameScheme sameType descriptorSource candidateSource packet
  obtain ⟨parameters, result, body⟩ := header packet captures unique initializer sourceEq
  have view : LambdaMetadataViews.MetadataView
      (function.instantiate semantic (produced ++ callerEvidence.applySubstitution semantic)).source
      packet.original.emission.prepared.source := by
    rw [sourceEq]
    exact .refl _
  have typedLowered : HasType (SourceCoreLocalCell.coreContext inputs.scope ++ captured.administrative)
      packet.original.lowered.expression (LanguageResult.resultType packet.original.lowered.type)
      prepared.layouts.definitions := by
    rw [packet.original.extracted, ← packet.original.nativeType]
    exact LanguageResult.success_hasType typed
  obtain ⟨code, compilation, active, id, lowered, policy, lowerBody, fuel, descriptor, certificate, codeView, reasons⟩ :=
    indexed.code_at_read _ captured.administrative parameters result body profile view typedLowered
  exact ⟨code, compilation, active, id, lowered, policy, lowerBody, fuel, descriptor, certificate, codeView, reasons,
    GeneralizedLocalMaterializedCode.value_eq indexed code lowered captured.embedding native actual⟩

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalNamedMaterialization
