import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedCatalogFormation
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalNamedMaterialization
import Solcore.SourceSemantics.CoreLowering.CallableAncestryComposition

/-! A stored closure retains the Source view of its actual allocation context.
The real local read selects the cumulative candidate. Its matcher fixes the
new substitution, so closed earlier substitutions transport that retained view
to the accepted candidate body. The same Packet and capture environment supply
Code; no body execution law or equality of unrelated ancestry states is used. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalContextualMaterialization
open Core Frontend SourceInference TypeSystem
open GeneralizedLocalInstanceCompilation (Inputs)
open GeneralizedLocalLambdaCompilation (Packet)
open LambdaMetadataViews
open CallableAncestryProfiles.SourceComposition

private theorem node_substitution {source view : Node} (related : NodeView source view)
    (substitution : Substitution) :
    NodeView (source.applySubstitution substitution) (view.applySubstitution substitution) := by
  cases related with
  | expression id form =>
      exact .expression id (congrArg (ExpressionForm.applySubstitution substitution) form)
  | statement node => exact .statement _

private theorem nodes_substitution {source view : List Node}
    (related : DataPatternValues.ListRel NodeView source view) (substitution : Substitution) :
    DataPatternValues.ListRel NodeView
      (source.map (Node.applySubstitution substitution))
      (view.map (Node.applySubstitution substitution)) := by
  induction related with
  | nil => exact .nil
  | cons head _ ih => exact .cons (node_substitution head substitution) ih

theorem substitute_view {source view : TypedSource} (related : MetadataView source view)
    (substitution : Substitution) :
    MetadataView (source.applySubstitution substitution) (view.applySubstitution substitution) :=
  ⟨related.owner, congrArg (List.map (TypedBinder.applySubstitution substitution)) related.inputs,
    related.roots, nodes_substitution related.nodes substitution⟩

/-- This is an attachment to the existing Snapshot. Creation supplies the
current body's view and its actual closed native context. -/
structure Attachment (function : Dynamic.GeneralizedClosure)
    (binding : SourceCoreLocalPolymorphism.Binding) (active : Substitution) : Prop where
  closed : RangesClosed active
  view : MetadataView function.source (binding.source.applySubstitution active)

theorem Attachment.named {function : Dynamic.GeneralizedClosure}
    {binding : SourceCoreLocalPolymorphism.Binding}
    (same : function.source = binding.source) : Attachment function binding [] :=
  ⟨RangesClosed.empty, by rw [EmptySourceSubstitution.source, same]; exact .refl _⟩

variable {catalog : SourceCoreLocalPolymorphism.Catalog} {caller : SourceCoreLocalPolymorphism.Key}
  {active : Substitution} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id : ExpressionId} {reason : Core.Word} {lowered : SourceCoreBasic.LoweredExpr}

theorem lookup_eq
    (receipt : GeneralizedLocalReadReceipts.Certificate catalog caller active source scope id reason lowered)
    {function : Dynamic.GeneralizedClosure} {context : Solcore.SourceSemantics.Context}
    {callerEvidence produced : Dynamic.EvidenceEnvironment} {actual : TypeSystem.Ty}
    {requirements : List RequirementId} {semantic : Substitution}
    (instantiation : Dynamic.LocalSchemeRuntimeInstantiation context callerEvidence
      function.binder actual requirements semantic produced)
    (sameScheme : function.binder.scheme = receipt.binding.binder.scheme.apply active)
    (sameType : actual = receipt.node.rawType) :
    ∀ metavariable, semantic.lookup? metavariable = receipt.child.lookup? metavariable := by
  have matched : SourceSpecialization.matchClosedSchemeInstance? function.binder.scheme actual =
      some receipt.child := by
    rw [sameScheme, sameType, ← receipt.rawType]
    exact receipt.matched
  exact CallableClosedSchemeSubstitutionAgreement.runtime_instantiation_lookup_eq matched instantiation

theorem source_view
    (receipt : GeneralizedLocalReadReceipts.Certificate catalog caller active source scope id reason lowered)
    {function : Dynamic.GeneralizedClosure} {context : Solcore.SourceSemantics.Context}
    {callerEvidence produced : Dynamic.EvidenceEnvironment} {actual : TypeSystem.Ty}
    {requirements : List RequirementId} {semantic : Substitution}
    (instantiation : Dynamic.LocalSchemeRuntimeInstantiation context callerEvidence
      function.binder actual requirements semantic produced)
    (sameScheme : function.binder.scheme = receipt.binding.binder.scheme.apply active)
    (sameType : actual = receipt.node.rawType)
    (attachment : Attachment function receipt.binding active)
    (candidateSource : receipt.candidate.origin.source = receipt.binding.source)
    {inputs : Inputs} {raw : Core.Expr}
    (packet : Packet inputs receipt.candidate raw) :
    MetadataView
      (function.instantiate semantic (produced ++ callerEvidence.applySubstitution semantic)).source
      packet.original.emission.prepared.source := by
  change MetadataView (function.source.applySubstitution semantic) _
  rw [CallableFlexibleSubstitutionAgreement.typedSource_congr
    (lookup_eq receipt instantiation sameScheme sameType) function.source]
  rw [GeneralizedLocalLambdaEmissionFacts.Emission.source, candidateSource,
    receipt.candidate_key, CallableAncestryProfiles.SourceComposition.source _ _ attachment.closed]
  exact substitute_view attachment.view receipt.child

theorem header_of_view
    {function : Dynamic.GeneralizedClosure} {semantic : Substitution} {evidence : Dynamic.EvidenceEnvironment}
    {inputs : Inputs} {candidate : SourceCoreLocalPolymorphism.Instance} {raw : Core.Expr}
    (packet : Packet inputs candidate raw)
    (captures : Dynamic.GeneralizedClosureCaptures function.definitionContext function.source function.captured
      function.binder function.initializer function)
    (unique : NodeOccurrencesUnique function.source)
    (initializer : function.initializer = inputs.initializer)
    (view : MetadataView (function.instantiate semantic evidence).source
      packet.original.emission.prepared.source) :
    (function.instantiate semantic evidence).parameters = packet.parameters ∧
    (function.instantiate semantic evidence).resultType = packet.result ∧
    (function.instantiate semantic evidence).body = packet.statements := by
  obtain ⟨node, occurrence, form, _⟩ := captures.occurrence
  have found := lookupExpression?_complete unique occurrence
  have substituted := SourceTypedRuntime.TypedSource.lookupExpression?_applySubstitution
    function.source semantic function.initializer node found
  obtain ⟨sameNode, sameFound, _, sameForm⟩ := view.expression packet.found
  change (function.source.applySubstitution semantic).lookupExpression? inputs.initializer = some sameNode at sameFound
  rw [initializer] at substituted
  have nodes := Option.some.inj (substituted.symm.trans sameFound)
  have forms := (congrArg ExpressionNode.form nodes).trans (sameForm.trans packet.form)
  simp only [ExpressionNode.applySubstitution, form, ExpressionForm.applySubstitution] at forms
  exact ExpressionForm.lambda.inj forms

theorem code_at_read
    (receipt : GeneralizedLocalReadReceipts.Certificate catalog caller active source scope id reason lowered)
    {function : Dynamic.GeneralizedClosure} {context : Solcore.SourceSemantics.Context}
    {callerEvidence produced : Dynamic.EvidenceEnvironment} {actualType : TypeSystem.Ty}
    {requirements : List RequirementId} {semantic : Substitution}
    (instantiation : Dynamic.LocalSchemeRuntimeInstantiation context callerEvidence
      function.binder actualType requirements semantic produced)
    (sameScheme : function.binder.scheme = receipt.binding.binder.scheme.apply active)
    (sameType : actualType = receipt.node.rawType)
    (attachment : Attachment function receipt.binding active)
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
  have view := source_view receipt instantiation sameScheme sameType attachment candidateSource packet
  obtain ⟨parameters, result, body⟩ := header_of_view packet captures unique initializer view
  have typedLowered : HasType (SourceCoreLocalCell.coreContext inputs.scope ++ captured.administrative)
      packet.original.lowered.expression (LanguageResult.resultType packet.original.lowered.type)
      prepared.layouts.definitions := by
    rw [packet.original.extracted, ← packet.original.nativeType]
    exact LanguageResult.success_hasType typed
  obtain ⟨code, compilation, active, id, lowered, policy, lowerBody, fuel, descriptor, certificate, codeView, reasons⟩ :=
    indexed.code_at_read _ captured.administrative parameters result body profile view typedLowered
  exact ⟨code, compilation, active, id, lowered, policy, lowerBody, fuel, descriptor, certificate, codeView, reasons,
    GeneralizedLocalMaterializedCode.value_eq indexed code lowered captured.embedding native actual⟩

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalContextualMaterialization
