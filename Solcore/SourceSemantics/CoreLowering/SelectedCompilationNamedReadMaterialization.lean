import Solcore.SourceSemantics.CoreLowering.SelectedCompilationLocalReadMaterialization
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalNamedAttachment
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedBodyCompiler

/-! A named caller reads under the empty active substitution. Its stored
Snapshot materializes with the same saved frame and carries the actual next
body entry, using the existing representation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedReadMaterialization
open Core Frontend SourceInference TypeSystem SourceSpecializationWorklist
open CallableLambdaBodyReachability CallableBodyMetadataViews
open GeneralizedLocalAcceptedMaterialization
open SelectedCompilationLocalReadMaterialization (Entry)
open GeneralizedLocalInstanceCompilation (Inputs)
open GeneralizedLocalLambdaCompilation (Packet)

private theorem packet_entry {cached : SourceCoreUnifiedCompilation.Compiled}
    {caller : SourceCoreLocalPolymorphism.Key} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {reason : Word} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : GeneralizedLocalReadReceipts.Certificate cached.indexed.base.locals
      caller .empty source scope id reason lowered)
    {descriptor : Dynamic.GeneralizedClosure} {lexical : Substitution}
    (saved : GeneralizedLocalCapturedScopes.Attachment descriptor receipt.binding lexical)
    (extension : GeneralizedLocalBundleContexts.ContextExtension lexical .empty)
    {inputs : Inputs} {candidate : SourceCoreLocalPolymorphism.Instance} {raw : Core.Expr}
    (same : candidate = receipt.candidate) (packet : Packet inputs candidate raw)
    (initializer : inputs.initializer = receipt.binding.initializer) :
    ResidualEntryCovered receipt.binding.source (packet.statements.map NodeId.statement)
      packet.original.emission.prepared.substitution.domain := by
  subst candidate
  exact GeneralizedLocalCapturedScopes.body_at_read cached receipt saved extension packet initializer

/-- The empty named context transports the saved attachment and the actual
accepted Packet supplies the new body scope. -/
theorem materialize_at_named_read
    {cached : SourceCoreUnifiedCompilation.Compiled}
    {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {caller : SourceCoreLocalPolymorphism.Key} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {reason : Word} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : GeneralizedLocalReadReceipts.Certificate cached.indexed.base.locals
      caller .empty source scope id reason lowered)
    {descriptor : Dynamic.GeneralizedClosure} {lexical : Substitution}
    {frameLocation : Core.Location} {native : Value} {attachment : Prop}
    (row : GeneralizedLocalAcceptedInstances.Snapshot cached.indexed mapping world descriptor
      receipt.binding lexical frameLocation attachment receipt.candidate native)
    (saved : GeneralizedLocalCapturedScopes.Attachment descriptor receipt.binding lexical)
    (extension : GeneralizedLocalBundleContexts.ContextExtension lexical .empty)
    (captures : Dynamic.GeneralizedClosureCaptures descriptor.definitionContext descriptor.source
      descriptor.captured descriptor.binder descriptor.initializer descriptor)
    (unique : NodeOccurrencesUnique descriptor.source)
    (initializer : descriptor.initializer = receipt.binding.initializer)
    {context : Solcore.SourceSemantics.Context} {callerEvidence produced : Dynamic.EvidenceEnvironment}
    {actualType : TypeSystem.Ty} {requirements : List RequirementId} {semantic : TypeSystem.Substitution}
    (instantiation : Dynamic.LocalSchemeRuntimeInstantiation context callerEvidence descriptor.binder
      actualType requirements semantic produced)
    (sameScheme : descriptor.binder.scheme = receipt.binding.binder.scheme.apply .empty)
    (sameType : actualType = receipt.node.rawType) :
    let function := descriptor.instantiate semantic (produced ++ callerEvidence.applySubstitution semantic)
    ∃ material : Materialization cached mapping world function
        (fun source view => BodyView source view (function.body.map NodeId.statement)),
      material.descriptor = descriptor ∧ material.binding = receipt.binding ∧ material.lexical = lexical ∧
      material.candidate = receipt.candidate ∧ material.actualType = actualType ∧ material.semantic = semantic ∧
      material.context = context ∧ material.callerEvidence = callerEvidence ∧ material.produced = produced ∧
      material.requirements = requirements ∧ material.frameLocation = frameLocation ∧ Entry material ∧
      native = CallableIndexedLambdaValues.value material.code material.captured.embedding
        material.origin.native material.actual := by
  have activeAttachment := GeneralizedLocalCapturedScopes.Attachment.at_empty extension saved
  obtain ⟨material, descriptorEq, bindingEq, lexicalEq, candidateEq, typeEq, semanticEq, contextEq,
      callerEvidenceEq, producedEq, requirementsEq, frameEq, originInitializer, nativeEq⟩ :=
    GeneralizedLocalReachedAssociation.materialize_snapshot_at_read receipt row activeAttachment
      captures unique initializer instantiation sameScheme sameType
  refine ⟨material, descriptorEq, bindingEq, lexicalEq, candidateEq, typeEq, semanticEq,
    contextEq, callerEvidenceEq, producedEq, requirementsEq, frameEq, ⟨originInitializer, ?_⟩, nativeEq⟩
  have covered := packet_entry receipt saved extension candidateEq material.packet
    (material.initializer.trans (congrArg SourceCoreLocalPolymorphism.Binding.initializer bindingEq))
  rw [(GeneralizedLocalAcceptedBodyCompiler.lambda_fields material).2.2, ← material.active] at covered
  have sourceEq : material.candidate.origin.source = receipt.binding.source := by
    rw [candidateEq]
    exact (GeneralizedLocalAcceptedCatalogFormation.read_origins receipt).2.1
  simpa only [sourceEq] using covered

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedReadMaterialization
