import Solcore.SourceSemantics.CoreLowering.SelectedCompilationLocalAttachmentTransport
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalReachedReadMaterialization

/-! A concrete contextual read consumes the transported capture and returns
the same native materialization together with its actual body-entry scope. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationLocalReadMaterialization
open Core Frontend SourceInference TypeSystem SourceSpecializationWorklist
open CallableLambdaBodyReachability CallableBodyMetadataViews
open GeneralizedLocalAcceptedMaterialization

private theorem expression_node {source : TypedSource} {id : ExpressionId}
    {node : ExpressionNode} (found : source.lookupExpression? id = some node) :
    source.lookupNode? id.occurrence = some (.expression node) := by
  unfold TypedSource.lookupExpression? at found
  cases selected : source.lookupNode? id.occurrence with
  | none => simp [selected] at found
  | some actual =>
    cases actual with
    | statement => simp [selected] at found
    | expression expression =>
      have same : expression = node := by simpa [selected] using found
      simp only [same]

/-- This evidence is attached to the existing materialization; it adds no
native value, body model, or assumed execution law. -/
structure Entry {cached : SourceCoreUnifiedCompilation.Compiled}
    {mapping : GeneralHeap.LocationMap} {world : StoreTyping} {function : Dynamic.Closure}
    {relation : TypedSource → TypedSource → Prop}
    (material : Materialization cached mapping world function relation) : Prop where
  initializer : material.candidate.origin.initializer = material.inputs.initializer
  covered : ResidualEntryCovered material.candidate.origin.source
    (function.body.map NodeId.statement) material.code.active.domain

/-- Every input comes from this invocation, its reached read, and the same
stored Snapshot. The active body view is derived before materialization. -/
theorem materialize_at_contextual_read
    {workspace : Workspace.RawWorkspace} {fuel : Nat}
    {compiled : SourceCoreCompiler.Compiled} {cached : SourceCoreUnifiedCompilation.Compiled}
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram workspace fuel = .ok compiled.program)
    {callerMapping : GeneralHeap.LocationMap} {callerWorld : StoreTyping} {callerFunction : Dynamic.Closure}
    {relation : TypedSource → TypedSource → Prop}
    (caller : Materialization cached callerMapping callerWorld callerFunction relation)
    (callerEntry : Entry caller)
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {reason : Word} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : GeneralizedLocalReadReceipts.Certificate cached.indexed.base.locals
      caller.code.compilation.owner caller.code.active caller.code.view scope id reason lowered)
    (reached : Reaches caller.code.view (callerFunction.body.map NodeId.statement) (.expression id))
    {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {descriptor : Dynamic.GeneralizedClosure} {lexical : Substitution}
    {frameLocation : Core.Location} {native : Value} {attachment : Prop}
    (row : GeneralizedLocalAcceptedInstances.Snapshot cached.indexed mapping world descriptor
      receipt.binding lexical frameLocation attachment receipt.candidate native)
    (saved : GeneralizedLocalCapturedScopes.Attachment descriptor receipt.binding lexical)
    (extension : GeneralizedLocalBundleContexts.ContextExtension lexical caller.code.active)
    (captures : Dynamic.GeneralizedClosureCaptures descriptor.definitionContext descriptor.source
      descriptor.captured descriptor.binder descriptor.initializer descriptor)
    (unique : NodeOccurrencesUnique descriptor.source)
    (initializer : descriptor.initializer = receipt.binding.initializer)
    {context : Solcore.SourceSemantics.Context} {callerEvidence produced : Dynamic.EvidenceEnvironment}
    {actualType : TypeSystem.Ty} {requirements : List RequirementId} {semantic : TypeSystem.Substitution}
    (instantiation : Dynamic.LocalSchemeRuntimeInstantiation context callerEvidence descriptor.binder
      actualType requirements semantic produced)
    (sameScheme : descriptor.binder.scheme = receipt.binding.binder.scheme.apply caller.code.active)
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
  have activeAttachment : GeneralizedLocalReachedAllocation.Attachment descriptor receipt.binding
      caller.code.active := by
    cases row with
    | retained packet indexed acceptedBody sameLexical owner instanceInitializer candidateSource candidateBinder
        savedAttachment origin captured declarations ownership issuer frameReference typed runtimeTyped =>
      exact SelectedCompilationLocalAttachmentTransport.attachment_at_contextual_read artifact checked
        caller callerEntry.initializer receipt reached packet indexed saved extension captures unique initializer
  obtain ⟨material, descriptorEq, bindingEq, lexicalEq, candidateEq, typeEq, semanticEq, contextEq,
      callerEvidenceEq, producedEq, requirementsEq, frameEq, originInitializer, nativeEq⟩ :=
    GeneralizedLocalReachedAssociation.materialize_snapshot_at_read receipt row activeAttachment
      captures unique initializer instantiation sameScheme sameType
  refine ⟨material, descriptorEq, bindingEq, lexicalEq, candidateEq, typeEq, semanticEq,
    contextEq, callerEvidenceEq, producedEq, requirementsEq, frameEq, ⟨originInitializer, ?_⟩, nativeEq⟩
  obtain ⟨node, parameters, result, found, form⟩ :=
    GeneralizedLocalCapturedLambdaHeader.captured_header saved captures unique initializer
  have covered := saved.captured.body
    (GeneralizedLocalCapturedScopes.read_keys receipt extension) (expression_node found) form
  have sourceEq : material.candidate.origin.source = receipt.binding.source := by
    rw [candidateEq]
    exact (GeneralizedLocalAcceptedCatalogFormation.read_origins receipt).2.1
  have activeEq : material.code.active = receipt.candidate.origin.substitution := by
    rw [material.active, GeneralizedLocalLambdaEmissionFacts.Emission.substitution, candidateEq]
  simpa only [sourceEq, activeEq, Dynamic.GeneralizedClosure.instantiate] using covered

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationLocalReadMaterialization
