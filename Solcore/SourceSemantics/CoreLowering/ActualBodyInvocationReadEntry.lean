import Solcore.SourceSemantics.CoreLowering.ActualBodyInvocationResidualEntry
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedReadMaterialization

/-! Both actual invocation forms consume the same stored Snapshot and return
scope evidence for the next body. The code and saved frame remain unchanged. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.ActualBodyInvocation
open Core Frontend SourceInference TypeSystem SourceSpecializationWorklist
open CallableBodyMetadataViews GeneralizedLocalAcceptedMaterialization
open SelectedCompilationLocalReadMaterialization (Entry)

theorem Index.materialize_read
    {workspace : Workspace.RawWorkspace} {fuel : Nat}
    {compiled : SourceCoreCompiler.Compiled} {cached : SourceCoreUnifiedCompilation.Compiled}
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram workspace fuel = .ok compiled.program)
    (index : Index cached ReachedView) (entry : index.ResidualEntry)
    {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {reason : Word} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : GeneralizedLocalReadReceipts.Certificate cached.indexed.base.locals
      index.owner index.active index.compilerSource scope id reason lowered)
    (site : index.Site (.expression id))
    {descriptor : Dynamic.GeneralizedClosure} {lexical : Substitution}
    {frameLocation : Core.Location} {native : Value} {attachment : Prop}
    (row : GeneralizedLocalAcceptedInstances.Snapshot cached.indexed mapping world descriptor
      receipt.binding lexical frameLocation attachment receipt.candidate native)
    (saved : GeneralizedLocalCapturedScopes.Attachment descriptor receipt.binding lexical)
    (extension : GeneralizedLocalBundleContexts.ContextExtension lexical index.active)
    (captures : Dynamic.GeneralizedClosureCaptures descriptor.definitionContext descriptor.source
      descriptor.captured descriptor.binder descriptor.initializer descriptor)
    (unique : NodeOccurrencesUnique descriptor.source)
    (initializer : descriptor.initializer = receipt.binding.initializer)
    {context : Solcore.SourceSemantics.Context} {callerEvidence produced : Dynamic.EvidenceEnvironment}
    {actualType : TypeSystem.Ty} {requirements : List RequirementId} {semantic : TypeSystem.Substitution}
    (instantiation : Dynamic.LocalSchemeRuntimeInstantiation context callerEvidence descriptor.binder
      actualType requirements semantic produced)
    (sameScheme : descriptor.binder.scheme = receipt.binding.binder.scheme.apply index.active)
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
  cases index with
  | named receiptNamed selected =>
    exact SelectedCompilationNamedReadMaterialization.materialize_at_named_read receipt row saved
      extension captures unique initializer instantiation sameScheme sameType
  | contextual caller view =>
    exact SelectedCompilationLocalReadMaterialization.materialize_at_contextual_read artifact checked
      caller entry receipt site.reached row saved extension captures unique initializer
      instantiation sameScheme sameType

end Solcore.SourceSemantics.CoreLowering.ActualBodyInvocation
