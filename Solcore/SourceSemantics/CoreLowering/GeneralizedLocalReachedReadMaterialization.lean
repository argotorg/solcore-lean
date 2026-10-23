import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalReachedAssociation

/-! A read materializes the same saved lexical Snapshot using a separately
proved active-context body view. Its code, captures and native value are retained. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalReachedAssociation
open Core Frontend SourceInference GeneralHeap ReadOnly
open GeneralizedLocalAcceptedMaterialization

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {mapping : LocationMap} {world : StoreTyping}
  {caller : SourceCoreLocalPolymorphism.Key} {active : TypeSystem.Substitution} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id : ExpressionId} {reason : Word} {lowered : SourceCoreBasic.LoweredExpr}

theorem materialize_snapshot_at_read
    (receipt : GeneralizedLocalReadReceipts.Certificate compiled.indexed.base.locals caller active source scope id reason lowered)
    {descriptor : Dynamic.GeneralizedClosure} {native : Value}
    {frameLocation : Core.Location} {lexical : TypeSystem.Substitution} {attachment : Prop}
    (row : GeneralizedLocalAcceptedInstances.Snapshot compiled.indexed mapping world descriptor
      receipt.binding lexical frameLocation attachment receipt.candidate native)
    (activeAttachment : GeneralizedLocalReachedAllocation.Attachment descriptor receipt.binding active)
    (captures : Dynamic.GeneralizedClosureCaptures descriptor.definitionContext descriptor.source descriptor.captured
      descriptor.binder descriptor.initializer descriptor)
    (unique : NodeOccurrencesUnique descriptor.source)
    (initializer : descriptor.initializer = receipt.binding.initializer)
    {context : Solcore.SourceSemantics.Context} {callerEvidence produced : Dynamic.EvidenceEnvironment}
    {actualType : TypeSystem.Ty} {requirements : List RequirementId} {semantic : TypeSystem.Substitution}
    (instantiation : Dynamic.LocalSchemeRuntimeInstantiation context callerEvidence descriptor.binder
      actualType requirements semantic produced)
    (sameScheme : descriptor.binder.scheme = receipt.binding.binder.scheme.apply active)
    (sameType : actualType = receipt.node.rawType)
    :
    let function := descriptor.instantiate semantic (produced ++ callerEvidence.applySubstitution semantic)
    ∃ material : Materialization compiled mapping world function
        (fun source view => CallableBodyMetadataViews.BodyView source view (function.body.map NodeId.statement)),
      material.descriptor = descriptor ∧ material.binding = receipt.binding ∧ material.lexical = lexical ∧ material.candidate = receipt.candidate ∧
      material.actualType = actualType ∧ material.semantic = semantic ∧ material.context = context ∧
      material.callerEvidence = callerEvidence ∧ material.produced = produced ∧ material.requirements = requirements ∧
      material.frameLocation = frameLocation ∧
      material.candidate.origin.initializer = material.inputs.initializer ∧
      native = CallableIndexedLambdaValues.value material.code material.captured.embedding material.origin.native material.actual := by
  cases row with
  | retained packet indexed acceptedBody sameLexical owner instanceInitializer candidateSource candidateBinder savedAttachment origin captured declarations ownership issuer frameReference typed runtimeTyped =>
    have initializerEq := initializer.trans instanceInitializer.symm
    obtain ⟨code, compilation, activeEq, _id, loweredEq, _policy, _lowerBody, _fuel, _descriptor, _certificate, codeView, reasons, valueEq⟩ :=
      GeneralizedLocalReachedMaterialization.code_at_read compiled receipt instantiation sameScheme sameType
        activeAttachment packet indexed captures unique initializerEq captured typed (SelectedCompilationPreparedRuntimeFacts.of_compiled compiled).1 origin.native
    have materializedUnique : NodeOccurrencesUnique
        (descriptor.instantiate semantic (produced ++ callerEvidence.applySubstitution semantic)).source := by
      change ((descriptor.source.applySubstitution semantic).nodes.map Node.occurrenceId).Nodup
      change (descriptor.source.nodes.map Node.occurrenceId).Nodup at unique
      simpa only [TypedSource.applySubstitution_nodeOccurrenceIds] using unique
    let material : Materialization compiled mapping world
        (descriptor.instantiate semantic (produced ++ callerEvidence.applySubstitution semantic))
        (fun source view => CallableBodyMetadataViews.BodyView source view (descriptor.body.map NodeId.statement)) :=
      { descriptor := descriptor, binding := receipt.binding, lexical := lexical
        inputs := _, candidate := receipt.candidate, raw := _, packet := packet, indexed := indexed, body := acceptedBody
        sameLexical := sameLexical, owner := owner, initializer := instanceInitializer
        candidateSource := candidateSource, candidateBinder := candidateBinder, descriptorInitializer := initializer
        origin := origin, descriptorUnique := unique, sourceCaptures := captures, context := context, callerEvidence := callerEvidence
        produced := produced, actualType := actualType, requirements := requirements, semantic := semantic
        instantiation := instantiation, materialized := rfl, actual := _, captured := captured
        capturedDeclarations := GeneralizedLocalScopeDeclarations.materialized declarations semantic (produced ++ callerEvidence.applySubstitution semantic)
        frameLocation := frameLocation, frameReference := frameReference, code := code
        compilation := compilation, active := activeEq, lowered := loweredEq, codeId := _id, policy := _policy, lowerBody := _lowerBody,
        fuel := _fuel, descriptorId := _descriptor, certificate := _certificate, view := codeView, reasons := reasons,
        rawTyped := valueEq.symm ▸ runtimeTyped,
        ownership := FlexibleSubstitution.LocalIdentityOwnership.applySubstitution semantic ownership,
        issuer := issuer, unique := materializedUnique }
    refine ⟨material, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, valueEq.symm⟩
    exact (GeneralizedLocalAcceptedCatalogFormation.read_origins receipt).2.2.2.trans instanceInitializer.symm

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalReachedAssociation
