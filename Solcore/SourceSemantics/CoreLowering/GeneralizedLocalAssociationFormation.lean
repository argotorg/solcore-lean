import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalMaterializedAssociation
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalInstanceFrames

/-! The selected row of an actual generalized allocation supplies the complete
materialized association. The Source substitution and dictionary are supplied
by the actual read rule; all compiler ancestry is recovered from that row. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAssociationFormation
open Core Frontend SourceInference GeneralHeap ReadOnly
open GeneralizedLocalMaterializedAssociation

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {mapping : LocationMap} {world : StoreTyping}
  {caller : SourceCoreLocalPolymorphism.Key} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id : ExpressionId} {reason : Word} {lowered : SourceCoreBasic.LoweredExpr}

theorem materialize
    (receipt : GeneralizedLocalReadReceipts.Certificate compiled.indexed.base.locals caller [] source scope id reason lowered)
    {descriptor : Dynamic.GeneralizedClosure} {lexical : TypeSystem.Substitution} {native : Value}
    (row : GeneralizedLocalInstanceValues.Represents compiled.indexed mapping world descriptor
      receipt.binding lexical receipt.candidate native)
    (captures : Dynamic.GeneralizedClosureCaptures descriptor.definitionContext descriptor.source descriptor.captured
      descriptor.binder descriptor.initializer descriptor)
    (unique : NodeOccurrencesUnique descriptor.source)
    (initializer : descriptor.initializer = receipt.binding.initializer)
    {context : Solcore.SourceSemantics.Context} {callerEvidence produced : Dynamic.EvidenceEnvironment}
    {actualType : TypeSystem.Ty} {requirements : List RequirementId} {semantic : TypeSystem.Substitution}
    (instantiation : Dynamic.LocalSchemeRuntimeInstantiation context callerEvidence descriptor.binder
      actualType requirements semantic produced)
    (sameScheme : descriptor.binder.scheme = receipt.binding.binder.scheme)
    (sameType : actualType = receipt.node.rawType)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    let function := descriptor.instantiate semantic (produced ++ callerEvidence.applySubstitution semantic)
    ∃ material : Materialization compiled mapping world function,
      material.descriptor = descriptor ∧ material.binding = receipt.binding ∧ material.lexical = lexical ∧ material.candidate = receipt.candidate ∧
      material.actualType = actualType ∧ material.semantic = semantic ∧ material.context = context ∧
      material.callerEvidence = callerEvidence ∧ material.produced = produced ∧ material.requirements = requirements ∧
      native = CallableIndexedLambdaValues.value material.code material.captured.embedding material.origin.native material.actual := by
  cases row with
  | retained packet indexed bodyProfile sameLexical owner instanceInitializer candidateSource candidateBinder descriptorSource origin namedLexical namedMetadata captured declarations ownership issuer frameLocation frameReference typed runtimeTyped =>
    have initializerEq := initializer.trans instanceInitializer.symm
    have sourceEq := GeneralizedLocalNamedMaterialization.source_eq receipt instantiation sameScheme sameType
      descriptorSource candidateSource packet
    obtain ⟨code, compilation, active, _id, loweredEq, _policy, _lowerBody, _fuel, _descriptor, _certificate, codeView, reasons, valueEq⟩ :=
      GeneralizedLocalNamedMaterialization.code_at_read receipt instantiation sameScheme sameType
        descriptorSource candidateSource packet indexed captures unique initializerEq captured typed profile origin.native
    have materializedUnique : NodeOccurrencesUnique
        (descriptor.instantiate semantic (produced ++ callerEvidence.applySubstitution semantic)).source := by
      change ((descriptor.source.applySubstitution semantic).nodes.map Node.occurrenceId).Nodup
      change (descriptor.source.nodes.map Node.occurrenceId).Nodup at unique
      simpa only [TypedSource.applySubstitution_nodeOccurrenceIds] using unique
    let material : Materialization compiled mapping world
        (descriptor.instantiate semantic (produced ++ callerEvidence.applySubstitution semantic)) :=
      { descriptor := descriptor, binding := receipt.binding, lexical := lexical
        inputs := _, candidate := receipt.candidate, raw := _, packet := packet, indexed := indexed, bodyProfile := bodyProfile
        sameLexical := sameLexical, owner := owner, initializer := instanceInitializer
        candidateSource := candidateSource, candidateBinder := candidateBinder, descriptorSource := descriptorSource, descriptorInitializer := initializer, binderScheme := sameScheme
        origin := origin, namedLexical := namedLexical, namedMetadata := namedMetadata, descriptorUnique := unique, sourceCaptures := captures, context := context, callerEvidence := callerEvidence
        produced := produced, actualType := actualType, requirements := requirements, semantic := semantic
        instantiation := instantiation, materialized := rfl, actual := _, captured := captured
        capturedDeclarations := GeneralizedLocalScopeDeclarations.materialized declarations semantic (produced ++ callerEvidence.applySubstitution semantic)
        frameLocation := frameLocation, frameReference := frameReference, code := code
        compilation := compilation, active := active, lowered := loweredEq, codeId := _id, policy := _policy, lowerBody := _lowerBody,
        fuel := _fuel, descriptorId := _descriptor, certificate := _certificate, view := codeView, reasons := reasons, source := sourceEq,
        rawTyped := valueEq.symm ▸ runtimeTyped,
        ownership := FlexibleSubstitution.LocalIdentityOwnership.applySubstitution semantic ownership,
        issuer := issuer, unique := materializedUnique }
    exact ⟨material, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, valueEq.symm⟩


theorem materialize_framed
    (receipt : GeneralizedLocalReadReceipts.Certificate compiled.indexed.base.locals caller [] source scope id reason lowered)
    {descriptor : Dynamic.GeneralizedClosure} {lexical : TypeSystem.Substitution} {native : Value}
    {frameLocation : Core.Location}
    (row : GeneralizedLocalInstanceValues.Framed compiled.indexed mapping world descriptor
      receipt.binding lexical frameLocation receipt.candidate native)
    (captures : Dynamic.GeneralizedClosureCaptures descriptor.definitionContext descriptor.source descriptor.captured
      descriptor.binder descriptor.initializer descriptor)
    (unique : NodeOccurrencesUnique descriptor.source)
    (initializer : descriptor.initializer = receipt.binding.initializer)
    {context : Solcore.SourceSemantics.Context} {callerEvidence produced : Dynamic.EvidenceEnvironment}
    {actualType : TypeSystem.Ty} {requirements : List RequirementId} {semantic : TypeSystem.Substitution}
    (instantiation : Dynamic.LocalSchemeRuntimeInstantiation context callerEvidence descriptor.binder
      actualType requirements semantic produced)
    (sameScheme : descriptor.binder.scheme = receipt.binding.binder.scheme)
    (sameType : actualType = receipt.node.rawType)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    let function := descriptor.instantiate semantic (produced ++ callerEvidence.applySubstitution semantic)
    ∃ material : Materialization compiled mapping world function,
      material.descriptor = descriptor ∧ material.binding = receipt.binding ∧ material.lexical = lexical ∧ material.candidate = receipt.candidate ∧
      material.actualType = actualType ∧ material.semantic = semantic ∧ material.context = context ∧
      material.callerEvidence = callerEvidence ∧ material.produced = produced ∧ material.requirements = requirements ∧
      material.frameLocation = frameLocation ∧
      native = CallableIndexedLambdaValues.value material.code material.captured.embedding material.origin.native material.actual := by
  cases row with
  | retained packet indexed bodyProfile sameLexical owner instanceInitializer candidateSource candidateBinder descriptorSource origin namedLexical namedMetadata captured declarations ownership issuer frameReference typed runtimeTyped =>
    have initializerEq := initializer.trans instanceInitializer.symm
    have sourceEq := GeneralizedLocalNamedMaterialization.source_eq receipt instantiation sameScheme sameType
      descriptorSource candidateSource packet
    obtain ⟨code, compilation, active, _id, loweredEq, _policy, _lowerBody, _fuel, _descriptor, _certificate, codeView, reasons, valueEq⟩ :=
      GeneralizedLocalNamedMaterialization.code_at_read receipt instantiation sameScheme sameType
        descriptorSource candidateSource packet indexed captures unique initializerEq captured typed profile origin.native
    have materializedUnique : NodeOccurrencesUnique
        (descriptor.instantiate semantic (produced ++ callerEvidence.applySubstitution semantic)).source := by
      change ((descriptor.source.applySubstitution semantic).nodes.map Node.occurrenceId).Nodup
      change (descriptor.source.nodes.map Node.occurrenceId).Nodup at unique
      simpa only [TypedSource.applySubstitution_nodeOccurrenceIds] using unique
    let material : Materialization compiled mapping world
        (descriptor.instantiate semantic (produced ++ callerEvidence.applySubstitution semantic)) :=
      { descriptor := descriptor, binding := receipt.binding, lexical := lexical
        inputs := _, candidate := receipt.candidate, raw := _, packet := packet, indexed := indexed, bodyProfile := bodyProfile
        sameLexical := sameLexical, owner := owner, initializer := instanceInitializer
        candidateSource := candidateSource, candidateBinder := candidateBinder, descriptorSource := descriptorSource, descriptorInitializer := initializer, binderScheme := sameScheme
        origin := origin, namedLexical := namedLexical, namedMetadata := namedMetadata, descriptorUnique := unique, sourceCaptures := captures, context := context, callerEvidence := callerEvidence
        produced := produced, actualType := actualType, requirements := requirements, semantic := semantic
        instantiation := instantiation, materialized := rfl, actual := _, captured := captured
        capturedDeclarations := GeneralizedLocalScopeDeclarations.materialized declarations semantic (produced ++ callerEvidence.applySubstitution semantic)
        frameLocation := frameLocation, frameReference := frameReference, code := code
        compilation := compilation, active := active, lowered := loweredEq, codeId := _id, policy := _policy, lowerBody := _lowerBody,
        fuel := _fuel, descriptorId := _descriptor, certificate := _certificate, view := codeView, reasons := reasons, source := sourceEq,
        rawTyped := valueEq.symm ▸ runtimeTyped,
        ownership := FlexibleSubstitution.LocalIdentityOwnership.applySubstitution semantic ownership,
        issuer := issuer, unique := materializedUnique }
    exact ⟨material, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, valueEq.symm⟩

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAssociationFormation
