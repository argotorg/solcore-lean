import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAssociationFormation
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalLocatedRows

/-! Actual first-match lookup and the descriptor allocation's retained row
supply materialization at a named read. The native read keeps both the store
and the exact previously created closure value. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalReachedMaterialization
open Core Frontend SourceInference GeneralHeap ReadOnly CompatibleEquality
open GeneralizedLocalLocatedRows GeneralizedLocalMaterializedAssociation

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {descriptor : Dynamic.GeneralizedClosure} {binding : SourceCoreLocalPolymorphism.Binding}
  {lexical : TypeSystem.Substitution} {location : Dynamic.Location}
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
  {caller : SourceCoreLocalPolymorphism.Key} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id : ExpressionId} {reason : Word} {lowered : SourceCoreBasic.LoweredExpr}

theorem preserves
    (located : Located (GeneralizedLocalInstanceValues.model compiled.indexed) descriptor binding lexical
      location mapping world heap store)
    (receipt : GeneralizedLocalReadReceipts.Certificate compiled.indexed.base.locals caller [] source scope id reason lowered)
    (sameCaller : caller = binding.caller) (sameBinder : receipt.binder = binding.binder.id)
    (contextExtension : GeneralizedLocalBundleContexts.ContextExtension lexical [])
    {administrative : Core.Context} {environment : Dynamic.Environment} {canonical actual : Core.Environment}
    {embedding : Renaming}
    (environments : DataHeap.EnvRepresents (storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
    (lookup : Dynamic.Environment.LooksUp environment receipt.binder location)
    (agrees : ReadOnly.EnvironmentsAgree embedding canonical actual)
    (unique : NodeOccurrencesUnique descriptor.source)
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
      Evaluates actual store (lowered.expression.rename embedding)
        (.inRight .word (CallableIndexedLambdaValues.value material.code material.captured.embedding
          material.origin.native material.actual)) store := by
  have sameBinding : receipt.binding = binding := by
    have selected := receipt.bindingFound
    have registered : compiled.indexed.base.locals.binding binding.caller binding.binder.id = .ok binding :=
      located.attachment.registered
    simp only [sameCaller, sameBinder, registered] at selected
    exact (Except.ok.inj selected).symm
  obtain ⟨native, represented, evaluated⟩ :=
    located.preserves_rename receipt sameCaller sameBinder contextExtension environments lookup agrees
  have represented : GeneralizedLocalInstanceValues.Represents compiled.indexed mapping world descriptor
      receipt.binding lexical receipt.candidate native := by
    rw [sameBinding]
    exact represented
  have initializer : descriptor.initializer = receipt.binding.initializer := by
    rw [sameBinding]
    exact located.attachment.initializer
  obtain ⟨material, descriptorEq, bindingEq, lexicalEq, candidateEq, typeEq, semanticEq, contextEq,
      callerEq, producedEq, requirementsEq, nativeEq⟩ :=
    GeneralizedLocalAssociationFormation.materialize receipt represented located.attachment.captures unique
      initializer instantiation sameScheme sameType profile
  refine ⟨material, descriptorEq, bindingEq, lexicalEq, candidateEq, typeEq, semanticEq, contextEq,
    callerEq, producedEq, requirementsEq, ?_⟩
  simpa only [nativeEq] using evaluated


theorem preserves_framed
    (located : Located (GeneralizedLocalInstanceValues.model compiled.indexed) descriptor binding lexical
      location mapping world heap store)
    {frameLocation : Core.Location} (frames : located.Frames frameLocation)
    (receipt : GeneralizedLocalReadReceipts.Certificate compiled.indexed.base.locals caller [] source scope id reason lowered)
    (sameCaller : caller = binding.caller) (sameBinder : receipt.binder = binding.binder.id)
    (contextExtension : GeneralizedLocalBundleContexts.ContextExtension lexical [])
    {administrative : Core.Context} {environment : Dynamic.Environment} {canonical actual : Core.Environment}
    {embedding : Renaming}
    (environments : DataHeap.EnvRepresents (storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
    (lookup : Dynamic.Environment.LooksUp environment receipt.binder location)
    (agrees : ReadOnly.EnvironmentsAgree embedding canonical actual)
    (unique : NodeOccurrencesUnique descriptor.source)
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
      Evaluates actual store (lowered.expression.rename embedding)
        (.inRight .word (CallableIndexedLambdaValues.value material.code material.captured.embedding
          material.origin.native material.actual)) store := by
  have sameBinding : receipt.binding = binding := by
    have selected := receipt.bindingFound
    have registered : compiled.indexed.base.locals.binding binding.caller binding.binder.id = .ok binding :=
      located.attachment.registered
    simp only [sameCaller, sameBinder, registered] at selected
    exact (Except.ok.inj selected).symm
  obtain ⟨native, represented, evaluated⟩ :=
    located.preserves_framed frames receipt sameCaller sameBinder contextExtension environments lookup agrees
  have framed : GeneralizedLocalInstanceValues.Framed compiled.indexed mapping world descriptor
      receipt.binding lexical frameLocation receipt.candidate native := by
    rw [sameBinding]
    exact represented
  have initializer : descriptor.initializer = receipt.binding.initializer := by
    rw [sameBinding]
    exact located.attachment.initializer
  obtain ⟨material, descriptorEq, bindingEq, lexicalEq, candidateEq, typeEq, semanticEq, contextEq,
      callerEq, producedEq, requirementsEq, frameEq, nativeEq⟩ :=
    GeneralizedLocalAssociationFormation.materialize_framed receipt framed located.attachment.captures unique
      initializer instantiation sameScheme sameType profile
  refine ⟨material, descriptorEq, bindingEq, lexicalEq, candidateEq, typeEq, semanticEq, contextEq,
    callerEq, producedEq, requirementsEq, frameEq, ?_⟩
  simpa only [nativeEq] using evaluated

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalReachedMaterialization
