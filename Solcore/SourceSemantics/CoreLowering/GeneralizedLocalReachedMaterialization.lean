import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAssociationFormation
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalLocatedRows
import Solcore.SourceSemantics.CoreLowering.CallableBodyViewSubstitution
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalClosedAllocation

/-! Actual local reads consume a reached-body attachment and the authentic
Packet. They create the same native Code without a global metadata view. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalReachedMaterialization
open Core Frontend SourceInference TypeSystem
open GeneralizedLocalInstanceCompilation (Inputs)
open GeneralizedLocalLambdaCompilation (Packet)
open CallableBodyMetadataViews CallableLambdaBodyReachability
open CallableAncestryProfiles.SourceComposition
variable {caller : SourceCoreLocalPolymorphism.Key} {active : Substitution}
  {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id : ExpressionId} {reason : Core.Word} {lowered : SourceCoreBasic.LoweredExpr}

theorem source_view (compiled : SourceCoreUnifiedCompilation.Compiled)
    (receipt : GeneralizedLocalReadReceipts.Certificate compiled.indexed.base.locals caller active source scope id reason lowered)
    {function : Dynamic.GeneralizedClosure} {context : Solcore.SourceSemantics.Context}
    {callerEvidence produced : Dynamic.EvidenceEnvironment} {actual : TypeSystem.Ty}
    {requirements : List RequirementId} {semantic : Substitution}
    (instantiation : Dynamic.LocalSchemeRuntimeInstantiation context callerEvidence
      function.binder actual requirements semantic produced)
    (sameScheme : function.binder.scheme = receipt.binding.binder.scheme.apply active)
    (sameType : actual = receipt.node.rawType)
    (attachment : GeneralizedLocalReachedAllocation.Attachment function receipt.binding active)
    {inputs : Inputs} {raw : Core.Expr}
    (packet : Packet inputs receipt.candidate raw) :
    BodyView
      (function.instantiate semantic (produced ++ callerEvidence.applySubstitution semantic)).source
      packet.original.emission.prepared.source (lambdaRoots function.initializer function.body) := by
  obtain ⟨_, candidateSource, _, _⟩ := GeneralizedLocalAcceptedCatalogFormation.read_origins receipt
  change BodyView (function.source.applySubstitution semantic) _ _
  rw [CallableFlexibleSubstitutionAgreement.typedSource_congr
    (GeneralizedLocalContextualMaterialization.lookup_eq receipt instantiation sameScheme sameType) function.source]
  rw [GeneralizedLocalLambdaEmissionFacts.Emission.source, candidateSource,
    receipt.candidate_key, CallableAncestryProfiles.SourceComposition.source _ _ attachment.closed]
  exact attachment.view.applySubstitution receipt.child

theorem header_of_view
    {function : Dynamic.GeneralizedClosure} {semantic : Substitution} {evidence : Dynamic.EvidenceEnvironment}
    {inputs : Inputs} {candidate : SourceCoreLocalPolymorphism.Instance} {raw : Core.Expr}
    (packet : Packet inputs candidate raw)
    (captures : Dynamic.GeneralizedClosureCaptures function.definitionContext function.source function.captured
      function.binder function.initializer function)
    (unique : NodeOccurrencesUnique function.source)
    (initializer : function.initializer = inputs.initializer)
    (view : BodyView (function.instantiate semantic evidence).source
      packet.original.emission.prepared.source (lambdaRoots function.initializer function.body)) :
    (function.instantiate semantic evidence).parameters = packet.parameters ∧
    (function.instantiate semantic evidence).resultType = packet.result ∧
    (function.instantiate semantic evidence).body = packet.statements := by
  obtain ⟨node, occurrence, form, _⟩ := captures.occurrence
  have found := lookupExpression?_complete unique occurrence
  have substituted := SourceTypedRuntime.TypedSource.lookupExpression?_applySubstitution
    function.source semantic function.initializer node found
  obtain ⟨sameNode, sameFound, _, sameForm⟩ := view.expression (.inl (.root (by simp [lambdaRoots, initializer]))) packet.found
  change (function.source.applySubstitution semantic).lookupExpression? inputs.initializer = some sameNode at sameFound
  rw [initializer] at substituted
  have nodes := Option.some.inj (substituted.symm.trans sameFound)
  have forms := (congrArg ExpressionNode.form nodes).trans (sameForm.trans packet.form)
  simp only [ExpressionNode.applySubstitution, form, ExpressionForm.applySubstitution] at forms
  exact ExpressionForm.lambda.inj forms

theorem code_at_read (compiled : SourceCoreUnifiedCompilation.Compiled)
    (receipt : GeneralizedLocalReadReceipts.Certificate compiled.indexed.base.locals caller active source scope id reason lowered)
    {function : Dynamic.GeneralizedClosure} {context : Solcore.SourceSemantics.Context}
    {callerEvidence produced : Dynamic.EvidenceEnvironment} {actualType : TypeSystem.Ty}
    {requirements : List RequirementId} {semantic : Substitution}
    (instantiation : Dynamic.LocalSchemeRuntimeInstantiation context callerEvidence
      function.binder actualType requirements semantic produced)
    (sameScheme : function.binder.scheme = receipt.binding.binder.scheme.apply active)
    (sameType : actualType = receipt.node.rawType)
    (attachment : GeneralizedLocalReachedAllocation.Attachment function receipt.binding active)
    {inputs : Inputs} {raw : Core.Expr}
    (packet : Packet inputs receipt.candidate raw)
    (indexed : GeneralizedLocalLambdaGeneration.Indexed compiled.indexed packet)
    (captures : Dynamic.GeneralizedClosureCaptures function.definitionContext function.source function.captured
      function.binder function.initializer function)
    (unique : NodeOccurrencesUnique function.source)
    (initializer : function.initializer = inputs.initializer)
    {mapping : GeneralHeap.LocationMap} {world : StoreTyping} {actual : Core.Environment}
    (captured : CallableIndexedLambdaValues.Captures compiled.indexed mapping world inputs.scope function.captured actual)
    (typed : HasType (SourceCoreLocalCell.coreContext inputs.scope ++ captured.administrative)
      raw receipt.candidate.type compiled.indexed.layouts.definitions)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (native : CallableIndexedHistory.NativeFrame) :
    let instantiated := function.instantiate semantic (produced ++ callerEvidence.applySubstitution semantic)
    ∃ code : CallableIndexedLambdaValues.Code compiled.indexed instantiated inputs.scope captured.administrative
        (fun source view => BodyView source view (function.body.map NodeId.statement)),
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
  have view := source_view compiled receipt instantiation sameScheme sameType attachment packet
  obtain ⟨parameters, result, body⟩ := header_of_view packet captures unique initializer view
  have typedLowered : HasType (SourceCoreLocalCell.coreContext inputs.scope ++ captured.administrative)
      packet.original.lowered.expression (LanguageResult.resultType packet.original.lowered.type)
      compiled.indexed.layouts.definitions := by
    rw [packet.original.extracted, ← packet.original.nativeType]
    exact LanguageResult.success_hasType typed
  obtain ⟨code, compilation, active, id, lowered, policy, lowerBody, fuel, descriptor, certificate, codeView, reasons⟩ :=
    indexed.code_at_read_with_view
      (viewRelation := fun source target => BodyView source target (function.body.map NodeId.statement))
      _ captured.administrative parameters result body profile
      (view.restrict (fun id member => .root (List.mem_cons_of_mem _ member)))
      (by
        obtain ⟨node, found, _, form⟩ := view.expression
          (.inl (.root (by simp [lambdaRoots, initializer]))) packet.found
        exact ⟨node, found, form⟩) typedLowered
  exact ⟨code, compilation, active, id, lowered, policy, lowerBody, fuel, descriptor, certificate, codeView, reasons,
    GeneralizedLocalMaterializedCode.value_eq indexed code lowered captured.embedding native actual⟩

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalReachedMaterialization

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
