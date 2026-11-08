import Solcore.SourceSemantics.Internal.Substitution.TraitLaws
import Solcore.SourceSemantics.Program
import Solcore.SourceSemantics.Internal.Substitution.StructuralLaws

/-!
# Typing certificates of selected bodies

What a selected body and operator supply to typing, and the uniqueness of the stored annotation
summary.
-/

section
-- leanmerge: from Solcore.SourceSemantics.SelectedBodyTypingCertificates
set_option autoImplicit false
set_option Elab.async false

namespace Solcore.SourceSemantics.Dynamic
open Frontend SourceInference TypeSystem

/-- The exact retained ordinary definition suffices for its own instance. -/
theorem FunctionInstantiates.certificate_of_valid
    {program : Program} {instantiation : DeclarationInstantiation}
    {bodyInstance : BodyInstance}
    (catalog : SignatureCatalogWellFormed program.signatures)
    (owners : (program.functions.map fun definition => definition.body.owner).Nodup)
    {selected : FunctionDefinition} (member : selected ∈ program.functions)
    (owner : selected.body.owner = instantiation.declaration)
    (valid : FunctionDefinition.Valid program.signatures selected)
    (instantiates : FunctionInstantiates program instantiation bodyInstance) :
    ∃ inputTypes lexicalContext facts,
      FunctionInstanceTypingCertificate program instantiation bodyInstance
        inputTypes lexicalContext facts := by
  cases instantiates with
  | @intro signature definition _ signatureMem definitionMem declarationEq
      ownerEq instantiationValid sourceEq resultEq contextEq =>
      have same : selected = definition :=
        StructuralSubstitution.eq_of_mem_of_mapped_nodup owners member definitionMem
          (owner.trans (declarationEq.trans ownerEq.symm))
      subst selected
      cases valid with
      | @intro typedSignature facts typedSignatureMem typedOwner bodyValid =>
          have typedSignatureEq : typedSignature = signature :=
            StructuralSubstitution.eq_of_mem_of_mapped_nodup
              catalog.function_ids typedSignatureMem
              signatureMem (by rw [← typedOwner, ownerEq])
          subst typedSignature
          cases instantiationValid with
          | intro selectedSignature selectedSignatureMem selectedDeclarationEq
              substitutionExact substitutionRange typeEq predicatesEq
              parameterComptimeEq returnComptimeEq =>
              have selectedSignatureEq : selectedSignature = signature :=
                StructuralSubstitution.eq_of_mem_of_mapped_nodup
                  catalog.function_ids
                  selectedSignatureMem signatureMem
                  (by rw [← selectedDeclarationEq, declarationEq])
              subst selectedSignature
              have rangeAfter :=
                StructuralSubstitution.ParameterSubstitution.RangeWellFormed.atApplyContextOfBase
                  (context := declarationContext program.signatures
                    definition.body.owner signature.scheme.parameters
                    signature.scheme.predicates definition.body.solvedRequirements)
                  substitutionRange
              obtain ⟨lexicalContext, inputsExtend, bodyTyped⟩ :=
                StructuralSubstitution.BodyDefinitionHasType.instantiate
                  instantiation.parameterSubstitution
                  catalog substitutionExact rangeAfter
                  bodyValid
              refine ⟨signature.parameterTypes.map
                instantiation.parameterSubstitution.apply, lexicalContext,
                StructuralSubstitution.applyBodyFacts
                  instantiation.parameterSubstitution facts, ?_⟩
              refine {
                typing := {
                  inputs_extend := ?_
                  body_typed := ?_
                }
                graph_closed := ?_
                local_identity_ownership := ?_
                requirement_ledger := ?_
                requirement_ownership := ?_
                owner := ?_
                locals_empty := ?_
                type_parameters_empty := ?_
                type_variables_empty := ?_
                residual_type_variables_open := ?_
                signatures_eq := ?_
                callable_type := ?_
              }
              · simpa [sourceEq, contextEq, predicatesEq,
                  StructuralSubstitution.applyTypedSource] using inputsExtend
              · simpa [sourceEq, resultEq] using bodyTyped
              · simpa [sourceEq] using
                  (StructuralSubstitution.OccurrenceGraphClosed.applyParameters
                    instantiation.parameterSubstitution
                    (StructuralSubstitution.BodyDefinitionHasType.graphClosed
                      bodyValid))
              · simpa [sourceEq] using
                  (StructuralSubstitution.LocalIdentityOwnership.applyParameters
                    instantiation.parameterSubstitution
                    (StructuralSubstitution.BodyDefinitionHasType.localIdentityOwnership
                      bodyValid))
              · simpa [sourceEq, contextEq, predicatesEq] using
                  (StructuralSubstitution.ScopedRequirementLedgerWellFormed.applyParameters
                    instantiation.parameterSubstitution
                    (StructuralSubstitution.BodyDefinitionHasType.requirementLedger
                      bodyValid))
              · simpa [sourceEq, contextEq, predicatesEq] using
                  (StructuralSubstitution.RequirementOwnership.applyParameters
                    instantiation.parameterSubstitution
                    (StructuralSubstitution.BodyDefinitionHasType.requirementOwnership
                      bodyValid))
              · simpa [sourceEq, contextEq,
                  StructuralSubstitution.applyTypedSource, declarationContext,
                  Context.ofSignatures, Context.forDeclaration,
                  Context.withAssumptions, Context.withSolvedRequirements,
                  Context.withResidualTypeVariables] using
                  congrArg some
                    (StructuralSubstitution.BodyDefinitionHasType.sourceOwner
                      bodyValid).symm
              · simp [contextEq, declarationContext, Context.ofSignatures,
                  Context.forDeclaration, Context.withAssumptions,
                  Context.withSolvedRequirements,
                  Context.withResidualTypeVariables]
              · simp [contextEq, declarationContext, Context.ofSignatures,
                  Context.forDeclaration, Context.withAssumptions,
                  Context.withSolvedRequirements,
                  Context.withResidualTypeVariables]
              · simp [contextEq, declarationContext, Context.ofSignatures,
                  Context.forDeclaration, Context.withAssumptions,
                  Context.withSolvedRequirements,
                  Context.withResidualTypeVariables]
              · simp [contextEq, declarationContext,
                  Context.withResidualTypeVariables]
              · simp [contextEq, declarationContext, Context.ofSignatures,
                  Context.forDeclaration, Context.withAssumptions,
                  Context.withSolvedRequirements,
                  Context.withResidualTypeVariables]
              · have signatureWellFormed :=
                  catalog.functions_semantic signature
                    signatureMem
                have instantiatedResult :
                    bodyInstance.resultType =
                      instantiation.parameterSubstitution.apply
                        (Ty.productMany signature.returnTypes) := by
                  rw [resultEq,
                    StructuralSubstitution.BodyDefinitionHasType.resultTypeEq
                      bodyValid]
                rw [typeEq, signatureWellFormed.scheme_body]
                simp [StructuralSubstitution.apply_productMany,
                  instantiatedResult]


/-- The exact retained method definition suffices for its own instance. -/
theorem TraitMethodInstantiates.certificate_of_valid
    {program : Program}
    {implementation : ProgramImplementationSignature}
    {method : ProgramImplMethodSignature}
    {trait : ProgramTraitSignature} {definition : MethodDefinition}
    {substitution : ParameterSubstitution} {bodyInstance : BodyInstance}
    (catalog : SignatureCatalogWellFormed program.signatures)
    (valid : MethodDefinition.Valid program.signatures definition)
    (instantiates : TraitMethodInstantiates program implementation method trait
      definition substitution bodyInstance) :
    ∃ inputTypes lexicalContext facts,
      TraitMethodInstanceTypingCertificate program method substitution definition
        bodyInstance inputTypes lexicalContext facts := by
  cases instantiates with
  | intro implementationMem methodMem traitMem traitOwner definitionMem
      definitionId ownerEq substitutionExact substitutionRange sourceEq resultEq
      contextEq =>
      cases valid with
      | @intro typedImplementation typedMethod typedTrait typedTraitMethod facts
          typedImplementationMem typedMethodMem methodIdEq methodOwner
          typedTraitMem traitMethodMem traitMethodIdEq typedTraitOwner typedOwner
          bodyValid =>
          have typedMethodCatalogMem :
              typedMethod ∈ program.signatures.implementations.flatMap
                (fun candidate => candidate.methods) :=
            List.mem_flatMap.mpr
              ⟨typedImplementation, typedImplementationMem, typedMethodMem⟩
          have methodCatalogMem :
              method ∈ program.signatures.implementations.flatMap
                (fun candidate => candidate.methods) :=
            List.mem_flatMap.mpr
              ⟨implementation, implementationMem, methodMem⟩
          have methodIdsNodup :
              ((program.signatures.implementations.flatMap
                (fun candidate => candidate.methods)).map
                  (fun candidate => candidate.id)).Nodup := by
            simpa [List.map_flatMap, Function.comp_def] using
              catalog.implementation_method_ids
          have typedMethodEq : typedMethod = method :=
            StructuralSubstitution.eq_of_mem_of_mapped_nodup
              methodIdsNodup
              typedMethodCatalogMem methodCatalogMem
              (by rw [← methodIdEq, definitionId])
          subst typedMethod
          have typedImplementationEq : typedImplementation = implementation :=
            StructuralSubstitution.eq_of_mem_of_mapped_nodup
              catalog.implementation_ids
              typedImplementationMem implementationMem
              (by rw [← typedOwner, ownerEq])
          subst typedImplementation
          have typedTraitIdEq : typedTrait.id = trait.id := by
            calc
              typedTrait.id = typedTraitMethod.id.trait := typedTraitOwner.symm
              _ = method.traitMethod.trait :=
                (congrArg (fun id => id.trait) traitMethodIdEq).symm
              _ = trait.id := traitOwner
          have typedTraitEq : typedTrait = trait :=
            StructuralSubstitution.eq_of_mem_of_mapped_nodup
              catalog.trait_ids typedTraitMem traitMem
              typedTraitIdEq
          subst typedTrait
          have rangeAfter :=
            StructuralSubstitution.ParameterSubstitution.RangeWellFormed.atApplyContextOfBase
              (context := declarationContext program.signatures
                definition.body.owner implementation.parameters
                (methodAssumptions trait implementation method)
                definition.body.solvedRequirements)
              substitutionRange
          obtain ⟨lexicalContext, inputsExtend, bodyTyped⟩ :=
            StructuralSubstitution.BodyDefinitionHasType.instantiate
              substitution catalog substitutionExact
              rangeAfter bodyValid
          refine ⟨method.parameterTypes.map substitution.apply, lexicalContext,
            StructuralSubstitution.applyBodyFacts substitution facts, ?_⟩
          refine {
            typing := {
              inputs_extend := ?_
              body_typed := ?_
            }
            graph_closed := ?_
            local_identity_ownership := ?_
            requirement_ledger := ?_
            requirement_ownership := ?_
            owner := ?_
            locals_empty := ?_
            type_parameters_empty := ?_
            type_variables_empty := ?_
            residual_type_variables_open := ?_
            signatures_eq := ?_
            input_types_eq := ?_
            result_type_eq := ?_
            callable_type := ?_
          }
          · simpa [sourceEq, contextEq,
              StructuralSubstitution.applyTypedSource] using inputsExtend
          · simpa [sourceEq, resultEq] using bodyTyped
          · simpa [sourceEq] using
              (StructuralSubstitution.OccurrenceGraphClosed.applyParameters
                substitution
                (StructuralSubstitution.BodyDefinitionHasType.graphClosed
                  bodyValid))
          · simpa [sourceEq] using
              (StructuralSubstitution.LocalIdentityOwnership.applyParameters
                substitution
                (StructuralSubstitution.BodyDefinitionHasType.localIdentityOwnership
                  bodyValid))
          · simpa [sourceEq, contextEq] using
              (StructuralSubstitution.ScopedRequirementLedgerWellFormed.applyParameters
                substitution
                (StructuralSubstitution.BodyDefinitionHasType.requirementLedger
                  bodyValid))
          · simpa [sourceEq, contextEq] using
              (StructuralSubstitution.RequirementOwnership.applyParameters
                substitution
                (StructuralSubstitution.BodyDefinitionHasType.requirementOwnership
                  bodyValid))
          · simpa [sourceEq, contextEq,
              StructuralSubstitution.applyTypedSource, declarationContext,
              Context.ofSignatures, Context.forDeclaration,
              Context.withAssumptions, Context.withSolvedRequirements,
              Context.withResidualTypeVariables] using
              congrArg some
                (StructuralSubstitution.BodyDefinitionHasType.sourceOwner
                  bodyValid).symm
          · simp [contextEq, declarationContext, Context.ofSignatures,
              Context.forDeclaration, Context.withAssumptions,
              Context.withSolvedRequirements,
              Context.withResidualTypeVariables]
          · simp [contextEq, declarationContext, Context.ofSignatures,
              Context.forDeclaration, Context.withAssumptions,
              Context.withSolvedRequirements,
              Context.withResidualTypeVariables]
          · simp [contextEq, declarationContext, Context.ofSignatures,
              Context.forDeclaration, Context.withAssumptions,
              Context.withSolvedRequirements,
              Context.withResidualTypeVariables]
          · simp [contextEq, declarationContext,
              Context.withResidualTypeVariables]
          · simp [contextEq, declarationContext, Context.ofSignatures,
              Context.forDeclaration, Context.withAssumptions,
              Context.withSolvedRequirements,
              Context.withResidualTypeVariables]
          · rfl
          · simpa [StructuralSubstitution.BodyDefinitionHasType.resultTypeEq
              bodyValid] using resultEq
          · rw [StructuralSubstitution.BodyDefinitionHasType.callableTypeEq
              bodyValid]
            simp [StructuralSubstitution.apply_productMany, resultEq,
              StructuralSubstitution.BodyDefinitionHasType.resultTypeEq
                bodyValid]


end Solcore.SourceSemantics.Dynamic
end

section
-- leanmerge: from Solcore.SourceSemantics.SelectedOperatorTypingCertificates
set_option autoImplicit false
set_option Elab.async false

namespace Solcore.SourceSemantics.Dynamic
open Frontend SourceInference TypeSystem

/-- The actual method-selection data and its exact static instance certificate.
The original dictionary, substitution, body and requirement sequence are retained. -/
inductive TypedOperatorMethodSelected (program : Program) (context : Context)
    (callerEvidence : EvidenceEnvironment)
    (traitName methodName : String) :
    List RequirementId → BodyInstance → EvidenceEnvironment → Prop where
  | intro
      {primary : RequirementId} {methodRequirements : List RequirementId}
      {goal : ProgramPredicate} {closedEvidence : TraitEvidence}
      {implementation : ProgramImplementationSignature}
      {method : ProgramImplMethodSignature}
      {trait : ProgramTraitSignature}
      {definition : MethodDefinition}
      {substitution : ParameterSubstitution}
      {bodyInstance : BodyInstance}
      {methodEvidence calleeEvidence : EvidenceEnvironment}
      (selects : RequirementSelectsMethod program context callerEvidence
        primary goal methodName definition closedEvidence)
      (closed_shape : ∃ premises,
        closedEvidence = .implementation goal
          (.declaration implementation.id) premises)
      (implementation_mem :
        implementation ∈ program.signatures.implementations)
      (trait_mem : trait ∈ program.signatures.traits)
      (trait_name : trait.name = traitName)
      (goal_trait : goal.trait = .declaration trait.id)
      (head_determined : ImplementationHeadDetermines implementation goal
        substitution)
      (method_mem : method ∈ implementation.methods)
      (method_name : method.name = methodName)
      (method_owner : method.traitMethod.trait = trait.id)
      (method_requirements : RequirementsProduceEnvironment context
        callerEvidence
        methodRequirements
        (method.wherePredicates.map
          (ProgramPredicate.applyParameters substitution)) methodEvidence)
      (instantiates : TraitMethodInstantiates program implementation method
        trait definition substitution bodyInstance)
      (callee_assembled : EvidenceEnvironment.AssembledFrom callerEvidence
        (closedEvidence :: methodEvidence.map Prod.snd)
        ((methodAssumptions trait implementation method).map
          (ProgramPredicate.applyParameters substitution)) calleeEvidence)
      (callee_covers : calleeEvidence.Covers bodyInstance.context)
      (certificate : ∃ inputTypes lexicalContext facts,
        TraitMethodInstanceTypingCertificate program method substitution definition
          bodyInstance inputTypes lexicalContext facts) :
      TypedOperatorMethodSelected program context callerEvidence traitName methodName
        (primary :: methodRequirements) bodyInstance calleeEvidence


/-- Forget only the static certificate; every actual selection field remains. -/
theorem TypedOperatorMethodSelected.selected
    {program : Program} {context : Context}
    {callerEvidence calleeEvidence : EvidenceEnvironment}
    {traitName methodName : String} {requirements : List RequirementId}
    {bodyInstance : BodyInstance}
    (typed : TypedOperatorMethodSelected program context callerEvidence traitName
      methodName requirements bodyInstance calleeEvidence) :
    OperatorMethodSelected program context callerEvidence traitName methodName
      requirements bodyInstance calleeEvidence := by
  cases typed with
  | intro selects closed implementation trait traitName goal head method methodName owner
      requirements instantiates assembled covers certificate =>
    exact .intro selects closed implementation trait traitName goal head method methodName owner
      requirements instantiates assembled covers

theorem TypedOperatorMethodSelected.certificateOfProfile
    {program : Program} {context : Context}
    {callerEvidence calleeEvidence : EvidenceEnvironment}
    {traitName methodName : String} {operand : Ty}
    {parameterTypes returnTypes : List Ty}
    {predicates : List ProgramPredicate}
    {requirements : List RequirementId} {bodyInstance : BodyInstance}
    (catalog : SignatureCatalogWellFormed program.signatures)
    (signatures_eq : context.signatures = program.signatures)
    (ledger : RequirementIdsUnique context)
    (profile : OperatorProfileInstantiates context traitName methodName operand
      parameterTypes returnTypes predicates)
    (requirementsProve : RequirementSequenceProves context requirements
      predicates)
    (selected : TypedOperatorMethodSelected program context callerEvidence traitName
      methodName requirements bodyInstance calleeEvidence) :
    ∃ lexicalContext facts,
      BodyInstanceTypingCertificate program bodyInstance parameterTypes
          lexicalContext facts ∧
        bodyInstance.resultType = Ty.productMany returnTypes := by
  cases profile with
  | @intro profileTrait profileMethod parameter profileTraitMem traitNameEq
      parametersEq methodUnique parameterTypesEq returnTypesEq =>
    cases selected with
    | @intro primary methodRequirements goal closedEvidence implementation method
        selectedTrait definition substitution _ methodEvidence _ selects
        closedShape implementationMem selectedTraitMem selectedTraitName
        goalTrait headDetermined methodMem methodNameEq methodOwner
        methodRequirementsProduce instantiates calleeAssembled calleeCovers bodyCertificate =>
      have dynamicPrimary : RequirementProves context primary goal := by
        cases selects with
        | intro produces _ => exact produces.requirement_valid
      have primaryGoalEq : goal = {
          trait := .declaration profileTrait.id
          subject := operand
          arguments := []
        } :=
        ledger.proves_predicate_eq dynamicPrimary requirementsProve.head
      have profileTraitMem' : profileTrait ∈ program.signatures.traits := by
        rw [← signatures_eq]
        exact profileTraitMem
      have selectedTraitIdEq : selectedTrait.id = profileTrait.id := by
        have traitRefEq :=
          (congrArg (fun predicate : ProgramPredicate => predicate.trait)
            primaryGoalEq).symm.trans goalTrait
        injection traitRefEq with profileIdEq
        exact profileIdEq.symm
      have selectedTraitEq : selectedTrait = profileTrait :=
        StructuralSubstitution.eq_of_mem_of_mapped_nodup
          catalog.trait_ids selectedTraitMem profileTraitMem'
          selectedTraitIdEq
      subst selectedTrait
      obtain ⟨headKeys, headExact, headEq⟩ := headDetermined
      have headSubjectEq : substitution.apply implementation.head.subject =
          operand := by
        have := congrArg (fun predicate : ProgramPredicate => predicate.subject)
          (headEq.trans primaryGoalEq)
        simpa [ProgramPredicate.applyParameters] using this
      have implementationWellFormed :=
        catalog.implementations_semantic implementation
          implementationMem
      have methodWellFormed := implementationWellFormed.methods method methodMem
      obtain ⟨catalogTrait, catalogMethod, catalogTraitMem, headTraitEq,
          catalogMethodMem, catalogMethodIdEq, catalogMethodName,
          implementationParameterTypesEq, implementationReturnTypesEq,
          parameterComptimeEq, returnComptimeEq,
          implementationPredicatesEq⟩ := methodWellFormed.trait_method
      have catalogMethodWellFormed :=
        (catalog.traits_semantic catalogTrait
          catalogTraitMem).methods catalogMethod catalogMethodMem
      have catalogTraitIdEq : catalogTrait.id = profileTrait.id := by
        calc
          catalogTrait.id = catalogMethod.id.trait :=
            catalogMethodWellFormed.owner.symm
          _ = method.traitMethod.trait :=
            congrArg (fun id => id.trait) catalogMethodIdEq
          _ = profileTrait.id := methodOwner
      have catalogTraitEq : catalogTrait = profileTrait :=
        StructuralSubstitution.eq_of_mem_of_mapped_nodup
          catalog.trait_ids catalogTraitMem profileTraitMem'
          catalogTraitIdEq
      subst catalogTrait
      have catalogMethodNameEq : catalogMethod.name = methodName := by
        rw [catalogMethodName, methodNameEq]
      have catalogMethodFiltered : catalogMethod ∈
          profileTrait.methods.filter
            (fun candidate => candidate.name == methodName) :=
        List.mem_filter.mpr ⟨catalogMethodMem, by simp [catalogMethodNameEq]⟩
      rw [methodUnique] at catalogMethodFiltered
      have catalogMethodEq : catalogMethod = profileMethod := by
        simpa using catalogMethodFiltered
      subst catalogMethod
      have profileTraitWellFormed :=
        catalog.traits_semantic profileTrait profileTraitMem'
      have profileMethodMem : profileMethod ∈ profileTrait.methods := by
        have : profileMethod ∈ profileTrait.methods.filter
            (fun candidate => candidate.name == methodName) := by
          rw [methodUnique]
          simp
        exact (List.mem_filter.mp this).1
      have profileMethodWellFormed :=
        profileTraitWellFormed.methods profileMethod profileMethodMem
      have profileSubstitutionExact :
          SourceSemantics.ParameterSubstitution.Exact [(parameter, operand)]
            profileTrait.parameters := by
        constructor
        · exact profileTraitWellFormed.parameters_nodup
        · rw [parametersEq]
          simp [SourceSemantics.ParameterSubstitution.domain]
      have headSubstitutionExact :
          SourceSemantics.ParameterSubstitution.Exact
            [(parameter, implementation.head.subject)] profileTrait.parameters := by
        constructor
        · exact profileTraitWellFormed.parameters_nodup
        · rw [parametersEq]
          simp [SourceSemantics.ParameterSubstitution.domain]
      have parameterCompose :=
        StructuralSubstitution.TypesWellFormed.applyParameters_compose
          substitution [(parameter, implementation.head.subject)]
          headSubstitutionExact profileMethodWellFormed.parameter_types
      have returnCompose :=
        StructuralSubstitution.TypesWellFormed.applyParameters_compose
          substitution [(parameter, implementation.head.subject)]
          headSubstitutionExact profileMethodWellFormed.return_types
      obtain ⟨actualInputs, lexicalContext, facts, certificate⟩ :=
        bodyCertificate
      have actualInputsEq : actualInputs = parameterTypes := by
        rw [certificate.input_types_eq, implementationParameterTypesEq]
        simp only [parametersEq, List.zip_cons_cons]
        change
          (profileMethod.parameterTypes.map
            (TypeSystem.ParameterSubstitution.apply
              [(parameter, implementation.head.subject)])).map
                substitution.apply = parameterTypes
        rw [parameterCompose]
        simpa [StructuralSubstitution.ParameterSubstitution.mapRange,
          headSubjectEq] using parameterTypesEq
      subst actualInputs
      refine ⟨lexicalContext, facts,
        certificate.toBodyInstanceTypingCertificate, ?_⟩
      rw [certificate.result_type_eq,
        StructuralSubstitution.apply_productMany,
        implementationReturnTypesEq]
      simp only [parametersEq, List.zip_cons_cons]
      change Ty.productMany
          ((profileMethod.returnTypes.map
            (TypeSystem.ParameterSubstitution.apply
              [(parameter, implementation.head.subject)])).map
                substitution.apply) =
        Ty.productMany returnTypes
      rw [returnCompose]
      congr 1
      simpa [StructuralSubstitution.ParameterSubstitution.mapRange,
        headSubjectEq] using returnTypesEq

/-- The coercion profile is the two-parameter specialization of the same
catalog bridge: the selected body accepts exactly the source value and returns
exactly the target type. -/
theorem TypedOperatorMethodSelected.coercionCertificateOfProfile
    {program : Program} {context : Context}
    {callerEvidence calleeEvidence : EvidenceEnvironment}
    {source target : Ty} {primary : ProgramPredicate}
    {methodPredicates : List ProgramPredicate}
    {requirements : List RequirementId} {bodyInstance : BodyInstance}
    (catalog : SignatureCatalogWellFormed program.signatures)
    (signatures_eq : context.signatures = program.signatures)
    (ledger : RequirementIdsUnique context)
    (profile : CoercionProfileInstantiates context source target primary
      methodPredicates)
    (requirementsProve : RequirementSequenceProves context requirements
      (primary :: methodPredicates))
    (selected : TypedOperatorMethodSelected program context callerEvidence "Coerce"
      "coerce" requirements bodyInstance calleeEvidence) :
    ∃ lexicalContext facts,
      BodyInstanceTypingCertificate program bodyInstance [source]
          lexicalContext facts ∧
        bodyInstance.resultType = target := by
  cases profile with
  | @intro profileTrait profileMethod fromParameter toParameter profileTraitMem
      traitNameEq parametersEq methodUnique parameterTypesEq returnTypesEq =>
    cases selected with
    | @intro selectedPrimary methodRequirements goal closedEvidence
        implementation method selectedTrait definition substitution _
        methodEvidence _ selects closedShape implementationMem selectedTraitMem
        selectedTraitName goalTrait headDetermined methodMem methodNameEq
        methodOwner methodRequirementsProduce instantiates calleeAssembled
        calleeCovers bodyCertificate =>
      have dynamicPrimary : RequirementProves context selectedPrimary goal := by
        cases selects with
        | intro produces _ => exact produces.requirement_valid
      have primaryGoalEq : goal = {
          trait := .declaration profileTrait.id
          subject := source
          arguments := [target]
        } :=
        ledger.proves_predicate_eq dynamicPrimary requirementsProve.head
      have profileTraitMem' : profileTrait ∈ program.signatures.traits := by
        rw [← signatures_eq]
        exact profileTraitMem
      have selectedTraitIdEq : selectedTrait.id = profileTrait.id := by
        have traitRefEq :=
          (congrArg (fun predicate : ProgramPredicate => predicate.trait)
            primaryGoalEq).symm.trans goalTrait
        injection traitRefEq with profileIdEq
        exact profileIdEq.symm
      have selectedTraitEq : selectedTrait = profileTrait :=
        StructuralSubstitution.eq_of_mem_of_mapped_nodup
          catalog.trait_ids selectedTraitMem profileTraitMem'
          selectedTraitIdEq
      subst selectedTrait
      obtain ⟨headKeys, headExact, headEq⟩ := headDetermined
      have instantiatedHeadEq :
          ProgramPredicate.applyParameters substitution implementation.head = {
            trait := .declaration profileTrait.id
            subject := source
            arguments := [target]
          } := headEq.trans primaryGoalEq
      have headSubjectEq : substitution.apply implementation.head.subject =
          source := by
        have := congrArg (fun predicate : ProgramPredicate => predicate.subject)
          instantiatedHeadEq
        simpa [ProgramPredicate.applyParameters] using this
      cases headArgumentsEq : implementation.head.arguments with
      | nil =>
          have impossible :=
            congrArg (fun predicate : ProgramPredicate => predicate.arguments)
              instantiatedHeadEq
          simp [ProgramPredicate.applyParameters, headArgumentsEq] at impossible
      | cons headArgument tailArguments =>
        have headArgumentEq : substitution.apply headArgument = target := by
          have argumentsEq :=
            congrArg (fun predicate : ProgramPredicate => predicate.arguments)
              instantiatedHeadEq
          simpa [ProgramPredicate.applyParameters, headArgumentsEq] using
            congrArg List.head? argumentsEq
        have implementationWellFormed :=
          catalog.implementations_semantic implementation
            implementationMem
        have methodWellFormed :=
          implementationWellFormed.methods method methodMem
        obtain ⟨catalogTrait, catalogMethod, catalogTraitMem, headTraitEq,
            catalogMethodMem, catalogMethodIdEq, catalogMethodName,
            implementationParameterTypesEq, implementationReturnTypesEq,
            parameterComptimeEq, returnComptimeEq,
            implementationPredicatesEq⟩ := methodWellFormed.trait_method
        have catalogMethodWellFormed :=
          (catalog.traits_semantic catalogTrait
            catalogTraitMem).methods catalogMethod catalogMethodMem
        have catalogTraitIdEq : catalogTrait.id = profileTrait.id := by
          calc
            catalogTrait.id = catalogMethod.id.trait :=
              catalogMethodWellFormed.owner.symm
            _ = method.traitMethod.trait :=
              congrArg (fun id => id.trait) catalogMethodIdEq
            _ = profileTrait.id := methodOwner
        have catalogTraitEq : catalogTrait = profileTrait :=
          StructuralSubstitution.eq_of_mem_of_mapped_nodup
            catalog.trait_ids catalogTraitMem
            profileTraitMem' catalogTraitIdEq
        subst catalogTrait
        have catalogMethodNameEq : catalogMethod.name = "coerce" := by
          rw [catalogMethodName, methodNameEq]
        have catalogMethodFiltered : catalogMethod ∈
            profileTrait.methods.filter
              (fun candidate => candidate.name == "coerce") :=
          List.mem_filter.mpr
            ⟨catalogMethodMem, by simp [catalogMethodNameEq]⟩
        rw [methodUnique] at catalogMethodFiltered
        have catalogMethodEq : catalogMethod = profileMethod := by
          simpa using catalogMethodFiltered
        subst catalogMethod
        have profileTraitWellFormed :=
          catalog.traits_semantic profileTrait
            profileTraitMem'
        have profileMethodMem : profileMethod ∈ profileTrait.methods := by
          have : profileMethod ∈ profileTrait.methods.filter
              (fun candidate => candidate.name == "coerce") := by
            rw [methodUnique]
            simp
          exact (List.mem_filter.mp this).1
        have profileMethodWellFormed :=
          profileTraitWellFormed.methods profileMethod profileMethodMem
        have headSubstitutionExact :
            SourceSemantics.ParameterSubstitution.Exact
              [(fromParameter, implementation.head.subject),
                (toParameter, headArgument)] profileTrait.parameters := by
          constructor
          · exact profileTraitWellFormed.parameters_nodup
          · rw [parametersEq]
            simp [SourceSemantics.ParameterSubstitution.domain]
        have parameterCompose :=
          StructuralSubstitution.TypesWellFormed.applyParameters_compose
            substitution
            [(fromParameter, implementation.head.subject),
              (toParameter, headArgument)]
            headSubstitutionExact profileMethodWellFormed.parameter_types
        have returnCompose :=
          StructuralSubstitution.TypesWellFormed.applyParameters_compose
            substitution
            [(fromParameter, implementation.head.subject),
              (toParameter, headArgument)]
            headSubstitutionExact profileMethodWellFormed.return_types
        obtain ⟨actualInputs, lexicalContext, facts, certificate⟩ :=
          bodyCertificate
        have actualInputsEq : actualInputs = [source] := by
          rw [certificate.input_types_eq, implementationParameterTypesEq]
          simp only [parametersEq, headArgumentsEq, List.zip_cons_cons]
          change
            (profileMethod.parameterTypes.map
              (TypeSystem.ParameterSubstitution.apply
                [(fromParameter, implementation.head.subject),
                  (toParameter, headArgument)])).map substitution.apply =
              [source]
          rw [parameterCompose]
          simpa [StructuralSubstitution.ParameterSubstitution.mapRange,
            headSubjectEq, headArgumentEq] using parameterTypesEq
        subst actualInputs
        refine ⟨lexicalContext, facts,
          certificate.toBodyInstanceTypingCertificate, ?_⟩
        rw [certificate.result_type_eq,
          StructuralSubstitution.apply_productMany,
          implementationReturnTypesEq]
        simp only [parametersEq, headArgumentsEq, List.zip_cons_cons]
        change Ty.productMany
            ((profileMethod.returnTypes.map
              (TypeSystem.ParameterSubstitution.apply
                [(fromParameter, implementation.head.subject),
                  (toParameter, headArgument)])).map substitution.apply) =
          target
        rw [returnCompose]
        have mappedReturnTypesEq :
            profileMethod.returnTypes.map
                (StructuralSubstitution.ParameterSubstitution.mapRange
                  substitution
                  [(fromParameter, implementation.head.subject),
                    (toParameter, headArgument)]).apply =
              [target] := by
          simpa [StructuralSubstitution.ParameterSubstitution.mapRange,
            headSubjectEq, headArgumentEq] using returnTypesEq
        rw [mappedReturnTypesEq]
        rfl


end Solcore.SourceSemantics.Dynamic
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceAnnotationSummaryUniqueness
/-! The stored statement annotations determine the legacy type/value/return
summary across independent declarative contexts and controls. Occurrence
uniqueness identifies the physical statement node; the mutual typing proof
compares the exact branch bodies and ordered match rows. No expected-result
or control-frame equality is assumed. -/
set_option autoImplicit false
set_option maxRecDepth 10000

namespace Solcore.SourceSemantics.SourceAnnotationSummaryUniqueness

open Frontend SourceInference

private def statementFlags (facts : StatementFacts) : Bool × Bool :=
  (facts.hasValue, facts.sawReturn)

private def bodySummary (facts : BodyFacts) : TypeSystem.Ty × Bool :=
  (facts.type, facts.sawReturn)

private theorem node_annotation
    {source : TypedSource} {control : ControlContext} {context final : Context}
    {id : StatementId} {facts : StatementFacts}
    (typing : StatementHasType source control context id final facts) :
    ∃ node, ContainsStatement source id node ∧ facts.type = node.type := by
  cases typing
  all_goals refine ⟨_, by assumption, ?_⟩
  all_goals symm; assumption

private theorem statement_type_eq
    {source : TypedSource} {leftControl rightControl : ControlContext}
    {leftContext leftFinal rightContext rightFinal : Context}
    {id : StatementId} {leftFacts rightFacts : StatementFacts}
    (unique : NodeOccurrencesUnique source)
    (left : StatementHasType source leftControl leftContext id leftFinal leftFacts)
    (right : StatementHasType source rightControl rightContext id rightFinal rightFacts) :
    leftFacts.type = rightFacts.type := by
  obtain ⟨leftNode, leftContains, leftAnnotation⟩ := node_annotation left
  obtain ⟨rightNode, rightContains, rightAnnotation⟩ := node_annotation right
  have same : leftNode = rightNode := Option.some.inj
    ((lookupStatement?_complete unique leftContains).symm.trans
      (lookupStatement?_complete unique rightContains))
  exact leftAnnotation.trans ((congrArg StatementNode.type same).trans rightAnnotation.symm)

private theorem all_returns_eq {left right : List BodyFacts}
    (same : left.map bodySummary = right.map bodySummary) :
    allBodiesSawReturn left = allBodiesSawReturn right := by
  have projected := congrArg (fun rows : List (TypeSystem.Ty × Bool) =>
    rows.all Prod.snd) same
  simpa only [List.all_map, Function.comp_def, bodySummary,
    allBodiesSawReturn] using projected

/-- Every nontrivial motive quantifies over a second independent derivation.
The expression, assignment and header judgments carry no summary obligation.
The local node and annotation lemmas are exact consequences of the two actual
membership/typing receipts, rather than new source assumptions. -/
local macro "summary_induction" "(" recursor:term "," source:term ","
    unique:term "," typing:term ")" : term =>
  `(by
    have nodeUnique : ∀ {id : StatementId} {left right : StatementNode},
        ContainsStatement $source id left → ContainsStatement $source id right →
        left = right := by
      intro id left right first second
      exact Option.some.inj
        ((lookupStatement?_complete $unique first).symm.trans
          (lookupStatement?_complete $unique second))
    have annotationUnique :
        ∀ {leftControl rightControl : ControlContext}
          {leftContext leftFinal rightContext rightFinal : Context}
          {id : StatementId} {leftFacts rightFacts : StatementFacts},
          StatementHasType $source leftControl leftContext id leftFinal leftFacts →
          StatementHasType $source rightControl rightContext id rightFinal rightFacts →
          leftFacts.type = rightFacts.type := by
      intro leftControl rightControl leftContext leftFinal rightContext rightFinal
        id leftFacts rightFacts left right
      exact statement_type_eq $unique left right
    intro otherControl otherContext otherFinal otherFacts
    refine $recursor (source := $source) (t := $typing)
      (motive_1 := fun _ _ _ _ => True)
      (motive_2 := fun _ _ _ _ _ => True)
      (motive_3 := fun _ _ _ _ => True)
      (motive_4 := fun _ _ _ _ _ => True)
      (motive_5 := fun _ _ _ _ => True)
      (motive_6 := fun _ _ _ _ _ => True)
      (motive_7 := fun _ _ _ => True)
      (motive_8 := fun _ _ id _ facts _ =>
        ∀ {otherControl : ControlContext} {otherContext otherFinal : Context}
          {otherFacts : StatementFacts}
          (other : StatementHasType $source otherControl otherContext id
            otherFinal otherFacts),
          statementFlags facts = statementFlags otherFacts)
      (motive_9 := fun _ _ statements _ facts _ =>
        ∀ {otherControl : ControlContext} {otherContext otherFinal : Context}
          {otherFacts : BodyFacts}
          (other : StatementsHaveType $source otherControl otherContext statements
            otherFinal otherFacts),
          bodySummary facts = bodySummary otherFacts)
      (motive_10 := fun _ _ _ _ _ => True)
      (motive_11 := fun _ _ _ _ _ => True)
      (motive_12 := fun _ _ _ arm facts _ =>
        ∀ {otherControl : ControlContext} {otherContext : Context}
          {otherType : TypeSystem.Ty} {otherFacts : BodyFacts}
          (other : MatchCaseHasType $source otherControl otherContext otherType
            arm otherFacts),
          bodySummary facts = bodySummary otherFacts)
      (motive_13 := fun _ _ _ arms facts _ =>
        ∀ {otherControl : ControlContext} {otherContext : Context}
          {otherType : TypeSystem.Ty} {otherFacts : List BodyFacts}
          (other : MatchCasesHaveType $source otherControl otherContext otherType
            arms otherFacts),
          facts.map bodySummary = otherFacts.map bodySummary)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals try { intros; exact True.intro }
    all_goals intros
    all_goals rename_i other
    all_goals cases other
    all_goals grind [statementFlags, bodySummary, BodyFacts.empty,
      BodyFacts.singleton, BodyFacts.cons, all_returns_eq])

private theorem statement_flags_eq
    {source : TypedSource} {leftControl rightControl : ControlContext}
    {leftContext leftFinal rightContext rightFinal : Context}
    {id : StatementId} {leftFacts rightFacts : StatementFacts}
    (unique : NodeOccurrencesUnique source)
    (left : StatementHasType source leftControl leftContext id leftFinal leftFacts)
    (right : StatementHasType source rightControl rightContext id rightFinal rightFacts) :
    statementFlags leftFacts = statementFlags rightFacts := by
  have result :
      ∀ {otherControl : ControlContext} {otherContext otherFinal : Context}
        {otherFacts : StatementFacts},
        StatementHasType source otherControl otherContext id otherFinal otherFacts →
        statementFlags leftFacts = statementFlags otherFacts :=
    summary_induction(StatementHasType.rec, source, unique, left)
  exact result right

/-- The same physical statement fixes its type, value flag and return flag,
without identifying the two lexical contexts or control contexts. -/
theorem statement_summary_eq
    {source : TypedSource} {leftControl rightControl : ControlContext}
    {leftContext leftFinal rightContext rightFinal : Context}
    {id : StatementId} {leftFacts rightFacts : StatementFacts}
    (unique : NodeOccurrencesUnique source)
    (left : StatementHasType source leftControl leftContext id leftFinal leftFacts)
    (right : StatementHasType source rightControl rightContext id rightFinal rightFacts) :
    leftFacts.type = rightFacts.type ∧
      leftFacts.hasValue = rightFacts.hasValue ∧
      leftFacts.sawReturn = rightFacts.sawReturn := by
  have flags := statement_flags_eq unique left right
  exact ⟨statement_type_eq unique left right,
    congrArg Prod.fst flags, congrArg Prod.snd flags⟩

/-- Ordered statement lists have the same annotated type and return flag under
any two actual declarative typing derivations at the same unique source. -/
theorem statements_summary_eq
    {source : TypedSource} {leftControl rightControl : ControlContext}
    {leftContext leftFinal rightContext rightFinal : Context}
    {statements : List StatementId} {leftFacts rightFacts : BodyFacts}
    (unique : NodeOccurrencesUnique source)
    (left : StatementsHaveType source leftControl leftContext statements leftFinal leftFacts)
    (right : StatementsHaveType source rightControl rightContext statements rightFinal rightFacts) :
    leftFacts.type = rightFacts.type ∧ leftFacts.sawReturn = rightFacts.sawReturn := by
  have result :
      ∀ {otherControl : ControlContext} {otherContext otherFinal : Context}
        {otherFacts : BodyFacts},
        StatementsHaveType source otherControl otherContext statements otherFinal otherFacts →
        bodySummary leftFacts = bodySummary otherFacts :=
    summary_induction(StatementsHaveType.rec, source, unique, left)
  have same := result right
  exact ⟨congrArg Prod.fst same, congrArg Prod.snd same⟩

/-- BodyHasType alone retains its actual facts annotation; it does not equate
that annotation with the declaration's expected result. -/
theorem body_facts_type_eq
    {source : TypedSource} {leftContext rightContext : Context}
    {leftResult rightResult : TypeSystem.Ty} {leftFacts rightFacts : BodyFacts}
    (unique : NodeOccurrencesUnique source)
    (left : BodyHasType source leftContext leftResult leftFacts)
    (right : BodyHasType source rightContext rightResult rightFacts) :
    leftFacts.type = rightFacts.type := by
  obtain ⟨leftFinal, leftTyped, _, _⟩ := left
  obtain ⟨rightFinal, rightTyped, _, _⟩ := right
  exact (statements_summary_eq unique leftTyped rightTyped).1

/-- Independent annotation equations identify the declaration results once
the actual body facts have been compared. These equations are fields of the
original BodyDefinitionHasType judgment, not desired-result assumptions. -/
theorem annotated_result_eq
    {source : TypedSource} {leftContext rightContext : Context}
    {leftResult rightResult : TypeSystem.Ty} {leftFacts rightFacts : BodyFacts}
    (unique : NodeOccurrencesUnique source)
    (left : BodyHasType source leftContext leftResult leftFacts)
    (right : BodyHasType source rightContext rightResult rightFacts)
    (leftAnnotation : leftFacts.type = leftResult)
    (rightAnnotation : rightFacts.type = rightResult) :
    leftResult = rightResult :=
  leftAnnotation.symm.trans ((body_facts_type_eq unique left right).trans rightAnnotation)

private theorem definition_annotation
    {signatures : ProgramSignatures} {parameters : List TypeSystem.TypeParameterId}
    {assumptions : List ProgramPredicate} {parameterNames : List String}
    {parameterTypes returnTypes : List TypeSystem.Ty}
    {parameterComptime : List Bool} {returnComptime : Bool}
    {definition : BodyDefinition} {facts : BodyFacts}
    (typing : BodyDefinitionHasType signatures parameters assumptions parameterNames
      parameterTypes parameterComptime returnTypes returnComptime definition facts) :
    ∃ context, BodyHasType definition.source context definition.resultType facts ∧
      facts.type = definition.resultType := by
  cases typing with
  | @intro lexicalContext _ _ _ _ _ resultType _ _ _ _ _ _ _ _ bodyTyped annotation =>
      refine ⟨lexicalContext, ?_, annotation.trans resultType.symm⟩
      simpa only [resultType] using bodyTyped

/-- Two genuine declaration-body judgments with the same source have the
same declared result, even when their signatures, parameter contexts and
control return indices differ. Both result annotations are extracted from
those original judgments. -/
theorem definition_result_eq
    {leftSignatures rightSignatures : ProgramSignatures}
    {leftParameters rightParameters : List TypeSystem.TypeParameterId}
    {leftAssumptions rightAssumptions : List ProgramPredicate}
    {leftNames rightNames : List String}
    {leftParameterTypes rightParameterTypes leftReturnTypes rightReturnTypes :
      List TypeSystem.Ty}
    {leftParameterComptime rightParameterComptime : List Bool}
    {leftReturnComptime rightReturnComptime : Bool}
    {leftDefinition rightDefinition : BodyDefinition}
    {leftFacts rightFacts : BodyFacts}
    (unique : NodeOccurrencesUnique leftDefinition.source)
    (sameSource : leftDefinition.source = rightDefinition.source)
    (left : BodyDefinitionHasType leftSignatures leftParameters leftAssumptions
      leftNames leftParameterTypes leftParameterComptime leftReturnTypes
      leftReturnComptime leftDefinition leftFacts)
    (right : BodyDefinitionHasType rightSignatures rightParameters rightAssumptions
      rightNames rightParameterTypes rightParameterComptime rightReturnTypes
      rightReturnComptime rightDefinition rightFacts) :
    leftDefinition.resultType = rightDefinition.resultType := by
  obtain ⟨leftContext, leftTyped, leftAnnotation⟩ := definition_annotation left
  obtain ⟨rightContext, rightTyped, rightAnnotation⟩ := definition_annotation right
  have rightAtLeft : BodyHasType leftDefinition.source rightContext
      rightDefinition.resultType rightFacts := by
    rw [sameSource]
    exact rightTyped
  exact annotated_result_eq unique leftTyped rightAtLeft leftAnnotation rightAnnotation

end Solcore.SourceSemantics.SourceAnnotationSummaryUniqueness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceBodyResultAnnotation
/-!
The legacy body result is either unit or a stored statement annotation.
Consequently two rigid substitutions that produce the same source agree on
that result. This follows from one original typing derivation and the ordered
source nodes; neither substituted body needs a separate typing derivation.
-/
set_option autoImplicit false

namespace Solcore.SourceSemantics.SourceBodyResultAnnotation
open Frontend SourceInference TypeSystem

private theorem statement_annotation
    {source : TypedSource} {control : ControlContext} {context final : Context}
    {id : StatementId} {facts : StatementFacts}
    (typing : StatementHasType source control context id final facts) :
    ∃ node, ContainsStatement source id node ∧ facts.type = node.type := by
  cases typing
  all_goals refine ⟨_, by assumption, ?_⟩
  all_goals symm; assumption

/-- The body summary selects unit or a physically stored statement type. -/
theorem statements_annotation
    {source : TypedSource} {control : ControlContext} {context final : Context}
    {statements : List StatementId} {facts : BodyFacts}
    (typing : StatementsHaveType source control context statements final facts) :
    facts.type = .unit ∨
      ∃ id node, ContainsStatement source id node ∧ facts.type = node.type := by
  induction statements generalizing context final facts with
  | nil => cases typing; exact Or.inl rfl
  | cons id rest ih =>
      cases typing with
      | singleton head =>
          obtain ⟨node, contained, annotation⟩ := statement_annotation head
          simp only [BodyFacts.singleton]
          split
          · exact Or.inr ⟨id, node, contained, annotation⟩
          · exact Or.inl rfl
      | cons head tail =>
          have tailAnnotation := ih tail
          obtain ⟨node, contained, annotation⟩ := statement_annotation head
          simp only [BodyFacts.cons]
          split
          · exact tailAnnotation
          · split
            · exact Or.inr ⟨id, node, contained, annotation⟩
            · exact tailAnnotation

/-- One original body derivation supplies the result annotation provenance. -/
theorem body_annotation
    {source : TypedSource} {context : Context} {result : Ty} {facts : BodyFacts}
    (typing : BodyHasType source context result facts) :
    facts.type = .unit ∨
      ∃ id node, ContainsStatement source id node ∧ facts.type = node.type := by
  obtain ⟨_, statements, _, _⟩ := typing
  exact statements_annotation statements

/-- Equal rigid instances retain the same ordered node annotations. No range
formation or occurrence-uniqueness premise is needed for this comparison. -/
theorem parameter_instances_result_eq
    {source : TypedSource} {context : Context} {result : Ty} {facts : BodyFacts}
    (typing : BodyHasType source context result facts)
    (left right : ParameterSubstitution)
    (same : StructuralSubstitution.applyTypedSource left source =
      StructuralSubstitution.applyTypedSource right source) :
    left.apply facts.type = right.apply facts.type := by
  rcases body_annotation typing with unit | ⟨id, node, contained, annotation⟩
  · rw [unit]
    rfl
  · have nodes := congrArg TypedSource.nodes same
    change source.nodes.map (StructuralSubstitution.applyNode left) =
      source.nodes.map (StructuralSubstitution.applyNode right) at nodes
    have nodeEq := (List.map_inj_left.mp nodes) (Node.statement node) contained.1
    have statementEq : StructuralSubstitution.applyStatementNode left node =
        StructuralSubstitution.applyStatementNode right node := Node.statement.inj nodeEq
    rw [annotation]
    exact congrArg StatementNode.type statementEq

end Solcore.SourceSemantics.SourceBodyResultAnnotation
end
