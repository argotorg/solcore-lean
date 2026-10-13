import Solcore.SourceSemantics.SelectedBodyTypingCertificates

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
