import Solcore.SourceSemantics.SubstitutionProperties
import Solcore.SourceSemantics.Graph

/-!
Rigid-parameter substitution preserves declarative trait evidence.

Implementation rules bind both rigid parameters and flexible variables.  To
substitute an already-instantiated evidence tree, the outer rigid
substitution is pushed into the ranges of both maps in the implementation
head witness.  Exact binder coverage, together with the collectors proved in
`Traits`, makes that operation commute with head and premise instantiation.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.StructuralSubstitution

open Frontend
open Frontend.SourceInference
open TypeSystem

/-- Push an outer rigid substitution through both ranges of an implementation
head substitution. -/
def mapImplSubstitutionRange (outer : ParameterSubstitution)
    (inner : SourceSemantics.ImplSubstitution) :
    SourceSemantics.ImplSubstitution := {
  parameters := ParameterSubstitution.mapRange outer inner.parameters
  variables := Substitution.mapRange outer inner.variables
}

theorem ImplSubstitution.ExactFor.mapRange
    {inner : SourceSemantics.ImplSubstitution}
    {rule : ProgramImplRule}
    (outer : ParameterSubstitution)
    (exact : inner.ExactFor rule) :
    (mapImplSubstitutionRange outer inner).ExactFor rule := by
  constructor
  · exact StructuralSubstitution.ParameterSubstitution.Exact.mapRange outer
      exact.parameters
  · exact StructuralSubstitution.Substitution.ExactSubstitution.mapRange outer
      exact.variables

private theorem applyType_mapRange_of_covered
    (outer : ParameterSubstitution)
    {inner : SourceSemantics.ImplSubstitution}
    {rule : ProgramImplRule}
    (exact : inner.ExactFor rule)
    {type : Ty}
    (parametersCovered : ∀ parameter,
      TypeParameterOccurs parameter type →
        parameter ∈ implRuleParameters rule)
    (variablesCovered : ∀ metavariable,
      metavariable ∈ type.freeVariables →
        metavariable ∈ implRuleVariables rule) :
    outer.apply (inner.applyType type) =
      (mapImplSubstitutionRange outer inner).applyType type := by
  induction type with
  | @«variable» metavariable =>
      obtain ⟨replacement, member, lookup⟩ :=
        StructuralSubstitution.Substitution.exists_lookup?_eq_some
          exact.variables (variablesCovered metavariable (by simp [Ty.freeVariables]))
      have mappedMember :
          (metavariable, outer.apply replacement) ∈
            Substitution.mapRange outer inner.variables :=
        List.mem_map.mpr ⟨(metavariable, replacement), member, rfl⟩
      have mappedLookup :=
        StructuralSubstitution.Substitution.lookup?_eq_some_of_mem_of_domain_nodup
          (StructuralSubstitution.Substitution.ExactSubstitution.mapRange outer
            exact.variables).domain_nodup mappedMember
      simp [SourceSemantics.ImplSubstitution.applyType,
        mapImplSubstitutionRange, lookup, mappedLookup]
  | @«parameter» parameter =>
      obtain ⟨replacement, member, lookup⟩ :=
        StructuralSubstitution.ParameterSubstitution.exists_lookup?_eq_some
          exact.parameters
          (parametersCovered parameter (by simp [TypeParameterOccurs]))
      have mappedMember :
          (parameter, outer.apply replacement) ∈
            ParameterSubstitution.mapRange outer inner.parameters :=
        List.mem_map.mpr ⟨(parameter, replacement), member, rfl⟩
      have mappedLookup :=
        StructuralSubstitution.ParameterSubstitution.lookup?_eq_some_of_mem_of_domain_nodup
          (StructuralSubstitution.ParameterSubstitution.Exact.mapRange outer
            exact.parameters).domain_nodup mappedMember
      simp [SourceSemantics.ImplSubstitution.applyType,
        mapImplSubstitutionRange, lookup, mappedLookup]
  | constructor constructor => rfl
  | application left right leftInduction rightInduction =>
      simp only [SourceSemantics.ImplSubstitution.applyType,
        TypeSystem.ParameterSubstitution.apply]
      rw [leftInduction
          (fun parameter occurs => parametersCovered parameter (Or.inl occurs))
          (fun metavariable member => variablesCovered metavariable
            (mem_freeVariables_application_iff.mpr (Or.inl member))),
        rightInduction
          (fun parameter occurs => parametersCovered parameter (Or.inr occurs))
          (fun metavariable member => variablesCovered metavariable
            (mem_freeVariables_application_iff.mpr (Or.inr member)))]
  | function domain codomain domainInduction codomainInduction =>
      simp only [SourceSemantics.ImplSubstitution.applyType,
        TypeSystem.ParameterSubstitution.apply]
      rw [domainInduction
          (fun parameter occurs => parametersCovered parameter (Or.inl occurs))
          (fun metavariable member => variablesCovered metavariable
            (mem_freeVariables_function_iff.mpr (Or.inl member))),
        codomainInduction
          (fun parameter occurs => parametersCovered parameter (Or.inr occurs))
          (fun metavariable member => variablesCovered metavariable
            (mem_freeVariables_function_iff.mpr (Or.inr member)))]
  | product left right leftInduction rightInduction =>
      simp only [SourceSemantics.ImplSubstitution.applyType,
        TypeSystem.ParameterSubstitution.apply]
      rw [leftInduction
          (fun parameter occurs => parametersCovered parameter (Or.inl occurs))
          (fun metavariable member => variablesCovered metavariable
            (mem_freeVariables_product_iff.mpr (Or.inl member))),
        rightInduction
          (fun parameter occurs => parametersCovered parameter (Or.inr occurs))
          (fun metavariable member => variablesCovered metavariable
            (mem_freeVariables_product_iff.mpr (Or.inr member)))]
  | mapping key value keyInduction valueInduction =>
      simp only [SourceSemantics.ImplSubstitution.applyType,
        TypeSystem.ParameterSubstitution.apply]
      rw [keyInduction
          (fun parameter occurs => parametersCovered parameter (Or.inl occurs))
          (fun metavariable member => variablesCovered metavariable
            (mem_freeVariables_mapping_iff.mpr (Or.inl member))),
        valueInduction
          (fun parameter occurs => parametersCovered parameter (Or.inr occurs))
          (fun metavariable member => variablesCovered metavariable
            (mem_freeVariables_mapping_iff.mpr (Or.inr member)))]
  | proxy inner induction =>
      simp only [SourceSemantics.ImplSubstitution.applyType,
        TypeSystem.ParameterSubstitution.apply]
      rw [induction
        (fun parameter occurs => parametersCovered parameter occurs)
        (fun metavariable member => variablesCovered metavariable member)]
  | comptime inner induction =>
      simp only [SourceSemantics.ImplSubstitution.applyType,
        TypeSystem.ParameterSubstitution.apply]
      rw [induction
        (fun parameter occurs => parametersCovered parameter occurs)
        (fun metavariable member => variablesCovered metavariable member)]
  | error => rfl

private theorem applyPredicate_mapRange_of_rule_position
    (outer : ParameterSubstitution)
    {inner : SourceSemantics.ImplSubstitution}
    {rule : ProgramImplRule}
    (exact : inner.ExactFor rule)
    {predicate : ProgramPredicate}
    (position : predicate = rule.head ∨ predicate ∈ rule.wherePredicates) :
    ProgramPredicate.applyParameters outer
        (inner.applyPredicate predicate) =
      (mapImplSubstitutionRange outer inner).applyPredicate predicate := by
  have parameterCoverage : ∀ type, type = predicate.subject ∨
      type ∈ predicate.arguments →
      ∀ parameter, TypeParameterOccurs parameter type →
        parameter ∈ implRuleParameters rule := by
    intro type typePosition parameter occurs
    apply mem_implRuleParameters_iff.mpr
    rcases position with rfl | predicateMem
    · apply Or.inl
      rcases typePosition with rfl | argumentMem
      · exact Or.inl occurs
      · exact Or.inr ⟨type, argumentMem, occurs⟩
    · apply Or.inr
      refine ⟨predicate, predicateMem, ?_⟩
      rcases typePosition with rfl | argumentMem
      · exact Or.inl occurs
      · exact Or.inr ⟨type, argumentMem, occurs⟩
  have variableCoverage : ∀ type, type = predicate.subject ∨
      type ∈ predicate.arguments →
      ∀ metavariable, metavariable ∈ type.freeVariables →
        metavariable ∈ implRuleVariables rule := by
    intro type typePosition metavariable occurs
    apply mem_implRuleVariables_iff.mpr
    rcases position with rfl | predicateMem
    · apply Or.inl
      rcases typePosition with rfl | argumentMem
      · exact Or.inl occurs
      · exact Or.inr ⟨type, argumentMem, occurs⟩
    · apply Or.inr
      refine ⟨predicate, predicateMem, ?_⟩
      rcases typePosition with rfl | argumentMem
      · exact Or.inl occurs
      · exact Or.inr ⟨type, argumentMem, occurs⟩
  cases predicate with
  | mk trait subject arguments =>
      simp only [ProgramPredicate.applyParameters,
        SourceSemantics.ImplSubstitution.applyPredicate]
      congr 1
      · exact applyType_mapRange_of_covered outer exact
          (parameterCoverage subject (Or.inl rfl))
          (variableCoverage subject (Or.inl rfl))
      · simp only [List.map_map]
        apply List.map_congr_left
        intro argument argumentMem
        exact applyType_mapRange_of_covered outer exact
          (parameterCoverage argument (Or.inr argumentMem))
          (variableCoverage argument (Or.inr argumentMem))

theorem ImplHeadInstantiates.applyParameters
    (outer : ParameterSubstitution)
    {rule : ProgramImplRule} {goal : ProgramPredicate}
    {premises : List ProgramPredicate}
    (instantiates : ImplHeadInstantiates rule goal premises) :
    ImplHeadInstantiates rule
      (ProgramPredicate.applyParameters outer goal)
      (premises.map (ProgramPredicate.applyParameters outer)) := by
  cases instantiates with
  | intro inner exact headEq premisesEq =>
      refine .intro (mapImplSubstitutionRange outer inner)
        (StructuralSubstitution.ImplSubstitution.ExactFor.mapRange outer exact)
        ?_ ?_
      · rw [← headEq]
        exact (applyPredicate_mapRange_of_rule_position outer exact
          (Or.inl rfl)).symm
      · rw [← premisesEq, List.map_map]
        apply List.map_congr_left
        intro predicate predicateMem
        exact (applyPredicate_mapRange_of_rule_position outer exact
          (Or.inr predicateMem)).symm

/-- Structural action of a rigid substitution on a semantic evidence tree. -/
def applyTraitEvidence (substitution : ParameterSubstitution) :
    TraitEvidence → TraitEvidence
  | .assumption goal =>
      .assumption (ProgramPredicate.applyParameters substitution goal)
  | .implementation goal implId premises =>
      .implementation (ProgramPredicate.applyParameters substitution goal)
        implId (premises.map (applyTraitEvidence substitution))

@[simp] theorem applyTraitEvidence_goal
    (substitution : ParameterSubstitution) (evidence : TraitEvidence) :
    (applyTraitEvidence substitution evidence).goal =
      ProgramPredicate.applyParameters substitution evidence.goal := by
  cases evidence <;> simp [applyTraitEvidence, TraitEvidence.goal]

theorem ImplementationEvidenceRepresents.applyParameters
    (substitution : ParameterSubstitution)
    {retained : TypedTraitResolution.Evidence}
    {semantic : TraitEvidence}
    (represents : ImplementationEvidenceRepresents retained semantic) :
    ImplementationEvidenceRepresents
      (applyEvidence substitution retained)
      (applyTraitEvidence substitution semantic) := by
  refine ImplementationEvidenceRepresents.rec
    (motive_1 := fun retained semantic _ =>
      ImplementationEvidenceRepresents
        (applyEvidence substitution retained)
        (applyTraitEvidence substitution semantic))
    (motive_2 := fun retained semantic _ =>
      Forall₂ ImplementationEvidenceRepresents
        (applyEvidences substitution retained)
        (semantic.map (applyTraitEvidence substitution)))
    ?_ ?_ ?_ represents
  · intro goal implId retainedPremises semanticPremises premises induction
    simpa [applyEvidence, applyEvidences, applyTraitEvidence] using
      (ImplementationEvidenceRepresents.byImpl induction)
  · exact .nil
  · intro retained semantic retainedRest semanticRest head tail
      headInduction tailInduction
    exact .cons headInduction tailInduction

theorem PredicateEvidenceRepresents.applyParameters
    (substitution : ParameterSubstitution)
    {retained : PredicateEvidence} {semantic : TraitEvidence}
    (represents : PredicateEvidenceRepresents retained semantic) :
    PredicateEvidenceRepresents
      (applyPredicateEvidence substitution retained)
      (applyTraitEvidence substitution semantic) := by
  cases represents with
  | assumption goal =>
      simpa [applyPredicateEvidence, applyTraitEvidence] using
        (PredicateEvidenceRepresents.assumption
          (ProgramPredicate.applyParameters substitution goal))
  | implementation implementationRepresents =>
      exact .implementation
        (StructuralSubstitution.ImplementationEvidenceRepresents.applyParameters
          substitution implementationRepresents)

theorem EvidenceValid.applyParameters
    (substitution : ParameterSubstitution)
    {assumptions : List ProgramPredicate} {rules : List ProgramImplRule}
    {goal : ProgramPredicate} {evidence : TraitEvidence}
    (valid : EvidenceValid assumptions rules goal evidence) :
    EvidenceValid
      (assumptions.map (ProgramPredicate.applyParameters substitution)) rules
      (ProgramPredicate.applyParameters substitution goal)
      (applyTraitEvidence substitution evidence) := by
  refine EvidenceValid.rec
    (motive_1 := fun goal evidence _ =>
      EvidenceValid
        (assumptions.map (ProgramPredicate.applyParameters substitution)) rules
        (ProgramPredicate.applyParameters substitution goal)
        (applyTraitEvidence substitution evidence))
    (motive_2 := fun goals evidence _ =>
      Forall₂
        (EvidenceValid
          (assumptions.map (ProgramPredicate.applyParameters substitution))
          rules)
        (goals.map (ProgramPredicate.applyParameters substitution))
        (evidence.map (applyTraitEvidence substitution)))
    ?_ ?_ ?_ ?_ valid
  · intro goal goalMem
    simpa [applyTraitEvidence] using
      (EvidenceValid.assumption
        (List.mem_map.mpr ⟨goal, goalMem, rfl⟩) :
        EvidenceValid
          (assumptions.map (ProgramPredicate.applyParameters substitution))
          rules (ProgramPredicate.applyParameters substitution goal)
          (.assumption (ProgramPredicate.applyParameters substitution goal)))
  · intro rule goal implId premiseGoals premiseEvidence ruleMem idEq
      headInstantiates premisesValid premisesInduction
    simpa [applyTraitEvidence] using
      (EvidenceValid.implementation ruleMem idEq
        (StructuralSubstitution.ImplHeadInstantiates.applyParameters substitution
          headInstantiates) premisesInduction)
  · exact .nil
  · intro goal evidence goals evidenceRest head tail headInduction tailInduction
    exact .cons headInduction tailInduction

theorem RetainedEvidenceValid.applyParameters
    (substitution : ParameterSubstitution)
    {assumptions : List ProgramPredicate} {rules : List ProgramImplRule}
    {goal : ProgramPredicate} {retained : PredicateEvidence}
    (valid : RetainedEvidenceValid assumptions rules goal retained) :
    RetainedEvidenceValid
      (assumptions.map (ProgramPredicate.applyParameters substitution)) rules
      (ProgramPredicate.applyParameters substitution goal)
      (applyPredicateEvidence substitution retained) := by
  cases valid with
  | intro represents semanticValid =>
      exact .intro
        (StructuralSubstitution.PredicateEvidenceRepresents.applyParameters
          substitution represents)
        (StructuralSubstitution.EvidenceValid.applyParameters substitution
          semanticValid)

theorem SolvedRequirementValid.applyParameters
    (substitution : ParameterSubstitution)
    {context : Context} {requirement : SolvedRequirement}
    (valid : SourceSemantics.SolvedRequirementValid context requirement) :
    SourceSemantics.SolvedRequirementValid (applyContext substitution context)
      (applySolvedRequirement substitution requirement) := by
  cases valid with
  | intro evidenceValid =>
      simpa [applyContext, applySolvedRequirement] using
        (SolvedRequirementValid.intro
          (StructuralSubstitution.RetainedEvidenceValid.applyParameters
            substitution evidenceValid))

theorem SolvedRequirementsValid.applyParameters
    (substitution : ParameterSubstitution)
    {context : Context} {requirements : List SolvedRequirement}
    (valid : SourceSemantics.SolvedRequirementsValid context requirements) :
    SourceSemantics.SolvedRequirementsValid (applyContext substitution context)
      (requirements.map (applySolvedRequirement substitution)) := by
  intro requirement member
  rcases List.mem_map.mp member with ⟨original, originalMem, rfl⟩
  exact StructuralSubstitution.SolvedRequirementValid.applyParameters
    substitution (valid original originalMem)

theorem RequirementLedgerWellFormed.applyParameters
    (substitution : ParameterSubstitution)
    {context : Context}
    (wellFormed : SourceSemantics.RequirementLedgerWellFormed context) :
    SourceSemantics.RequirementLedgerWellFormed
      (applyContext substitution context) := by
  constructor
  · simpa [RequirementIdsUnique, applyContext, applySolvedRequirement,
      List.map_map, Function.comp_def] using wellFormed.idsUnique
  · intro requirement member
    change requirement ∈
      context.solvedRequirements.map (applySolvedRequirement substitution) at member
    rcases List.mem_map.mp member with ⟨original, originalMem, rfl⟩
    exact StructuralSubstitution.SolvedRequirementValid.applyParameters
      substitution (wellFormed.entriesValid original originalMem)

/-- Exact/range-valid rigid substitutions automatically satisfy the evidence
premise needed by the structural source-typing transport whenever the source
ledger itself is well formed. -/
theorem ContextSubstitutionValid.ofRequirementLedger
    {substitution : ParameterSubstitution} {context : Context}
    (exact : SourceSemantics.ParameterSubstitution.Exact substitution
      context.typeParameters)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (applyContext substitution context) substitution)
    (ledger : SourceSemantics.RequirementLedgerWellFormed context) :
    ContextSubstitutionValid substitution context := {
  exact
  range
  implementationRequirements := fun requirement _ member _ =>
    StructuralSubstitution.SolvedRequirementValid.applyParameters
      substitution (ledger.entriesValid requirement member)
}

/-- Instantiate a well-typed generic body without exposing the internal
solved-requirement transport premise.  Its validated ledger supplies exactly
the evidence closure required by structural source-typing substitution. -/
theorem BodyDefinitionHasType.instantiate
    {signatures : ProgramSignatures}
    {parameters : List TypeParameterId}
    {assumptions : List ProgramPredicate}
    {parameterNames : List String} {parameterTypes : List Ty}
    {parameterComptime : List Bool} {returnTypes : List Ty}
    {returnComptime : Bool} {definition : BodyDefinition} {facts : BodyFacts}
    (substitution : ParameterSubstitution)
    (catalog : SignatureCatalogWellFormed signatures)
    (exact : SourceSemantics.ParameterSubstitution.Exact substitution parameters)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (applyContext substitution
        (declarationContext signatures definition.owner parameters assumptions
          definition.solvedRequirements)) substitution)
    (typing : BodyDefinitionHasType signatures parameters assumptions
      parameterNames parameterTypes parameterComptime returnTypes returnComptime
      definition facts) :
    ∃ lexicalContext,
      MonoBindersExtend definition.source.owner
        (applyContext substitution
          (declarationContext signatures definition.owner parameters assumptions
            definition.solvedRequirements))
        (definition.source.inputs.map (applyBinder substitution))
        (parameterTypes.map substitution.apply) lexicalContext ∧
      BodyHasType (applyTypedSource substitution definition.source)
        lexicalContext (substitution.apply definition.resultType)
        (applyBodyFacts substitution facts) := by
  exact StructuralSubstitution.BodyDefinitionHasType.instantiate_with_context
    substitution catalog
    (ContextSubstitutionValid.ofRequirementLedger exact range
      (StructuralSubstitution.BodyDefinitionHasType.requirementLedger typing))
    typing

end Solcore.SourceSemantics.StructuralSubstitution

namespace Solcore.SourceSemantics.Dynamic

open Frontend
open Frontend.SourceInference
open TypeSystem

/-- Complete static package for invoking one whole-program body instance. -/
structure BodyInstanceTypingCertificate (program : Program)
    (bodyInstance : BodyInstance) (inputTypes : List Ty)
    (lexicalContext : Context) (facts : BodyFacts) : Prop where
  typing : StructuralSubstitution.StaticBodyInstanceHasType bodyInstance
    inputTypes lexicalContext facts
  graph_closed : OccurrenceGraphClosed bodyInstance.source
  local_identity_ownership : LocalIdentityOwnership bodyInstance.source
  requirement_ledger : RequirementLedgerWellFormed bodyInstance.context
  requirement_ownership : RequirementOwnership bodyInstance.context
    bodyInstance.source
  owner : bodyInstance.context.currentDeclaration = some bodyInstance.source.owner
  locals_empty : bodyInstance.context.locals = []
  type_parameters_empty : bodyInstance.context.typeParameters = []
  type_variables_empty : bodyInstance.context.typeVariables = []
  residual_type_variables_open :
    bodyInstance.context.residualTypeVariables = true
  signatures_eq : bodyInstance.context.signatures = program.signatures

structure FunctionInstanceTypingCertificate (program : Program)
    (instantiation : DeclarationInstantiation) (bodyInstance : BodyInstance)
    (inputTypes : List Ty) (lexicalContext : Context)
    (facts : BodyFacts) extends
    BodyInstanceTypingCertificate program bodyInstance inputTypes lexicalContext
      facts where
  callable_type : instantiation.type =
    .function (Ty.productMany inputTypes) bodyInstance.resultType

structure TraitMethodInstanceTypingCertificate (program : Program)
    (method : ProgramImplMethodSignature) (substitution : ParameterSubstitution)
    (definition : MethodDefinition) (bodyInstance : BodyInstance)
    (inputTypes : List Ty) (lexicalContext : Context)
    (facts : BodyFacts) extends
    BodyInstanceTypingCertificate program bodyInstance inputTypes lexicalContext
      facts where
  input_types_eq : inputTypes = method.parameterTypes.map substitution.apply
  result_type_eq : bodyInstance.resultType =
    substitution.apply (Ty.productMany method.returnTypes)
  callable_type : substitution.apply definition.body.type =
    .function (Ty.productMany inputTypes) bodyInstance.resultType

/-- Whole-program validity turns a structural top-level function
instantiation into the static certificate consumed by call preservation. -/
theorem FunctionInstantiates.certificate
    {program : Program} {instantiation : DeclarationInstantiation}
    {bodyInstance : BodyInstance}
    (programWellFormed : ProgramWellFormed program)
    (instantiates : FunctionInstantiates program instantiation bodyInstance) :
    ∃ inputTypes lexicalContext facts,
      FunctionInstanceTypingCertificate program instantiation bodyInstance
        inputTypes lexicalContext facts := by
  cases instantiates with
  | @intro signature definition _ signatureMem definitionMem declarationEq
      ownerEq instantiationValid sourceEq resultEq contextEq =>
      cases programWellFormed.functions_valid definition definitionMem with
      | @intro typedSignature facts typedSignatureMem typedOwner bodyValid =>
          have typedSignatureEq : typedSignature = signature :=
            StructuralSubstitution.eq_of_mem_of_mapped_nodup
              programWellFormed.signatures.function_ids typedSignatureMem
              signatureMem (by rw [← typedOwner, ownerEq])
          subst typedSignature
          cases instantiationValid with
          | intro selectedSignature selectedSignatureMem selectedDeclarationEq
              substitutionExact substitutionRange typeEq predicatesEq
              parameterComptimeEq returnComptimeEq =>
              have selectedSignatureEq : selectedSignature = signature :=
                StructuralSubstitution.eq_of_mem_of_mapped_nodup
                  programWellFormed.signatures.function_ids
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
                  programWellFormed.signatures substitutionExact rangeAfter
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
              · simpa [contextEq, predicatesEq] using
                  (StructuralSubstitution.RequirementLedgerWellFormed.applyParameters
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
                  programWellFormed.signatures.functions_semantic signature
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

theorem FunctionInstantiates.hasType
    {program : Program} {instantiation : DeclarationInstantiation}
    {bodyInstance : BodyInstance}
    (programWellFormed : ProgramWellFormed program)
    (instantiates : FunctionInstantiates program instantiation bodyInstance) :
    ∃ inputTypes lexicalContext facts,
      StructuralSubstitution.StaticBodyInstanceHasType bodyInstance inputTypes
        lexicalContext facts := by
  obtain ⟨inputTypes, lexicalContext, facts, certificate⟩ :=
    instantiates.certificate programWellFormed
  exact ⟨inputTypes, lexicalContext, facts,
    certificate.toBodyInstanceTypingCertificate.typing⟩

/-- Whole-program validity supplies the same invocation package for a selected
trait implementation method. -/
theorem TraitMethodInstantiates.certificate
    {program : Program}
    {implementation : ProgramImplementationSignature}
    {method : ProgramImplMethodSignature}
    {trait : ProgramTraitSignature} {definition : MethodDefinition}
    {substitution : ParameterSubstitution} {bodyInstance : BodyInstance}
    (programWellFormed : ProgramWellFormed program)
    (instantiates : TraitMethodInstantiates program implementation method trait
      definition substitution bodyInstance) :
    ∃ inputTypes lexicalContext facts,
      TraitMethodInstanceTypingCertificate program method substitution definition
        bodyInstance inputTypes lexicalContext facts := by
  cases instantiates with
  | intro implementationMem methodMem traitMem traitOwner definitionMem
      definitionId ownerEq substitutionExact substitutionRange sourceEq resultEq
      contextEq =>
      cases programWellFormed.methods_valid definition definitionMem with
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
              programWellFormed.signatures.implementation_method_ids
          have typedMethodEq : typedMethod = method :=
            StructuralSubstitution.eq_of_mem_of_mapped_nodup
              methodIdsNodup
              typedMethodCatalogMem methodCatalogMem
              (by rw [← methodIdEq, definitionId])
          subst typedMethod
          have typedImplementationEq : typedImplementation = implementation :=
            StructuralSubstitution.eq_of_mem_of_mapped_nodup
              programWellFormed.signatures.implementation_ids
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
              programWellFormed.signatures.trait_ids typedTraitMem traitMem
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
              substitution programWellFormed.signatures substitutionExact
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
          · simpa [contextEq] using
              (StructuralSubstitution.RequirementLedgerWellFormed.applyParameters
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

theorem TraitMethodInstantiates.hasType
    {program : Program}
    {implementation : ProgramImplementationSignature}
    {method : ProgramImplMethodSignature}
    {trait : ProgramTraitSignature} {definition : MethodDefinition}
    {substitution : ParameterSubstitution} {bodyInstance : BodyInstance}
    (programWellFormed : ProgramWellFormed program)
    (instantiates : TraitMethodInstantiates program implementation method trait
      definition substitution bodyInstance) :
    ∃ inputTypes lexicalContext facts,
      StructuralSubstitution.StaticBodyInstanceHasType bodyInstance inputTypes
        lexicalContext facts := by
  obtain ⟨inputTypes, lexicalContext, facts, certificate⟩ :=
    instantiates.certificate programWellFormed
  exact ⟨inputTypes, lexicalContext, facts,
    certificate.toBodyInstanceTypingCertificate.typing⟩

/-- A statically selected operator profile and the dynamically selected method
name the same catalog method.  Consequently the method body certificate has
the profile's exact input and result types. -/
theorem OperatorMethodSelected.certificateOfProfile
    {program : Program} {context : Context}
    {callerEvidence calleeEvidence : EvidenceEnvironment}
    {traitName methodName : String} {operand : Ty}
    {parameterTypes returnTypes : List Ty}
    {predicates : List ProgramPredicate}
    {requirements : List RequirementId} {bodyInstance : BodyInstance}
    (programWellFormed : ProgramWellFormed program)
    (signatures_eq : context.signatures = program.signatures)
    (ledger : RequirementIdsUnique context)
    (profile : OperatorProfileInstantiates context traitName methodName operand
      parameterTypes returnTypes predicates)
    (requirementsProve : RequirementSequenceProves context requirements
      predicates)
    (selected : OperatorMethodSelected program context callerEvidence traitName
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
        methodRequirementsProduce instantiates calleeAssembled calleeCovers =>
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
          programWellFormed.signatures.trait_ids selectedTraitMem profileTraitMem'
          selectedTraitIdEq
      subst selectedTrait
      obtain ⟨headKeys, headExact, headEq⟩ := headDetermined
      have headSubjectEq : substitution.apply implementation.head.subject =
          operand := by
        have := congrArg (fun predicate : ProgramPredicate => predicate.subject)
          (headEq.trans primaryGoalEq)
        simpa [ProgramPredicate.applyParameters] using this
      have implementationWellFormed :=
        programWellFormed.signatures.implementations_semantic implementation
          implementationMem
      have methodWellFormed := implementationWellFormed.methods method methodMem
      obtain ⟨catalogTrait, catalogMethod, catalogTraitMem, headTraitEq,
          catalogMethodMem, catalogMethodIdEq, catalogMethodName,
          implementationParameterTypesEq, implementationReturnTypesEq,
          parameterComptimeEq, returnComptimeEq,
          implementationPredicatesEq⟩ := methodWellFormed.trait_method
      have catalogMethodWellFormed :=
        (programWellFormed.signatures.traits_semantic catalogTrait
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
          programWellFormed.signatures.trait_ids catalogTraitMem profileTraitMem'
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
        programWellFormed.signatures.traits_semantic profileTrait profileTraitMem'
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
        instantiates.certificate programWellFormed
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
theorem OperatorMethodSelected.coercionCertificateOfProfile
    {program : Program} {context : Context}
    {callerEvidence calleeEvidence : EvidenceEnvironment}
    {source target : Ty} {primary : ProgramPredicate}
    {methodPredicates : List ProgramPredicate}
    {requirements : List RequirementId} {bodyInstance : BodyInstance}
    (programWellFormed : ProgramWellFormed program)
    (signatures_eq : context.signatures = program.signatures)
    (ledger : RequirementIdsUnique context)
    (profile : CoercionProfileInstantiates context source target primary
      methodPredicates)
    (requirementsProve : RequirementSequenceProves context requirements
      (primary :: methodPredicates))
    (selected : OperatorMethodSelected program context callerEvidence "Coerce"
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
        calleeCovers =>
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
          programWellFormed.signatures.trait_ids selectedTraitMem profileTraitMem'
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
          programWellFormed.signatures.implementations_semantic implementation
            implementationMem
        have methodWellFormed :=
          implementationWellFormed.methods method methodMem
        obtain ⟨catalogTrait, catalogMethod, catalogTraitMem, headTraitEq,
            catalogMethodMem, catalogMethodIdEq, catalogMethodName,
            implementationParameterTypesEq, implementationReturnTypesEq,
            parameterComptimeEq, returnComptimeEq,
            implementationPredicatesEq⟩ := methodWellFormed.trait_method
        have catalogMethodWellFormed :=
          (programWellFormed.signatures.traits_semantic catalogTrait
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
            programWellFormed.signatures.trait_ids catalogTraitMem
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
          programWellFormed.signatures.traits_semantic profileTrait
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
          instantiates.certificate programWellFormed
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
