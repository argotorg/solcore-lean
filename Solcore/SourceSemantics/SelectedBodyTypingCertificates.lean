import Solcore.SourceSemantics.TraitSubstitutionProperties

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
