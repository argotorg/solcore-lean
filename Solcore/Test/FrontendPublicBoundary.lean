import Solcore.Frontend

set_option autoImplicit false

namespace Tests

example := @Solcore.Frontend.SourceSpecialization.matchClosedSchemeInstance?
example :=
  @Solcore.Frontend.SourceSpecialization.matchClosedSchemeInstance?_sound

example := @Solcore.Frontend.loadValidatedProgram_success_environment
example := @Solcore.Frontend.loadProgram_success_environment
example := @Solcore.Frontend.loadProgram_success_declarations_nodup
example := @Solcore.Frontend.buildProgramEnvironment_success_modules_nodup
example := @Solcore.Frontend.buildProgramEnvironment_success_declarations_nodup
example :=
  @Solcore.Frontend.buildProgramEnvironment_success_declarations_eq_flatMap
example :=
  @Solcore.Frontend.buildProgramEnvironment_success_declaration_module_exists
example := @Solcore.Frontend.ProgramEnvironment.declaration?_sound
example :=
  @Solcore.Frontend.ProgramEnvironment.declaration?_eq_some_of_mem_of_ids_nodup
example :=
  @Solcore.Frontend.buildProgramEnvironment_success_declaration?_eq_some
example :=
  @Solcore.Frontend.buildProgramEnvironment_success_declaration?_eq_some_iff
example :=
  @Solcore.Frontend.resolveProgramTypeExprWithBudgets_success_variablesBelow
example :=
  @Solcore.Frontend.resolveProgramTypeExprListWithBudgets_success_variablesBelow
example :=
  @Solcore.Frontend.resolveProgramTypeAliasBodyWithBudgets_success_variablesBelow
example :=
  @Solcore.Frontend.ProgramSignatureError.implementationParameterNotInHead
example :=
  @Solcore.Frontend.ProgramSignatureError.missingImplementationTraitPredicate
example := @Solcore.Frontend.buildProgramSignatures_success_implRules_eq
example := @Solcore.Frontend.buildProgramSignatures_success_implRule_mem_iff
example := @Solcore.Frontend.ProgramContractSignature
example := @Solcore.Frontend.ProgramSignatures.contract?
example := @Solcore.Frontend.ProgramFunctionSignature.parameterNames_length
example := @Solcore.Frontend.ProgramFunctionSignature.parameterTypes_length
example := @Solcore.Frontend.ProgramFunctionSignature.parameterComptime_length
example :=
  @Solcore.Frontend.ConstrainedDeclarationScheme.instantiate_parameterSubstitution_domain_permutation
example :=
  @Solcore.Frontend.ConstrainedDeclarationScheme.instantiate_parameterSubstitution_range_is_variable
example :=
  @Solcore.Frontend.ConstrainedDeclarationScheme.instantiate_body
example :=
  @Solcore.Frontend.ConstrainedDeclarationScheme.instantiate_predicates
example := @Solcore.Frontend.buildProgramSignatures_success_function_shape
example :=
  @Solcore.Frontend.buildProgramSignatures_success_function_parameter_names_nodup
example := @Solcore.Frontend.buildProgramSignatures_success_function_scheme_body
example := @Solcore.Frontend.DataSignatureStructuralWellFormed
example :=
  @Solcore.Frontend.DataSignatureStructuralWellFormed.constructor_ids_nodup
example := @Solcore.Frontend.buildProgramSignatures_success_data_structure
example :=
  @Solcore.Frontend.buildProgramSignatures_success_data_constructor_names_nodup
example :=
  @Solcore.Frontend.buildProgramSignatures_success_data_constructor_owners
example :=
  @Solcore.Frontend.buildProgramSignatures_success_data_constructor_positions
example := @Solcore.Frontend.TraitSignatureStructuralWellFormed
example :=
  @Solcore.Frontend.TraitSignatureStructuralWellFormed.method_ids_nodup
example := @Solcore.Frontend.buildProgramSignatures_success_trait_structure
example :=
  @Solcore.Frontend.buildProgramSignatures_success_trait_method_names_nodup
example :=
  @Solcore.Frontend.buildProgramSignatures_success_trait_method_owners
example :=
  @Solcore.Frontend.buildProgramSignatures_success_trait_method_positions
example :=
  @Solcore.Frontend.buildProgramSignatures_success_trait_method_parameter_names_nodup
example := @Solcore.Frontend.ImplementationSignatureStructuralWellFormed
example := @Solcore.Frontend.ImplementationSignatureHeadValidated
example := @Solcore.Frontend.ImplementationSignatureMethodCatalogValidated
example := @Solcore.Frontend.ProgramSignatureFormationError
example := @Solcore.Frontend.SignatureTypeFormationValidated
example := @Solcore.Frontend.SignatureTypesFormationValidated
example := @Solcore.Frontend.SignaturePredicateFormationValidated
example := @Solcore.Frontend.SignaturePredicatesFormationValidated
example := @Solcore.Frontend.ProgramSignatureFormationValidated
example := @Solcore.Frontend.validateProgramSignatureFormation
example := @Solcore.Frontend.validateProgramSignatureFormation_success
example := @Solcore.Frontend.validateResolvedTypeFormation
example := @Solcore.Frontend.validateResolvedTypeFormation_success
example := @Solcore.Frontend.SignatureTypeFormationValidated.apply_eq_self
example := @Solcore.Frontend.SignatureTypesFormationValidated.apply_eq_self
example :=
  @Solcore.Frontend.SignatureTypesFormationValidated.apply_productMany_eq_self
example :=
  @Solcore.Frontend.ImplementationSignatureStructuralWellFormed.method_ids_nodup
example := @Solcore.Frontend.buildProgramSignatures_success_implementation_structure
example :=
  @Solcore.Frontend.buildProgramSignatures_success_implementation_head_validated
example :=
  @Solcore.Frontend.buildProgramSignatures_success_implementation_method_catalog_validated
example :=
  @Solcore.Frontend.buildProgramSignatures_success_implementation_method_names_nodup
example :=
  @Solcore.Frontend.buildProgramSignatures_success_implementation_method_owners
example :=
  @Solcore.Frontend.buildProgramSignatures_success_implementation_method_positions
example :=
  @Solcore.Frontend.buildProgramSignatures_success_implementation_method_parameter_names_nodup
example := @Solcore.Frontend.SignatureParametersWellFormed
example := @Solcore.Frontend.SignatureParametersWellFormed.parameters_nodup
example := @Solcore.Frontend.SignatureParametersWellFormed.parameter_owners
example := @Solcore.Frontend.SignatureParametersWellFormed.parameter_positions
example := @Solcore.Frontend.ProgramSignatureParametersWellFormed
example :=
  @Solcore.Frontend.buildProgramSignatures_success_parameters_wellFormed
example :=
  @Solcore.Frontend.buildProgramSignatures_success_function_parameters
example := @Solcore.Frontend.buildProgramSignatures_success_data_parameters
example := @Solcore.Frontend.buildProgramSignatures_success_trait_parameters
example :=
  @Solcore.Frontend.buildProgramSignatures_success_implementation_parameters
example := @Solcore.Frontend.buildProgramSignatures_success_contract_parameters
example :=
  @Solcore.Frontend.buildProgramSignatures_success_declaration_ids_nodup
example := @Solcore.Frontend.buildProgramSignatures_success_function_ids_nodup
example := @Solcore.Frontend.buildProgramSignatures_success_data_ids_nodup
example := @Solcore.Frontend.data_constructor_ids_nodup_of_structural
example :=
  @Solcore.Frontend.buildProgramSignatures_success_constructor_ids_nodup
example := @Solcore.Frontend.buildProgramSignatures_success_trait_ids_nodup
example := @Solcore.Frontend.trait_signature_eq_of_mem_of_id_eq
example := @Solcore.Frontend.trait_method_ids_nodup_of_structural
example :=
  @Solcore.Frontend.buildProgramSignatures_success_trait_method_ids_nodup
example :=
  @Solcore.Frontend.buildProgramSignatures_success_implementation_ids_nodup
example := @Solcore.Frontend.implementation_method_ids_nodup_of_structural
example :=
  @Solcore.Frontend.buildProgramSignatures_success_implementation_method_ids_nodup
example := @Solcore.Frontend.buildProgramSignatures_success_contract_ids_nodup
example := @Solcore.Frontend.ProgramImplementationSignature.methodAssumptions
example :=
  @Solcore.Frontend.ProgramImplementationSignature.functionSignatureOfMethodWithTrait
example := @Solcore.Frontend.CheckedImplementationMethod
example := @Solcore.Frontend.CheckedProgram.methods
example := @Solcore.Frontend.ImplementationMethodCheckTarget
example := @Solcore.Frontend.implementationMethodCheckTargets
example := @Solcore.Frontend.ImplementationMethodBodyChecked
example := @Solcore.Frontend.ImplementationMethodBodiesChecked
example :=
  @Solcore.Frontend.SourceInference.checkFunctionBody_success_declaration
example :=
  @Solcore.Frontend.SourceInference.checkFunctionBody_success_witness
example := @Solcore.Frontend.SourceInference.FunctionBodiesChecked
example :=
  @Solcore.Frontend.SourceInference.FunctionBodiesChecked.exists_signature_of_function_mem
example := @Solcore.Frontend.SourceInference.State.Header
example := @Solcore.Frontend.SourceInference.State.binderEnvironment
example := @Solcore.Frontend.SourceInference.State.NodesBelowNextOccurrence
example := @Solcore.Frontend.SourceInference.State.InferenceProgress
example := @Solcore.Frontend.SourceInference.State.InferenceProgress.refl
example :=
  @Solcore.Frontend.SourceInference.State.InferenceProgress.of_inference_eq
example := @Solcore.Frontend.SourceInference.State.InferenceProgress.trans
example := @Solcore.Frontend.SourceInference.State.InferenceProgress.fresh
example := @Solcore.Frontend.SourceInference.State.InferenceProgress.withLocals
example :=
  @Solcore.Frontend.SourceInference.State.InferenceProgress.restoreLexicalScope
example :=
  @Solcore.Frontend.SourceInference.State.InferenceProgress.allocateBinder
example :=
  @Solcore.Frontend.SourceInference.State.InferenceProgress.allocateHiddenLocal
example :=
  @Solcore.Frontend.SourceInference.State.InferenceProgress.allocateExpressionId
example :=
  @Solcore.Frontend.SourceInference.State.InferenceProgress.allocateStatementId
example := @Solcore.Frontend.SourceInference.State.InferenceProgress.recordNode
example :=
  @Solcore.Frontend.SourceInference.State.InferenceProgress.modifyExpressionNode
example :=
  @Solcore.Frontend.SourceInference.State.InferenceProgress.modifyStatementNode
example :=
  @Solcore.Frontend.SourceInference.State.InferenceProgress.addRequirementWithId
example :=
  @Solcore.Frontend.SourceInference.State.InferenceProgress.addRequirement
example :=
  @Solcore.Frontend.SourceInference.State.InferenceProgress.addRequirementsWithIds
example :=
  @Solcore.Frontend.SourceInference.State.InferenceProgress.addRequirements
example :=
  @Solcore.Frontend.SourceInference.State.InferenceProgress.markDirectCallRequirements
example :=
  @Solcore.Frontend.SourceInference.State.initial_binderEnvironment
example :=
  @Solcore.Frontend.SourceInference.State.withLocals_binderEnvironment
example :=
  @Solcore.Frontend.SourceInference.State.restoreLexicalScope_binderEnvironment
example :=
  @Solcore.Frontend.SourceInference.State.allocateBinder_binderEnvironment
example :=
  @Solcore.Frontend.SourceInference.State.initial_nodesBelowNextOccurrence
example :=
  @Solcore.Frontend.SourceInference.State.fresh_preserves_nodesBelowNextOccurrence
example :=
  @Solcore.Frontend.SourceInference.State.withLocals_preserves_nodesBelowNextOccurrence
example :=
  @Solcore.Frontend.SourceInference.State.restoreLexicalScope_preserves_nodesBelowNextOccurrence
example :=
  @Solcore.Frontend.SourceInference.State.allocateBinder_preserves_nodesBelowNextOccurrence
example :=
  @Solcore.Frontend.SourceInference.State.allocateHiddenLocal_preserves_nodesBelowNextOccurrence
example :=
  @Solcore.Frontend.SourceInference.State.allocateExpressionId_preserves_nodesBelowNextOccurrence
example :=
  @Solcore.Frontend.SourceInference.State.allocateStatementId_preserves_nodesBelowNextOccurrence
example :=
  @Solcore.Frontend.SourceInference.State.allocateExpressionId_index_lt_nextOccurrence
example :=
  @Solcore.Frontend.SourceInference.State.allocateStatementId_index_lt_nextOccurrence
example :=
  @Solcore.Frontend.SourceInference.State.recordNode_preserves_nodesBelowNextOccurrence
example := @Solcore.Frontend.SourceInference.State.recordNode_nodesPrefix
example :=
  @Solcore.Frontend.SourceInference.State.modifyExpressionNode_preserves_nodesBelowNextOccurrence
example :=
  @Solcore.Frontend.SourceInference.State.modifyStatementNode_preserves_nodesBelowNextOccurrence
example :=
  @Solcore.Frontend.SourceInference.State.addRequirementWithId_preserves_nodesBelowNextOccurrence
example :=
  @Solcore.Frontend.SourceInference.State.addRequirement_preserves_nodesBelowNextOccurrence
example :=
  @Solcore.Frontend.SourceInference.State.addRequirementsWithIds_preserves_nodesBelowNextOccurrence
example :=
  @Solcore.Frontend.SourceInference.State.addRequirements_preserves_nodesBelowNextOccurrence
example :=
  @Solcore.Frontend.SourceInference.State.markDirectCallRequirements_preserves_nodesBelowNextOccurrence
example :=
  @Solcore.Frontend.SourceInference.Detail.inferExprFuel_nextOccurrence_le
example :=
  @Solcore.Frontend.SourceInference.Detail.inferConstructorApplicationFuel_nextOccurrence_le
example :=
  @Solcore.Frontend.SourceInference.Detail.inferConstructorArgumentsFuel_nextOccurrence_le
example :=
  @Solcore.Frontend.SourceInference.Detail.inferStatementsFuel_nextOccurrence_le
example :=
  @Solcore.Frontend.SourceInference.Detail.inferStatementFuel_nextOccurrence_le
example :=
  @Solcore.Frontend.SourceInference.Detail.inferForItemsFuel_nextOccurrence_le
example :=
  @Solcore.Frontend.SourceInference.Detail.inferForItemFuel_nextOccurrence_le
example :=
  @Solcore.Frontend.SourceInference.Detail.inferPlaceFuel_nextOccurrence_le
example :=
  @Solcore.Frontend.SourceInference.Detail.inferAssignedValueFuel_nextOccurrence_le
example :=
  @Solcore.Frontend.SourceInference.Detail.inferExprsFuel_nextOccurrence_le
example :=
  @Solcore.Frontend.SourceInference.Detail.inferExprsFuel_success_ids_fresh
example :=
  @Solcore.Frontend.SourceInference.Detail.inferMatchCasesFuel_nextOccurrence_le
example :=
  @Solcore.Frontend.SourceInference.State.initial_requirementsWellFormed
example := @Solcore.Frontend.SourceInference.State.fresh_preserves_requirementsWellFormed
example := @Solcore.Frontend.SourceInference.State.fresh_requirements_subset
example := @Solcore.Frontend.SourceInference.State.withLocals_requirements_subset
example :=
  @Solcore.Frontend.SourceInference.State.restoreLexicalScope_requirements_subset
example :=
  @Solcore.Frontend.SourceInference.State.allocateBinder_requirements_subset
example :=
  @Solcore.Frontend.SourceInference.State.allocateHiddenLocal_requirements_subset
example :=
  @Solcore.Frontend.SourceInference.State.allocateExpressionId_requirements_subset
example :=
  @Solcore.Frontend.SourceInference.State.allocateStatementId_requirements_subset
example := @Solcore.Frontend.SourceInference.State.recordNode_requirements_subset
example :=
  @Solcore.Frontend.SourceInference.State.modifyExpressionNode_requirements_subset
example :=
  @Solcore.Frontend.SourceInference.State.modifyStatementNode_requirements_subset
example :=
  @Solcore.Frontend.SourceInference.State.markDirectCallRequirements_requirements_subset
example :=
  @Solcore.Frontend.SourceInference.State.addRequirementWithId_requirements_subset
example :=
  @Solcore.Frontend.SourceInference.State.addRequirement_requirements_subset
example :=
  @Solcore.Frontend.SourceInference.State.addRequirementsWithIds_requirements_subset
example :=
  @Solcore.Frontend.SourceInference.State.addRequirements_requirements_subset
example :=
  @Solcore.Frontend.SourceInference.State.withLocals_preserves_requirementsWellFormed
example :=
  @Solcore.Frontend.SourceInference.State.restoreLexicalScope_preserves_requirementsWellFormed
example :=
  @Solcore.Frontend.SourceInference.State.allocateBinder_preserves_requirementsWellFormed
example :=
  @Solcore.Frontend.SourceInference.State.allocateHiddenLocal_preserves_requirementsWellFormed
example :=
  @Solcore.Frontend.SourceInference.State.allocateExpressionId_preserves_requirementsWellFormed
example :=
  @Solcore.Frontend.SourceInference.State.allocateStatementId_preserves_requirementsWellFormed
example :=
  @Solcore.Frontend.SourceInference.State.recordNode_preserves_requirementsWellFormed
example :=
  @Solcore.Frontend.SourceInference.State.modifyExpressionNode_preserves_requirementsWellFormed
example :=
  @Solcore.Frontend.SourceInference.State.modifyStatementNode_preserves_requirementsWellFormed
example :=
  @Solcore.Frontend.SourceInference.State.markDirectCallRequirements_preserves_requirementsWellFormed
example :=
  @Solcore.Frontend.SourceInference.Detail.inferStatementsFuel_state_header
example := @Solcore.Frontend.SourceInference.Detail.unify_resolve_eq
example := @Solcore.Frontend.SourceInference.Detail.unify_preserves_resolve_eq
example :=
  @Solcore.Frontend.SourceInference.Detail.localFunctionsNamed_subset_catalog
example :=
  @Solcore.Frontend.SourceInference.Detail.signaturesForDeclarations_subset_catalog
example :=
  @Solcore.Frontend.SourceInference.Detail.functionsNamed_success_subset_catalog
example :=
  @Solcore.Frontend.SourceInference.Detail.qualifiedFunctionsNamed_success_subset_catalog
example :=
  @Solcore.Frontend.SourceInference.Detail.PlannedCoercionPath.isValid
example :=
  @Solcore.Frontend.SourceInference.Detail.PlannedCoercionStep.ProfileConsistent
example :=
  @Solcore.Frontend.SourceInference.Detail.coercionPlan?_some_isValid
example :=
  @Solcore.Frontend.SourceInference.Detail.coercionPlan?_some_profileConsistent
example :=
  @Solcore.Frontend.SourceInference.Detail.commitCoercionPlan_resolve
example :=
  @Solcore.Frontend.SourceInference.Detail.withExpected_success_coercions_isValid
example :=
  @Solcore.Frontend.SourceInference.Detail.withExpected_success_cases
example :=
  @Solcore.Frontend.SourceInference.Detail.unify_preserves_requirementsWellFormed
example :=
  @Solcore.Frontend.SourceInference.Detail.unify_requirements_subset
example :=
  @Solcore.Frontend.SourceInference.Detail.commitCoercionPlan_preserves_requirementsWellFormed
example := @Solcore.Frontend.SourceInference.RequirementPredicatesCorrespond
example :=
  @Solcore.Frontend.SourceInference.Detail.PlannedCoercionStep.CommitCorresponds
example :=
  @Solcore.Frontend.SourceInference.Detail.CoercionPlanCommitCorresponds
example :=
  @Solcore.Frontend.SourceInference.Detail.CoercionPlanCommitCorresponds.mono
example :=
  @Solcore.Frontend.SourceInference.Detail.CoercionPlanCommitCorresponds.isValid
example :=
  @Solcore.Frontend.SourceInference.Detail.withExpected_requirements_subset
example :=
  @Solcore.Frontend.SourceInference.Detail.commitCoercionPlan_corresponds
example :=
  @Solcore.Frontend.SourceInference.Detail.commitCoercionPlan_isValid
example :=
  @Solcore.Frontend.SourceInference.Detail.commitCoercionPlan_requirementPredicates
example :=
  @Solcore.Frontend.SourceInference.Detail.withExpected_preserves_requirementsWellFormed
example :=
  @Solcore.Frontend.SourceInference.Detail.candidateWithExpected_preserves_requirementsWellFormed
example :=
  @Solcore.Frontend.SourceInference.Detail.candidateWithExpected_requirements_subset
example :=
  @Solcore.Frontend.SourceInference.Detail.fitArguments_preserves_requirementsWellFormed
example :=
  @Solcore.Frontend.SourceInference.Detail.fitArguments_requirements_subset
example :=
  @Solcore.Frontend.SourceInference.Detail.tryFunctionCandidate_preserves_requirementsWellFormed
example :=
  @Solcore.Frontend.SourceInference.Detail.tryFunctionCandidate_requirements_subset
example :=
  @Solcore.Frontend.SourceInference.Detail.selectFunctionCandidateFrom_requirements_subset
example :=
  @Solcore.Frontend.SourceInference.Detail.selectFunctionCandidate_requirements_subset
example :=
  @Solcore.Frontend.SourceInference.Detail.inferUnaryOperator_requirements_subset
example :=
  @Solcore.Frontend.SourceInference.Detail.inferBinaryOperator_requirements_subset
example :=
  @Solcore.Frontend.SourceInference.Detail.attachExpressionCoercions_preserves_requirementsWellFormed
example :=
  @Solcore.Frontend.SourceInference.Detail.attachExpressionCoercions_requirements_subset
example :=
  @Solcore.Frontend.SourceInference.Detail.recordExpression_preserves_requirementsWellFormed
example :=
  @Solcore.Frontend.SourceInference.Detail.recordExpression_requirements_subset
example :=
  @Solcore.Frontend.SourceInference.Detail.recordExpressionWithExpected_preserves_requirementsWellFormed
example :=
  @Solcore.Frontend.SourceInference.Detail.recordExpressionWithExpected_requirements_subset
example :=
  @Solcore.Frontend.SourceInference.Detail.recordSelectedCallResult_preserves_requirementsWellFormed
example :=
  @Solcore.Frontend.SourceInference.Detail.recordSelectedCallResult_requirements_subset
example :=
  @Solcore.Frontend.SourceInference.Detail.recordSelectedCall_preserves_requirementsWellFormed
example :=
  @Solcore.Frontend.SourceInference.Detail.recordSelectedCall_requirements_subset
example :=
  @Solcore.Frontend.SourceInference.Detail.recordIndirectCall_preserves_requirementsWellFormed
example :=
  @Solcore.Frontend.SourceInference.Detail.recordIndirectCall_requirements_subset
example :=
  @Solcore.Frontend.SourceInference.Detail.applyFunctionType_requirements_subset
example :=
  @Solcore.Frontend.SourceInference.Detail.bindLambdaParameters_requirements_subset
example :=
  @Solcore.Frontend.SourceInference.Detail.freshTypes_requirements_subset
example :=
  @Solcore.Frontend.SourceInference.Detail.freshDataConstructorInstantiation_requirements_subset
example :=
  @Solcore.Frontend.SourceInference.Detail.inferMatchPatternFuel_requirements_subset
example :=
  @Solcore.Frontend.SourceInference.Detail.unifyBuiltinFunctionArgumentsEqual_requirements_subset
example :=
  @Solcore.Frontend.SourceInference.Detail.recordBuiltinFunctionCall_requirements_subset
example :=
  @Solcore.Frontend.SourceInference.Detail.inferExprFuel_requirements_subset
example :=
  @Solcore.Frontend.SourceInference.Detail.inferConstructorApplicationFuel_requirements_subset
example :=
  @Solcore.Frontend.SourceInference.Detail.inferConstructorArgumentsFuel_requirements_subset
example :=
  @Solcore.Frontend.SourceInference.Detail.inferStatementsFuel_requirements_subset
example :=
  @Solcore.Frontend.SourceInference.Detail.inferStatementFuel_requirements_subset
example :=
  @Solcore.Frontend.SourceInference.Detail.inferForItemsFuel_requirements_subset
example :=
  @Solcore.Frontend.SourceInference.Detail.inferForItemFuel_requirements_subset
example :=
  @Solcore.Frontend.SourceInference.Detail.inferPlaceFuel_requirements_subset
example :=
  @Solcore.Frontend.SourceInference.Detail.inferAssignedValueFuel_requirements_subset
example :=
  @Solcore.Frontend.SourceInference.Detail.inferExprsFuel_requirements_subset
example :=
  @Solcore.Frontend.SourceInference.Detail.inferMatchCasesFuel_requirements_subset
example :=
  @Solcore.Frontend.SourceInference.Detail.tryFunctionCandidate_some_instantiation
example :=
  @Solcore.Frontend.SourceInference.Detail.selectFunctionCandidateFrom_success_candidate
example :=
  @Solcore.Frontend.SourceInference.Detail.selectFunctionCandidateFrom_preserves_requirementsWellFormed
example :=
  @Solcore.Frontend.SourceInference.Detail.selectFunctionCandidate_preserves_requirementsWellFormed
example :=
  @Solcore.Frontend.SourceInference.Detail.resolveSourceType_success_formation
example :=
  @Solcore.Frontend.SourceInference.Detail.resolveSourceType_success_apply_eq_self
example :=
  @Solcore.Frontend.SourceInference.Detail.inferStatementsFuel_preserves_owner
example :=
  @Solcore.Frontend.SourceInference.Detail.inferStatementsFuel_preserves_inputs
example := @Solcore.Frontend.SourceInference.checkFunctionBody_success_type
example :=
  @Solcore.Frontend.SourceInference.checkFunctionBody_success_returnComptime
example :=
  @Solcore.Frontend.SourceInference.checkFunctionBody_success_inferredBodyType
example :=
  @Solcore.Frontend.SourceInference.checkFunctionBody_success_inferredBodyType_eq_declared
example :=
  @Solcore.Frontend.SourceInference.checkFunctionBody_success_typedBody_owner
example :=
  @Solcore.Frontend.SourceInference.checkFunctionBody_success_typedBody_inputs
example :=
  @Solcore.Frontend.SourceInference.checkFunctionBody_success_typedBody_inputs_eq_initial_of_types_fixed
example :=
  @Solcore.Frontend.SourceInference.checkFunctionBody_success_typedBody_inputs_eq_initial
example :=
  @Solcore.Frontend.SourceInference.checkFunctionBody_success_typedBody_inputNames
example :=
  @Solcore.Frontend.SourceInference.checkFunctionBody_success_typedBody_inputComptime
example :=
  @Solcore.Frontend.SourceInference.checkFunctionBodies_success_declaration_ids
example :=
  @Solcore.Frontend.SourceInference.checkFunctionBodies_success_corresponds
example := @Solcore.Frontend.checkImplementationMethodBodies
example := @Solcore.Frontend.checkImplementationMethodBodies_success_ids
example :=
  @Solcore.Frontend.checkImplementationMethodBodies_success_corresponds
example :=
  @Solcore.Frontend.ImplementationMethodBodiesChecked.exists_target_of_method_mem
example :=
  @Solcore.Frontend.checkImplementationMethodBodies_success_member
example := @Solcore.Frontend.checkLoadedProgram_success_environment
example := @Solcore.Frontend.checkLoadedProgram_success_signatures
example := @Solcore.Frontend.checkLoadedProgram_success_signature_formation
example :=
  @Solcore.Frontend.checkLoadedProgram_success_signature_parameters_wellFormed
example :=
  @Solcore.Frontend.checkLoadedProgram_success_function_signature_shape
example :=
  @Solcore.Frontend.checkLoadedProgram_success_data_signature_structure
example :=
  @Solcore.Frontend.checkLoadedProgram_success_trait_signature_structure
example :=
  @Solcore.Frontend.checkLoadedProgram_success_implementation_signature_structure
example :=
  @Solcore.Frontend.checkLoadedProgram_success_implementation_head_validated
example :=
  @Solcore.Frontend.checkLoadedProgram_success_implementation_method_catalog_validated
example := @Solcore.Frontend.checkLoadedProgram_success_ids
example := @Solcore.Frontend.checkLoadedProgram_success_body_checks
example := @Solcore.Frontend.checkLoadedProgram_success_function_body
example := @Solcore.Frontend.checkLoadedProgram_success_method_body
example := @Solcore.Frontend.checkProgram_success_load
example := @Solcore.Frontend.checkProgram_success_signature_formation
example := @Solcore.Frontend.checkProgram_success_ids
example := @Solcore.Frontend.checkProgram_success_body_checks
example := @Solcore.Frontend.checkProgram_success_function_body
example := @Solcore.Frontend.checkProgram_success_method_body
example := @Solcore.Frontend.checkProgram_success_declarations_nodup
example := @Solcore.Frontend.checkProgram_success_signature_declaration_ids_nodup
example :=
  @Solcore.Frontend.checkProgram_success_signature_parameters_wellFormed
example := @Solcore.Frontend.checkProgram_success_function_signature_shape
example := @Solcore.Frontend.checkProgram_success_data_signature_structure
example := @Solcore.Frontend.checkProgram_success_constructor_ids_nodup
example := @Solcore.Frontend.checkProgram_success_trait_signature_structure
example := @Solcore.Frontend.checkProgram_success_trait_method_ids_nodup
example :=
  @Solcore.Frontend.checkProgram_success_implementation_signature_structure
example := @Solcore.Frontend.checkProgram_success_implementation_head_validated
example :=
  @Solcore.Frontend.checkProgram_success_implementation_method_catalog_validated
example := @Solcore.Frontend.checkProgram_success_implementation_method_ids_nodup
example := @Solcore.Frontend.ProgramCheckError.methodInference
example := @Solcore.Frontend.ProgramCheckError.signatureFormation
example := @Solcore.Frontend.ProgramCheckError.methodNoSolution
example := @Solcore.Frontend.ProgramCheckError.methodInconclusive

example := @Solcore.Frontend.TraitResolution.ResolutionEvidenceValid
example := @Solcore.Frontend.TraitResolution.ResolutionPremisesValid
example := @Solcore.Frontend.TraitResolution.resolve_success_sound
example := @Solcore.Frontend.TypedTraitResolution.RuleMatchSubstitution
example := @Solcore.Frontend.TypedTraitResolution.HeadMatchCertificate
example := @Solcore.Frontend.TypedTraitResolution.ruleVariables_nodup
example := @Solcore.Frontend.TypedTraitResolution.ruleParameters_nodup
example := @Solcore.Frontend.TypedTraitResolution.mem_ruleVariables_iff
example := @Solcore.Frontend.TypedTraitResolution.mem_ruleParameters_iff
example := @Solcore.Frontend.TypedTraitResolution.matchImplHeadWithParameters?_certificate
example := @Solcore.Frontend.TypedTraitResolution.matchImplHead?_certificate

example :=
  @Solcore.Frontend.SourceInference.Detail.solveRequirements_ids_nodup
example := @Solcore.Frontend.SourceInference.State.requirementIds_nodup
example :=
  @Solcore.Frontend.SourceInference.State.requirements_length_eq_nextRequirement
example :=
  @Solcore.Frontend.SourceInference.State.requirement_id_lt_nextRequirement
example :=
  @Solcore.Frontend.SourceInference.State.mem_take_requirements_iff
example :=
  @Solcore.Frontend.SourceInference.State.mem_drop_requirements_iff
example :=
  @Solcore.Frontend.SourceInference.State.IntegerLiteralLedgerCorrespondence
example :=
  @Solcore.Frontend.SourceInference.Detail.generalizeValueBlockingRequirements
example :=
  @Solcore.Frontend.SourceInference.Detail.mem_generalizeValueBlockingRequirements_iff
example :=
  @Solcore.Frontend.SourceInference.Detail.generalizeValueBlockedVariables
example :=
  @Solcore.Frontend.SourceInference.Detail.mem_generalizeValueBlockedVariables_iff
example :=
  @Solcore.Frontend.SourceInference.Detail.generalizeValue_scheme_body
example :=
  @Solcore.Frontend.SourceInference.Detail.generalizeValue_scheme_quantified
example :=
  @Solcore.Frontend.SourceInference.Detail.generalizeValue_scheme_quantified_nodup
example :=
  @Solcore.Frontend.SourceInference.Detail.generalizeValue_requirement_depends_on_quantified
example :=
  @Solcore.Frontend.SourceInference.Detail.generalizeValue_requirements_empty_of_quantified_eq_nil
example :=
  @Solcore.Frontend.SourceInference.Detail.generalizeValue_requirement_source
example :=
  @Solcore.Frontend.SourceInference.Detail.generalizeValue_templateIds_sublist
example :=
  @Solcore.Frontend.SourceInference.Detail.generalizeValue_templateIds_fresh
example := @Solcore.Frontend.SourceInference.Detail.supportedIntegerTarget
example :=
  @Solcore.Frontend.SourceInference.Detail.validateOccurrenceTableFrom
example := @Solcore.Frontend.SourceInference.Detail.validateOccurrenceTable
example := @Solcore.Frontend.SourceInference.MatchPatternInstruction.binderIds
example := @Solcore.Frontend.SourceInference.TypedMatchPattern.binderIds
example := @Solcore.Frontend.SourceInference.LocalSchemeTemplateSite
example := @Solcore.Frontend.SourceInference.PrimaryRequirementSite
example := @Solcore.Frontend.SourceInference.ForItemForm.definedLocalIds
example := @Solcore.Frontend.SourceInference.ExpressionForm.definedLocalIds
example := @Solcore.Frontend.SourceInference.StatementForm.definedLocalIds
example := @Solcore.Frontend.SourceInference.Node.definedLocalIds
example := @Solcore.Frontend.SourceInference.TypedSource.definedLocalIds
example := @Solcore.Frontend.SourceInference.ForItemForm.localSchemeTemplateSites
example := @Solcore.Frontend.SourceInference.StatementForm.localSchemeTemplateSites
example := @Solcore.Frontend.SourceInference.Node.localSchemeTemplateSites
example := @Solcore.Frontend.SourceInference.TypedSource.localSchemeTemplateSites
example := @Solcore.Frontend.SourceInference.ForItemForm.localSchemeTemplateIds
example := @Solcore.Frontend.SourceInference.StatementForm.localSchemeTemplateIds
example := @Solcore.Frontend.SourceInference.Node.localSchemeTemplateIds
example := @Solcore.Frontend.SourceInference.TypedSource.localSchemeTemplateIds
example := @Solcore.Frontend.SourceInference.ForItemForm.primaryRequirementIds
example := @Solcore.Frontend.SourceInference.StatementForm.primaryRequirementIds
example := @Solcore.Frontend.SourceInference.Node.primaryRequirementIds
example := @Solcore.Frontend.SourceInference.TypedSource.primaryRequirementIds
example := @Solcore.Frontend.SourceInference.Node.primaryRequirementSites
example := @Solcore.Frontend.SourceInference.TypedSource.primaryRequirementSites
example := @Solcore.Frontend.SourceInference.Detail.localIdMember
example :=
  @Solcore.Frontend.SourceInference.Detail.validateLocalIdentitiesFrom
example :=
  @Solcore.Frontend.SourceInference.Detail.validateSourceLocalIdentities
example := @Solcore.Frontend.SourceInference.Detail.requirementIdMember
example :=
  @Solcore.Frontend.SourceInference.Detail.validateRequirementIdsUniqueFrom
example :=
  @Solcore.Frontend.SourceInference.Detail.validateRequirementIdsContained
example :=
  @Solcore.Frontend.SourceInference.Detail.validateSourceRequirementOwnership
example :=
  @Solcore.Frontend.SourceInference.Detail.validateSourceTemplateTracking
example := @Solcore.Frontend.SourceInference.Detail.sourceContainsNodeId
example := @Solcore.Frontend.SourceInference.Detail.validateSourceRootsFrom
example := @Solcore.Frontend.SourceInference.Detail.validateSourceRoots
example :=
  @Solcore.Frontend.SourceInference.Detail.validateSourceReferencesFrom
example :=
  @Solcore.Frontend.SourceInference.Detail.validateSourceNodeChildren
example :=
  @Solcore.Frontend.SourceInference.Detail.validateSourceChildrenFrom
example := @Solcore.Frontend.SourceInference.Detail.validateSourceChildren
example := @Solcore.Frontend.SourceInference.TypedSource.incomingNodeIds
example := @Solcore.Frontend.SourceInference.TypedSource.lookupNodeId?
example := @Solcore.Frontend.SourceInference.Detail.nodeIdMember
example :=
  @Solcore.Frontend.SourceInference.Detail.validateIncomingNodeIdsFrom
example :=
  @Solcore.Frontend.SourceInference.Detail.collectReachableNodeIdsFuel
example := @Solcore.Frontend.SourceInference.Detail.sourceReachableNodeIds
example := @Solcore.Frontend.SourceInference.Detail.sourceSubtreeNodeIds
example := @Solcore.Frontend.SourceInference.Detail.validateSourceTemplateScope
example :=
  @Solcore.Frontend.SourceInference.Detail.validateSourceTemplateScopesFrom
example := @Solcore.Frontend.SourceInference.Detail.validateSourceTemplateScopes
example :=
  @Solcore.Frontend.SourceInference.Detail.validateAllSourceNodesReachedFrom
example := @Solcore.Frontend.SourceInference.Detail.validateSourceForest
example := @Solcore.Frontend.SourceInference.Detail.validateSourceGraph
example :=
  @Solcore.Frontend.SourceInference.Detail.sourceContainsNodeId_eq_true_iff
example :=
  @Solcore.Frontend.SourceInference.Detail.validateOccurrenceTable_success_nodesOwned
example :=
  @Solcore.Frontend.SourceInference.Detail.validateOccurrenceTable_success_nodeOccurrencesUnique
example :=
  @Solcore.Frontend.SourceInference.Detail.validateSourceLocalIdentities_success_unique
example :=
  @Solcore.Frontend.SourceInference.Detail.validateSourceLocalIdentities_success_owned
example :=
  @Solcore.Frontend.SourceInference.Detail.validateSourceRequirementOwnership_success
example :=
  @Solcore.Frontend.SourceInference.Detail.validateSourceTemplateTracking_success
example :=
  @Solcore.Frontend.SourceInference.Detail.validateSourceTemplateScope_success
example :=
  @Solcore.Frontend.SourceInference.Detail.validateSourceTemplateScopes_success
example :=
  @Solcore.Frontend.SourceInference.Detail.validateSourceRoots_success_rootsExist
example :=
  @Solcore.Frontend.SourceInference.Detail.validateSourceChildren_success_childEdgesExist
example :=
  @Solcore.Frontend.SourceInference.Detail.SourceForestValidationWitness
example :=
  @Solcore.Frontend.SourceInference.Detail.validateSourceForest_success_witness
example :=
  @Solcore.Frontend.SourceInference.Detail.validateSourceForest_success_incomingNodeIds_nodup
example :=
  @Solcore.Frontend.SourceInference.Detail.validateSourceForest_success_allNodesReached
example :=
  @Solcore.Frontend.SourceInference.Detail.SourceGraphValidationWitness
example :=
  @Solcore.Frontend.SourceInference.Detail.validateSourceGraph_success_witness
example :=
  @Solcore.Frontend.SourceInference.Detail.validateSourceGraph_success_nodeOccurrencesUnique
example :=
  @Solcore.Frontend.SourceInference.Detail.validateSourceGraph_success_nodesOwned
example :=
  @Solcore.Frontend.SourceInference.Detail.validateSourceGraph_success_rootsExist
example :=
  @Solcore.Frontend.SourceInference.Detail.validateSourceGraph_success_childEdgesExist
example :=
  @Solcore.Frontend.SourceInference.Detail.validateSourceGraph_success_incomingNodeIds_nodup
example :=
  @Solcore.Frontend.SourceInference.Detail.validateSourceGraph_success_allNodesReached
example :=
  @Solcore.Frontend.SourceInference.Detail.supportedIntegerTarget_eq_true_iff
example :=
  @Solcore.Frontend.SourceInference.Detail.validateIntegerPatternTarget_success_supported
example :=
  @Solcore.Frontend.SourceInference.Detail.validateIntegerPatternTargets_success_supported
example :=
  @Solcore.Frontend.SourceInference.Detail.validateIntegerLiteralTarget_success_supported
example :=
  @Solcore.Frontend.SourceInference.Detail.validateIntegerLiteralTargets_success_supported
example :=
  @Solcore.Frontend.SourceInference.Detail.validateIntegerLiteralNode
example :=
  @Solcore.Frontend.SourceInference.Detail.validateIntegerLiteralNodes
example :=
  @Solcore.Frontend.SourceInference.Detail.validateIntegerLiteralLedger
example :=
  @Solcore.Frontend.SourceInference.Detail.validateIntegerLiteralLedger_success_correspondence
example :=
  @Solcore.Frontend.SourceInference.Detail.defaultIntegerPatternTargets_requirements
example :=
  @Solcore.Frontend.SourceInference.Detail.defaultIntegerLiteralTargets_requirements
example :=
  @Solcore.Frontend.SourceInference.Detail.FinalizeSuccessWitness
example :=
  @Solcore.Frontend.SourceInference.Detail.finalize_success_witness
example := @Solcore.Frontend.SourceInference.Detail.finalize_type
example :=
  @Solcore.Frontend.SourceInference.Detail.finalize_validateSourceGraph
example :=
  @Solcore.Frontend.SourceInference.Detail.finalize_validateSourceLocalIdentities
example :=
  @Solcore.Frontend.SourceInference.Detail.finalize_validateSourceTemplateTracking
example :=
  @Solcore.Frontend.SourceInference.Detail.finalize_validateSourceRequirementOwnership
example :=
  @Solcore.Frontend.SourceInference.Detail.finalize_validateIntegerLiteralLedger
example :=
  @Solcore.Frontend.SourceInference.Detail.finalize_integerLiteralLedgerCorrespondence
example :=
  @Solcore.Frontend.SourceInference.Detail.finalize_integerPatternTarget_supported
example :=
  @Solcore.Frontend.SourceInference.Detail.finalize_integerLiteralTarget_supported
example :=
  @Solcore.Frontend.SourceInference.Detail.finalize_preserves_resolve_eq
example := @Solcore.Frontend.SourceInference.Detail.unify_then_finalize_eq
example :=
  @Solcore.Frontend.SourceInference.Detail.unify_then_finalize_annotation_eq
example := @Solcore.Frontend.SourceInference.Detail.finalize_typedSource
example := @Solcore.Frontend.SourceInference.Detail.finalize_typedSource_owner
example := @Solcore.Frontend.SourceInference.Detail.finalize_typedSource_inputs
example := @Solcore.Frontend.SourceInference.Detail.finalize_typedSource_inputIds
example := @Solcore.Frontend.SourceInference.Detail.finalize_typedSource_inputNames
example := @Solcore.Frontend.SourceInference.Detail.finalize_typedSource_inputComptime
example := @Solcore.Frontend.SourceInference.TypedBinder.applySubstitution_name
example := @Solcore.Frontend.SourceInference.TypedBinder.applySubstitution_comptime
example := @Solcore.Frontend.SourceInference.PlaceResolution.references
example := @Solcore.Frontend.SourceInference.AssignmentResolution.references
example := @Solcore.Frontend.SourceInference.ForItemForm.references
example := @Solcore.Frontend.SourceInference.TypedMatchCase.references
example := @Solcore.Frontend.SourceInference.MatchResolution.references
example := @Solcore.Frontend.SourceInference.ExpressionForm.references
example := @Solcore.Frontend.SourceInference.StatementForm.references
example := @Solcore.Frontend.SourceInference.Node.references
example :=
  @Solcore.Frontend.SourceInference.Node.applySubstitution_references
example :=
  @Solcore.Frontend.SourceInference.CoercionPath.isValid_applySubstitution
example := @Solcore.Frontend.SourceInference.TypedSource.applySubstitution_inputNames
example := @Solcore.Frontend.SourceInference.TypedSource.applySubstitution_inputComptime

example := @Solcore.Frontend.LocalNameTable
example := @Solcore.Frontend.LocalNameTable.lookup?
example := @Solcore.Frontend.LocalNameTable.Lookup
example := @Solcore.Frontend.resolveLocalReference?
example := @Solcore.Frontend.ResolvesLocalReference
example := @Solcore.Frontend.LocalNameTable.lookup?_iff
example := @Solcore.Frontend.LocalNameTable.Lookup.id_unique
example := @Solcore.Frontend.LocalNameTable.Lookup.mem
example := @Solcore.Frontend.LocalNameTable.lookup?_eq_none_iff
example := @Solcore.Frontend.ResolvesLocalReference.complete
example := @Solcore.Frontend.resolveLocalReference?_sound
example := @Solcore.Frontend.resolveLocalReference?_iff
example := @Solcore.Frontend.resolveLocalReference?_eq_some_iff
example := @Solcore.Frontend.ResolvesLocalReference.id_unique
example := @Solcore.Frontend.ResolvesLocalReference.mem
example := @Solcore.Frontend.resolveLocalReference?_eq_none_iff
example := @Solcore.Frontend.resolveLocalReference?_span
example := @Solcore.Frontend.resolveLocalReference?_identifier_value_eq
example := @Solcore.Frontend.resolveLocalReference?_group
example := @Solcore.Frontend.elaborateLocalReference?
example := @Solcore.Frontend.LocalReferenceHasType
example := @Solcore.Frontend.elaborateLocalReference?_sound
example := @Solcore.Frontend.elaborateLocalReference?_complete
example := @Solcore.Frontend.elaborateLocalReference?_iff
example := @Solcore.Frontend.localReferenceHasType_iff_elaborates
example := @Solcore.Frontend.elaborateLocalReference?_core_hasType
example := @Solcore.Frontend.elaborateLocalReference?_eq_none_of_missing_id
example := @Solcore.Frontend.elaborateLocalReference?_eq_none_iff
example := @Solcore.Frontend.LocalReferenceEvaluates
example := @Solcore.Frontend.LocalReferenceEvaluates.deterministic
example := @Solcore.Frontend.LocalReferenceEvaluates.toCore
example := @Solcore.Frontend.LocalReferenceEvaluates.exact_run
example := @Solcore.Frontend.elaborateLocalReference?_evaluates_iff
example := @Solcore.Frontend.LocalReferenceHasType.evaluates
example := @Solcore.Frontend.LocalReferenceEvaluates.preserves_type
example := @Solcore.Frontend.elaborateLocalReference?_exact_run
example := @Solcore.Frontend.elaborateLocalReference?_typed_execution

example := @Solcore.Frontend.resolveLocalExpression?
example := @Solcore.Frontend.ResolvesLocalExpression
example := @Solcore.Frontend.LocalExpressionEvaluates
example := @Solcore.Frontend.LocalExpressionEvaluates.store_eq
example := @Solcore.Frontend.LocalExpressionEvaluates.deterministic
example := @Solcore.Frontend.ResolvesLocalExpression.preserves_evaluation
example := @Solcore.Frontend.ResolvesLocalExpression.reflects_evaluation
example := @Solcore.Frontend.ResolvesLocalExpression.evaluates_iff
example := @Solcore.Frontend.ResolvesLocalExpression.core_evaluates_iff
example := @Solcore.Frontend.elaborateLocalExpression?_evaluates_iff
example := @Solcore.Frontend.elaborateLocalExpression?_run_done_sound
example := @Solcore.Frontend.elaborateLocalExpression?_evaluates_iff_run_done
example := @Solcore.Frontend.elaborateLocalExpression?_typed_execution
example := @Solcore.Frontend.elaborateLocalExpression?_run_never_faults
example := @Solcore.Frontend.ResolvesLocalExpression.complete
example := @Solcore.Frontend.resolveLocalExpression?_sound
example := @Solcore.Frontend.resolveLocalExpression?_iff
example := @Solcore.Frontend.resolveLocalExpression?_eq_none_iff
example := @Solcore.Frontend.ResolvesLocalExpression.deterministic
example := @Solcore.Frontend.resolveLocalExpression?_span
example := @Solcore.Frontend.resolveLocalExpression?_conditional_spans
example := @Solcore.Frontend.resolveLocalExpression?_identifier_value_eq
example := @Solcore.Frontend.resolveLocalExpression?_group
example := @Solcore.Frontend.ResolvesLocalReference.toLocalExpression
example := @Solcore.Frontend.LocalExpressionHasType.evaluates
example := @Solcore.Frontend.LocalExpressionEvaluates.preserves_type
example := @Solcore.Frontend.LocalExpressionHasType
example := @Solcore.Frontend.elaborateLocalExpression?
example := @Solcore.Frontend.LocalExpressionHasType.resolves
example := @Solcore.Frontend.ResolvesLocalExpression.reflects_type
example := @Solcore.Frontend.ResolvesLocalExpression.preserves_type
example := @Solcore.Frontend.ResolvesLocalExpression.typing_iff
example := @Solcore.Frontend.localExpressionHasType_iff_resolves
example := @Solcore.Frontend.elaborateLocalExpression?_sound
example := @Solcore.Frontend.elaborateLocalExpression?_complete
example := @Solcore.Frontend.elaborateLocalExpression?_iff
example := @Solcore.Frontend.localExpressionHasType_iff_elaborates
example := @Solcore.Frontend.elaborateLocalExpression?_core_hasType
example := @Solcore.Frontend.LocalExpressionHasType.type_unique
example := @Solcore.Frontend.elaborateLocalExpression?_type_unique
example := @Solcore.Frontend.elaborateLocalExpression?_eq_none_iff
example := @Solcore.Frontend.elaborateLocalFunctionApplication?
example := @Solcore.Frontend.LocalFunctionApplicationHasType
example := @Solcore.Frontend.LocalFunctionApplicationHasType.call
example := @Solcore.Frontend.LocalFunctionApplicationElaborates
example := @Solcore.Frontend.LocalFunctionApplicationElaborates.call
example := @Solcore.Frontend.elaborateLocalFunctionApplication?_children
example := @Solcore.Frontend.LocalFunctionApplicationElaborates.complete
example := @Solcore.Frontend.elaborateLocalFunctionApplication?_sound
example := @Solcore.Frontend.elaborateLocalFunctionApplication?_iff
example := @Solcore.Frontend.LocalFunctionApplicationElaborates.hasType
example := @Solcore.Frontend.LocalFunctionApplicationHasType.elaborates_exact
example := @Solcore.Frontend.localFunctionApplicationHasType_iff_elaborates
example := @Solcore.Frontend.LocalFunctionApplicationElaborates.result_unique
example := @Solcore.Frontend.LocalFunctionApplicationHasType.type_unique
example := @Solcore.Frontend.LocalFunctionApplicationElaborates.core_hasType
example := @Solcore.Frontend.elaborateLocalFunctionApplication?_core_hasType
example := @Solcore.Frontend.elaborateLocalFunctionApplication?_eq_none_iff
example := @Solcore.Frontend.LocalFunctionApplicationEvaluates
example := @Solcore.Frontend.LocalFunctionApplicationEvaluates.call
example := @Solcore.Frontend.LocalFunctionApplicationEvaluatesWithCost
example := @Solcore.Frontend.LocalFunctionApplicationEvaluatesWithCost.call
example := @Solcore.Frontend.LocalFunctionApplicationEvaluates.deterministic
example := @Solcore.Frontend.LocalFunctionApplicationEvaluatesWithCost.erase
example := @Solcore.Frontend.LocalFunctionApplicationEvaluates.exists_cost
example := @Solcore.Frontend.localFunctionApplicationEvaluates_iff_exists_cost
example := @Solcore.Frontend.LocalFunctionApplicationEvaluatesWithCost.cost_pos
example := @Solcore.Frontend.LocalFunctionApplicationEvaluatesWithCost.deterministic
example := @Solcore.Frontend.LocalFunctionApplicationEvaluatesWithCost.cost_unique
example := @Solcore.Frontend.CostStepComposition.apply
example := @Solcore.Frontend.LocalFunctionApplicationElaborates.evaluates_iff
example := @Solcore.Frontend.LocalFunctionApplicationEvaluatesWithCost.toStepsWithContinuation
example := @Solcore.Frontend.LocalFunctionApplicationEvaluatesWithCost.toSteps
example := @Solcore.Frontend.LocalFunctionApplicationElaborates.evaluatesWithCost_iff_steps
example := @Solcore.Frontend.LocalFunctionApplicationElaborates.evaluates_iff_exists_uniform_steps
example := @Solcore.Frontend.elaborateLocalFunctionApplication?_evaluates_iff
example := @Solcore.Frontend.elaborateLocalFunctionApplication?_evaluatesWithCost_iff_steps
example := @Solcore.Frontend.LocalFunctionApplicationEvaluates.preserves_runtime_type
example := @Solcore.Frontend.LocalFunctionApplicationHasType.runtime_evaluates
example := @Solcore.Frontend.LocalFunctionApplicationElaborates.runtime_typed_execution
example := @Solcore.Frontend.elaborateLocalFunctionApplication?_runtime_run_done_sound
example := @Solcore.Frontend.LocalFunctionApplicationElaborates.runtime_state_hasType
example := @Solcore.Frontend.LocalFunctionApplicationElaborates.runtime_run_never_faults
example := @Solcore.Frontend.LocalFunctionApplicationElaborates.runtime_checkpoint_hasType
example := @Solcore.Frontend.LocalFunctionApplicationElaborates.runtime_checkpoint_never_faults
example := @Solcore.Frontend.LocalInputs.checkApplication?
example := @Solcore.Frontend.LocalInputs.runApplication?
example := @Solcore.Frontend.LocalInputs.checkApplication?_iff_elaborates
example := @Solcore.Frontend.LocalInputs.checkApplication?_iff_hasType
example := @Solcore.Frontend.LocalInputs.runApplication?_eq_some_iff
example := @Solcore.Frontend.LocalInputs.runApplication?_eq_none_iff
example := @Solcore.Frontend.LocalInputs.runApplication?_done_sound
example := @Solcore.Frontend.LocalInputs.runApplication?_done_iff_typed_evaluation
example := @Solcore.Frontend.LocalInputs.runApplication?_done_iff_of_cost
example := @Solcore.Frontend.LocalInputs.runApplication?_outOfFuel_iff_of_cost
example := @Solcore.Frontend.LocalInputs.runApplication?_done_iff_typed_cost
example := @Solcore.Frontend.LocalInputs.runApplication?_residual_of_outOfFuel
example := @Solcore.Frontend.LocalInputs.runApplication?_resume
example := @Solcore.Frontend.LocalInputs.runApplication?_runtime_done_sound
example := @Solcore.Frontend.LocalInputs.runApplication?_runtime_has_exact_cost
example := @Solcore.Frontend.LocalInputs.runApplication?_runtime_never_faults
example := @Solcore.Frontend.elaborateLocalApplicationReturnBody?
example := @Solcore.Frontend.LocalApplicationReturnBodyHasType
example := @Solcore.Frontend.LocalApplicationReturnBodyHasType.application
example := @Solcore.Frontend.LocalApplicationReturnBodyElaborates
example := @Solcore.Frontend.LocalApplicationReturnBodyElaborates.application
example := @Solcore.Frontend.LocalApplicationReturnBodyEvaluates
example := @Solcore.Frontend.LocalApplicationReturnBodyEvaluates.application
example := @Solcore.Frontend.LocalApplicationReturnBodyEvaluatesWithCost
example := @Solcore.Frontend.LocalApplicationReturnBodyEvaluatesWithCost.application
example := @Solcore.Frontend.LocalInputs.checkApplicationReturnBody?
example := @Solcore.Frontend.LocalInputs.runApplicationReturnBody?
example := @Solcore.Frontend.LocalApplicationReturnBodyElaborates.complete
example := @Solcore.Frontend.elaborateLocalApplicationReturnBody?_sound
example := @Solcore.Frontend.elaborateLocalApplicationReturnBody?_iff
example := @Solcore.Frontend.LocalApplicationReturnBodyElaborates.hasType
example := @Solcore.Frontend.LocalApplicationReturnBodyHasType.elaborates_exact
example := @Solcore.Frontend.localApplicationReturnBodyHasType_iff_elaborates
example := @Solcore.Frontend.LocalApplicationReturnBodyElaborates.result_unique
example := @Solcore.Frontend.LocalApplicationReturnBodyHasType.type_unique
example := @Solcore.Frontend.LocalApplicationReturnBodyElaborates.core_hasType
example := @Solcore.Frontend.elaborateLocalApplicationReturnBody?_core_hasType
example := @Solcore.Frontend.elaborateLocalApplicationReturnBody?_eq_none_iff
example := @Solcore.Frontend.LocalApplicationReturnBodyEvaluates.deterministic
example := @Solcore.Frontend.LocalApplicationReturnBodyEvaluatesWithCost.erase
example := @Solcore.Frontend.LocalApplicationReturnBodyEvaluates.exists_cost
example := @Solcore.Frontend.localApplicationReturnBodyEvaluates_iff_exists_cost
example := @Solcore.Frontend.LocalApplicationReturnBodyEvaluatesWithCost.deterministic
example := @Solcore.Frontend.LocalApplicationReturnBodyElaborates.evaluates_iff
example := @Solcore.Frontend.LocalApplicationReturnBodyEvaluatesWithCost.toStepsWithContinuation
example := @Solcore.Frontend.LocalApplicationReturnBodyElaborates.evaluatesWithCost_iff_steps
example := @Solcore.Frontend.LocalInputs.checkApplicationReturnBody?_return
example := @Solcore.Frontend.LocalInputs.runApplicationReturnBody?_return
example := @Solcore.Frontend.LocalInputs.checkApplicationReturnBody?_iff_elaborates
example := @Solcore.Frontend.LocalInputs.runApplicationReturnBody?_eq_some_iff
example := @Solcore.Frontend.LocalInputs.runApplicationReturnBody?_eq_none_iff
example := @Solcore.Frontend.LocalInputs.runApplicationReturnBody?_done_iff_typed_cost
example := @Solcore.Frontend.RuntimeApplicationFunctionCompiles
example := @Solcore.Frontend.compileRuntimeApplicationFunction?
example := @Solcore.Frontend.RuntimeApplicationFunctionPrepares
example := @Solcore.Frontend.prepareRuntimeApplicationFunction?
example := @Solcore.Frontend.runRuntimeApplicationFunction?
example := @Solcore.Frontend.RuntimeApplicationFunctionCompiles.complete
example := @Solcore.Frontend.compileRuntimeApplicationFunction?_sound
example := @Solcore.Frontend.compileRuntimeApplicationFunction?_iff
example := @Solcore.Frontend.RuntimeApplicationFunctionCompiles.result_unique
example := @Solcore.Frontend.compileRuntimeApplicationFunction?_eq_none_iff
example := @Solcore.Frontend.RuntimeApplicationFunctionCompiles.core_hasType
example := @Solcore.Frontend.RuntimeApplicationFunctionPrepares.complete
example := @Solcore.Frontend.prepareRuntimeApplicationFunction?_sound
example := @Solcore.Frontend.prepareRuntimeApplicationFunction?_iff
example := @Solcore.Frontend.RuntimeApplicationFunctionPrepares.result_unique
example := @Solcore.Frontend.prepareRuntimeApplicationFunction?_eq_none_iff
example := @Solcore.Frontend.RuntimeApplicationFunctionPrepares.core_hasType
example := @Solcore.Frontend.runRuntimeApplicationFunction?_eq_some_iff
example := @Solcore.Frontend.runRuntimeApplicationFunction?_eq_none_iff
example := @Solcore.Frontend.RuntimeApplicationFunctionPrepares.run_eq_body
example := @Solcore.Frontend.RuntimeApplicationFunctionPrepares.compiles
example := @Solcore.Frontend.RuntimeApplicationFunctionCompiles.prepare_arguments
example := @Solcore.Frontend.runtimeApplicationFunctionPrepares_toCompiled_iff
example := @Solcore.Frontend.prepareRuntimeApplicationFunction?_factorization
example := @Solcore.Frontend.RuntimeApplicationFunctionCompiles.run_eq
example := @Solcore.Frontend.LocalFunctionApplicationElaborates.core_evaluates_insert_iff
example := @Solcore.Frontend.LocalFunctionApplicationElaborates.core_hasType_insert_iff
example := @Solcore.Frontend.LocalFunctionApplicationElaborates.core_insertion_paths
example := @Solcore.Frontend.LocalFunctionApplicationElaborates.core_steps_insert
example := @Solcore.Frontend.LocalFunctionApplicationElaborates.core_steps_reflect_insert
example := @Solcore.Frontend.LocalFunctionApplicationElaborates.core_steps_insert_iff
example := @Solcore.Frontend.elaborateLocalComputation?
example := @Solcore.Frontend.LocalComputationHasType
example := @Solcore.Frontend.LocalComputationHasType.pure
example := @Solcore.Frontend.LocalComputationHasType.application
example := @Solcore.Frontend.LocalComputationElaborates
example := @Solcore.Frontend.LocalComputationElaborates.pure
example := @Solcore.Frontend.LocalComputationElaborates.application
example := @Solcore.Frontend.LocalComputationEvaluates
example := @Solcore.Frontend.LocalComputationEvaluates.pure
example := @Solcore.Frontend.LocalComputationEvaluates.application
example := @Solcore.Frontend.LocalComputationEvaluatesWithCost
example := @Solcore.Frontend.LocalComputationEvaluatesWithCost.pure
example := @Solcore.Frontend.LocalComputationEvaluatesWithCost.application
example := @Solcore.Frontend.elaborateLocalComputation?_iff
example := @Solcore.Frontend.localComputationHasType_iff_elaborates
example := @Solcore.Frontend.LocalComputationElaborates.core_hasType
example := @Solcore.Frontend.localComputationEvaluates_iff_exists_cost
example := @Solcore.Frontend.LocalComputationEvaluatesWithCost.deterministic
example := @Solcore.Frontend.LocalComputationElaborates.evaluates_iff
example := @Solcore.Frontend.LocalComputationEvaluatesWithCost.toStepsWithContinuation
example := @Solcore.Frontend.LocalComputationElaborates.evaluatesWithCost_iff_steps
example := @Solcore.Frontend.LocalComputationElaborates.core_hasType_insert_iff
example := @Solcore.Frontend.LocalComputationElaborates.core_evaluates_insert_iff
example := @Solcore.Frontend.LocalComputationElaborates.core_insertion_paths
example := @Solcore.Frontend.LocalComputationFragment
example := @Solcore.Frontend.LocalComputationFragment.pure
example := @Solcore.Frontend.LocalComputationFragment.application
example := @Solcore.Frontend.LocalComputationFragment.letE
example := @Solcore.Frontend.LocalComputationFragment.ifE
example := @Solcore.Frontend.elaborateLocalComputationReturnTree?
example := @Solcore.Frontend.LocalComputationReturnTreeHasType
example := @Solcore.Frontend.LocalComputationReturnTreeHasType.bare
example := @Solcore.Frontend.LocalComputationReturnTreeHasType.expression
example := @Solcore.Frontend.LocalComputationReturnTreeHasType.block
example := @Solcore.Frontend.LocalComputationReturnTreeHasType.binding
example := @Solcore.Frontend.LocalComputationReturnTreeHasType.inferred
example := @Solcore.Frontend.LocalComputationReturnTreeHasType.discard
example := @Solcore.Frontend.LocalComputationReturnTreeHasType.conditional
example := @Solcore.Frontend.LocalComputationReturnTreeElaborates
example := @Solcore.Frontend.LocalComputationReturnTreeElaborates.bare
example := @Solcore.Frontend.LocalComputationReturnTreeElaborates.expression
example := @Solcore.Frontend.LocalComputationReturnTreeElaborates.block
example := @Solcore.Frontend.LocalComputationReturnTreeElaborates.binding
example := @Solcore.Frontend.LocalComputationReturnTreeElaborates.inferred
example := @Solcore.Frontend.LocalComputationReturnTreeElaborates.discard
example := @Solcore.Frontend.LocalComputationReturnTreeElaborates.conditional
example := @Solcore.Frontend.LocalComputationReturnTreeEvaluates
example := @Solcore.Frontend.LocalComputationReturnTreeEvaluates.bare
example := @Solcore.Frontend.LocalComputationReturnTreeEvaluates.expression
example := @Solcore.Frontend.LocalComputationReturnTreeEvaluates.block
example := @Solcore.Frontend.LocalComputationReturnTreeEvaluates.binding
example := @Solcore.Frontend.LocalComputationReturnTreeEvaluates.inferred
example := @Solcore.Frontend.LocalComputationReturnTreeEvaluates.discard
example := @Solcore.Frontend.LocalComputationReturnTreeEvaluates.ifTrue
example := @Solcore.Frontend.LocalComputationReturnTreeEvaluates.ifFalse
example := @Solcore.Frontend.LocalComputationReturnTreeEvaluatesWithCost
example := @Solcore.Frontend.LocalComputationReturnTreeEvaluatesWithCost.bare
example := @Solcore.Frontend.LocalComputationReturnTreeEvaluatesWithCost.expression
example := @Solcore.Frontend.LocalComputationReturnTreeEvaluatesWithCost.block
example := @Solcore.Frontend.LocalComputationReturnTreeEvaluatesWithCost.binding
example := @Solcore.Frontend.LocalComputationReturnTreeEvaluatesWithCost.inferred
example := @Solcore.Frontend.LocalComputationReturnTreeEvaluatesWithCost.discard
example := @Solcore.Frontend.LocalComputationReturnTreeEvaluatesWithCost.ifTrue
example := @Solcore.Frontend.LocalComputationReturnTreeEvaluatesWithCost.ifFalse
example := @Solcore.Frontend.LocalComputationFragment.weakenAt
example := @Solcore.Frontend.LocalComputationElaborates.core_fragment
example := @Solcore.Frontend.LocalComputationReturnTreeElaborates.core_fragment
example := @Solcore.Frontend.LocalComputationFragment.evaluates_insert_iff
example := @Solcore.Frontend.LocalComputationFragment.insertion_paths
example := @Solcore.Frontend.elaborateLocalComputationReturnTree?_iff
example := @Solcore.Frontend.localComputationReturnTreeHasType_iff_elaborates
example := @Solcore.Frontend.LocalComputationReturnTreeElaborates.core_hasType
example := @Solcore.Frontend.localComputationReturnTreeEvaluates_iff_exists_cost
example := @Solcore.Frontend.LocalComputationReturnTreeEvaluatesWithCost.deterministic
example := @Solcore.Frontend.TypedLetReturnTreeElaborates.toLocalComputationReturnTree
example := @Solcore.Frontend.LocalComputationReturnTreeElaborates.evaluates_iff
example := @Solcore.Frontend.LocalComputationReturnTreeEvaluatesWithCost.toStepsWithContinuation
example := @Solcore.Frontend.LocalComputationReturnTreeElaborates.evaluatesWithCost_iff_steps
example := @Solcore.Frontend.RuntimeComputationFunctionCompiles
example := @Solcore.Frontend.compileRuntimeComputationFunction?
example := @Solcore.Frontend.RuntimeComputationFunctionPrepares
example := @Solcore.Frontend.prepareRuntimeComputationFunction?
example := @Solcore.Frontend.runRuntimeComputationFunction?
example := @Solcore.Frontend.compileRuntimeComputationFunction?_iff
example := @Solcore.Frontend.prepareRuntimeComputationFunction?_iff
example := @Solcore.Frontend.prepareRuntimeComputationFunction?_factorization
example := @Solcore.Frontend.runRuntimeComputationFunction?_factorization
example := @Solcore.Frontend.elaborateRecursiveLocalComputation?
example := @Solcore.Frontend.RecursiveLocalComputationHasType
example := @Solcore.Frontend.RecursiveLocalComputationHasType.pure
example := @Solcore.Frontend.RecursiveLocalComputationHasType.group
example := @Solcore.Frontend.RecursiveLocalComputationHasType.application
example := @Solcore.Frontend.RecursiveLocalComputationElaborates
example := @Solcore.Frontend.RecursiveLocalComputationElaborates.pure
example := @Solcore.Frontend.RecursiveLocalComputationElaborates.group
example := @Solcore.Frontend.RecursiveLocalComputationElaborates.application
example := @Solcore.Frontend.RecursiveLocalComputationEvaluates
example := @Solcore.Frontend.RecursiveLocalComputationEvaluates.pure
example := @Solcore.Frontend.RecursiveLocalComputationEvaluates.group
example := @Solcore.Frontend.RecursiveLocalComputationEvaluates.application
example := @Solcore.Frontend.RecursiveLocalComputationEvaluatesWithCost
example := @Solcore.Frontend.RecursiveLocalComputationEvaluatesWithCost.pure
example := @Solcore.Frontend.RecursiveLocalComputationEvaluatesWithCost.group
example := @Solcore.Frontend.RecursiveLocalComputationEvaluatesWithCost.application
example := @Solcore.Frontend.RecursiveLocalComputationFragment
example := @Solcore.Frontend.RecursiveLocalComputationFragment.pure
example := @Solcore.Frontend.RecursiveLocalComputationFragment.application
example := @Solcore.Frontend.elaborateRecursiveLocalComputation?_iff
example := @Solcore.Frontend.recursiveLocalComputationHasType_iff_elaborates
example := @Solcore.Frontend.RecursiveLocalComputationElaborates.core_hasType
example := @Solcore.Frontend.recursiveLocalComputationEvaluates_iff_exists_cost
example := @Solcore.Frontend.RecursiveLocalComputationEvaluatesWithCost.deterministic
example := @Solcore.Frontend.RecursiveLocalComputationElaborates.evaluates_iff
example := @Solcore.Frontend.RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation
example := @Solcore.Frontend.RecursiveLocalComputationElaborates.evaluatesWithCost_iff_steps
example := @Solcore.Frontend.LocalComputationElaborates.toRecursiveLocalComputation
example := @Solcore.Frontend.LocalComputationEvaluatesWithCost.toRecursiveLocalComputation
example := @Solcore.Frontend.RecursiveLocalComputationFragment.weakenAt
example := @Solcore.Frontend.RecursiveLocalComputationElaborates.core_fragment
example := @Solcore.Frontend.RecursiveLocalComputationFragment.evaluates_insert_iff
example := @Solcore.Frontend.RecursiveLocalComputationFragment.insertion_paths
example := @Solcore.Frontend.DirectWordBinary
example := @Solcore.Frontend.DirectWordBinary.add
example := @Solcore.Frontend.DirectWordBinary.subtract
example := @Solcore.Frontend.DirectWordBinary.multiply
example := @Solcore.Frontend.DirectWordBinary.divide
example := @Solcore.Frontend.DirectWordBinary.modulo
example := @Solcore.Frontend.DirectWordBinary.bitAnd
example := @Solcore.Frontend.DirectWordBinary.bitOr
example := @Solcore.Frontend.DirectWordBinary.bitXor
example := @Solcore.Frontend.DirectWordBinary.greater
example := @Solcore.Frontend.DirectWordBinary.equal
example := @Solcore.Frontend.directWordBinary?
example := @Solcore.Frontend.directWordBinary?_iff
example := @Solcore.Frontend.RecursiveLocalComputationHasType.binary
example := @Solcore.Frontend.RecursiveLocalComputationElaborates.binary
example := @Solcore.Frontend.RecursiveLocalComputationEvaluates.binary
example := @Solcore.Frontend.RecursiveLocalComputationEvaluatesWithCost.binary
example := @Solcore.Frontend.RecursiveLocalComputationFragment.binary
example := @Solcore.Frontend.RecursiveLocalComputationHasType.conditional
example := @Solcore.Frontend.RecursiveLocalComputationElaborates.conditional
example := @Solcore.Frontend.RecursiveLocalComputationEvaluates.ifTrue
example := @Solcore.Frontend.RecursiveLocalComputationEvaluates.ifFalse
example := @Solcore.Frontend.RecursiveLocalComputationEvaluatesWithCost.ifTrue
example := @Solcore.Frontend.RecursiveLocalComputationEvaluatesWithCost.ifFalse
example := @Solcore.Frontend.RecursiveLocalComputationFragment.ifE
example := @Solcore.Frontend.RecursiveLocalComputationHasType.logicalNot
example := @Solcore.Frontend.RecursiveLocalComputationHasType.bitNot
example := @Solcore.Frontend.RecursiveLocalComputationElaborates.logicalNot
example := @Solcore.Frontend.RecursiveLocalComputationElaborates.bitNot
example := @Solcore.Frontend.RecursiveLocalComputationEvaluates.logicalNot
example := @Solcore.Frontend.RecursiveLocalComputationEvaluates.bitNot
example := @Solcore.Frontend.RecursiveLocalComputationEvaluatesWithCost.logicalNot
example := @Solcore.Frontend.RecursiveLocalComputationEvaluatesWithCost.bitNot
example := @Solcore.Frontend.RecursiveLocalComputationFragment.unary
example := @Solcore.Frontend.RecursiveLocalComputationHasType.logicalAnd
example := @Solcore.Frontend.RecursiveLocalComputationHasType.logicalOr
example := @Solcore.Frontend.RecursiveLocalComputationElaborates.logicalAnd
example := @Solcore.Frontend.RecursiveLocalComputationElaborates.logicalOr
example := @Solcore.Frontend.RecursiveLocalComputationEvaluates.andTrue
example := @Solcore.Frontend.RecursiveLocalComputationEvaluates.andFalse
example := @Solcore.Frontend.RecursiveLocalComputationEvaluates.orTrue
example := @Solcore.Frontend.RecursiveLocalComputationEvaluates.orFalse
example := @Solcore.Frontend.RecursiveLocalComputationEvaluatesWithCost.andTrue
example := @Solcore.Frontend.RecursiveLocalComputationEvaluatesWithCost.andFalse
example := @Solcore.Frontend.RecursiveLocalComputationEvaluatesWithCost.orTrue
example := @Solcore.Frontend.RecursiveLocalComputationEvaluatesWithCost.orFalse
example := @Solcore.Frontend.RecursiveLocalComputationHasType.notEqual
example := @Solcore.Frontend.RecursiveLocalComputationHasType.lessEqual
example := @Solcore.Frontend.RecursiveLocalComputationElaborates.notEqual
example := @Solcore.Frontend.RecursiveLocalComputationElaborates.lessEqual
example := @Solcore.Frontend.RecursiveLocalComputationEvaluates.notEqual
example := @Solcore.Frontend.RecursiveLocalComputationEvaluates.lessEqual
example := @Solcore.Frontend.RecursiveLocalComputationEvaluatesWithCost.notEqual
example := @Solcore.Frontend.RecursiveLocalComputationEvaluatesWithCost.lessEqual
example := @Solcore.Frontend.RecursiveLocalComputationHasType.less
example := @Solcore.Frontend.RecursiveLocalComputationHasType.greaterEqual
example := @Solcore.Frontend.RecursiveLocalComputationElaborates.less
example := @Solcore.Frontend.RecursiveLocalComputationElaborates.greaterEqual
example := @Solcore.Frontend.RecursiveLocalComputationEvaluates.less
example := @Solcore.Frontend.RecursiveLocalComputationEvaluates.greaterEqual
example := @Solcore.Frontend.RecursiveLocalComputationEvaluatesWithCost.less
example := @Solcore.Frontend.RecursiveLocalComputationEvaluatesWithCost.greaterEqual
example := @Solcore.Frontend.RecursiveLocalComputationFragment.letE
example := @Solcore.Frontend.RecursiveLocalComputationHasType.pair
example := @Solcore.Frontend.RecursiveLocalComputationHasType.many
example := @Solcore.Frontend.RecursiveLocalComputationElaborates.pair
example := @Solcore.Frontend.RecursiveLocalComputationElaborates.many
example := @Solcore.Frontend.RecursiveLocalComputationEvaluates.pair
example := @Solcore.Frontend.RecursiveLocalComputationEvaluates.many
example := @Solcore.Frontend.RecursiveLocalComputationEvaluatesWithCost.pair
example := @Solcore.Frontend.RecursiveLocalComputationEvaluatesWithCost.many
example := @Solcore.Frontend.RecursiveLocalComputationFragment.pair
example := @Solcore.Frontend.ComputationBodyFragment
example := @Solcore.Frontend.WordMatchPatternDenotes
example := @Solcore.Frontend.interpretWordMatchPattern?
example := @Solcore.Frontend.WordMatchPatternClassifies
example := @Solcore.Frontend.WordMatchPatternClassifies.literal
example := @Solcore.Frontend.WordMatchPatternClassifies.wildcard
example := @Solcore.Frontend.WordMatchPatternClassifies.group
example := @Solcore.Frontend.WordMatchPatternClassifies.tag_unique
example := @Solcore.Frontend.WordMatchPatternClassifies.value_unique
example := @Solcore.Frontend.interpretWordMatchPattern?_iff
example := @Solcore.Frontend.WordMatchChooses
example := @Solcore.Frontend.WordMatchChooses.fallback
example := @Solcore.Frontend.WordMatchChooses.wildcard
example := @Solcore.Frontend.WordMatchChooses.hit
example := @Solcore.Frontend.WordMatchChooses.miss
example := @Solcore.Frontend.WordMatchPatternDenotes.value_unique
example := @Solcore.Frontend.WordMatchChooses.deterministic
example := @Solcore.Frontend.ComputationBodyFragment.wordTest
example := @Solcore.Frontend.ComputationReturnTreeHasType.wordMatch
example := @Solcore.Frontend.ComputationReturnTreeElaborates.wordMatch
example := @Solcore.Frontend.ComputationReturnTreeChecking.match_iff
example := @Solcore.Frontend.ComputationReturnTreeEvaluates.wordMatch
example := @Solcore.Frontend.ComputationReturnTreeEvaluatesWithCost.wordMatch
example := @Solcore.Frontend.ComputationBodyFragment.unit
example := @Solcore.Frontend.ComputationBodyFragment.leaf
example := @Solcore.Frontend.ComputationBodyFragment.letE
example := @Solcore.Frontend.ComputationBodyFragment.ifE
example := @Solcore.Frontend.ComputationBodyFragment.insertion_paths
example := @Solcore.Frontend.ComputationBodyFragment.evaluates_insert_iff
example := @Solcore.Frontend.ComputationBodyFragment.weakenAt
example := @Solcore.Frontend.elaborateComputationReturnTree?
example := @Solcore.Frontend.ComputationReturnTreeHasType
example := @Solcore.Frontend.ComputationReturnTreeHasType.bare
example := @Solcore.Frontend.ComputationReturnTreeHasType.expression
example := @Solcore.Frontend.ComputationReturnTreeHasType.block
example := @Solcore.Frontend.ComputationReturnTreeHasType.binding
example := @Solcore.Frontend.ComputationReturnTreeHasType.inferred
example := @Solcore.Frontend.ComputationReturnTreeHasType.discard
example := @Solcore.Frontend.ComputationReturnTreeHasType.conditional
example := @Solcore.Frontend.ComputationReturnTreeElaborates
example := @Solcore.Frontend.ComputationReturnTreeElaborates.bare
example := @Solcore.Frontend.ComputationReturnTreeElaborates.expression
example := @Solcore.Frontend.ComputationReturnTreeElaborates.block
example := @Solcore.Frontend.ComputationReturnTreeElaborates.binding
example := @Solcore.Frontend.ComputationReturnTreeElaborates.inferred
example := @Solcore.Frontend.ComputationReturnTreeElaborates.discard
example := @Solcore.Frontend.ComputationReturnTreeElaborates.conditional
example := @Solcore.Frontend.ComputationReturnTreeEvaluatesWithCost.toStepsWithContinuation
example := @Solcore.Frontend.ComputationReturnTreeElaborates.evaluatesWithCost_iff_steps
example := @Solcore.Frontend.ComputationReturnTreeEvaluates
example := @Solcore.Frontend.ComputationReturnTreeEvaluates.bare
example := @Solcore.Frontend.ComputationReturnTreeEvaluates.expression
example := @Solcore.Frontend.ComputationReturnTreeEvaluates.block
example := @Solcore.Frontend.ComputationReturnTreeEvaluates.binding
example := @Solcore.Frontend.ComputationReturnTreeEvaluates.inferred
example := @Solcore.Frontend.ComputationReturnTreeEvaluates.discard
example := @Solcore.Frontend.ComputationReturnTreeEvaluates.ifTrue
example := @Solcore.Frontend.ComputationReturnTreeEvaluates.ifFalse
example := @Solcore.Frontend.ComputationReturnTreeEvaluatesWithCost
example := @Solcore.Frontend.ComputationReturnTreeEvaluatesWithCost.bare
example := @Solcore.Frontend.ComputationReturnTreeEvaluatesWithCost.expression
example := @Solcore.Frontend.ComputationReturnTreeEvaluatesWithCost.block
example := @Solcore.Frontend.ComputationReturnTreeEvaluatesWithCost.binding
example := @Solcore.Frontend.ComputationReturnTreeEvaluatesWithCost.inferred
example := @Solcore.Frontend.ComputationReturnTreeEvaluatesWithCost.discard
example := @Solcore.Frontend.ComputationReturnTreeEvaluatesWithCost.ifTrue
example := @Solcore.Frontend.ComputationReturnTreeEvaluatesWithCost.ifFalse
example := @Solcore.Frontend.computationReturnTreeEvaluates_iff_exists_cost
example := @Solcore.Frontend.ComputationReturnTreeEvaluatesWithCost.deterministic
example := @Solcore.Frontend.ComputationReturnTreeElaborates.evaluates_iff
example := @Solcore.Frontend.ComputationReturnTreeElaborates.core_fragment
example := @Solcore.Frontend.elaborateComputationReturnTree?_iff
example := @Solcore.Frontend.computationReturnTreeHasType_iff_elaborates
example := @Solcore.Frontend.ComputationReturnTreeElaborates.core_hasType
example := @Solcore.Frontend.ComputationReturnTreeElaborates.runtime_typed_execution
example := @Solcore.Frontend.ComputationReturnTreeElaborates.runtime_checkpoint_safety
example := @Solcore.Frontend.ComputationReturnTreeElaborates.runtime_checkpoint_world_extension
example := @Solcore.Frontend.elaborateRecursiveComputationReturnTree?
example := @Solcore.Frontend.RecursiveComputationReturnTreeHasType
example := @Solcore.Frontend.RecursiveComputationReturnTreeElaborates
example := @Solcore.Frontend.RecursiveComputationReturnTreeEvaluates
example := @Solcore.Frontend.RecursiveComputationReturnTreeEvaluatesWithCost
example := @Solcore.Frontend.LocalComputationReturnTreeElaborates.toRecursiveComputationReturnTree
example := @Solcore.Frontend.LocalComputationReturnTreeEvaluatesWithCost.toRecursiveComputationReturnTree
example := @Solcore.Frontend.ComputationFunctionCompiles
example := @Solcore.Frontend.compileComputationFunction?
example := @Solcore.Frontend.ComputationFunctionPrepares
example := @Solcore.Frontend.prepareComputationFunction?
example := @Solcore.Frontend.runComputationFunction?
example := @Solcore.Frontend.compileComputationFunction?_iff
example := @Solcore.Frontend.prepareComputationFunction?_iff
example := @Solcore.Frontend.prepareComputationFunction?_factorization
example := @Solcore.Frontend.runComputationFunction?_factorization
example := @Solcore.Frontend.ComputationFunctionPrepares.runtime_typed_execution
example := @Solcore.Frontend.validateRuntimeInputs
example := @Solcore.Frontend.validateRuntimeInputs_iff
example := @Solcore.Frontend.buildRuntimeArgument?
example := @Solcore.Frontend.buildRuntimeArgument?_iff
example := @Solcore.Frontend.RecursiveComputationFunctionCompiles
example := @Solcore.Frontend.RecursiveComputationFunctionPrepares
example := @Solcore.Frontend.compileRecursiveComputationFunction?
example := @Solcore.Frontend.prepareRecursiveComputationFunction?
example := @Solcore.Frontend.runRecursiveComputationFunction?
example := @Solcore.Frontend.ResolvesLocalExpression.toLocalReference
example := @Solcore.Frontend.resolvesLocalExpression_var_iff_reference
example := @Solcore.Frontend.resolveLocalExpression?_var_iff_reference
example := @Solcore.Frontend.elaborateLocalExpression?_eq_reference
example := @Solcore.Frontend.localExpressionEvaluates_iff_reference

example := @Solcore.Frontend.TypedLocalBinding
example := @Solcore.Frontend.LocalInputs
example := @Solcore.Frontend.LocalInputs.ids
example := @Solcore.Frontend.LocalInputs.names
example := @Solcore.Frontend.LocalInputs.context
example := @Solcore.Frontend.LocalInputs.environment
example := @Solcore.Frontend.LocalInputs.empty
example := @Solcore.Frontend.LocalInputs.bindFresh
example := @Solcore.Frontend.LocalInputs.check?
example := @Solcore.Frontend.LocalInputs.run?
example := @Solcore.Frontend.LocalInputs.check?_iff_hasType
example := @Solcore.Frontend.LocalInputs.run?_eq_some_iff
example := @Solcore.Frontend.LocalInputs.run?_eq_none_iff
example := @Solcore.Frontend.LocalInputs.run?_done_sound
example := @Solcore.Frontend.LocalInputs.typed_run_has_sufficient_fuel
example := @Solcore.Frontend.LocalInputs.run?_done_iff_typed_evaluation
example := @Solcore.Frontend.LocalInputs.run?_never_faults
example := @Solcore.Frontend.LocalInputs.context_lookup_of_mem
example := @Solcore.Frontend.LocalInputs.environment_lookup_of_mem
example := @Solcore.Frontend.LocalInputs.lookup?_binding
example := @Solcore.Frontend.LocalInputs.bindFresh_lookups
example := @Solcore.Frontend.LocalInputs.context_ids
example := @Solcore.Frontend.LocalInputs.environment_ids
example := @Solcore.Frontend.LocalInputs.sameIds
example := @Solcore.Frontend.LocalInputs.environmentTyped
example := @Solcore.Frontend.LocalInputs.empty_ids
example := @Solcore.Frontend.LocalInputs.empty_names
example := @Solcore.Frontend.LocalInputs.empty_context
example := @Solcore.Frontend.LocalInputs.empty_environment
example := @Solcore.Frontend.LocalInputs.bindFresh_bindings
example := @Solcore.Frontend.LocalInputs.bindFresh_ids
example := @Solcore.Frontend.LocalInputs.bindFresh_names
example := @Solcore.Frontend.LocalInputs.bindFresh_context
example := @Solcore.Frontend.LocalInputs.bindFresh_environment
example := @Solcore.Frontend.LocalInputs.bindFresh_id_fresh

example := @Solcore.Frontend.AvoidsLocalName
example := @Solcore.Frontend.LocalNameTable.lookup_cons_iff_of_ne
example := @Solcore.Frontend.AvoidsLocalName.resolves_cons_iff
example := @Solcore.Frontend.AvoidsLocalName.resolve_cons_eq
example := @Solcore.Frontend.AvoidsLocalName.bindFresh_hasType_iff
example := @Solcore.Frontend.AvoidsLocalName.bindFresh_evaluates_iff
example := @Solcore.Frontend.AvoidsLocalName.check_bindFresh_complete
example := @Solcore.Frontend.AvoidsLocalName.check_bindFresh_eq
example := @Solcore.Frontend.AvoidsLocalName.bindFresh_run_done_iff
example := @Solcore.Frontend.ResolvesLocalExpression.logicalNot
example := @Solcore.Frontend.LocalExpressionHasType.logicalNot
example := @Solcore.Frontend.LocalExpressionEvaluates.logicalNot
example := @Solcore.Frontend.AvoidsLocalName.logicalNot
example := @Solcore.Frontend.resolveLocalExpression?_logicalNot_spans
example := @Solcore.Frontend.ResolvesLocalExpression.logicalAnd
example := @Solcore.Frontend.ResolvesLocalExpression.logicalOr
example := @Solcore.Frontend.LocalExpressionHasType.logicalAnd
example := @Solcore.Frontend.LocalExpressionHasType.logicalOr
example := @Solcore.Frontend.LocalExpressionEvaluates.andTrue
example := @Solcore.Frontend.LocalExpressionEvaluates.andFalse
example := @Solcore.Frontend.LocalExpressionEvaluates.orTrue
example := @Solcore.Frontend.LocalExpressionEvaluates.orFalse
example := @Solcore.Frontend.AvoidsLocalName.logicalAnd
example := @Solcore.Frontend.AvoidsLocalName.logicalOr
example := @Solcore.Frontend.resolveLocalExpression?_logicalAnd_spans
example := @Solcore.Frontend.resolveLocalExpression?_logicalOr_spans
example := @Solcore.Frontend.ResolvesLocalExpression.mapIds
example := @Solcore.Frontend.resolvesLocalExpression_mapIds_iff_exists
example := @Solcore.Frontend.resolveLocalExpression?_mapIds
example := @Solcore.Frontend.elaborateLocalExpression?_mapIds
example := @Solcore.Frontend.localExpressionHasType_mapIds_iff
example := @Solcore.Frontend.localExpressionEvaluates_mapIds_iff
example := @Solcore.Frontend.TypedLocalBinding.mapIds
example := @Solcore.Frontend.TypedLocalBinding.mapIds_id
example := @Solcore.Frontend.TypedLocalBinding.mapIds_comp
example := @Solcore.Frontend.LocalInputs.mapIds
example := @Solcore.Frontend.LocalInputs.mapIds_bindings
example := @Solcore.Frontend.LocalInputs.mapIds_ids
example := @Solcore.Frontend.LocalInputs.mapIds_names
example := @Solcore.Frontend.LocalInputs.mapIds_context
example := @Solcore.Frontend.LocalInputs.mapIds_environment
example := @Solcore.Frontend.LocalInputs.mapIds_id
example := @Solcore.Frontend.LocalInputs.mapIds_comp
example := @Solcore.Frontend.LocalInputs.check?_mapIds
example := @Solcore.Frontend.LocalInputs.run?_mapIds
example := @Solcore.Frontend.LocalInputs.hasType_mapIds_iff
example := @Solcore.Frontend.LocalInputs.evaluates_mapIds_iff
example := @Solcore.Frontend.LocalNameTable.mapIds
example := @Solcore.Frontend.LocalNameTable.mapIds_id
example := @Solcore.Frontend.LocalNameTable.mapIds_comp
example := @Solcore.Frontend.LocalNameTable.lookup?_mapIds
example := @Solcore.Frontend.LocalNameTable.lookup_mapIds_iff_exists
example := @Solcore.Frontend.LocalNameTable.lookup_mapIds_iff
example := @Solcore.Frontend.ResolvesLocalExpression.bitNot
example := @Solcore.Frontend.LocalExpressionHasType.bitNot
example := @Solcore.Frontend.LocalExpressionEvaluates.bitNot
example := @Solcore.Frontend.AvoidsLocalName.bitNot
example := @Solcore.Frontend.resolveLocalExpression?_bitNot_spans
example := @Solcore.Frontend.NumericRadix
example := @Solcore.Frontend.NumericRadix.base
example := @Solcore.Frontend.numericDigitValue?
example := @Solcore.Frontend.NumericDigitDenotes
example := @Solcore.Frontend.numericDigitsValue?
example := @Solcore.Frontend.NumericDigitsDenote
example := @Solcore.Frontend.NumericDigitDenotes.complete
example := @Solcore.Frontend.numericDigitValue?_sound
example := @Solcore.Frontend.numericDigitValue?_iff
example := @Solcore.Frontend.NumericDigitDenotes.value_unique
example := @Solcore.Frontend.NumericDigitDenotes.lt_base
example := @Solcore.Frontend.numericDigitValue?_eq_none_iff
example := @Solcore.Frontend.NumericDigitsDenote.complete
example := @Solcore.Frontend.numericDigitsValue?_sound
example := @Solcore.Frontend.numericDigitsValue?_iff
example := @Solcore.Frontend.NumericDigitsDenote.value_unique
example := @Solcore.Frontend.numericDigitsValue?_eq_none_iff
example := @Solcore.Frontend.numericDigitsValue?_leading_zero
example := @Solcore.Frontend.NumericDigitsDenote.leading_zeros
example := @Solcore.Frontend.numericLiteralValue?
example := @Solcore.Frontend.NumericLiteralDenotes
example := @Solcore.Frontend.interpretWordLiteral?
example := @Solcore.Frontend.WordLiteralDenotes
example := @Solcore.Frontend.numericLiteralValue?_sound
example := @Solcore.Frontend.numericLiteralValue?_complete
example := @Solcore.Frontend.numericLiteralValue?_iff
example := @Solcore.Frontend.NumericLiteralDenotes.value_unique
example := @Solcore.Frontend.numericLiteralValue?_eq_none_iff
example := @Solcore.Frontend.interpretWordLiteral?_sound
example := @Solcore.Frontend.interpretWordLiteral?_complete
example := @Solcore.Frontend.interpretWordLiteral?_iff
example := @Solcore.Frontend.WordLiteralDenotes.value_unique
example := @Solcore.Frontend.interpretWordLiteral?_complete_of_lt
example := @Solcore.Frontend.interpretWordLiteral?_value_and_range
example := @Solcore.Frontend.interpretWordLiteral?_eq_none_of_out_of_range
example := @Solcore.Frontend.interpretWordLiteral?_eq_none_iff
example := @Solcore.Frontend.interpretWordLiteral?_span
example := @Solcore.Frontend.wordLiteralDenotes_span
example := @Solcore.Frontend.NumericRadix.decimal
example := @Solcore.Frontend.NumericRadix.hexadecimal
example := @Solcore.Frontend.NumericDigitDenotes.decimal
example := @Solcore.Frontend.NumericDigitDenotes.hexLower
example := @Solcore.Frontend.NumericDigitDenotes.hexUpper
example := @Solcore.Frontend.NumericDigitsDenote.nil
example := @Solcore.Frontend.NumericDigitsDenote.cons
example := @Solcore.Frontend.NumericLiteralDenotes.decimal
example := @Solcore.Frontend.NumericLiteralDenotes.hexadecimal
example := @Solcore.Frontend.instReprNumericRadix
example := @Solcore.Frontend.instDecidableEqNumericRadix
example := @Solcore.Frontend.ResolvesLocalExpression.wordLiteral
example := @Solcore.Frontend.LocalExpressionHasType.wordLiteral
example := @Solcore.Frontend.LocalExpressionEvaluates.wordLiteral
example := @Solcore.Frontend.AvoidsLocalName.literal
example := @Solcore.Frontend.resolveLocalExpression?_literal_spans
example := @Solcore.Frontend.ResolvesLocalExpression.bitAnd
example := @Solcore.Frontend.ResolvesLocalExpression.bitOr
example := @Solcore.Frontend.ResolvesLocalExpression.bitXor
example := @Solcore.Frontend.LocalExpressionHasType.bitAnd
example := @Solcore.Frontend.LocalExpressionHasType.bitOr
example := @Solcore.Frontend.LocalExpressionHasType.bitXor
example := @Solcore.Frontend.LocalExpressionEvaluates.bitAnd
example := @Solcore.Frontend.LocalExpressionEvaluates.bitOr
example := @Solcore.Frontend.LocalExpressionEvaluates.bitXor
example := @Solcore.Frontend.AvoidsLocalName.bitAnd
example := @Solcore.Frontend.AvoidsLocalName.bitOr
example := @Solcore.Frontend.AvoidsLocalName.bitXor
example := @Solcore.Frontend.resolveLocalExpression?_bitAnd_spans
example := @Solcore.Frontend.resolveLocalExpression?_bitOr_spans
example := @Solcore.Frontend.resolveLocalExpression?_bitXor_spans
example := @Solcore.Core.Steps.final_unique
example := @Solcore.Core.Steps.runStateful_done_iff
example := @Solcore.Core.Steps.runStateful_outOfFuel_iff
example := @Solcore.Frontend.LocalExpressionEvaluatesWithCost
example := @Solcore.Frontend.LocalExpressionEvaluatesWithCost.erase
example := @Solcore.Frontend.LocalExpressionEvaluates.exists_cost
example := @Solcore.Frontend.localExpressionEvaluates_iff_exists_cost
example := @Solcore.Frontend.LocalExpressionEvaluatesWithCost.store_eq
example := @Solcore.Frontend.LocalExpressionEvaluatesWithCost.cost_pos
example := @Solcore.Frontend.LocalExpressionEvaluatesWithCost.deterministic
example := @Solcore.Frontend.LocalExpressionEvaluatesWithCost.cost_unique
example := @Solcore.Frontend.CostStepComposition.unary
example := @Solcore.Frontend.CostStepComposition.binary
example := @Solcore.Frontend.CostStepComposition.ifTrue
example := @Solcore.Frontend.CostStepComposition.ifFalse
example := @Solcore.Frontend.LocalExpressionEvaluatesWithCost.toStepsWithContinuation
example := @Solcore.Frontend.LocalExpressionEvaluatesWithCost.toSteps
example := @Solcore.Frontend.LocalExpressionEvaluatesWithCost.runStateful_done_iff
example := @Solcore.Frontend.LocalExpressionEvaluatesWithCost.runStateful_outOfFuel_iff
example := @Solcore.Frontend.LocalExpressionEvaluatesWithCost.checked_toSteps
example := @Solcore.Frontend.LocalExpressionEvaluatesWithCost.checked_runStateful_done_iff
example := @Solcore.Frontend.LocalExpressionEvaluatesWithCost.checked_runStateful_outOfFuel_iff
example := @Solcore.Frontend.elaborateLocalExpression?_run_done_iff_cost
example := @Solcore.Frontend.elaborateLocalExpression?_typed_cost_execution
example := @Solcore.Frontend.LocalInputs.run?_done_iff_typed_cost
example := @Solcore.Frontend.LocalInputs.typed_cost_execution
example := @Solcore.Frontend.LocalExpressionEvaluatesWithCost.identifier
example := @Solcore.Frontend.LocalExpressionEvaluatesWithCost.wordLiteral
example := @Solcore.Frontend.LocalExpressionEvaluatesWithCost.group
example := @Solcore.Frontend.LocalExpressionEvaluatesWithCost.logicalNot
example := @Solcore.Frontend.LocalExpressionEvaluatesWithCost.bitNot
example := @Solcore.Frontend.LocalExpressionEvaluatesWithCost.bitAnd
example := @Solcore.Frontend.LocalExpressionEvaluatesWithCost.bitOr
example := @Solcore.Frontend.LocalExpressionEvaluatesWithCost.bitXor
example := @Solcore.Frontend.LocalExpressionEvaluatesWithCost.andTrue
example := @Solcore.Frontend.LocalExpressionEvaluatesWithCost.andFalse
example := @Solcore.Frontend.LocalExpressionEvaluatesWithCost.orTrue
example := @Solcore.Frontend.LocalExpressionEvaluatesWithCost.orFalse
example := @Solcore.Frontend.LocalExpressionEvaluatesWithCost.ifTrue
example := @Solcore.Frontend.LocalExpressionEvaluatesWithCost.ifFalse
example := @Solcore.Frontend.localExpressionEvaluatesWithCost_mapIds_iff
example := @Solcore.Frontend.AvoidsLocalName.bindFresh_cost_iff
example := @Solcore.Frontend.LocalInputs.run?_outOfFuel_iff_typed_cost
example := @Solcore.Frontend.AvoidsLocalName.bindFresh_run_done_at_fuel_iff
example := @Solcore.Frontend.AvoidsLocalName.bindFresh_run_outOfFuel_iff
example := @Solcore.Frontend.TypeNameTable
example := @Solcore.Frontend.TypeNameTable.lookup?
example := @Solcore.Frontend.TypeNameTable.Lookup
example := @Solcore.Frontend.qualifiedTypeNameKey
example := @Solcore.Frontend.interpretTypeName?
example := @Solcore.Frontend.interpretStructuralType?
example := @Solcore.Frontend.StructuralTypeDenotes
example := @Solcore.Frontend.StructuralTypeDenotes.complete
example := @Solcore.Frontend.interpretStructuralType?_sound
example := @Solcore.Frontend.interpretStructuralType?_iff
example := @Solcore.Frontend.StructuralTypeDenotes.type_unique
example := @Solcore.Frontend.interpretStructuralType?_eq_none_iff
example := @Solcore.Frontend.interpretStructuralType?_span
example := @Solcore.Frontend.TypeNameDenotes.structural
example := @Solcore.Frontend.interpretStructuralType?_of_typeName
example := @Solcore.Frontend.interpretStructuralType?_named_eq_typeName
example := @Solcore.Frontend.StructuralTypeDenotes.extend_types
example := @Solcore.Frontend.interpretStructuralType?_some_of_extends
example := @Solcore.Frontend.interpretStructuralType?_congr_lookup
example := @Solcore.Frontend.interpretStructuralType?_eq_of_mutual_extends
example := @Solcore.Frontend.StructuralTypeDenotes.named
example := @Solcore.Frontend.StructuralTypeDenotes.unit
example := @Solcore.Frontend.StructuralTypeDenotes.single
example := @Solcore.Frontend.StructuralTypeDenotes.pair
example := @Solcore.Frontend.StructuralTypeDenotes.many
example := @Solcore.Frontend.TypeNameDenotes
example := @Solcore.Frontend.TypeNameTable.lookup?_iff
example := @Solcore.Frontend.TypeNameTable.Lookup.type_unique
example := @Solcore.Frontend.TypeNameTable.Lookup.mem
example := @Solcore.Frontend.TypeNameTable.lookup?_eq_none_iff
example := @Solcore.Frontend.TypeNameDenotes.complete
example := @Solcore.Frontend.interpretTypeName?_sound
example := @Solcore.Frontend.interpretTypeName?_iff
example := @Solcore.Frontend.TypeNameDenotes.type_unique
example := @Solcore.Frontend.TypeNameDenotes.mem
example := @Solcore.Frontend.interpretTypeName?_eq_none_iff
example := @Solcore.Frontend.interpretTypeName?_span
example := @Solcore.Frontend.interpretTypeName?_key_eq
example := @Solcore.Frontend.TypeNameTable.Lookup.head
example := @Solcore.Frontend.TypeNameTable.Lookup.tail
example := @Solcore.Frontend.TypeNameDenotes.named
example := @Solcore.Frontend.TypedRuntimeArgument
example := @Solcore.Frontend.RuntimeParametersBindFrom
example := @Solcore.Frontend.RuntimeParametersBind
example := @Solcore.Frontend.bindRuntimeParameters?
example := @Solcore.Frontend.bindRuntimeParameters?_iff
example := @Solcore.Frontend.RuntimeParametersBind.complete
example := @Solcore.Frontend.bindRuntimeParameters?_sound
example := @Solcore.Frontend.bindRuntimeParameters?_eq_none_iff
example := @Solcore.Frontend.RuntimeParametersBindFrom.result_unique
example := @Solcore.Frontend.RuntimeParametersBindFrom.extend_types
example := @Solcore.Frontend.RuntimeParametersBind.extend_types
example := @Solcore.Frontend.bindRuntimeParameters?_some_of_extends
example := @Solcore.Frontend.bindRuntimeParameters?_eq_of_mutual_extends
example := @Solcore.Frontend.RuntimeParameterRow
example := @Solcore.Frontend.RuntimeParameterRows
example := @Solcore.Frontend.RuntimeParameterRows.arity
example := @Solcore.Frontend.RuntimeParameterRows.argument_types
example := @Solcore.Frontend.RuntimeParameterRows.argument_values
example := @Solcore.Frontend.RuntimeParameterRows.row_at
example := @Solcore.Frontend.RuntimeParametersBindFrom.rows
example := @Solcore.Frontend.RuntimeParametersBindFrom.arity
example := @Solcore.Frontend.RuntimeParametersBindFrom.bindings_length
example := @Solcore.Frontend.RuntimeParametersBindFrom.argument_types
example := @Solcore.Frontend.RuntimeParametersBindFrom.argument_values
example := @Solcore.Frontend.RuntimeParametersBindFrom.names_nodup
example := @Solcore.Frontend.RuntimeParametersBindFrom.generated_ids
example := @Solcore.Frontend.RuntimeParametersBind.rows
example := @Solcore.Frontend.RuntimeParametersBind.arity
example := @Solcore.Frontend.RuntimeParametersBind.bindings_length
example := @Solcore.Frontend.RuntimeParametersBind.argument_types
example := @Solcore.Frontend.RuntimeParametersBind.argument_values
example := @Solcore.Frontend.RuntimeParametersBind.names_nodup
example := @Solcore.Frontend.RuntimeParametersBind.generated_ids
example := @Solcore.Frontend.TypedRuntimeArgument.mk
example := @Solcore.Frontend.TypedRuntimeArgument.type
example := @Solcore.Frontend.TypedRuntimeArgument.value
example := @Solcore.Frontend.TypedRuntimeArgument.valueTyped
example := @Solcore.Frontend.RuntimeParametersBindFrom.nil
example := @Solcore.Frontend.RuntimeParametersBindFrom.cons
example := @Solcore.Frontend.RuntimeParameterRow.typed
example := @Solcore.Frontend.RuntimeParameterRows.nil
example := @Solcore.Frontend.RuntimeParameterRows.cons
example := @Solcore.Frontend.elaborateReturnBody?
example := @Solcore.Frontend.ReturnBodyHasType
example := @Solcore.Frontend.ReturnBodyEvaluates
example := @Solcore.Frontend.ReturnBodyEvaluatesWithCost
example := @Solcore.Frontend.LocalInputs.checkReturnBody?
example := @Solcore.Frontend.LocalInputs.runReturnBody?
example := @Solcore.Frontend.ReturnBodyHasType.elaborates
example := @Solcore.Frontend.elaborateReturnBody?_sound
example := @Solcore.Frontend.returnBodyHasType_iff_elaborates
example := @Solcore.Frontend.elaborateReturnBody?_core_hasType
example := @Solcore.Frontend.ReturnBodyHasType.type_unique
example := @Solcore.Frontend.elaborateReturnBody?_eq_none_iff
example := @Solcore.Frontend.elaborateReturnBody?_spans
example := @Solcore.Frontend.ReturnBodyEvaluates.store_eq
example := @Solcore.Frontend.ReturnBodyEvaluates.deterministic
example := @Solcore.Frontend.ReturnBodyHasType.evaluates
example := @Solcore.Frontend.ReturnBodyEvaluates.preserves_type
example := @Solcore.Frontend.ReturnBodyEvaluatesWithCost.erase
example := @Solcore.Frontend.ReturnBodyEvaluates.exists_cost
example := @Solcore.Frontend.returnBodyEvaluates_iff_exists_cost
example := @Solcore.Frontend.ReturnBodyEvaluatesWithCost.store_eq
example := @Solcore.Frontend.ReturnBodyEvaluatesWithCost.cost_pos
example := @Solcore.Frontend.ReturnBodyEvaluatesWithCost.deterministic
example := @Solcore.Frontend.elaborateReturnBody?_evaluates_iff
example := @Solcore.Frontend.ReturnBodyEvaluatesWithCost.checked_toSteps
example := @Solcore.Frontend.ReturnBodyEvaluatesWithCost.checked_runStateful_done_iff
example := @Solcore.Frontend.ReturnBodyEvaluatesWithCost.checked_runStateful_outOfFuel_iff
example := @Solcore.Frontend.elaborateReturnBody?_run_done_iff_cost
example := @Solcore.Frontend.LocalInputs.runReturnBody?_eq_some_iff
example := @Solcore.Frontend.LocalInputs.runReturnBody?_done_iff_typed_cost
example := @Solcore.Frontend.LocalInputs.returnBody_typed_cost_execution
example := @Solcore.Frontend.LocalInputs.runReturnBody?_outOfFuel_iff_typed_cost
example := @Solcore.Frontend.LocalInputs.runReturnBody?_never_faults
example := @Solcore.Frontend.ReturnBodyHasType.bare
example := @Solcore.Frontend.ReturnBodyHasType.expression
example := @Solcore.Frontend.ReturnBodyEvaluates.bare
example := @Solcore.Frontend.ReturnBodyEvaluates.expression
example := @Solcore.Frontend.ReturnBodyEvaluatesWithCost.bare
example := @Solcore.Frontend.ReturnBodyEvaluatesWithCost.expression
example := @Solcore.Frontend.ReturnBodyElaborates
example := @Solcore.Frontend.ReturnBodyElaborates.complete
example := @Solcore.Frontend.elaborateReturnBody?_elaborates
example := @Solcore.Frontend.elaborateReturnBody?_iff
example := @Solcore.Frontend.ReturnBodyElaborates.hasType
example := @Solcore.Frontend.ReturnBodyHasType.elaborates_exact
example := @Solcore.Frontend.ReturnBodyElaborates.result_unique
example := @Solcore.Frontend.RuntimeReturnTypeDenotes
example := @Solcore.Frontend.interpretRuntimeReturnType?
example := @Solcore.Frontend.RuntimeFunctionHeader
example := @Solcore.Frontend.interpretRuntimeFunctionHeader?
example := @Solcore.Frontend.interpretRuntimeReturnType?_iff
example := @Solcore.Frontend.RuntimeReturnTypeDenotes.type_unique
example := @Solcore.Frontend.interpretRuntimeFunctionHeader?_iff
example := @Solcore.Frontend.RuntimeFunctionHeader.type_unique
example := @Solcore.Frontend.interpretRuntimeFunctionHeader?_eq_none_iff
example := @Solcore.Frontend.PreparedRuntimeFunction
example := @Solcore.Frontend.RuntimeFunctionPrepares
example := @Solcore.Frontend.RuntimeFunctionHasType
example := @Solcore.Frontend.prepareRuntimeFunction?
example := @Solcore.Frontend.runRuntimeFunction?
example := @Solcore.Frontend.RuntimeFunctionPrepares.complete
example := @Solcore.Frontend.prepareRuntimeFunction?_sound
example := @Solcore.Frontend.prepareRuntimeFunction?_iff
example := @Solcore.Frontend.RuntimeFunctionPrepares.result_unique
example := @Solcore.Frontend.RuntimeFunctionPrepares.hasType
example := @Solcore.Frontend.runtimeFunctionHasType_iff_prepares
example := @Solcore.Frontend.prepareRuntimeFunction?_eq_none_iff
example := @Solcore.Frontend.RuntimeFunctionPrepares.core_hasType
example := @Solcore.Frontend.RuntimeFunctionPrepares.extend_types
example := @Solcore.Frontend.RuntimeFunctionHasType.extend_types
example := @Solcore.Frontend.prepareRuntimeFunction?_some_of_extends
example := @Solcore.Frontend.prepareRuntimeFunction?_eq_of_mutual_extends
example := @Solcore.Frontend.runRuntimeFunction?_some_of_extends
example := @Solcore.Frontend.runRuntimeFunction?_eq_of_mutual_extends
example := @Solcore.Frontend.RuntimeFunctionEvaluatesWithCost
example := @Solcore.Frontend.RuntimeFunctionEvaluatesWithCost.hasType
example := @Solcore.Frontend.RuntimeFunctionEvaluatesWithCost.preserves_type
example := @Solcore.Frontend.RuntimeFunctionEvaluatesWithCost.store_eq
example := @Solcore.Frontend.RuntimeFunctionEvaluatesWithCost.cost_pos
example := @Solcore.Frontend.RuntimeFunctionEvaluatesWithCost.deterministic
example := @Solcore.Frontend.runRuntimeFunction?_eq_some_iff
example := @Solcore.Frontend.RuntimeFunctionEvaluatesWithCost.run_done_iff
example := @Solcore.Frontend.RuntimeFunctionEvaluatesWithCost.run_outOfFuel_iff
example := @Solcore.Frontend.runRuntimeFunction?_done_iff_cost
example := @Solcore.Frontend.runRuntimeFunction?_outOfFuel_iff_cost
example := @Solcore.Frontend.RuntimeFunctionHasType.typed_cost_execution
example := @Solcore.Frontend.runRuntimeFunction?_never_faults
example := @Solcore.Frontend.ReturnBodyElaborates.bare
example := @Solcore.Frontend.ReturnBodyElaborates.expression
example := @Solcore.Frontend.RuntimeReturnTypeDenotes.absent
example := @Solcore.Frontend.RuntimeReturnTypeDenotes.single
example := @Solcore.Frontend.RuntimeFunctionHeader.mk
example := @Solcore.Frontend.RuntimeFunctionHeader.noGenerics
example := @Solcore.Frontend.RuntimeFunctionHeader.noWhere
example := @Solcore.Frontend.RuntimeFunctionHeader.noPublic
example := @Solcore.Frontend.RuntimeFunctionHeader.noPayable
example := @Solcore.Frontend.RuntimeFunctionHeader.returnsMeaning
example := @Solcore.Frontend.PreparedRuntimeFunction.mk
example := @Solcore.Frontend.PreparedRuntimeFunction.inputs
example := @Solcore.Frontend.PreparedRuntimeFunction.core
example := @Solcore.Frontend.PreparedRuntimeFunction.returnType
example := @Solcore.Frontend.RuntimeFunctionPrepares.mk
example := @Solcore.Frontend.RuntimeFunctionPrepares.header
example := @Solcore.Frontend.RuntimeFunctionPrepares.parameters
example := @Solcore.Frontend.RuntimeFunctionPrepares.body
example := @Solcore.Frontend.RuntimeFunctionEvaluatesWithCost.intro
example := @Solcore.Frontend.RuntimeParametersBind.position
example := @Solcore.Frontend.RuntimeParametersBind.reference_resolves_at
example := @Solcore.Frontend.RuntimeParametersBind.reference_elaborates_at
example := @Solcore.Frontend.RuntimeParametersBind.reference_cost_at
example := @Solcore.Frontend.RuntimeParametersBind.reference_return_elaborates_at
example := @Solcore.Frontend.runtimeFunction_parameter_prepares
example := @Solcore.Frontend.runtimeFunction_parameter_cost
example := @Solcore.Frontend.runRuntimeFunction?_parameter
example := @Solcore.Frontend.RuntimeParametersBindFrom.transport_types
example := @Solcore.Frontend.RuntimeFunctionPrepares.transport_argument_types
example := @Solcore.Frontend.prepareRuntimeFunction?_static_projection_eq
example := @Solcore.Frontend.ownerLocalIdMap
example := @Solcore.Frontend.ownerLocalIdMap_injective
example := @Solcore.Frontend.RuntimeParametersBind.map_owner
example := @Solcore.Frontend.ReturnBodyElaborates.mapIds
example := @Solcore.Frontend.RuntimeFunctionPrepares.mapOwner
example := @Solcore.Frontend.prepareRuntimeFunction?_owner_projection_eq
example := @Solcore.Frontend.runRuntimeFunction?_owner_eq
example := @Solcore.Frontend.LocalTypeBinding
example := @Solcore.Frontend.LocalTypeInputs
example := @Solcore.Frontend.LocalTypeInputs.ids
example := @Solcore.Frontend.LocalTypeInputs.names
example := @Solcore.Frontend.LocalTypeInputs.context
example := @Solcore.Frontend.LocalTypeInputs.empty
example := @Solcore.Frontend.LocalTypeInputs.bindFresh
example := @Solcore.Frontend.LocalTypeInputs.context_ids
example := @Solcore.Frontend.LocalTypeInputs.empty_ids
example := @Solcore.Frontend.LocalTypeInputs.empty_names
example := @Solcore.Frontend.LocalTypeInputs.empty_context
example := @Solcore.Frontend.LocalTypeInputs.bindFresh_bindings
example := @Solcore.Frontend.LocalTypeInputs.bindFresh_ids
example := @Solcore.Frontend.LocalTypeInputs.bindFresh_names
example := @Solcore.Frontend.LocalTypeInputs.bindFresh_context
example := @Solcore.Frontend.LocalTypeInputs.bindFresh_id_fresh
example := @Solcore.Frontend.RuntimeParametersDeclareFrom
example := @Solcore.Frontend.RuntimeParametersDeclare
example := @Solcore.Frontend.declareRuntimeParameters?
example := @Solcore.Frontend.RuntimeParametersDeclare.complete
example := @Solcore.Frontend.declareRuntimeParameters?_sound
example := @Solcore.Frontend.declareRuntimeParameters?_iff
example := @Solcore.Frontend.declareRuntimeParameters?_eq_none_iff
example := @Solcore.Frontend.RuntimeParametersDeclareFrom.result_unique
example := @Solcore.Frontend.LocalInputs.toTypeInputs
example := @Solcore.Frontend.LocalInputs.toTypeInputs_ids
example := @Solcore.Frontend.LocalInputs.toTypeInputs_names
example := @Solcore.Frontend.LocalInputs.toTypeInputs_context
example := @Solcore.Frontend.LocalInputs.toTypeInputs_empty
example := @Solcore.Frontend.LocalInputs.toTypeInputs_bindFresh
example := @Solcore.Frontend.RuntimeParametersBindFrom.erase_values
example := @Solcore.Frontend.RuntimeParametersBind.erase_values
example := @Solcore.Frontend.RuntimeParametersDeclareFrom.bind_typed_arguments
example := @Solcore.Frontend.RuntimeParametersDeclare.bind_typed_arguments
example := @Solcore.Frontend.LocalTypeBinding.mk
example := @Solcore.Frontend.LocalTypeBinding.name
example := @Solcore.Frontend.LocalTypeBinding.id
example := @Solcore.Frontend.LocalTypeBinding.type
example := @Solcore.Frontend.LocalTypeInputs.mk
example := @Solcore.Frontend.LocalTypeInputs.bindings
example := @Solcore.Frontend.LocalTypeInputs.ids_nodup
example := @Solcore.Frontend.RuntimeParametersDeclareFrom.nil
example := @Solcore.Frontend.RuntimeParametersDeclareFrom.cons
example := @Solcore.Frontend.CompiledRuntimeFunction
example := @Solcore.Frontend.RuntimeFunctionCompiles
example := @Solcore.Frontend.compileRuntimeFunction?
example := @Solcore.Frontend.RuntimeFunctionCompiles.complete
example := @Solcore.Frontend.compileRuntimeFunction?_sound
example := @Solcore.Frontend.compileRuntimeFunction?_iff
example := @Solcore.Frontend.RuntimeFunctionCompiles.result_unique
example := @Solcore.Frontend.compileRuntimeFunction?_eq_none_iff
example := @Solcore.Frontend.RuntimeFunctionCompiles.core_hasType
example := @Solcore.Frontend.PreparedRuntimeFunction.toCompiled
example := @Solcore.Frontend.RuntimeFunctionPrepares.compiles
example := @Solcore.Frontend.RuntimeFunctionCompiles.prepare_arguments
example := @Solcore.Frontend.runtimeFunctionPrepares_toCompiled_iff
example := @Solcore.Frontend.prepareRuntimeFunction?_factorization
example := @Solcore.Frontend.CompiledRuntimeFunction.mk
example := @Solcore.Frontend.CompiledRuntimeFunction.inputs
example := @Solcore.Frontend.CompiledRuntimeFunction.core
example := @Solcore.Frontend.CompiledRuntimeFunction.returnType
example := @Solcore.Frontend.RuntimeFunctionCompiles.mk
example := @Solcore.Frontend.RuntimeFunctionCompiles.header
example := @Solcore.Frontend.RuntimeFunctionCompiles.parameters
example := @Solcore.Frontend.RuntimeFunctionCompiles.body
example := @Solcore.Frontend.ResolvesLocalExpression.add
example := @Solcore.Frontend.LocalExpressionHasType.add
example := @Solcore.Frontend.AvoidsLocalName.add
example := @Solcore.Frontend.LocalExpressionEvaluates.add
example := @Solcore.Frontend.LocalExpressionEvaluatesWithCost.add
example := @Solcore.Frontend.resolveLocalExpression?_add_spans
example := @Solcore.Frontend.ResolvesLocalExpression.subtract
example := @Solcore.Frontend.ResolvesLocalExpression.multiply
example := @Solcore.Frontend.LocalExpressionHasType.subtract
example := @Solcore.Frontend.LocalExpressionHasType.multiply
example := @Solcore.Frontend.AvoidsLocalName.subtract
example := @Solcore.Frontend.AvoidsLocalName.multiply
example := @Solcore.Frontend.LocalExpressionEvaluates.subtract
example := @Solcore.Frontend.LocalExpressionEvaluates.multiply
example := @Solcore.Frontend.LocalExpressionEvaluatesWithCost.subtract
example := @Solcore.Frontend.LocalExpressionEvaluatesWithCost.multiply
example := @Solcore.Frontend.resolveLocalExpression?_subtract_spans
example := @Solcore.Frontend.resolveLocalExpression?_multiply_spans
example := @Solcore.Frontend.LocalInputExtensionSupport.fresh_ne_of_named
example := @Solcore.Frontend.LocalInputExtensionSupport.identity_lookup_cons_iff
example := @Solcore.Frontend.ResolvesLocalExpression.greater
example := @Solcore.Frontend.LocalExpressionHasType.greater
example := @Solcore.Frontend.AvoidsLocalName.greater
example := @Solcore.Frontend.LocalExpressionEvaluates.greater
example := @Solcore.Frontend.LocalExpressionEvaluatesWithCost.greater
example := @Solcore.Frontend.resolveLocalExpression?_greater_spans
example := @Solcore.Frontend.RuntimeFunctionCompiles.run_eq
example := @Solcore.Frontend.runRuntimeFunction?_factorization
example := @Solcore.Frontend.runRuntimeFunction?_eq_some_compiled_iff
example := @Solcore.Frontend.RuntimeFunctionEvaluatesWithCost.compiled_contract
example := @Solcore.Frontend.RuntimeFunctionEvaluatesWithCost.compiled_toSteps
example := @Solcore.Frontend.RuntimeFunctionEvaluatesWithCost.compiled_run_done_iff
example := @Solcore.Frontend.RuntimeFunctionEvaluatesWithCost.compiled_run_outOfFuel_iff
example := @Solcore.Frontend.RuntimeFunctionCompiles.typed_compiled_execution
example := @Solcore.Frontend.RuntimeFunctionCompiles.compiled_never_faults
example := @Solcore.Frontend.RuntimeFunctionCompiles.returnType_eq_of_same_core
example := @Solcore.Frontend.RuntimeFunctionCompiles.run_eq_of_same_core
example := @Solcore.Frontend.RuntimeFunctionCompiles.cost_iff_of_same_core
example := @Solcore.Frontend.LocalExpressionEvaluatesWithCost.change_store
example := @Solcore.Frontend.LocalExpressionEvaluates.change_store
example := @Solcore.Frontend.localExpressionEvaluatesWithCost_store_iff
example := @Solcore.Frontend.localExpressionEvaluates_store_iff
example := @Solcore.Frontend.ReturnBodyEvaluates.change_store
example := @Solcore.Frontend.ReturnBodyEvaluatesWithCost.change_store
example := @Solcore.Frontend.RuntimeFunctionEvaluatesWithCost.change_store
example := @Solcore.Frontend.runtimeFunctionEvaluatesWithCost_store_iff
example := @Solcore.Frontend.runRuntimeFunction?_done_store_iff
example := @Solcore.Frontend.runRuntimeFunction?_outOfFuel_store_iff
example := @Solcore.Frontend.RuntimeFunctionCompiles.compiled_done_store_iff
example := @Solcore.Frontend.RuntimeFunctionCompiles.compiled_outOfFuel_store_iff
example := @Solcore.Frontend.localExpressionFuelBound
example := @Solcore.Frontend.LocalExpressionEvaluatesWithCost.cost_le_fuelBound
example := @Solcore.Frontend.elaborateLocalExpression?_run_done_of_fuelBound
example := @Solcore.Frontend.LocalInputs.run?_done_of_fuelBound
example := @Solcore.Frontend.returnBodyFuelBound
example := @Solcore.Frontend.ReturnBodyEvaluatesWithCost.cost_le_fuelBound
example := @Solcore.Frontend.elaborateReturnBody?_run_done_of_fuelBound
example := @Solcore.Frontend.LocalInputs.runReturnBody?_done_of_fuelBound
example := @Solcore.Frontend.RuntimeFunctionEvaluatesWithCost.cost_le_fuelBound
example := @Solcore.Frontend.RuntimeFunctionHasType.run_done_of_fuelBound
example := @Solcore.Frontend.RuntimeFunctionCompiles.run_done_of_fuelBound
example := @Solcore.Core.runStateful_resume
example := @Solcore.Core.Steps.residual_of_outOfFuel
example := @Solcore.Core.Steps.resumed_done_iff
example := @Solcore.Core.Steps.resumed_outOfFuel_iff
example := @Solcore.Frontend.LocalExpressionEvaluatesWithCost.residual_of_outOfFuel
example := @Solcore.Frontend.LocalExpressionEvaluatesWithCost.checked_residual_of_outOfFuel
example := @Solcore.Frontend.LocalInputs.run?_resume
example := @Solcore.Frontend.ReturnBodyEvaluatesWithCost.checked_residual_of_outOfFuel
example := @Solcore.Frontend.LocalInputs.runReturnBody?_resume
example := @Solcore.Frontend.runRuntimeFunction?_resume
example := @Solcore.Frontend.RuntimeFunctionEvaluatesWithCost.residual_of_outOfFuel
example := @Solcore.Frontend.RuntimeFunctionEvaluatesWithCost.compiled_residual_of_outOfFuel
example := @Solcore.Frontend.ResolvesLocalExpression.equal
example := @Solcore.Frontend.LocalExpressionHasType.equal
example := @Solcore.Frontend.AvoidsLocalName.equal
example := @Solcore.Frontend.LocalExpressionEvaluates.equal
example := @Solcore.Frontend.LocalExpressionEvaluatesWithCost.equal
example := @Solcore.Frontend.resolveLocalExpression?_equal_spans
example := @Solcore.Frontend.ResolvesLocalExpression.notEqual
example := @Solcore.Frontend.LocalExpressionHasType.notEqual
example := @Solcore.Frontend.AvoidsLocalName.notEqual
example := @Solcore.Frontend.LocalExpressionEvaluates.notEqual
example := @Solcore.Frontend.LocalExpressionEvaluatesWithCost.notEqual
example := @Solcore.Frontend.resolveLocalExpression?_notEqual_spans
example := @Solcore.Frontend.ResolvesLocalExpression.lessEqual
example := @Solcore.Frontend.LocalExpressionHasType.lessEqual
example := @Solcore.Frontend.AvoidsLocalName.lessEqual
example := @Solcore.Frontend.LocalExpressionEvaluates.lessEqual
example := @Solcore.Frontend.LocalExpressionEvaluatesWithCost.lessEqual
example := @Solcore.Frontend.resolveLocalExpression?_lessEqual_spans
example := @Solcore.Resolved.Expr.wordLtWithIds
example := @Solcore.Resolved.Expr.renameIds_wordLtWithIds
example := @Solcore.Resolved.Lowers.wordLtWithIds
example := @Solcore.Resolved.HasType.wordLtWithIds
example := @Solcore.Resolved.Expr.lower?_wordLtWithIds
example := @Solcore.Resolved.infer_wordLtWithIds
example := @Solcore.Resolved.Evaluates.wordLtWithIds
example := @Solcore.Resolved.Evaluates.wordLtWithIds_inv
example := @Solcore.Resolved.wordLtWithIds_evaluates_iff
example := @Solcore.Frontend.CostStepComposition.letE
example := @Solcore.Frontend.CostStepComposition.wordLt
example := @Solcore.Core.Expr.LocalFragment
example := @Solcore.Core.Expr.LocalFragment.weakenAt
example := @Solcore.Core.Expr.LocalFragment.unit
example := @Solcore.Core.Expr.LocalFragment.bool
example := @Solcore.Core.Expr.LocalFragment.word
example := @Solcore.Core.Expr.LocalFragment.var
example := @Solcore.Core.Expr.LocalFragment.pair
example := @Solcore.Core.Expr.LocalFragment.unary
example := @Solcore.Core.Expr.LocalFragment.binary
example := @Solcore.Core.Expr.LocalFragment.letE
example := @Solcore.Core.Expr.LocalFragment.ifE
example := @Solcore.Core.Expr.LocalFragment.evaluates_insert_iff
example := @Solcore.Core.Expr.LocalFragment.evaluates_weaken_zero_iff
example := @Solcore.Core.Evaluates.weakenAt_zero_localFragment
example := @Solcore.Core.Evaluates.reflect_weakenAt_zero_localFragment
example := @Solcore.Resolved.Lowers.localFragment
example := @Solcore.Core.Expr.LocalFragment.hasType_insert_iff
example := @Solcore.Core.Expr.LocalFragment.hasType_weaken_zero_iff
example := @Solcore.Core.HasType.weakenAt_zero_localFragment
example := @Solcore.Core.HasType.reflect_weakenAt_zero_localFragment
example := @Solcore.Core.Expr.LocalFragment.infer_insert
example := @Solcore.Core.Expr.LocalFragment.infer_weaken_zero
example := @Solcore.Core.Expr.LocalFragment.insertion_paths
example := @Solcore.Core.Expr.LocalFragment.steps_insert
example := @Solcore.Core.Expr.LocalFragment.steps_reflect_insert
example := @Solcore.Core.Expr.LocalFragment.steps_insert_iff
example := @Solcore.Core.Steps.weakenAt_zero_localFragment
example := @Solcore.Core.Steps.reflect_weakenAt_zero_localFragment
example := @Solcore.Core.Expr.LocalFragment.wordLt
example := @Solcore.Core.HasType.wordLt_inv_local_right
example := @Solcore.Core.Evaluates.wordLt_local_right
example := @Solcore.Core.Evaluates.wordLt_inv_local_right
example := @Solcore.Core.wordLt_evaluates_iff_local_right
example := @Solcore.Frontend.CostStepComposition.wordLt_of_local_right
example := @Solcore.Resolved.Expr.wordLt
example := @Solcore.Resolved.Lowers.wordLt
example := @Solcore.Resolved.HasType.wordLt
example := @Solcore.Resolved.Evaluates.wordLt
example := @Solcore.Resolved.WellScoped.wordLt
example := @Solcore.Resolved.Expr.pair
example := @Solcore.Resolved.Lowers.pair
example := @Solcore.Resolved.HasType.pair
example := @Solcore.Resolved.Evaluates.pair
example := @Solcore.Resolved.WellScoped.pair
example := @Solcore.Frontend.ResolvesLocalExpression.pair
example := @Solcore.Frontend.LocalExpressionHasType.pair
example := @Solcore.Frontend.AvoidsLocalName.pair
example := @Solcore.Frontend.LocalExpressionEvaluates.pair
example := @Solcore.Frontend.LocalExpressionEvaluatesWithCost.pair
example := @Solcore.Frontend.ResolvesLocalExpression.many
example := @Solcore.Frontend.LocalExpressionHasType.many
example := @Solcore.Frontend.AvoidsLocalName.many
example := @Solcore.Frontend.LocalExpressionEvaluates.many
example := @Solcore.Frontend.LocalExpressionEvaluatesWithCost.many
example := @Solcore.Frontend.ResolvesLocalExpression.unit
example := @Solcore.Frontend.LocalExpressionHasType.unit
example := @Solcore.Frontend.AvoidsLocalName.unit
example := @Solcore.Frontend.LocalExpressionEvaluates.unit
example := @Solcore.Frontend.LocalExpressionEvaluatesWithCost.unit
example := @Solcore.Frontend.ResolvesLocalExpression.less
example := @Solcore.Frontend.LocalExpressionHasType.less
example := @Solcore.Frontend.AvoidsLocalName.less
example := @Solcore.Frontend.LocalExpressionEvaluates.less
example := @Solcore.Frontend.LocalExpressionEvaluatesWithCost.less
example := @Solcore.Frontend.resolveLocalExpression?_less_spans
example := @Solcore.Frontend.ResolvesLocalExpression.greaterEqual
example := @Solcore.Frontend.LocalExpressionHasType.greaterEqual
example := @Solcore.Frontend.AvoidsLocalName.greaterEqual
example := @Solcore.Frontend.LocalExpressionEvaluates.greaterEqual
example := @Solcore.Frontend.LocalExpressionEvaluatesWithCost.greaterEqual
example := @Solcore.Frontend.resolveLocalExpression?_greaterEqual_spans
example := @Solcore.Frontend.elaborateConditionalReturnBody?
example := @Solcore.Frontend.ConditionalReturnBodyHasType
example := @Solcore.Frontend.ConditionalReturnBodyElaborates
example := @Solcore.Frontend.LocalInputs.checkConditionalReturnBody?
example := @Solcore.Frontend.LocalInputs.runConditionalReturnBody?
example := @Solcore.Frontend.elaborateConditionalReturnBody?_children
example := @Solcore.Frontend.ConditionalReturnBodyElaborates.complete
example := @Solcore.Frontend.elaborateConditionalReturnBody?_elaborates
example := @Solcore.Frontend.elaborateConditionalReturnBody?_iff
example := @Solcore.Frontend.ConditionalReturnBodyElaborates.hasType
example := @Solcore.Frontend.ConditionalReturnBodyHasType.elaborates_exact
example := @Solcore.Frontend.ConditionalReturnBodyHasType.elaborates
example := @Solcore.Frontend.elaborateConditionalReturnBody?_sound
example := @Solcore.Frontend.conditionalReturnBodyHasType_iff_elaborates
example := @Solcore.Frontend.elaborateConditionalReturnBody?_core_hasType
example := @Solcore.Frontend.ConditionalReturnBodyElaborates.result_unique
example := @Solcore.Frontend.ConditionalReturnBodyHasType.type_unique
example := @Solcore.Frontend.elaborateConditionalReturnBody?_eq_none_iff
example := @Solcore.Frontend.elaborateConditionalReturnBody?_spans
example := @Solcore.Frontend.ConditionalReturnBodyEvaluates
example := @Solcore.Frontend.ConditionalReturnBodyEvaluatesWithCost
example := @Solcore.Frontend.ConditionalReturnBodyEvaluates.store_eq
example := @Solcore.Frontend.ConditionalReturnBodyEvaluates.deterministic
example := @Solcore.Frontend.ConditionalReturnBodyHasType.evaluates
example := @Solcore.Frontend.ConditionalReturnBodyEvaluates.preserves_type
example := @Solcore.Frontend.ConditionalReturnBodyEvaluatesWithCost.erase
example := @Solcore.Frontend.ConditionalReturnBodyEvaluates.exists_cost
example := @Solcore.Frontend.conditionalReturnBodyEvaluates_iff_exists_cost
example := @Solcore.Frontend.ConditionalReturnBodyEvaluatesWithCost.store_eq
example := @Solcore.Frontend.ConditionalReturnBodyEvaluatesWithCost.cost_pos
example := @Solcore.Frontend.ConditionalReturnBodyEvaluatesWithCost.deterministic
example := @Solcore.Frontend.ReturnBodyEvaluatesWithCost.checked_toStepsWithContinuation
example := @Solcore.Frontend.elaborateConditionalReturnBody?_evaluates_iff
example := @Solcore.Frontend.ConditionalReturnBodyEvaluatesWithCost.checked_toStepsWithContinuation
example := @Solcore.Frontend.ConditionalReturnBodyEvaluatesWithCost.checked_toSteps
example := @Solcore.Frontend.ConditionalReturnBodyEvaluatesWithCost.checked_runStateful_done_iff
example := @Solcore.Frontend.ConditionalReturnBodyEvaluatesWithCost.checked_runStateful_outOfFuel_iff
example := @Solcore.Frontend.elaborateConditionalReturnBody?_run_done_iff_cost
example := @Solcore.Frontend.LocalInputs.runConditionalReturnBody?_eq_some_iff
example := @Solcore.Frontend.LocalInputs.runConditionalReturnBody?_done_iff_typed_cost
example := @Solcore.Frontend.LocalInputs.conditionalReturnBody_typed_cost_execution
example := @Solcore.Frontend.LocalInputs.runConditionalReturnBody?_outOfFuel_iff_typed_cost
example := @Solcore.Frontend.LocalInputs.runConditionalReturnBody?_never_faults
example := @Solcore.Frontend.conditionalReturnBodyFuelBound
example := @Solcore.Frontend.ConditionalReturnBodyEvaluatesWithCost.cost_le_fuelBound
example := @Solcore.Frontend.elaborateConditionalReturnBody?_run_done_of_fuelBound
example := @Solcore.Frontend.LocalInputs.runConditionalReturnBody?_done_of_fuelBound
example := @Solcore.Frontend.ConditionalReturnBodyEvaluatesWithCost.checked_residual_of_outOfFuel
example := @Solcore.Frontend.LocalInputs.runConditionalReturnBody?_resume
example := @Solcore.Frontend.ConditionalReturnBodyHasType.intro
example := @Solcore.Frontend.ConditionalReturnBodyElaborates.intro
example := @Solcore.Frontend.ConditionalReturnBodyEvaluates.ifTrue
example := @Solcore.Frontend.ConditionalReturnBodyEvaluates.ifFalse
example := @Solcore.Frontend.ConditionalReturnBodyEvaluatesWithCost.ifTrue
example := @Solcore.Frontend.ConditionalReturnBodyEvaluatesWithCost.ifFalse
example := @Solcore.Frontend.elaborateTerminalReturnBody?
example := @Solcore.Frontend.TerminalReturnBodyHasType
example := @Solcore.Frontend.TerminalReturnBodyElaborates
example := @Solcore.Frontend.LocalInputs.checkTerminalReturnBody?
example := @Solcore.Frontend.LocalInputs.runTerminalReturnBody?
example := @Solcore.Frontend.elaborateTerminalReturnBody?_single
example := @Solcore.Frontend.elaborateTerminalReturnBody?_conditional
example := @Solcore.Frontend.ReturnBodyElaborates.terminal_complete
example := @Solcore.Frontend.ConditionalReturnBodyElaborates.terminal_complete
example := @Solcore.Frontend.TerminalReturnBodyElaborates.complete
example := @Solcore.Frontend.elaborateTerminalReturnBody?_elaborates
example := @Solcore.Frontend.elaborateTerminalReturnBody?_iff
example := @Solcore.Frontend.TerminalReturnBodyElaborates.hasType
example := @Solcore.Frontend.TerminalReturnBodyHasType.elaborates_exact
example := @Solcore.Frontend.TerminalReturnBodyHasType.elaborates
example := @Solcore.Frontend.elaborateTerminalReturnBody?_sound
example := @Solcore.Frontend.terminalReturnBodyHasType_iff_elaborates
example := @Solcore.Frontend.elaborateTerminalReturnBody?_core_hasType
example := @Solcore.Frontend.TerminalReturnBodyElaborates.result_unique
example := @Solcore.Frontend.TerminalReturnBodyHasType.type_unique
example := @Solcore.Frontend.elaborateTerminalReturnBody?_eq_none_iff
example := @Solcore.Frontend.TerminalReturnBodyEvaluates
example := @Solcore.Frontend.TerminalReturnBodyEvaluatesWithCost
example := @Solcore.Frontend.TerminalReturnBodyEvaluates.store_eq
example := @Solcore.Frontend.TerminalReturnBodyEvaluates.deterministic
example := @Solcore.Frontend.TerminalReturnBodyHasType.evaluates
example := @Solcore.Frontend.TerminalReturnBodyEvaluates.preserves_type
example := @Solcore.Frontend.TerminalReturnBodyEvaluatesWithCost.erase
example := @Solcore.Frontend.TerminalReturnBodyEvaluates.exists_cost
example := @Solcore.Frontend.terminalReturnBodyEvaluates_iff_exists_cost
example := @Solcore.Frontend.TerminalReturnBodyEvaluatesWithCost.store_eq
example := @Solcore.Frontend.TerminalReturnBodyEvaluatesWithCost.cost_pos
example := @Solcore.Frontend.TerminalReturnBodyEvaluatesWithCost.deterministic
example := @Solcore.Frontend.elaborateTerminalReturnBody?_evaluates_iff
example := @Solcore.Frontend.TerminalReturnBodyEvaluatesWithCost.checked_toStepsWithContinuation
example := @Solcore.Frontend.TerminalReturnBodyEvaluatesWithCost.checked_toSteps
example := @Solcore.Frontend.TerminalReturnBodyEvaluatesWithCost.checked_runStateful_done_iff
example := @Solcore.Frontend.TerminalReturnBodyEvaluatesWithCost.checked_runStateful_outOfFuel_iff
example := @Solcore.Frontend.elaborateTerminalReturnBody?_run_done_iff_cost
example := @Solcore.Frontend.LocalInputs.runTerminalReturnBody?_single
example := @Solcore.Frontend.LocalInputs.runTerminalReturnBody?_conditional
example := @Solcore.Frontend.LocalInputs.runTerminalReturnBody?_eq_some_iff
example := @Solcore.Frontend.LocalInputs.runTerminalReturnBody?_done_iff_typed_cost
example := @Solcore.Frontend.LocalInputs.terminalReturnBody_typed_cost_execution
example := @Solcore.Frontend.LocalInputs.runTerminalReturnBody?_outOfFuel_iff_typed_cost
example := @Solcore.Frontend.LocalInputs.runTerminalReturnBody?_never_faults
example := @Solcore.Frontend.terminalReturnBodyFuelBound
example := @Solcore.Frontend.TerminalReturnBodyEvaluatesWithCost.cost_le_fuelBound
example := @Solcore.Frontend.elaborateTerminalReturnBody?_run_done_of_fuelBound
example := @Solcore.Frontend.LocalInputs.runTerminalReturnBody?_done_of_fuelBound
example := @Solcore.Frontend.TerminalReturnBodyEvaluatesWithCost.checked_residual_of_outOfFuel
example := @Solcore.Frontend.LocalInputs.runTerminalReturnBody?_resume
example := @Solcore.Frontend.TerminalReturnBodyHasType.single
example := @Solcore.Frontend.TerminalReturnBodyHasType.conditional
example := @Solcore.Frontend.TerminalReturnBodyElaborates.single
example := @Solcore.Frontend.TerminalReturnBodyElaborates.conditional
example := @Solcore.Frontend.TerminalReturnBodyEvaluates.single
example := @Solcore.Frontend.TerminalReturnBodyEvaluates.conditional
example := @Solcore.Frontend.TerminalReturnBodyEvaluatesWithCost.single
example := @Solcore.Frontend.TerminalReturnBodyEvaluatesWithCost.conditional
example := @Solcore.Frontend.elaborateReturnBody?_mapIds
example := @Solcore.Frontend.LocalInputs.checkReturnBody?_mapIds
example := @Solcore.Frontend.LocalInputs.runReturnBody?_mapIds
example := @Solcore.Frontend.ConditionalReturnBodyElaborates.mapIds
example := @Solcore.Frontend.elaborateConditionalReturnBody?_mapIds
example := @Solcore.Frontend.LocalInputs.checkConditionalReturnBody?_mapIds
example := @Solcore.Frontend.LocalInputs.runConditionalReturnBody?_mapIds
example := @Solcore.Frontend.TerminalReturnBodyElaborates.mapIds
example := @Solcore.Frontend.elaborateTerminalReturnBody?_mapIds
example := @Solcore.Frontend.LocalInputs.checkTerminalReturnBody?_mapIds
example := @Solcore.Frontend.LocalInputs.runTerminalReturnBody?_mapIds
example := @Solcore.Frontend.returnBodyEvaluates_store_iff
example := @Solcore.Frontend.returnBodyEvaluatesWithCost_store_iff
example := @Solcore.Frontend.LocalInputs.runReturnBody?_done_store_iff
example := @Solcore.Frontend.LocalInputs.runReturnBody?_outOfFuel_store_iff
example := @Solcore.Frontend.ConditionalReturnBodyEvaluates.change_store
example := @Solcore.Frontend.ConditionalReturnBodyEvaluatesWithCost.change_store
example := @Solcore.Frontend.conditionalReturnBodyEvaluates_store_iff
example := @Solcore.Frontend.conditionalReturnBodyEvaluatesWithCost_store_iff
example := @Solcore.Frontend.LocalInputs.runConditionalReturnBody?_done_store_iff
example := @Solcore.Frontend.LocalInputs.runConditionalReturnBody?_outOfFuel_store_iff
example := @Solcore.Frontend.TerminalReturnBodyEvaluates.change_store
example := @Solcore.Frontend.TerminalReturnBodyEvaluatesWithCost.change_store
example := @Solcore.Frontend.terminalReturnBodyEvaluates_store_iff
example := @Solcore.Frontend.terminalReturnBodyEvaluatesWithCost_store_iff
example := @Solcore.Frontend.LocalInputs.runTerminalReturnBody?_done_store_iff
example := @Solcore.Frontend.LocalInputs.runTerminalReturnBody?_outOfFuel_store_iff

example := @Solcore.Frontend.ResolvesLocalExpression.divide
example := @Solcore.Frontend.ResolvesLocalExpression.modulo
example := @Solcore.Frontend.LocalExpressionHasType.divide
example := @Solcore.Frontend.LocalExpressionHasType.modulo
example := @Solcore.Frontend.AvoidsLocalName.divide
example := @Solcore.Frontend.AvoidsLocalName.modulo
example := @Solcore.Frontend.LocalExpressionEvaluates.divide
example := @Solcore.Frontend.LocalExpressionEvaluates.modulo
example := @Solcore.Frontend.LocalExpressionEvaluatesWithCost.divide
example := @Solcore.Frontend.LocalExpressionEvaluatesWithCost.modulo
example := @Solcore.Frontend.resolveLocalExpression?_divide_spans
example := @Solcore.Frontend.resolveLocalExpression?_modulo_spans

example := @Solcore.Frontend.LocalTypeBinding.mapIds
example := @Solcore.Frontend.LocalTypeBinding.mapIds_id
example := @Solcore.Frontend.LocalTypeBinding.mapIds_comp
example := @Solcore.Frontend.LocalTypeInputs.mapIds
example := @Solcore.Frontend.LocalTypeInputs.mapIds_bindings
example := @Solcore.Frontend.LocalTypeInputs.mapIds_ids
example := @Solcore.Frontend.LocalTypeInputs.mapIds_names
example := @Solcore.Frontend.LocalTypeInputs.mapIds_context
example := @Solcore.Frontend.LocalTypeInputs.mapIds_id
example := @Solcore.Frontend.LocalTypeInputs.mapIds_comp
example := @Solcore.Frontend.LocalInputs.toTypeInputs_mapIds
example := @Solcore.Frontend.RuntimeParametersDeclare.map_owner
example := @Solcore.Frontend.RuntimeFunctionCompiles.mapOwner
example := @Solcore.Frontend.compileRuntimeFunction?_owner_projection_eq

example := @Solcore.Frontend.RuntimeParameterDeclarationRow
example := @Solcore.Frontend.RuntimeParameterDeclarationRows
example := @Solcore.Frontend.RuntimeParameterDeclarationRows.arity
example := @Solcore.Frontend.RuntimeParameterDeclarationRows.row_at
example := @Solcore.Frontend.RuntimeParametersDeclareFrom.rows
example := @Solcore.Frontend.RuntimeParametersDeclareFrom.bindings_length
example := @Solcore.Frontend.RuntimeParametersDeclareFrom.names_nodup
example := @Solcore.Frontend.RuntimeParametersDeclareFrom.generated_ids
example := @Solcore.Frontend.RuntimeParametersDeclare.rows
example := @Solcore.Frontend.RuntimeParametersDeclare.bindings_length
example := @Solcore.Frontend.RuntimeParametersDeclare.names_nodup
example := @Solcore.Frontend.RuntimeParametersDeclare.generated_ids
example := @Solcore.Frontend.RuntimeParameterDeclarationRow.typed
example := @Solcore.Frontend.RuntimeParameterDeclarationRows.nil
example := @Solcore.Frontend.RuntimeParameterDeclarationRows.cons
example := @Solcore.Frontend.RuntimeParametersDeclare.position
example := @Solcore.Frontend.RuntimeParametersDeclare.reference_resolves_at
example := @Solcore.Frontend.RuntimeParametersDeclare.reference_elaborates_at
example := @Solcore.Frontend.RuntimeParametersDeclare.reference_return_elaborates_at

example := @Solcore.Frontend.runtimeFunction_parameter_compiles
example := @Solcore.Frontend.compileRuntimeFunction?_parameter
example := @Solcore.Frontend.RuntimeFunctionCompiles.parameter_return_core
example := @Solcore.Frontend.runtimeFunction_conditional_parameters_compiles
example := @Solcore.Frontend.compileRuntimeFunction?_conditional_parameters
example := @Solcore.Frontend.RuntimeFunctionCompiles.conditional_parameters_core

example := @Solcore.Frontend.TypeNameTable.Extends
example := @Solcore.Frontend.TypeNameTable.Extends.refl
example := @Solcore.Frontend.TypeNameTable.Extends.trans
example := @Solcore.Frontend.TypeNameTable.Extends.append_right
example := @Solcore.Frontend.TypeNameTable.Extends.cons_fresh
example := @Solcore.Frontend.TypeNameTable.lookup?_eq_of_mutual_extends
example := @Solcore.Frontend.TypeNameDenotes.extend_types
example := @Solcore.Frontend.interpretTypeName?_some_of_extends
example := @Solcore.Frontend.interpretTypeName?_eq_of_mutual_extends
example := @Solcore.Frontend.RuntimeReturnTypeDenotes.extend_types
example := @Solcore.Frontend.RuntimeFunctionHeader.extend_types
example := @Solcore.Frontend.RuntimeParametersDeclareFrom.extend_types
example := @Solcore.Frontend.RuntimeParametersDeclare.extend_types
example := @Solcore.Frontend.declareRuntimeParameters?_some_of_extends
example := @Solcore.Frontend.declareRuntimeParameters?_eq_of_mutual_extends
example := @Solcore.Frontend.RuntimeFunctionCompiles.extend_types
example := @Solcore.Frontend.compileRuntimeFunction?_some_of_extends
example := @Solcore.Frontend.compileRuntimeFunction?_eq_of_mutual_extends

example := @Solcore.Frontend.elaborateTerminalReturnTree?
example := @Solcore.Frontend.TerminalReturnTreeHasType
example := @Solcore.Frontend.TerminalReturnTreeElaborates
example := @Solcore.Frontend.elaborateTerminalReturnTree?_single
example := @Solcore.Frontend.elaborateTerminalReturnTree?_children
example := @Solcore.Frontend.TerminalReturnTreeElaborates.complete
example := @Solcore.Frontend.elaborateTerminalReturnTree?_elaborates
example := @Solcore.Frontend.elaborateTerminalReturnTree?_iff
example := @Solcore.Frontend.TerminalReturnTreeElaborates.hasType
example := @Solcore.Frontend.TerminalReturnTreeHasType.elaborates_exact
example := @Solcore.Frontend.terminalReturnTreeHasType_iff_elaborates_exact
example := @Solcore.Frontend.TerminalReturnTreeHasType.elaborates
example := @Solcore.Frontend.elaborateTerminalReturnTree?_sound
example := @Solcore.Frontend.terminalReturnTreeHasType_iff_elaborates
example := @Solcore.Frontend.elaborateTerminalReturnTree?_core_hasType
example := @Solcore.Frontend.TerminalReturnTreeElaborates.result_unique
example := @Solcore.Frontend.TerminalReturnTreeHasType.type_unique
example := @Solcore.Frontend.elaborateTerminalReturnTree?_eq_none_iff
example := @Solcore.Frontend.elaborateTerminalReturnTree?_spans
example := @Solcore.Frontend.ReturnBodyHasType.returnTree
example := @Solcore.Frontend.ReturnBodyElaborates.returnTree
example := @Solcore.Frontend.ReturnBodyElaborates.returnTree_complete
example := @Solcore.Frontend.ConditionalReturnBodyHasType.returnTree
example := @Solcore.Frontend.ConditionalReturnBodyElaborates.returnTree
example := @Solcore.Frontend.ConditionalReturnBodyElaborates.returnTree_complete
example := @Solcore.Frontend.TerminalReturnBodyHasType.returnTree
example := @Solcore.Frontend.TerminalReturnBodyElaborates.returnTree
example := @Solcore.Frontend.TerminalReturnBodyElaborates.returnTree_complete
example := @Solcore.Frontend.elaborateTerminalReturnTree?_single_terminal
example := @Solcore.Frontend.elaborateTerminalReturnTree?_conditional_singletons
example := @Solcore.Frontend.elaborateTerminalReturnTree?_conditional_singletons_terminal
example := @Solcore.Frontend.TerminalReturnTreeHasType.single
example := @Solcore.Frontend.TerminalReturnTreeHasType.conditional
example := @Solcore.Frontend.TerminalReturnTreeElaborates.single
example := @Solcore.Frontend.TerminalReturnTreeElaborates.conditional

example := @Solcore.Frontend.TerminalReturnTreeEvaluates
example := @Solcore.Frontend.TerminalReturnTreeEvaluatesWithCost
example := @Solcore.Frontend.TerminalReturnTreeEvaluates.store_eq
example := @Solcore.Frontend.TerminalReturnTreeEvaluates.deterministic
example := @Solcore.Frontend.TerminalReturnTreeHasType.evaluates
example := @Solcore.Frontend.TerminalReturnTreeEvaluates.preserves_type
example := @Solcore.Frontend.TerminalReturnTreeEvaluatesWithCost.erase
example := @Solcore.Frontend.TerminalReturnTreeEvaluates.exists_cost
example := @Solcore.Frontend.terminalReturnTreeEvaluates_iff_exists_cost
example := @Solcore.Frontend.TerminalReturnTreeEvaluatesWithCost.store_eq
example := @Solcore.Frontend.TerminalReturnTreeEvaluatesWithCost.cost_pos
example := @Solcore.Frontend.TerminalReturnTreeEvaluatesWithCost.deterministic
example := @Solcore.Frontend.elaborateTerminalReturnTree?_evaluates_iff
example := @Solcore.Frontend.TerminalReturnTreeEvaluatesWithCost.checked_toStepsWithContinuation
example := @Solcore.Frontend.TerminalReturnTreeEvaluatesWithCost.checked_toSteps
example := @Solcore.Frontend.ReturnBodyEvaluates.returnTree
example := @Solcore.Frontend.ReturnBodyEvaluatesWithCost.returnTree
example := @Solcore.Frontend.ConditionalReturnBodyEvaluates.returnTree
example := @Solcore.Frontend.ConditionalReturnBodyEvaluatesWithCost.returnTree
example := @Solcore.Frontend.TerminalReturnBodyEvaluates.returnTree
example := @Solcore.Frontend.TerminalReturnBodyEvaluatesWithCost.returnTree
example := @Solcore.Frontend.TerminalReturnTreeEvaluates.single
example := @Solcore.Frontend.TerminalReturnTreeEvaluates.ifTrue
example := @Solcore.Frontend.TerminalReturnTreeEvaluates.ifFalse
example := @Solcore.Frontend.TerminalReturnTreeEvaluatesWithCost.single
example := @Solcore.Frontend.TerminalReturnTreeEvaluatesWithCost.ifTrue
example := @Solcore.Frontend.TerminalReturnTreeEvaluatesWithCost.ifFalse

example := @Solcore.Frontend.LocalInputs.checkTerminalReturnTree?
example := @Solcore.Frontend.LocalInputs.runTerminalReturnTree?
example := @Solcore.Frontend.TerminalReturnTreeEvaluatesWithCost.checked_runStateful_done_iff
example := @Solcore.Frontend.TerminalReturnTreeEvaluatesWithCost.checked_runStateful_outOfFuel_iff
example := @Solcore.Frontend.elaborateTerminalReturnTree?_run_done_iff_cost
example := @Solcore.Frontend.LocalInputs.runTerminalReturnTree?_eq_none_iff
example := @Solcore.Frontend.LocalInputs.runTerminalReturnTree?_eq_some_iff
example := @Solcore.Frontend.LocalInputs.runTerminalReturnTree?_done_iff_typed_cost
example := @Solcore.Frontend.LocalInputs.terminalReturnTree_typed_cost_execution
example := @Solcore.Frontend.LocalInputs.runTerminalReturnTree?_outOfFuel_iff_typed_cost
example := @Solcore.Frontend.LocalInputs.runTerminalReturnTree?_never_faults
example := @Solcore.Frontend.terminalReturnTreeFuelBound
example := @Solcore.Frontend.TerminalReturnTreeEvaluatesWithCost.cost_le_fuelBound
example := @Solcore.Frontend.elaborateTerminalReturnTree?_run_done_of_fuelBound
example := @Solcore.Frontend.LocalInputs.runTerminalReturnTree?_done_of_fuelBound
example := @Solcore.Frontend.TerminalReturnTreeEvaluatesWithCost.checked_residual_of_outOfFuel
example := @Solcore.Frontend.LocalInputs.runTerminalReturnTree?_resume
example := @Solcore.Frontend.LocalInputs.runTerminalReturnTree?_single
example := @Solcore.Frontend.LocalInputs.runTerminalReturnTree?_single_terminal
example := @Solcore.Frontend.LocalInputs.runTerminalReturnTree?_conditional_singletons
example := @Solcore.Frontend.LocalInputs.runTerminalReturnTree?_conditional_singletons_terminal

example := @Solcore.Frontend.TerminalReturnTreeElaborates.mapIds
example := @Solcore.Frontend.elaborateTerminalReturnTree?_mapIds
example := @Solcore.Frontend.LocalInputs.checkTerminalReturnTree?_mapIds
example := @Solcore.Frontend.LocalInputs.runTerminalReturnTree?_mapIds
example := @Solcore.Frontend.TerminalReturnTreeEvaluates.change_store
example := @Solcore.Frontend.TerminalReturnTreeEvaluatesWithCost.change_store
example := @Solcore.Frontend.terminalReturnTreeEvaluates_store_iff
example := @Solcore.Frontend.terminalReturnTreeEvaluatesWithCost_store_iff
example := @Solcore.Frontend.LocalInputs.runTerminalReturnTree?_done_store_iff
example := @Solcore.Frontend.LocalInputs.runTerminalReturnTree?_outOfFuel_store_iff

example := @Solcore.Frontend.elaborateTypedLetReturnBody?
example := @Solcore.Frontend.TypedLetReturnBodyHasType
example := @Solcore.Frontend.TypedLetReturnBodyElaborates
example := @Solcore.Frontend.elaborateTypedLetReturnBody?_binding_children
example := @Solcore.Frontend.TypedLetReturnBodyElaborates.complete
example := @Solcore.Frontend.elaborateTypedLetReturnBody?_elaborates
example := @Solcore.Frontend.elaborateTypedLetReturnBody?_iff
example := @Solcore.Frontend.TypedLetReturnBodyHasType.terminal
example := @Solcore.Frontend.TypedLetReturnBodyHasType.binding
example := @Solcore.Frontend.TypedLetReturnBodyElaborates.terminal
example := @Solcore.Frontend.TypedLetReturnBodyElaborates.binding

example := @Solcore.Frontend.TypedLetReturnBodyElaborates.hasType
example := @Solcore.Frontend.TypedLetReturnBodyHasType.elaborates_exact
example := @Solcore.Frontend.typedLetReturnBodyHasType_iff_elaborates_exact
example := @Solcore.Frontend.TypedLetReturnBodyHasType.elaborates
example := @Solcore.Frontend.elaborateTypedLetReturnBody?_sound
example := @Solcore.Frontend.typedLetReturnBodyHasType_iff_elaborates
example := @Solcore.Frontend.elaborateTypedLetReturnBody?_core_hasType
example := @Solcore.Frontend.TypedLetReturnBodyElaborates.result_unique
example := @Solcore.Frontend.TypedLetReturnBodyHasType.type_unique
example := @Solcore.Frontend.elaborateTypedLetReturnBody?_eq_none_iff
example := @Solcore.Frontend.TerminalReturnTreeHasType.typedLetReturnBody
example := @Solcore.Frontend.TerminalReturnTreeElaborates.typedLetReturnBody
example := @Solcore.Frontend.TerminalReturnTreeElaborates.typedLetReturnBody_complete
example := @Solcore.Frontend.elaborateTypedLetReturnBody?_single
example := @Solcore.Frontend.elaborateTypedLetReturnBody?_conditional
example := @Solcore.Frontend.elaborateTypedLetReturnBody?_conditional_singletons

example := @Solcore.Frontend.LocalTypeInputs.names_ids
example := @Solcore.Frontend.TypedLetReturnBodyEvaluates
example := @Solcore.Frontend.TypedLetReturnBodyEvaluatesWithCost
example := @Solcore.Frontend.TypedLetReturnBodyEvaluates.store_eq
example := @Solcore.Frontend.TypedLetReturnBodyEvaluates.deterministic
example := @Solcore.Frontend.TypedLetReturnBodyHasType.evaluates
example := @Solcore.Frontend.TypedLetReturnBodyEvaluates.preserves_type
example := @Solcore.Frontend.TypedLetReturnBodyEvaluatesWithCost.erase
example := @Solcore.Frontend.TypedLetReturnBodyEvaluates.exists_cost
example := @Solcore.Frontend.typedLetReturnBodyEvaluates_iff_exists_cost
example := @Solcore.Frontend.TypedLetReturnBodyEvaluatesWithCost.store_eq
example := @Solcore.Frontend.TypedLetReturnBodyEvaluatesWithCost.cost_pos
example := @Solcore.Frontend.TypedLetReturnBodyEvaluatesWithCost.deterministic
example := @Solcore.Frontend.elaborateTypedLetReturnBody?_evaluates_iff
example := @Solcore.Frontend.TypedLetReturnBodyEvaluatesWithCost.checked_toStepsWithContinuation
example := @Solcore.Frontend.TypedLetReturnBodyEvaluatesWithCost.checked_toSteps
example := @Solcore.Frontend.TerminalReturnTreeEvaluates.typedLetReturnBody
example := @Solcore.Frontend.TerminalReturnTreeEvaluatesWithCost.typedLetReturnBody
example := @Solcore.Frontend.TypedLetReturnBodyEvaluates.terminal
example := @Solcore.Frontend.TypedLetReturnBodyEvaluates.binding
example := @Solcore.Frontend.TypedLetReturnBodyEvaluatesWithCost.terminal
example := @Solcore.Frontend.TypedLetReturnBodyEvaluatesWithCost.binding

example := @Solcore.Frontend.LocalInputs.checkTypedLetReturnBody?
example := @Solcore.Frontend.LocalInputs.runTypedLetReturnBody?
example := @Solcore.Frontend.TypedLetReturnBodyEvaluatesWithCost.checked_runStateful_done_iff
example := @Solcore.Frontend.TypedLetReturnBodyEvaluatesWithCost.checked_runStateful_outOfFuel_iff
example := @Solcore.Frontend.elaborateTypedLetReturnBody?_run_done_iff_cost
example := @Solcore.Frontend.LocalInputs.runTypedLetReturnBody?_eq_none_iff
example := @Solcore.Frontend.LocalInputs.runTypedLetReturnBody?_eq_some_iff
example := @Solcore.Frontend.LocalInputs.runTypedLetReturnBody?_done_iff_typed_cost
example := @Solcore.Frontend.LocalInputs.typedLetReturnBody_typed_cost_execution
example := @Solcore.Frontend.LocalInputs.runTypedLetReturnBody?_outOfFuel_iff_typed_cost
example := @Solcore.Frontend.LocalInputs.runTypedLetReturnBody?_never_faults
example := @Solcore.Frontend.typedLetReturnBodyFuelBound
example := @Solcore.Frontend.TypedLetReturnBodyEvaluatesWithCost.cost_le_fuelBound
example := @Solcore.Frontend.elaborateTypedLetReturnBody?_run_done_of_fuelBound
example := @Solcore.Frontend.LocalInputs.runTypedLetReturnBody?_done_of_fuelBound
example := @Solcore.Frontend.TypedLetReturnBodyEvaluatesWithCost.checked_residual_of_outOfFuel
example := @Solcore.Frontend.LocalInputs.runTypedLetReturnBody?_resume
example := @Solcore.Frontend.LocalInputs.runTypedLetReturnBody?_single
example := @Solcore.Frontend.LocalInputs.runTypedLetReturnBody?_conditional
example := @Solcore.Frontend.LocalInputs.runTypedLetReturnBody?_conditional_singletons

example := @Solcore.Frontend.TypedLetReturnBodyEvaluates.change_store
example := @Solcore.Frontend.TypedLetReturnBodyEvaluatesWithCost.change_store
example := @Solcore.Frontend.typedLetReturnBodyEvaluates_store_iff
example := @Solcore.Frontend.typedLetReturnBodyEvaluatesWithCost_store_iff
example := @Solcore.Frontend.LocalInputs.runTypedLetReturnBody?_done_store_iff
example := @Solcore.Frontend.LocalInputs.runTypedLetReturnBody?_outOfFuel_store_iff

example := @Solcore.Frontend.LocalTypeInputs.bindFresh_mapOwner
example := @Solcore.Frontend.TypedLetReturnBodyElaborates.mapOwner
example := @Solcore.Frontend.TypedLetReturnBodyHasType.mapOwner
example := @Solcore.Frontend.elaborateTypedLetReturnBody?_mapOwner
example := @Solcore.Frontend.LocalInputs.checkTypedLetReturnBody?_mapOwner
example := @Solcore.Frontend.LocalInputs.runTypedLetReturnBody?_mapOwner

example := @Solcore.Frontend.TypedLetReturnBodyElaborates.extend_types
example := @Solcore.Frontend.TypedLetReturnBodyHasType.extend_types
example := @Solcore.Frontend.elaborateTypedLetReturnBody?_some_of_extends
example := @Solcore.Frontend.elaborateTypedLetReturnBody?_eq_of_mutual_extends
example := @Solcore.Frontend.LocalInputs.checkTypedLetReturnBody?_some_of_extends
example := @Solcore.Frontend.LocalInputs.checkTypedLetReturnBody?_eq_of_mutual_extends
example := @Solcore.Frontend.LocalInputs.runTypedLetReturnBody?_some_of_extends
example := @Solcore.Frontend.LocalInputs.runTypedLetReturnBody?_eq_of_mutual_extends

section RecursiveTypedLetEntryContracts

open Solcore Solcore.Frontend

variable {types : TypeNameTable} {owner : Resolved.DeclarationId}
  {declaration : Syntax.FunctionDecl} {arguments : List TypedRuntimeArgument}
  {compiled : CompiledRuntimeFunction} {prepared : PreparedRuntimeFunction}
  {initialStore finalStore : Core.Store} {type : Core.Ty} {value : Core.Value} {cost : Nat}

example (compilation : RuntimeFunctionCompiles types owner declaration compiled) :
    TypedLetReturnTreeElaborates types owner compiled.inputs
      declaration.value.body compiled.core compiled.returnType := compilation.body

example (preparation : RuntimeFunctionPrepares types owner declaration arguments prepared) :
    TypedLetReturnTreeElaborates types owner prepared.inputs.toTypeInputs
      declaration.value.body prepared.core prepared.returnType := preparation.body

example (preparation : RuntimeFunctionPrepares types owner declaration arguments prepared)
    (bodyCost : TypedLetReturnTreeEvaluatesWithCost owner prepared.inputs.names prepared.inputs.environment
      initialStore declaration.value.body value finalStore cost) :
    RuntimeFunctionEvaluatesWithCost types owner declaration arguments
      initialStore prepared.returnType value finalStore cost := .intro preparation bodyCost

example (evaluation : RuntimeFunctionEvaluatesWithCost types owner declaration arguments
    initialStore type value finalStore cost) :
    cost ≤ typedLetReturnTreeFuelBound declaration.value.body := evaluation.cost_le_fuelBound

example (typing : RuntimeFunctionHasType types owner declaration arguments type)
    (store : Core.Store) (fuel : Nat) (enough : typedLetReturnTreeFuelBound declaration.value.body ≤ fuel) :
    ∃ value, Core.ValueHasType value type ∧ runRuntimeFunction? types owner declaration arguments fuel store =
      some (type, .done value store) := typing.run_done_of_fuelBound store fuel enough

example (compilation : RuntimeFunctionCompiles types owner declaration compiled)
    (matchingTypes : arguments.map (·.type) = compiled.inputs.context.values.reverse)
    (store : Core.Store) (fuel : Nat) (enough : typedLetReturnTreeFuelBound declaration.value.body ≤ fuel) :
    ∃ value, Core.ValueHasType value compiled.returnType ∧
      runRuntimeFunction? types owner declaration arguments fuel store = some (compiled.returnType, .done value store) ∧
      Core.runStateful fuel (Core.State.initial compiled.core (arguments.reverse.map (·.value)) store) =
        .done value store := compilation.run_done_of_fuelBound arguments matchingTypes store fuel enough

end RecursiveTypedLetEntryContracts

example := @Solcore.Frontend.elaborateTypedLetReturnTree?
example := @Solcore.Frontend.TypedLetReturnTreeHasType
example := @Solcore.Frontend.TypedLetReturnTreeElaborates
example := @Solcore.Frontend.TypedLetReturnTreeHasType.single
example := @Solcore.Frontend.TypedLetReturnTreeHasType.block
example := @Solcore.Frontend.TypedLetReturnTreeHasType.binding
example := @Solcore.Frontend.TypedLetReturnTreeHasType.inferred
example := @Solcore.Frontend.TypedLetReturnTreeHasType.discard
example := @Solcore.Frontend.TypedLetReturnTreeHasType.conditional
example := @Solcore.Frontend.TypedLetReturnTreeElaborates.single
example := @Solcore.Frontend.TypedLetReturnTreeElaborates.block
example := @Solcore.Frontend.TypedLetReturnTreeElaborates.binding
example := @Solcore.Frontend.TypedLetReturnTreeElaborates.inferred
example := @Solcore.Frontend.TypedLetReturnTreeElaborates.discard
example := @Solcore.Frontend.TypedLetReturnTreeElaborates.conditional
example := @Solcore.Frontend.elaborateTypedLetReturnTree?_single
example := @Solcore.Frontend.elaborateTypedLetReturnTree?_block
example := @Solcore.Frontend.elaborateTypedLetReturnTree?_binding_children
example := @Solcore.Frontend.elaborateTypedLetReturnTree?_inferred_children
example := @Solcore.Frontend.elaborateTypedLetReturnTree?_discard_children
example := @Solcore.Frontend.elaborateLocalExpression?_localFragment
example := @Solcore.Frontend.ReturnBodyElaborates.localFragment
example := @Solcore.Frontend.TerminalReturnTreeElaborates.localFragment
example := @Solcore.Frontend.TypedLetReturnTreeElaborates.localFragment
example := @Solcore.Frontend.RuntimeFunctionCompiles.localFragment
example := @Solcore.Frontend.RuntimeFunctionPrepares.localFragment
example := @Solcore.Frontend.compileRuntimeFunction?_localFragment
example := @Solcore.Frontend.prepareRuntimeFunction?_localFragment
example := @Solcore.Frontend.elaborateTypedLetReturnTree?_conditional_children
example := @Solcore.Frontend.TypedLetReturnTreeElaborates.complete
example := @Solcore.Frontend.elaborateTypedLetReturnTree?_elaborates
example := @Solcore.Frontend.elaborateTypedLetReturnTree?_iff
example := @Solcore.Frontend.TypedLetReturnTreeElaborates.hasType
example := @Solcore.Frontend.TypedLetReturnTreeHasType.elaborates_exact
example := @Solcore.Frontend.typedLetReturnTreeHasType_iff_elaborates_exact
example := @Solcore.Frontend.TypedLetReturnTreeHasType.elaborates
example := @Solcore.Frontend.elaborateTypedLetReturnTree?_sound
example := @Solcore.Frontend.typedLetReturnTreeHasType_iff_elaborates
example := @Solcore.Frontend.elaborateTypedLetReturnTree?_core_hasType
example := @Solcore.Frontend.TypedLetReturnTreeElaborates.result_unique
example := @Solcore.Frontend.TypedLetReturnTreeHasType.type_unique
example := @Solcore.Frontend.elaborateTypedLetReturnTree?_eq_none_iff
example := @Solcore.Frontend.TerminalReturnTreeHasType.typedLetReturnTree
example := @Solcore.Frontend.TerminalReturnTreeElaborates.typedLetReturnTree
example := @Solcore.Frontend.TypedLetReturnBodyHasType.returnTree
example := @Solcore.Frontend.TypedLetReturnBodyElaborates.returnTree
example := @Solcore.Frontend.elaborateTypedLetReturnTree?_some_of_terminalReturnTree
example := @Solcore.Frontend.elaborateTypedLetReturnTree?_some_of_typedLetReturnBody

example := @Solcore.Frontend.TypedLetReturnTreeEvaluates
example := @Solcore.Frontend.TypedLetReturnTreeEvaluatesWithCost
example := @Solcore.Frontend.TypedLetReturnTreeEvaluates.single
example := @Solcore.Frontend.TypedLetReturnTreeEvaluates.block
example := @Solcore.Frontend.TypedLetReturnTreeEvaluates.binding
example := @Solcore.Frontend.TypedLetReturnTreeEvaluates.inferred
example := @Solcore.Frontend.TypedLetReturnTreeEvaluates.discard
example := @Solcore.Frontend.TypedLetReturnTreeEvaluates.ifTrue
example := @Solcore.Frontend.TypedLetReturnTreeEvaluates.ifFalse
example := @Solcore.Frontend.TypedLetReturnTreeEvaluatesWithCost.single
example := @Solcore.Frontend.TypedLetReturnTreeEvaluatesWithCost.block
example := @Solcore.Frontend.TypedLetReturnTreeEvaluatesWithCost.binding
example := @Solcore.Frontend.TypedLetReturnTreeEvaluatesWithCost.inferred
example := @Solcore.Frontend.TypedLetReturnTreeEvaluatesWithCost.discard
example := @Solcore.Frontend.TypedLetReturnTreeEvaluatesWithCost.ifTrue
example := @Solcore.Frontend.TypedLetReturnTreeEvaluatesWithCost.ifFalse
example := @Solcore.Frontend.TypedLetReturnTreeEvaluates.store_eq
example := @Solcore.Frontend.TypedLetReturnTreeEvaluates.deterministic
example := @Solcore.Frontend.TypedLetReturnTreeHasType.evaluates
example := @Solcore.Frontend.TypedLetReturnTreeEvaluates.preserves_type
example := @Solcore.Frontend.TypedLetReturnTreeEvaluatesWithCost.erase
example := @Solcore.Frontend.TypedLetReturnTreeEvaluates.exists_cost
example := @Solcore.Frontend.typedLetReturnTreeEvaluates_iff_exists_cost
example := @Solcore.Frontend.TypedLetReturnTreeEvaluatesWithCost.store_eq
example := @Solcore.Frontend.TypedLetReturnTreeEvaluatesWithCost.cost_pos
example := @Solcore.Frontend.TypedLetReturnTreeEvaluatesWithCost.deterministic
example := @Solcore.Frontend.elaborateTypedLetReturnTree?_evaluates_iff
example := @Solcore.Frontend.TypedLetReturnTreeEvaluatesWithCost.checked_toStepsWithContinuation
example := @Solcore.Frontend.TypedLetReturnTreeEvaluatesWithCost.checked_toSteps
example := @Solcore.Frontend.TerminalReturnTreeEvaluates.typedLetReturnTree
example := @Solcore.Frontend.TerminalReturnTreeEvaluatesWithCost.typedLetReturnTree
example := @Solcore.Frontend.TypedLetReturnBodyEvaluates.returnTree
example := @Solcore.Frontend.TypedLetReturnBodyEvaluatesWithCost.returnTree

example := @Solcore.Frontend.LocalInputs.checkTypedLetReturnTree?
example := @Solcore.Frontend.LocalInputs.runTypedLetReturnTree?
example := @Solcore.Frontend.TypedLetReturnTreeEvaluatesWithCost.checked_runStateful_done_iff
example := @Solcore.Frontend.TypedLetReturnTreeEvaluatesWithCost.checked_runStateful_outOfFuel_iff
example := @Solcore.Frontend.elaborateTypedLetReturnTree?_run_done_iff_cost
example := @Solcore.Frontend.LocalInputs.runTypedLetReturnTree?_eq_none_iff
example := @Solcore.Frontend.LocalInputs.runTypedLetReturnTree?_eq_some_iff
example := @Solcore.Frontend.LocalInputs.runTypedLetReturnTree?_done_iff_typed_cost
example := @Solcore.Frontend.LocalInputs.typedLetReturnTree_typed_cost_execution
example := @Solcore.Frontend.LocalInputs.runTypedLetReturnTree?_outOfFuel_iff_typed_cost
example := @Solcore.Frontend.LocalInputs.runTypedLetReturnTree?_never_faults
example := @Solcore.Frontend.typedLetReturnTreeFuelBound
example := @Solcore.Frontend.TypedLetReturnTreeEvaluatesWithCost.cost_le_fuelBound
example := @Solcore.Frontend.elaborateTypedLetReturnTree?_run_done_of_fuelBound
example := @Solcore.Frontend.LocalInputs.runTypedLetReturnTree?_done_of_fuelBound
example := @Solcore.Frontend.TypedLetReturnTreeEvaluatesWithCost.checked_residual_of_outOfFuel
example := @Solcore.Frontend.LocalInputs.runTypedLetReturnTree?_resume
example := @Solcore.Frontend.LocalInputs.runTypedLetReturnTree?_single
example := @Solcore.Frontend.LocalInputs.runTypedLetReturnTree?_some_of_terminalReturnTree
example := @Solcore.Frontend.LocalInputs.runTypedLetReturnTree?_some_of_typedLetReturnBody

example := @Solcore.Frontend.TypedLetReturnTreeEvaluates.change_store
example := @Solcore.Frontend.TypedLetReturnTreeEvaluatesWithCost.change_store
example := @Solcore.Frontend.typedLetReturnTreeEvaluates_store_iff
example := @Solcore.Frontend.typedLetReturnTreeEvaluatesWithCost_store_iff
example := @Solcore.Frontend.LocalInputs.runTypedLetReturnTree?_done_store_iff
example := @Solcore.Frontend.LocalInputs.runTypedLetReturnTree?_outOfFuel_store_iff

example := @Solcore.Frontend.TypedLetReturnTreeElaborates.mapOwner
example := @Solcore.Frontend.TypedLetReturnTreeHasType.mapOwner
example := @Solcore.Frontend.elaborateTypedLetReturnTree?_mapOwner
example := @Solcore.Frontend.LocalInputs.checkTypedLetReturnTree?_mapOwner
example := @Solcore.Frontend.LocalInputs.runTypedLetReturnTree?_mapOwner

example := @Solcore.Frontend.TypedLetReturnTreeElaborates.extend_types
example := @Solcore.Frontend.TypedLetReturnTreeHasType.extend_types
example := @Solcore.Frontend.elaborateTypedLetReturnTree?_some_of_extends
example := @Solcore.Frontend.elaborateTypedLetReturnTree?_eq_of_mutual_extends
example := @Solcore.Frontend.LocalInputs.checkTypedLetReturnTree?_some_of_extends
example := @Solcore.Frontend.LocalInputs.checkTypedLetReturnTree?_eq_of_mutual_extends
example := @Solcore.Frontend.LocalInputs.runTypedLetReturnTree?_some_of_extends
example := @Solcore.Frontend.LocalInputs.runTypedLetReturnTree?_eq_of_mutual_extends

example := @Solcore.Frontend.evaluateLocalWordBinaryWithCost?
example := @Solcore.Frontend.evaluateLocalExpressionWithCost?
example := @Solcore.Frontend.evaluateLocalExpressionWithCost?_sound
example := @Solcore.Frontend.evaluateLocalExpressionWithCost?_complete
example := @Solcore.Frontend.evaluateLocalExpressionWithCost?_iff
example := @Solcore.Frontend.localExpressionEvaluatesWithCost_iff_evaluate
example := @Solcore.Frontend.evaluateLocalExpressionWithCost?_eq_none_iff
example := @Solcore.Frontend.evaluateLocalExpressionWithCost?_exists_cost_iff
example := @Solcore.Frontend.evaluateLocalExpressionWithCost?_value_iff
example := @Solcore.Frontend.evaluateLocalExpressionWithCost?_checked_toStepsWithContinuation
example := @Solcore.Frontend.evaluateLocalExpressionWithCost?_checked_runStateful_done_iff
example := @Solcore.Frontend.evaluateLocalExpressionWithCost?_checked_runStateful_outOfFuel_iff
example := @Solcore.Frontend.elaborateLocalExpression?_run_done_iff_evaluator
example := @Solcore.Frontend.elaborateLocalExpression?_typed_evaluator_exists
example := @Solcore.Frontend.LocalInputs.run?_done_iff_evaluator
example := @Solcore.Frontend.LocalInputs.run?_outOfFuel_iff_evaluator
example := @Solcore.Frontend.LocalInputs.typed_evaluator_execution

example := @Solcore.Frontend.evaluateTypedLetReturnTreeWithCost?
example := @Solcore.Frontend.evaluateTypedLetReturnTreeWithCost?_sound
example := @Solcore.Frontend.evaluateTypedLetReturnTreeWithCost?_complete
example := @Solcore.Frontend.evaluateTypedLetReturnTreeWithCost?_iff
example := @Solcore.Frontend.typedLetReturnTreeEvaluatesWithCost_iff_evaluate
example := @Solcore.Frontend.evaluateTypedLetReturnTreeWithCost?_eq_none_iff
example := @Solcore.Frontend.evaluateTypedLetReturnTreeWithCost?_exists_cost_iff
example := @Solcore.Frontend.evaluateTypedLetReturnTreeWithCost?_value_iff
example := @Solcore.Frontend.evaluateTypedLetReturnTreeWithCost?_checked_toStepsWithContinuation
example := @Solcore.Frontend.evaluateTypedLetReturnTreeWithCost?_checked_runStateful_done_iff
example := @Solcore.Frontend.evaluateTypedLetReturnTreeWithCost?_checked_runStateful_outOfFuel_iff
example := @Solcore.Frontend.elaborateTypedLetReturnTree?_run_done_iff_evaluator
example := @Solcore.Frontend.elaborateTypedLetReturnTree?_typed_evaluator_exists
example := @Solcore.Frontend.LocalInputs.runTypedLetReturnTree?_done_iff_evaluator
example := @Solcore.Frontend.LocalInputs.runTypedLetReturnTree?_outOfFuel_iff_evaluator
example := @Solcore.Frontend.LocalInputs.typedLetReturnTree_evaluator_execution

example := @Solcore.Frontend.evaluateRuntimeFunctionWithCost?
example := @Solcore.Frontend.runtimeFunctionEvaluatesWithCost_iff_evaluate
example := @Solcore.Frontend.evaluateRuntimeFunctionWithCost?_eq_none_iff

example := @Solcore.Frontend.evaluateTypedLetReturnTreeWithCost?_mapOwner
example := @Solcore.Frontend.typedLetReturnTreeEvaluatesWithCost_mapOwner_iff
example := @Solcore.Frontend.typedLetReturnTreeEvaluates_mapOwner_iff

example := @Solcore.Frontend.evaluateLocalExpressionWithCost?_congr_lookup
example := @Solcore.Frontend.evaluateTypedLetReturnTreeWithCost?_congr_lookup
example := @Solcore.Frontend.typedLetReturnTreeEvaluatesWithCost_congr_lookup_iff
example := @Solcore.Frontend.typedLetReturnTreeEvaluates_congr_lookup_iff

end Tests
