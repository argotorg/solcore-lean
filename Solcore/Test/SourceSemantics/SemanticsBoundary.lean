import Solcore.SourceSemantics
import Solcore.SourceSemantics.SourceInferenceSoundness
import Solcore.SourceSemantics.StaticValidation

/-!
# Source semantics boundary tests

The public boundary of the source semantics, scoped requirements and static validation.
-/

section
-- leanmerge: from Solcore.Test.SourceSemanticsPublicBoundary
set_option autoImplicit false

namespace Tests

example := @Solcore.SourceSemantics.SchemeInstantiates.of_matchInstance?
example := @Solcore.SourceSemantics.SchemeInstantiatesAt.of_matchInstance?
example :=
  @Solcore.SourceSemantics.SchemeInstantiatesAt.of_instantiateWithSubstitution

example := @Solcore.SourceSemantics.Context
example := @Solcore.SourceSemantics.Context.ofSignatures
example := @Solcore.SourceSemantics.Context.withLocal
example := @Solcore.SourceSemantics.Context.withTypeVariables
example := @Solcore.SourceSemantics.Context.withResidualTypeVariables
example := @Solcore.SourceSemantics.Context.withAssumption
example := @Solcore.SourceSemantics.Context.LocalLookup
example := @Solcore.SourceSemantics.Context.LocalSchemeRequirementsLookup
example := @Solcore.SourceSemantics.Context.localSchemeRequirementsLookup_withLocal_self
example := @Solcore.SourceSemantics.Context.HasAssumption
example := @Solcore.SourceSemantics.SourceProjectionsHaveType.append
example := @Solcore.SourceSemantics.SourcePlaceHasType.snocIndex

example := @Solcore.SourceSemantics.ContainsNode
example := @Solcore.SourceSemantics.ContainsExpression
example := @Solcore.SourceSemantics.ContainsStatement
example := @Solcore.SourceSemantics.ContainsExpression.primaryRequirementOccursAt
example := @Solcore.SourceSemantics.ContainsStatement.primaryRequirementOccursAt
example :=
  @Solcore.SourceSemantics.ContainsStatement.matchCasePatternRequirementOccursAt
example := @Solcore.SourceSemantics.ContainsNode.of_nodes_prefix
example := @Solcore.SourceSemantics.ContainsExpression.of_nodes_prefix
example := @Solcore.SourceSemantics.ContainsStatement.of_nodes_prefix
example := @Solcore.SourceSemantics.NodeOccurrencesUnique
example := @Solcore.SourceSemantics.OccurrenceGraphWellFormed
example := @Solcore.SourceSemantics.RootsExist.contains_root
example := @Solcore.SourceSemantics.RootsExist.expression_root_exists
example := @Solcore.SourceSemantics.RootsExist.statement_root_exists
example := @Solcore.SourceSemantics.rootsOwned_of_nodesOwned_of_rootsExist
example :=
  @Solcore.SourceSemantics.OccurrenceGraphWellFormed.expression_root_exists
example :=
  @Solcore.SourceSemantics.OccurrenceGraphWellFormed.statement_root_exists
example := @Solcore.SourceSemantics.OccurrenceGraphClosed
example := @Solcore.SourceSemantics.OccurrenceGraphClosed.call_arguments_nodup
example := @Solcore.SourceSemantics.lookupExpression?_sound
example := @Solcore.SourceSemantics.lookupExpression?_complete

example := @Solcore.SourceSemantics.ExactSubstitution
example := @Solcore.SourceSemantics.SchemeInstantiates
example := @Solcore.SourceSemantics.SchemeInstantiatesAt
example := @Solcore.SourceSemantics.SchemeInstantiatesAt.type_admissible
example := @Solcore.SourceSemantics.SubstitutionRangeWellFormed
example := @Solcore.SourceSemantics.SubstitutionRangeAdmissible
example := @Solcore.SourceSemantics.SubstitutionRangeAdmissible.toWellFormed
example := @Solcore.SourceSemantics.ParameterSubstitution.Exact
example := @Solcore.SourceSemantics.ParameterSubstitution.exact_zip
example := @Solcore.SourceSemantics.ParameterSubstitution.orderedArguments_zip
example := @Solcore.SourceSemantics.ParameterSubstitution.RangeWellFormed
example := @Solcore.SourceSemantics.ParameterSubstitution.RangeAdmissible
example := @Solcore.SourceSemantics.ParameterSubstitution.RangeAdmissible.toWellFormed
example := @Solcore.SourceSemantics.DeclarationInstantiation.Valid
example := @Solcore.SourceSemantics.DeclarationInstantiation.Admissible
example := @Solcore.SourceSemantics.DeclarationInstantiation.Valid.toAdmissible
example := @Solcore.SourceSemantics.DeclarationInstantiation.Admissible.toValid
example := @Solcore.SourceSemantics.DataConstructorInstantiation.Valid
example := @Solcore.SourceSemantics.DataConstructorInstantiation.Admissible
example := @Solcore.SourceSemantics.DataConstructorInstantiation.Valid.toAdmissible
example := @Solcore.SourceSemantics.DataConstructorInstantiation.Admissible.toValid
example :=
  @Solcore.SourceSemantics.DataConstructorInstantiation.Admissible.result_type_admissible
example :=
  @Solcore.SourceSemantics.DataConstructorInstantiation.Admissible.payload_type_admissible

example := @Solcore.SourceSemantics.Forall₂
example := @Solcore.SourceSemantics.Forall₂.functional
example := @Solcore.SourceSemantics.implRuleVariables
example := @Solcore.SourceSemantics.implRuleParameters
example := @Solcore.SourceSemantics.ImplSubstitution
example := @Solcore.SourceSemantics.ImplSubstitution.ExactFor
example := @Solcore.SourceSemantics.ImplHeadInstantiates
example := @Solcore.SourceSemantics.TraitEvidence
example := @Solcore.SourceSemantics.EvidenceValid
example := @Solcore.SourceSemantics.Entails
example := @Solcore.SourceSemantics.EvidenceValid.evidence_goal_eq
example := @Solcore.SourceSemantics.PredicateEvidenceRepresents
example := @Solcore.SourceSemantics.ImplementationEvidenceRepresents.functional
example := @Solcore.SourceSemantics.PredicateEvidenceRepresents.functional
example := @Solcore.SourceSemantics.RetainedEvidenceValid
example := @Solcore.SourceSemantics.TraitResolutionSoundness.toImplSubstitution
example := @Solcore.SourceSemantics.TraitResolutionSoundness.toImplSubstitution_applyType
example := @Solcore.SourceSemantics.TraitResolutionSoundness.toImplSubstitution_applyPredicate
example := @Solcore.SourceSemantics.TraitResolutionSoundness.matchImplHead?_sound
example := @Solcore.SourceSemantics.TraitResolutionSoundness.resolutionEvidenceValid_sound
example := @Solcore.SourceSemantics.TraitResolutionSoundness.resolutionPremisesValid_sound
example := @Solcore.SourceSemantics.TraitResolutionSoundness.resolve_success_evidenceValid
example := @Solcore.SourceSemantics.TraitResolutionSoundness.resolve_success_entails
example := @Solcore.SourceSemantics.TraitResolutionSoundness.resolve_success_retainedEvidenceValid
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferenceTypeFormationValidated_typeAdmissible_afterSubstitution
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.bindLambdaParameters_success_typesAdmissible_afterSubstitution
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.closedBinderLocals
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.closedBinderRequirements
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.LocalEnvironmentAligned
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.LocalEnvironmentAligned.ofMonoBindersExtend
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.LocalEnvironmentAligned.ofInitialMonoBindersExtend
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.LocalEnvironmentAligned.withLocals
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.LocalEnvironmentAligned.allocateBinder
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.LocalEnvironmentAligned.allocateBinder_of_localBindersBelowNextLocal
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.LocalEnvironmentAligned.binderExtends_of_allocateBinder
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.LocalEnvironmentAligned.monomorphicBinderExtends_of_allocateBinder
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.LocalEnvironmentAligned.lookup_of_lookupBinder?
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.LocalEnvironmentAligned.localSchemes_perm
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.LocalEnvironmentAligned.localFresh_of_not_mem_localBinders
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.LocalEnvironmentAligned.mem_local_freeVariables_iff
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.LocalEnvironmentAligned.congr_localBinders
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.LocalEnvironmentAligned.restoreLexicalScope
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.LocalEnvironmentAligned.restoreLexicalScope_recordNode
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.ActiveLocalFormation
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.ActiveLocalFormation.facts_of_lookupBinder?
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.ActiveLocalFormation.congr_localBinders
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.ActiveLocalFormation.withLocals
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.ActiveLocalFormation.restoreLexicalScope
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.ActiveLocalFormation.restoreLexicalScope_recordNode
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.ActiveLocalFormation.withLocal
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.ActiveLocalFormation.ofMonoBindersExtend
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.ActiveLocalFormation.allocateBinder
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.ActiveBinderCaptureOrigins
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.ActiveBinderCaptureOrigins.of_monomorphic
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.ActiveBinderCaptureOrigins.congr_localBinders
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.ActiveBinderCaptureOrigins.monoWholeSource
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.ActiveBinderCaptureOrigins.weakenWholeSource
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.ActiveBinderCaptureOrigins.origin_of_lookupBinder?
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.ActiveBinderCaptureOrigins.noCapture_of_lookupBinder?
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.ActiveBinderCaptureOrigins.inferExprFuel
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.ActiveBinderCaptureOrigins.inferExprsFuel
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.ActiveBinderCaptureOrigins.restoreLexicalScope
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.ActiveBinderCaptureOrigins.allocateBinder
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.ActiveLocalContextInvariant
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.ActiveLocalContextInvariant.congr_localBinders
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.ActiveLocalContextInvariant.inferExprFuel
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.ActiveLocalContextInvariant.inferExprsFuel
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.ActiveLocalContextInvariant.inferPlaceFuel
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.ActiveLocalContextInvariant.inferAssignedValueFuel
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.ActiveLocalContextInvariant.writableLocal_of_lookupBinder?
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.ActiveLocalContextInvariant.withLocals
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.ActiveLocalContextInvariant.allocateStatementId
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.ActiveLocalContextInvariant.allocateHiddenLocal
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.ActiveLocalContextInvariant.recordNode
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.ActiveLocalContextInvariant.unify
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.ActiveLocalContextInvariant.restoreLexicalScope
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.ActiveLocalContextInvariant.restoreLexicalScope_recordNode
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.ActiveLocalContextInvariant.allocateBinder_of_localBindersBelowNextLocal
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.bindLambdaParameters_success_monoBindersExtend_afterSubstitution
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferPlaceFuel_success_identifier_facts
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferPlaceFuel_success_identifier_sound
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferPlaceFuel_success_sound
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferAssignedValueFuel_success_sound
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.localReferenceEnvironmentFacts_of_lookupBinder?
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.checkFunctionBody_success_initialLocalEnvironmentFacts
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.checkFunctionBody_success_initialActiveLocalContextInvariant
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.localBinderInstantiationNoCapture_predicateRangeAvoids
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.canonicalLocalSchemeInstantiationValid_afterSubstitution
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.canonicalLocalReferenceUseValid_afterSubstitution
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.referenceUseValid_requirementIdsValid
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.localReferenceExpressionHasType_of_referenceUseValid
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.canonicalLocalReferenceExpressionHasType_afterSubstitution
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.generalizeValue_closed_facts
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.generalizeValue_schemeGeneralizesExcept_of_barrier
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.generalizeValue_binderFormation_afterSubstitution
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.toTypedSource_containsExpression_of_mem
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.toTypedSource_containsStatement_of_mem
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.modifyExpressionNode_containsExpression_self
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.modifyExpressionNode_containsExpression_other
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.attachExpressionCoercions_containsExpression_of_not_mem
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.attachExpressionCoercions_containsExpression
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.recordNode_containsExpression
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.recordNode_containsStatement
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.recordExpression_containsExpression
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.recordExpressionWithExpected_success_containsExpression
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferExprFuel_success_expected_type_afterProgress
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferExprFuel_success_group_facts
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.groupBranchExpressionHasType_afterSubstitution
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.StatementResultMatchesFactsAfterSubstitution.letDecl
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferStatementFuel_success_letAnnotatedUninitialized_facts
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.resolvedAnnotationBinderFacts_afterSubstitution
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.letAnnotatedUninitializedStatementHasType_afterSubstitution
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.letInitializedMonomorphicStatementHasType_afterSubstitution
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.letInitializedGeneralizedStatementHasType_afterSubstitution
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.letAnnotatedInitializedStatementHasType_afterSubstitution
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.resolvedAnnotationBinderPreservesActiveLocalContextInvariant_afterSubstitution
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferStatementFuel_success_letAnnotatedUninitialized_sound
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferStatementFuel_success_letUnannotatedInitialized_facts
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.UnannotatedInitializedLetCertificate
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferStatementFuel_success_letUnannotatedInitialized_sound
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferStatementFuel_success_letAnnotatedInitialized_facts
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferStatementFuel_success_letAnnotatedInitialized_sound
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferStatementFuel_success_expression_facts
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferStatementFuel_success_assignValue_facts
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferStatementFuel_success_assignBitNot_facts
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferStatementFuel_success_ifWithoutElse_facts
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferStatementFuel_success_ifWithElse_facts
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.expressionStatementDiscardHasType_afterSubstitution
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.expressionStatementValueHasType_afterSubstitution
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.assignValueStatementHasType_afterSubstitution
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.assignBitNotStatementHasType_afterSubstitution
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferStatementFuel_success_expression_sound
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferStatementFuel_success_returnUnit_facts
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferStatementFuel_success_returnValue_facts
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferStatementFuel_success_break_facts
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferStatementFuel_success_continue_facts
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferStatementFuel_success_block_facts
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferMatchScrutineesFuel
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferExprFuel_success_typingSourceExtends
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferConstructorArgumentsFuel_success_typingSourceExtends
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferConstructorArgumentsFuel_success_expressionsHaveTypes_local
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferExprsFuel_success_expressionsHaveTypes
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferMatchScrutineesFuel_success_expressionHasType_in
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferMatchScrutineesFuel_inferenceProperties
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.ActiveLocalContextInvariant.inferMatchScrutineesFuel
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.ActiveLocalContextInvariant.inferMatchCasesFuel
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferStatementFuel_success_matchWithoutDefault_facts
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferStatementFuel_success_matchWithDefault_facts
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferStatementFuel_success_forLoop_facts
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferStatementFuel_success_whileLoop_facts
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.returnUnitStatementHasType_afterSubstitution
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.returnValueStatementHasType_afterSubstitution
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.breakStatementHasType_afterSubstitution
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.continueStatementHasType_afterSubstitution
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.ifWithoutElseStatementHasType_afterSubstitution
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.ifWithElseStatementHasType_afterSubstitution
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.blockStatementHasType_afterSubstitution
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.matchWithoutDefaultStatementHasType_afterSubstitution
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.mergeBodyControls_withDefault_eq_some
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.matchCasesHaveType_facts_ne_nil_of_cases_ne_nil
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.mergeBodyControls_withoutDefault_eq_some_of_ne_nil
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.matchWithDefaultStatementHasType_afterSubstitution
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.forLoopStatementHasType_afterSubstitution
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.whileLoopStatementHasType_afterSubstitution
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.StatementResultMatchesFactsAfterSubstitution
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.BlockResultMatchesFactsAfterSubstitution
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.StatementResultMatchesFactsAfterSubstitution.ordinaryUnit
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.StatementResultMatchesFactsAfterSubstitution.returned
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.StatementResultMatchesFactsAfterSubstitution.breakStmt
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.StatementResultMatchesFactsAfterSubstitution.continueStmt
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.StatementResultMatchesFactsAfterSubstitution.ifWithoutElse
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.StatementResultMatchesFactsAfterSubstitution.ifWithElse
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.StatementResultMatchesFactsAfterSubstitution.matchWithoutDefault
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.StatementResultMatchesFactsAfterSubstitution.matchWithDefault
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.StatementResultMatchesFactsAfterSubstitution.block
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.StatementResultMatchesFactsAfterSubstitution.forLoop
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.StatementResultMatchesFactsAfterSubstitution.whileLoop
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferStatementFuel_success_assignValue_sound
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferStatementFuel_success_assignValue_deep_sound
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferStatementFuel_success_assignBitNot_sound
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferStatementFuel_success_assignBitNot_deep_sound
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferStatementFuel_success_returnUnit_sound
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferStatementFuel_success_returnValue_sound
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferStatementFuel_success_break_sound
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferStatementFuel_success_continue_sound
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferStatementFuel_success_block_sound
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferStatementFuel_success_ifWithoutElse_sound
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferStatementFuel_success_ifWithElse_sound
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferStatementFuel_success_matchWithoutDefault_sound
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.consumeIrrefutableInstruction_true_sound
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.consumeIrrefutableInstructions_true_sound
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.constructorArgumentsIrrefutable_sound
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.typedPatternIsCatchall_true_sound
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.matchExhaustiveWithoutDefault_of_nominal
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.matchExhaustiveWithoutDefault_of_guard
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferStatementFuel_success_matchWithoutDefault_deep_sound
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferStatementFuel_success_matchWithoutDefault_deep_sound_at
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferStatementFuel_success_matchWithDefault_sound
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferStatementFuel_success_matchWithDefault_deep_sound
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferStatementFuel_success_matchWithDefault_deep_sound_at
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.ForItemInferenceSoundnessCallbacks
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.ForItemInferenceSoundnessCallbacks.weakenSource
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferForItemFuel_success_forItemHasType_of_callbacks
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferForItemsFuel_success_forItemsHaveType_of_callbacks
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferStatementFuel_success_forLoop_sound
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferStatementFuel_success_whileLoop_sound
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.StatementInferenceSoundnessCallbacks
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferStatementFuel_success_sound_of_callbacks
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferStatementFuel_success_sound_of_callbacks_at
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferStatementsFuel_success_nil_facts
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferStatementsFuel_success_singleton_facts
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferStatementsFuel_success_cons_facts
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferStatementsFuel_success_statements_eq_cons
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.BlockResultMatchesFactsAfterSubstitution.empty
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.BlockResultMatchesFactsAfterSubstitution.singleton
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.BlockResultMatchesFactsAfterSubstitution.cons
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.IntegerPatternEvidenceAt
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.IntegerPatternEvidenceAt.restrictSource
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.IntegerPatternEvidenceAt.integerLiteralValid_of_flat
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.MatchPatternFlatInferenceCertificate
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.MatchPatternsFlatInferenceCertificate
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.MatchPatternInferenceCertificate
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.MatchPatternFlatStateCallbacks
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.matchPatternFlatStateCallbacks
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.MatchPatternBranchSoundnessCallbacks
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferMatchPatternsFlatFuel_success_sound
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferMatchPatternFlatFuel_success_sound
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferMatchPatternFlatFuel_success_literal_sound_at
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferMatchPatternFlatFuel_success_sound_at
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferMatchPatternsFlatFuel_success_sound_at
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferMatchPatternFuel_success_sound_of_flat
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferMatchPatternFuel_success_sound
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferMatchPatternFuel_success_sound_at
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.MatchCaseInferenceCertificate
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferMatchCaseFuel_success_sound
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferMatchCaseFuel_success_sound_at
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.MatchCaseInferenceCertificate.toMatchCaseHasType
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferMatchCasesFuel_success_matchCasesHaveType
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferMatchCasesFuel_success_sound
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferMatchCasesFuel_success_sound_at
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferMatchScrutineesFuel_preserves_localBindersBelowNextLocal
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferStatementFuel_success_typingSourceExtends
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferStatementsFuel_success_typingSourceExtends
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferStatementsFuel_success_statementsHaveType
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferStatementsFuel_success_statementsHaveType_from_local
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferStatementsFuel_success_statementsHaveType_under_ambient
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferExprFuel_success_localIdentifier_containsExpression
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferExprFuel_success_localIdentifier_facts
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferExprFuel_success_builtinBoolean_containsExpression
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.builtinBooleanExpressionHasType_afterSubstitution
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.validateSourceGraph_success_occurrenceGraphWellFormed
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.validateSourceLocalIdentities_success_localIdentityOwnership
example :=
  @Solcore.SourceSemantics.OccurrenceGraphClosed.of_wellFormed_incomingUnique_reachable
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.sourceReachableNodeIds_sound
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.sourceSubtreeNodeIds_sound
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.validateSourceTemplateScopes_success_rowScoped
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.validateSourceGraph_success_allNodesReachable
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.validateSourceGraph_success_occurrenceGraphClosed
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.finalize_occurrenceGraphWellFormed
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.finalize_occurrenceGraphClosed
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.checkFunctionBody_success_occurrenceGraphClosed
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.finalize_localIdentityOwnership
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.checkFunctionBody_success_localIdentityOwnership
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.finalize_requirementOwnership
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.checkFunctionBody_success_requirementOwnership
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.finalize_expression_root_exists
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.finalize_statement_root_exists
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.finalize_containsExpression_of_mem
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.finalize_containsStatement_of_mem
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.binaryOperatorDispatch_traitMethod
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.unaryOperatorDispatch_traitMethod
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.UnaryOperatorInferenceCase
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.BinaryOperatorInferenceCase
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.binaryBuiltin_hasType
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.binaryInteger_hasType
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.addRequirementsWithIds_resolve
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.addRequirementsWithIds_correspond
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferUnaryOperator_success_case
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferBinaryOperator_success_case
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.operatorTraitPredicates_instantiates
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.operatorTraitPredicates_instantiatesAfterSubstitution
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.unaryOperatorTrait_hasTypeAfterSubstitution
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.unaryOperatorInferenceCase_hasType_afterFinalization_scoped
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.binaryOperatorTrait_hasTypeAfterSubstitution
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.binaryOperatorInferenceCase_hasType_afterFinalization_scoped
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.freshDataConstructorInstantiation_admissible
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.tryFunctionCandidate_instantiationAdmissible
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.tryFunctionCandidate_declarationApplicationValid
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.selectFunctionCandidateFrom_success_semanticCandidate
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.selectFunctionCandidateFrom_declarationApplicationValid
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.selectFunctionCandidate_declarationApplicationValid
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.coercionMethodProfile?_some_instantiates
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.plannedCoercionStep_profileInstantiatesAfterSubstitution
example := @Solcore.SourceSemantics.SourceInferenceSoundness.solveNormalizedPredicate_sound
example := @Solcore.SourceSemantics.SourceInferenceSoundness.solvePredicate_sound
example := @Solcore.SourceSemantics.SourceInferenceSoundness.solveRequirementEvidence_ordinary_sound
example := @Solcore.SourceSemantics.SourceInferenceSoundness.solveRequirementEvidence_template_eq
example := @Solcore.SourceSemantics.SourceInferenceSoundness.solveRequirements_corresponds
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.solveRequirements_requirementIdsValid
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.solveRequirements_requirementIdsValid_of_subset
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.solveRequirements_correspondingSequenceProves
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.solveRequirements_correspondingSequenceProvesAt
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.localReferenceRequirementSequenceProves_afterProgress
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.localIdentifierBranchExpressionHasType_afterProgress
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.integerLiteralValid_of_evidence
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.integerLiteralValid_of_solved
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.solveRequirements_committedCoercionStepSequenceProves
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.committedCoercionStepValid
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.committedCoercionStepValidAt
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.committedCoercionPlanValid
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.coercionPlan?_some_committedPathValid
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.coercionPlan?_some_committedPathValid_at
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.coercionPlan?_some_committedPathValid_at_scoped
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.withExpected_success_coercionPathValid_afterFinalization
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.withExpected_success_coercionPathValid_afterFinalization_scoped
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.ArgumentCoercionsValid
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.ArgumentCoercionsValid.nil
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.ArgumentCoercionsValid.cons
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.ArgumentCoercionsValid.expression_ids
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.ExpressionTypingBase
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.ExpressionTypingBase.intro
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.ExpressionTypingBase.weakenNodeSource
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.ExpressionTypingBase.ofRecordIndirectCall
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferExprsFuel_inferExprFuel_applyFunctionType_recordIndirectCall_success_expressionTypingBase_scoped
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.ArgumentTypingBasesValid
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.ArgumentTypingBasesValid.nil
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.ArgumentTypingBasesValid.cons
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.ArgumentTypingBasesValid.containsExpression_of_mem
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.ArgumentTypingBasesValid.weakenNodeSource
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.ArgumentTypingBasesValid.attachExpressionCoercions_primaryRequirementOccursAt
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferExprsFuel_success_argumentTypingBasesValid
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.ExpressionNodesPreservedAt
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.ExpressionNodesPreservedAt.ofTypingSourceExtends
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.ExpressionNodesPreservedAt.ofAttachExpressionCoercions_of_disjoint
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.ExpressionRequirementsRetainedAt
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.ExpressionRequirementsRetainedAt.ofTypingSourceExtends
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.ExpressionRequirementsRetainedAt.monoBefore
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.ExpressionRequirementsRetainedAt.ofAttachExpressionCoercions
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.argumentRequirementsRetainedAt_attachExpressionCoercions
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.ExpressionTypingBase.expressionHasType
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.argumentFitTrace_argumentCoercionsValid_afterFinalization_scoped
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.tryFunctionCandidate_some_argumentCoercionsValid_afterFinalization_scoped
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.tryFunctionCandidate_some_directCallRequirementsValid_afterFinalization_scoped
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.argumentTypingBasesValid_attachExpressionCoercions_expressionsHaveTypes
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.recordBuiltinFunctionCall_success_expressionTypingBase
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.recordSelectedCallResult_success_containsExpression
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.recordSelectedCallResult_success_argumentDirectChild
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.recordSelectedCallResult_success_primaryRequirementOccursAt
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.recordSelectedCallResult_success_attachedTypingSourceExtends
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.recordSelectedCallResult_success_directDeclarationCalleeValid
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.recordSelectedCallResult_success_expressionTypingBase
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.recordSelectedCallResult_success_expressionHasType
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.tryFunctionCandidate_some_recordSelectedCallResult_success_expressionTypingBase_scoped
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.tryFunctionCandidate_some_recordSelectedCallResult_success_expressionTypingBase_scoped_of_retained
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.selectFunctionCandidateFrom_recordSelectedCall_success_expressionTypingBase_scoped_of_retained
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.tryFunctionCandidate_some_recordSelectedCallResult_success_expressionHasType_scoped
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferExprsFuel_selectFunctionCandidateFrom_recordSelectedCall_success_expressionTypingBase_scoped
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferExprsFuel_selectFunctionCandidateFrom_recordSelectedCall_success_expressionHasType_scoped
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.recordExpressionWithExpected_success_ordinaryExpressionTypingBase_scoped_of_retained
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferExprFuel_success_localIdentifier_expressionTypingBase_scoped_of_retained
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferExprFuel_success_builtinBooleanIdentifier_expressionTypingBase_scoped_of_retained
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferExprFuel_success_proxy_expressionTypingBase_scoped_of_retained
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferExprFuel_success_group_expressionTypingBase_scoped_of_retained
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferExprFuel_success_tuple_expressionTypingBase_scoped_of_retained
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferExprFuel_success_conditional_expressionTypingBase_scoped_of_retained
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferExprFuel_success_index_expressionTypingBase_scoped_of_retained
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferUnaryOperator_recordExpressionWithExpected_success_expressionTypingBase_scoped_of_retained
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferBinaryOperator_recordExpressionWithExpected_success_expressionTypingBase_scoped_of_retained
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.recordExpressionWithExpected_success_ordinaryExpressionTypingBase_scoped
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.recordExpressionWithExpected_success_ordinaryExpressionHasType_scoped
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferExprFuel_success_declarationIdentifier_expressionTypingBase_scoped
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferExprFuel_success_builtinFunctionIdentifier_expressionTypingBase_scoped
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferConstructorApplicationFuel_success_expressionTypingBase_scoped
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.inferConstructorApplicationFuel_success_expressionHasType_scoped
example := @Solcore.SourceSemantics.SourceInferenceSoundness.solveRequirements_template_evidence
example := @Solcore.SourceSemantics.SourceInferenceSoundness.solveRequirements_ordinary_sound
example := @Solcore.SourceSemantics.SourceInferenceSoundness.solveRequirements_scoped_entries_sound
example := @Solcore.SourceSemantics.SourceInferenceSoundness.solveRequirements_scoped_ledger_sound
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.solveRequirements_scoped_ledger_sound_of_nodup
example := @Solcore.SourceSemantics.SourceInferenceSoundness.nodeLocalSchemeTemplateIds
example := @Solcore.SourceSemantics.SourceInferenceSoundness.recordNode_sourceLocalSchemeTemplateIds
example := @Solcore.SourceSemantics.SourceInferenceSoundness.TemplateTracking
example := @Solcore.SourceSemantics.SourceInferenceSoundness.TemplateTracking.initial
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.TemplateTracking.ofValidation
example := @Solcore.SourceSemantics.SourceInferenceSoundness.TemplateTracking.replaceLocals
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.TemplateTracking.addRequirementsWithIds
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.TemplateTracking.lookupBinderRequirementAllocationCertificate
example := @Solcore.SourceSemantics.SourceInferenceSoundness.TemplateTracking.allocateBinder
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.TemplateTracking.allocateGeneralizedValue
example := @Solcore.SourceSemantics.SourceInferenceSoundness.TemplateTracking.recordNode
example := @Solcore.SourceSemantics.SourceInferenceSoundness.TemplateTracking.restoreLexicalScope
example := @Solcore.SourceSemantics.SourceInferenceSoundness.TemplateTracking.ownership
example := @Solcore.SourceSemantics.SourceInferenceSoundness.TemplateTracking.classified_iff
example := @Solcore.SourceSemantics.SourceInferenceSoundness.TemplateTracking.source_ids_subset_requirements
example := @Solcore.SourceSemantics.SourceInferenceSoundness.finalize_templateTracking
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.finalize_localSchemeTemplateOwnership
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.checkFunctionBody_success_localSchemeTemplateOwnership
example := @Solcore.SourceSemantics.SourceInferenceSoundness.TemplateIdsAligned
example := @Solcore.SourceSemantics.SourceInferenceSoundness.finalize_templateIdsAligned
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.finalize_templateIdsAligned_validated
example := @Solcore.SourceSemantics.SourceInferenceSoundness.finalize_template_evidence
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.finalize_template_evidence_validated
example := @Solcore.SourceSemantics.SourceInferenceSoundness.finalizedRequirementContext
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.checkedFinalizedRequirementContext
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.finalize_scopedRequirementLedgerWellFormed
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.finalize_contextSubstitutionValid
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.FinalInferenceResources
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.FinalInferenceResources.ofFinalize
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.FinalInferenceResources.noCapture_of_lookupBinder?
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.FinalInferenceResources.integerLiteralTargetSupported_of_subset
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.FinalInferenceResources.expressionTypeFormationValidated
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.FinalInferenceResources.expressionTypeAdmissible_afterSubstitution
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.FinalInferenceResources.expressionHasType_of_typingBase
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.FinalInferenceResources.expressionsHaveTypes_of_argumentTypingBases
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.FinalInferenceResources.inferExprsFuel_recordBuiltinFunctionCall_success_expressionTypingBase
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.FinalInferenceResources.requirementProvesAt
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.FinalInferenceResources.integerLiteralValidAt
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.FinalInferenceResources.inferExprFuel_success_numericLiteral_expressionTypingBase
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.FinalInferenceResources.integerPatternValidAt
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.FinalInferenceResources.integerPatternEvidenceAt
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.FinalInferenceResources.integerPatternValidAt_of_flatLiteral
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.checkFunctionBody_success_scopedRequirementLedgerWellFormed
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.checkFunctionBody_success_scopedRequirementLedgerWellFormed_bodyContext
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.finalize_integerLiteralValid_of_mem
example := @Solcore.SourceSemantics.SourceInferenceSoundness.finalize_solvedRequirementsValid
example :=
  @Solcore.SourceSemantics.SourceInferenceSoundness.finalize_integerLiteralValid_of_mem_ordinary

example := @Solcore.SourceSemantics.ReferenceHasRawType
example := @Solcore.SourceSemantics.ReferenceHasRawType.local_iff
example := @Solcore.SourceSemantics.ReferenceExpressionHasRawType
example := @Solcore.SourceSemantics.SolvedRequirementValid
example := @Solcore.SourceSemantics.SolvedRequirementsValid

example := @Solcore.SourceSemantics.StructuralSubstitution.applyTypedSource
example := @Solcore.SourceSemantics.StructuralSubstitution.applySolvedRequirement
example := @Solcore.SourceSemantics.StructuralSubstitution.applyTypedSource_frontend_eq
example := @Solcore.SourceSemantics.StructuralSubstitution.ContextSubstitutionValid
example :=
  @Solcore.SourceSemantics.StructuralSubstitution.TypeWellScoped.applyParametersTo
example :=
  @Solcore.SourceSemantics.StructuralSubstitution.TypesWellScoped.applyParametersTo
example :=
  @Solcore.SourceSemantics.StructuralSubstitution.TypeWellScoped.applyParametersAdmissibleTo
example :=
  @Solcore.SourceSemantics.StructuralSubstitution.TypeWellFormed.applyParametersTo
example :=
  @Solcore.SourceSemantics.StructuralSubstitution.TypesWellFormed.applyParametersTo
example :=
  @Solcore.SourceSemantics.StructuralSubstitution.TypesWellFormed.transportContext
example :=
  @Solcore.SourceSemantics.StructuralSubstitution.TypeAdmissible.transportContext
example :=
  @Solcore.SourceSemantics.StructuralSubstitution.SchemeWellFormed.ofLocalSchemeInitializerAdmissible
example :=
  @Solcore.SourceSemantics.StructuralSubstitution.LocalSchemeRequirementWellFormed.transportContext
example :=
  @Solcore.SourceSemantics.StructuralSubstitution.LocalSchemeRequirementsWellFormed.transportContext
example :=
  @Solcore.SourceSemantics.StructuralSubstitution.LocalSchemeRequirementWellFormed.afterBinderExtends
example :=
  @Solcore.SourceSemantics.StructuralSubstitution.LocalSchemeRequirementsWellFormed.afterBinderExtends
example :=
  @Solcore.SourceSemantics.FlexibleSubstitution.ScopedRequirementLedgerWellFormed.localSchemeRequirementsWellFormed_afterSubstitution
example :=
  @Solcore.SourceSemantics.StructuralSubstitution.PredicateWellFormed.applyParametersTo
example :=
  @Solcore.SourceSemantics.StructuralSubstitution.PredicatesWellFormed.applyParametersTo
example :=
  @Solcore.SourceSemantics.StructuralSubstitution.ParameterSubstitution.RangeWellFormed.transportContext
example := @Solcore.SourceSemantics.StructuralSubstitution.OccurrenceGraphClosed.applyParameters
example := @Solcore.SourceSemantics.StructuralSubstitution.ImplHeadInstantiates.applyParameters
example := @Solcore.SourceSemantics.StructuralSubstitution.EvidenceValid.applyParameters
example := @Solcore.SourceSemantics.StructuralSubstitution.RetainedEvidenceValid.applyParameters
example := @Solcore.SourceSemantics.StructuralSubstitution.RequirementLedgerWellFormed.applyParameters
example := @Solcore.SourceSemantics.StructuralSubstitution.RuntimeRequirementLedgerValid.applyParameters
example := @Solcore.SourceSemantics.StructuralSubstitution.ScopedRequirementLedgerWellFormed.applyParameters
example := @Solcore.SourceSemantics.StructuralSubstitution.ContextSubstitutionValid.ofRequirementLedger
example := @Solcore.SourceSemantics.StructuralSubstitution.ContextSubstitutionValid.ofRuntimeRequirementLedger
example := @Solcore.SourceSemantics.StructuralSubstitution.ContextSubstitutionValid.ofScopedRequirementLedger
example := @Solcore.SourceSemantics.StructuralSubstitution.SchemeGeneralizes.applyParameters
example := @Solcore.SourceSemantics.StructuralSubstitution.SchemeGeneralizesExcept.applyParameters
example := @Solcore.SourceSemantics.StructuralSubstitution.LocalSchemeRequirementWellFormed.applyParameters
example := @Solcore.SourceSemantics.StructuralSubstitution.LocalSchemeRequirementsWellFormed.applyParameters
example := @Solcore.SourceSemantics.StructuralSubstitution.LocalSchemeRequirementsLookup.applyParameters
example := @Solcore.SourceSemantics.StructuralSubstitution.LocalSchemeInstantiationValid.applyParameters
example := @Solcore.SourceSemantics.StructuralSubstitution.ReferenceUseValid.applyParameters
example := @Solcore.SourceSemantics.StructuralSubstitution.applyContext_withResidualTypeVariables
example := @Solcore.SourceSemantics.StructuralSubstitution.StatementsHaveType.applyParameters
example := @Solcore.SourceSemantics.StructuralSubstitution.BodyHasType.applyParameters
example := @Solcore.SourceSemantics.StructuralSubstitution.BodyDefinitionHasType.instantiate
example := @Solcore.SourceSemantics.StructuralSubstitution.LocalIdentityOwnership.applyParameters
example := @Solcore.SourceSemantics.StructuralSubstitution.RequirementOwnership.applyParameters
example := @Solcore.SourceSemantics.FlexibleSubstitution.applyEvidence
example := @Solcore.SourceSemantics.FlexibleSubstitution.applyPredicateEvidence
example := @Solcore.SourceSemantics.FlexibleSubstitution.applySolvedRequirement
example := @Solcore.SourceSemantics.FlexibleSubstitution.applyLocals
example := @Solcore.SourceSemantics.FlexibleSubstitution.forLocal
example := @Solcore.SourceSemantics.FlexibleSubstitution.applyLocalSchemeRequirements
example := @Solcore.SourceSemantics.FlexibleSubstitution.applyContext
example := @Solcore.SourceSemantics.FlexibleSubstitution.closeContext
example := @Solcore.SourceSemantics.FlexibleSubstitution.ContextCloses
example := @Solcore.SourceSemantics.FlexibleSubstitution.applyControlSummary
example := @Solcore.SourceSemantics.FlexibleSubstitution.applyControlContext
example := @Solcore.SourceSemantics.FlexibleSubstitution.applyStatementFacts
example := @Solcore.SourceSemantics.FlexibleSubstitution.applyBodyFacts
example := @Solcore.SourceSemantics.FlexibleSubstitution.applyExpressionRequirementPlan
example := @Solcore.SourceSemantics.FlexibleSubstitution.apply_function
example := @Solcore.SourceSemantics.FlexibleSubstitution.apply_product
example := @Solcore.SourceSemantics.FlexibleSubstitution.apply_mapping
example := @Solcore.SourceSemantics.FlexibleSubstitution.apply_proxy
example := @Solcore.SourceSemantics.FlexibleSubstitution.apply_comptime
example := @Solcore.SourceSemantics.FlexibleSubstitution.apply_productMany
example := @Solcore.SourceSemantics.FlexibleSubstitution.coercionRequirementIds_applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.LocalSchemesFreshFor
example := @Solcore.SourceSemantics.FlexibleSubstitution.ContextSubstitutionValid
example := @Solcore.SourceSemantics.FlexibleSubstitution.LocalSchemesFreshFor.target
example := @Solcore.SourceSemantics.FlexibleSubstitution.LocalSchemesFreshFor.ofBinderWellFormed
example := @Solcore.SourceSemantics.FlexibleSubstitution.LocalSchemesFreshFor.afterBinder
example := @Solcore.SourceSemantics.FlexibleSubstitution.LocalSchemesFreshFor.afterBinders
example := @Solcore.SourceSemantics.FlexibleSubstitution.LocalSchemesFreshFor.afterMonoBinders
example := @Solcore.SourceSemantics.FlexibleSubstitution.applyContext_typeVariables
example := @Solcore.SourceSemantics.FlexibleSubstitution.applyContext_withLocal
example := @Solcore.SourceSemantics.FlexibleSubstitution.applyContext_withAssumptions
example := @Solcore.SourceSemantics.FlexibleSubstitution.applyContext_withSolvedRequirements
example := @Solcore.SourceSemantics.FlexibleSubstitution.applyContext_withResidualTypeVariables
example := @Solcore.SourceSemantics.FlexibleSubstitution.applyContext_withTypeVariables
example := @Solcore.SourceSemantics.FlexibleSubstitution.applyContext_withTypeVariables_append
example := @Solcore.SourceSemantics.FlexibleSubstitution.ContextCloses.close
example := @Solcore.SourceSemantics.FlexibleSubstitution.ContextCloses.withLocal
example := @Solcore.SourceSemantics.FlexibleSubstitution.ContextCloses.withAssumptions
example := @Solcore.SourceSemantics.FlexibleSubstitution.ContextCloses.withSolvedRequirements
example := @Solcore.SourceSemantics.FlexibleSubstitution.ContextCloses.withResidualTypeVariables
example := @Solcore.SourceSemantics.FlexibleSubstitution.ContextCloses.withTypeVariables
example := @Solcore.SourceSemantics.FlexibleSubstitution.ContextCloses.afterBinder
example := @Solcore.SourceSemantics.FlexibleSubstitution.ContextCloses.afterBinders
example := @Solcore.SourceSemantics.FlexibleSubstitution.ContextCloses.afterMonoBinders
example := @Solcore.SourceSemantics.FlexibleSubstitution.Substitution.mem_freeVariables_apply_of_not_mem_domain
example := @Solcore.SourceSemantics.FlexibleSubstitution.Ty.apply_eq_self_of_domain_disjoint_freeVariables
example := @Solcore.SourceSemantics.FlexibleSubstitution.Substitution.mem_freeVariables_apply_iff
example := @Solcore.SourceSemantics.FlexibleSubstitution.Substitution.freeVariables_apply
example := @Solcore.SourceSemantics.FlexibleSubstitution.Substitution.mem_predicateVariables_applySubstitution_of_not_mem_domain
example := @Solcore.SourceSemantics.FlexibleSubstitution.Substitution.lookup?_without_of_not_mem
example := @Solcore.SourceSemantics.FlexibleSubstitution.Substitution.without_eq_self_of_disjoint_domain
example := @Solcore.SourceSemantics.FlexibleSubstitution.Substitution.mem_domain_without_iff
example := @Solcore.SourceSemantics.FlexibleSubstitution.Substitution.domain_without_nodup
example := @Solcore.SourceSemantics.FlexibleSubstitution.Substitution.mapRange
example := @Solcore.SourceSemantics.FlexibleSubstitution.Substitution.ExactSubstitution.mapRange
example := @Solcore.SourceSemantics.FlexibleSubstitution.ParameterSubstitution.mapRange
example := @Solcore.SourceSemantics.FlexibleSubstitution.ParameterSubstitution.Exact.mapRange
example := @Solcore.SourceSemantics.FlexibleSubstitution.ParameterSubstitution.RangeWellFormed.applyFlexible
example := @Solcore.SourceSemantics.FlexibleSubstitution.ParameterSubstitution.RangeAdmissible.applyFlexible
example := @Solcore.SourceSemantics.FlexibleSubstitution.ParameterSubstitution.orderedArguments_mapRange
example := @Solcore.SourceSemantics.FlexibleSubstitution.SubstitutionRangeWellFormed.without
example := @Solcore.SourceSemantics.FlexibleSubstitution.Scheme.apply_without_quantified
example := @Solcore.SourceSemantics.FlexibleSubstitution.Scheme.apply_eq_self_of_domain_disjoint_freeVariables
example := @Solcore.SourceSemantics.FlexibleSubstitution.applyTypedBinder_id
example := @Solcore.SourceSemantics.FlexibleSubstitution.applyTypedBinder_scheme
example := @Solcore.SourceSemantics.FlexibleSubstitution.applyTypedBinder_scheme_quantified
example := @Solcore.SourceSemantics.FlexibleSubstitution.applyTypedBinder_schemeRequirements
example := @Solcore.SourceSemantics.FlexibleSubstitution.applyDeclarationInstantiation_parameterSubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.applyDataConstructorInstantiation_parameterSubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.localSchemeTemplateIds_applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.applyLocalSchemeRequirement_templateRequirement
example := @Solcore.SourceSemantics.FlexibleSubstitution.TypeWellScoped.applySubstitution
example :=
  @Solcore.SourceSemantics.FlexibleSubstitution.TypeWellScoped.applyExactAdmissible
example := @Solcore.SourceSemantics.FlexibleSubstitution.TypeWellScoped.applyFlexible_compose
example :=
  @Solcore.SourceSemantics.FlexibleSubstitution.Ty.applyFlexible_compose_of_rangeAvoidsVariablesOn
example :=
  @Solcore.SourceSemantics.FlexibleSubstitution.PredicateRangeAvoidsVariablesOn
example :=
  @Solcore.SourceSemantics.FlexibleSubstitution.TypedTraitResolution.applySubstitution_compose_of_rangeAvoidsVariablesOn
example := @Solcore.SourceSemantics.FlexibleSubstitution.TypeWellScoped.applyFlexible_composeParameters
example := @Solcore.SourceSemantics.FlexibleSubstitution.TypesWellScoped.applyFlexible_composeParameters
example := @Solcore.SourceSemantics.FlexibleSubstitution.TypesWellScoped.applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.TypeAdmissible.applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.TypeWellFormed.applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.SchemeWellFormed.applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.PredicateAdmissible.applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.PredicateAdmissible.applyFlexible_compose
example := @Solcore.SourceSemantics.FlexibleSubstitution.PredicateWellFormed.applyFlexible_composeParameters
example := @Solcore.SourceSemantics.FlexibleSubstitution.PredicatesWellFormed.applyFlexible_composeParameters
example := @Solcore.SourceSemantics.FlexibleSubstitution.RequirementProves.applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.RequirementValid.applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.RequirementIdsValid.applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.RequirementSequenceProves.applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.IntegerLiteralValid.applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.SchemeGeneralizesExcept.quantified_fresh
example := @Solcore.SourceSemantics.FlexibleSubstitution.applyLocals_eq_self_of_generalizes
example := @Solcore.SourceSemantics.FlexibleSubstitution.SchemeGeneralizesExcept.applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.SchemeGeneralizes.applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.ContextCloses.localSchemeInitializer
example := @Solcore.SourceSemantics.FlexibleSubstitution.LocalSchemeRequirementWellFormed.applySubstitution_of_fresh
example := @Solcore.SourceSemantics.FlexibleSubstitution.LocalSchemeRequirementWellFormed.applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.LocalSchemeRequirementsWellFormed.applySubstitution_of_fresh
example := @Solcore.SourceSemantics.FlexibleSubstitution.LocalSchemeRequirementsWellFormed.applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.instantiateLocalSchemePredicates_applySubstitution
example :=
  @Solcore.SourceSemantics.FlexibleSubstitution.instantiateLocalSchemePredicates_applySubstitution_of_rangeAvoidsVariablesOn
example :=
  @Solcore.SourceSemantics.FlexibleSubstitution.SubstitutionRangeAdmissible.mapRange_instantiateWithSubstitution
example :=
  @Solcore.SourceSemantics.FlexibleSubstitution.LocalSchemeInstantiationValid.of_instantiateWithSubstitution_afterSubstitution_atTarget
example :=
  @Solcore.SourceSemantics.FlexibleSubstitution.LocalSchemeInstantiationValid.of_instantiateWithSubstitution_afterSubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.LocalSchemeInstantiationValid.applySubstitution_of_fresh
example := @Solcore.SourceSemantics.FlexibleSubstitution.DeclarationInstantiation.Valid.applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.DeclarationInstantiation.Admissible.applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.DataConstructorInstantiation.Valid.applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.DataConstructorInstantiation.Admissible.applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.LocalLookup.applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.LocalSchemeRequirementsLookup.applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.ContextSubstitutionValid.localSchemeFresh
example := @Solcore.SourceSemantics.FlexibleSubstitution.ContextSubstitutionValid.withLocal
example := @Solcore.SourceSemantics.FlexibleSubstitution.ContextSubstitutionValid.afterBinder
example := @Solcore.SourceSemantics.FlexibleSubstitution.ContextSubstitutionValid.afterBinders
example := @Solcore.SourceSemantics.FlexibleSubstitution.ContextSubstitutionValid.afterMonoBinders
example := @Solcore.SourceSemantics.FlexibleSubstitution.ContextSubstitutionValid.localSchemeInitializer
example := @Solcore.SourceSemantics.FlexibleSubstitution.ReferenceUseValid.applySubstitution_local
example := @Solcore.SourceSemantics.FlexibleSubstitution.ReferenceUseValid.applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.CoercionProfileInstantiates.applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.CoercionStepValid.applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.CoercionPathValid.applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.OperatorProfileInstantiates.applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.UnaryOperatorHasType.applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.BinaryOperatorHasType.applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.DeclarationApplicationValid.applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.DirectDeclarationCalleeValid.applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.DirectBuiltinCalleeValid.applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.DirectCallRequirementsValid.applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.IndirectApplicationValid.applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.ExpressionRequirementPlan.Valid.applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.WritableLocal.applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.UniformMemberProjection.applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.PatternBinderValid.applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.PatternBindersDistinct.applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.PatternInstructionHasType.applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.PatternInstructionsHaveTypes.applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.matchPatternResolutionInstructions_applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.ConstructorPatternSpellingValid.applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.MatchPatternSourceRepresents.applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.PatternInstructionIrrefutable.applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.PatternInstructionsIrrefutable.applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.TypedMatchPatternIrrefutable.applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.TypedMatchPatternHasType.applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.PatternCoversConstructor.applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.MatchExhaustive.applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.BinderWellFormed.applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.LocalFresh.applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.BinderExtends.applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.BindersExtend.applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.MonoBindersExtend.applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.StatementHasType.contextCloses
example := @Solcore.SourceSemantics.FlexibleSubstitution.StatementsHaveType.contextCloses
example := @Solcore.SourceSemantics.FlexibleSubstitution.ForItemHasType.contextCloses
example := @Solcore.SourceSemantics.FlexibleSubstitution.ForItemsHaveType.contextCloses
example := @Solcore.SourceSemantics.FlexibleSubstitution.StatementHasType.contextSubstitutionValid
example := @Solcore.SourceSemantics.FlexibleSubstitution.StatementsHaveType.contextSubstitutionValid
example := @Solcore.SourceSemantics.FlexibleSubstitution.ForItemHasType.contextSubstitutionValid
example := @Solcore.SourceSemantics.FlexibleSubstitution.ForItemsHaveType.contextSubstitutionValid
example := @Solcore.SourceSemantics.FlexibleSubstitution.StatementsHaveType.applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.ExpressionFormHasRawType.applySubstitution_lambda
example := @Solcore.SourceSemantics.FlexibleSubstitution.BodyHasType.applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.BodyHasType.close
example := @Solcore.SourceSemantics.FlexibleSubstitution.finalize_bodyHasType
example := @Solcore.SourceSemantics.FlexibleSubstitution.BodyCompletes.applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.mergeBodyControls_applyBodyFacts
example := @Solcore.SourceSemantics.FlexibleSubstitution.applySolvedRequirement_id
example := @Solcore.SourceSemantics.FlexibleSubstitution.forLocal_eq_without_of_lookup?
example := @Solcore.SourceSemantics.FlexibleSubstitution.forLocal_eq_without_of_lookup
example := @Solcore.SourceSemantics.FlexibleSubstitution.closeContext_typeVariables
example := @Solcore.SourceSemantics.FlexibleSubstitution.closeContext_solvedRequirementIds
example := @Solcore.SourceSemantics.FlexibleSubstitution.closeContext_localSchemeInitializerContext
example := @Solcore.SourceSemantics.FlexibleSubstitution.ExactSubstitution.localSchemeInitializerContext
example := @Solcore.SourceSemantics.FlexibleSubstitution.ContainsExpression.applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.ContainsStatement.applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.containsNode_applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.containsNode_of_applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.directChild_applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.directChild_of_applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.descends_applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.descends_of_applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.reachable_applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.OccurrenceGraphWellFormed.applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.OccurrenceGraphClosed.applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.definedLocalIds_applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.LocalIdentityOwnership.applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.applyLocalSchemeTemplateOwner
example := @Solcore.SourceSemantics.FlexibleSubstitution.applyLocalSchemeTemplateRow
example := @Solcore.SourceSemantics.FlexibleSubstitution.sourceLocalSchemeTemplateIds_applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.LocalSchemeTemplateRowOwned.applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.primaryRequirementOccurrences_applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.LocalSchemeTemplateRowScoped.applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.RequirementOwnership.applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.mapImplSubstitutionRange
example := @Solcore.SourceSemantics.FlexibleSubstitution.ImplSubstitution.ExactFor.mapRange
example := @Solcore.SourceSemantics.FlexibleSubstitution.ImplHeadInstantiates.applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.applyTraitEvidence
example := @Solcore.SourceSemantics.FlexibleSubstitution.applyTraitEvidence_goal
example := @Solcore.SourceSemantics.FlexibleSubstitution.ImplementationEvidenceRepresents.applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.PredicateEvidenceRepresents.applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.EvidenceValid.applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.RetainedEvidenceValid.applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.SolvedRequirementValid.applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.SolvedRequirementsValid.applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.RequirementLedgerWellFormed.applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.RuntimeRequirementLedgerValid.applySubstitution
example := @Solcore.SourceSemantics.FlexibleSubstitution.ContextSubstitutionValid.ofRequirementLedger
example := @Solcore.SourceSemantics.FlexibleSubstitution.ContextSubstitutionValid.ofRuntimeRequirementLedger
example := @Solcore.SourceSemantics.FlexibleSubstitution.ContextSubstitutionValid.ofScopedRequirementLedger
example :=
  @Solcore.SourceSemantics.FlexibleSubstitution.ContextSubstitutionValid.ofTargetScopedRequirementLedger
example := @Solcore.SourceSemantics.RequirementLedgerWellFormed.proves_predicate_eq
example := @Solcore.SourceSemantics.RequirementProves.transportContext
example := @Solcore.SourceSemantics.RequirementSequenceProves.transportContext
example := @Solcore.SourceSemantics.RequirementIdsUnique.proves_predicate_eq
example := @Solcore.SourceSemantics.RequirementIdsUnique.filter_id_eq_singleton
example := @Solcore.SourceSemantics.RequirementLedgerWellFormed.transport
example := @Solcore.SourceSemantics.RequirementIdsValid.of_subset
example := @Solcore.SourceSemantics.RequirementLedgerWellFormed
example := @Solcore.SourceSemantics.LocalSchemeTemplateRowScoped
example := @Solcore.SourceSemantics.ScopedRequirementEntryValid
example := @Solcore.SourceSemantics.ScopedRequirementLedgerWellFormed
example :=
  @Solcore.SourceSemantics.ScopedRequirementLedgerWellFormed.transportContext
example :=
  @Solcore.SourceSemantics.ScopedRequirementLedgerWellFormed.requirementProvesAt
example :=
  @Solcore.SourceSemantics.ScopedRequirementLedgerWellFormed.requirementValidAt
example :=
  @Solcore.SourceSemantics.ScopedRequirementLedgerWellFormed.requirementIdsValidAt
example := @Solcore.SourceSemantics.ScopedRequirementLedgerWellFormed.template_exact
example :=
  @Solcore.SourceSemantics.ScopedRequirementLedgerWellFormed.localSchemeRequirementWellFormed
example :=
  @Solcore.SourceSemantics.ScopedRequirementLedgerWellFormed.localSchemeRequirementsWellFormed
example := @Solcore.SourceSemantics.ScopedRequirementLedgerWellFormed.toRuntime
example := @Solcore.SourceSemantics.RuntimeRequirementLedgerValid
example := @Solcore.SourceSemantics.LocalIdentityOwnership
example := @Solcore.SourceSemantics.RequirementOwnership
example := @Solcore.SourceSemantics.RequirementOwnership.primaryOccurrence_unique
example := @Solcore.SourceSemantics.TemplateScopeCovered
example := @Solcore.SourceSemantics.InitializedLetBinding.directChild
example :=
  @Solcore.SourceSemantics.LocalSchemeTemplateOwner.scopes_parent_of_scopes_child
example := @Solcore.SourceSemantics.TemplateScopeCovered.root
example := @Solcore.SourceSemantics.TemplateScopeCovered.child
example := @Solcore.SourceSemantics.TemplateScopeCovered.expressionStatementChild
example :=
  @Solcore.SourceSemantics.TemplateScopeCovered.localSchemeInitializer_of_newRoots
example := @Solcore.SourceSemantics.LocalSchemeTemplateOwnership.owner_unique
example := @Solcore.SourceSemantics.patternInstructionBinderIds_eq_carrier
example := @Solcore.SourceSemantics.patternBinderIds_eq_carrier
example := @Solcore.SourceSemantics.forItemDefinedLocalIds_eq_carrier
example := @Solcore.SourceSemantics.expressionDefinedLocalIds_eq_carrier
example := @Solcore.SourceSemantics.statementDefinedLocalIds_eq_carrier
example := @Solcore.SourceSemantics.nodeDefinedLocalIds_eq_carrier
example := @Solcore.SourceSemantics.typedSourceDefinedLocalIds_eq_carrier
example := @Solcore.SourceSemantics.forItemPrimaryRequirementIds_eq_carrier
example :=
  @Solcore.SourceSemantics.statementPrimaryRequirementIds_eq_carrier
example := @Solcore.SourceSemantics.nodePrimaryRequirementIds_eq_carrier
example :=
  @Solcore.SourceSemantics.typedSourcePrimaryRequirementIds_eq_carrier
example := @Solcore.SourceSemantics.typedSourcePrimaryRequirementSites_eq_carrier
example := @Solcore.SourceSemantics.TypeWellScoped
example := @Solcore.SourceSemantics.TypesWellScoped
example := @Solcore.SourceSemantics.TypeWellScoped.contractNominal
example := @Solcore.SourceSemantics.TypeWellScoped.withLocal
example := @Solcore.SourceSemantics.TypeWellScoped.product_components
example := @Solcore.SourceSemantics.TypeWellFormed
example := @Solcore.SourceSemantics.TypeWellFormed.withLocal
example := @Solcore.SourceSemantics.BindersExtend.ids_fresh_for_source
example := @Solcore.SourceSemantics.BindersExtend.ids_nodup
example := @Solcore.SourceSemantics.TypeAdmissible
example := @Solcore.SourceSemantics.admissibleTypeVariables
example := @Solcore.SourceSemantics.TypeAdmissible.toWellFormed
example := @Solcore.SourceSemantics.TypeAdmissible.nominal_data_arguments
example :=
  @Solcore.SourceSemantics.DataConstructorInstantiation.Admissible.instantiateDataConstructor_applySubstitution
example := @Solcore.SourceSemantics.TypeAdmissible.function_parameter
example := @Solcore.SourceSemantics.TypeAdmissible.function_result
example := @Solcore.SourceSemantics.TypeAdmissible.product_left
example := @Solcore.SourceSemantics.TypeAdmissible.product_right
example := @Solcore.SourceSemantics.TypeAdmissible.productMany_member
example := @Solcore.SourceSemantics.TypeAdmissible.mapping_key
example := @Solcore.SourceSemantics.TypeAdmissible.mapping_value
example := @Solcore.SourceSemantics.TypeParameterBindersWellFormed.withResidualTypeVariables
example := @Solcore.SourceSemantics.PredicateAdmissible
example := @Solcore.SourceSemantics.GeneralizationBlockedVariablesExcept
example := @Solcore.SourceSemantics.SchemeGeneralizesExcept
example := @Solcore.SourceSemantics.SchemeGeneralizes
example := @Solcore.SourceSemantics.StaticValidationError
example := @Solcore.SourceSemantics.validateTypeParameterBinders
example := @Solcore.SourceSemantics.validateTypeParameterBinders_success
example := @Solcore.SourceSemantics.validateTypeWellScoped
example := @Solcore.SourceSemantics.validateTypeWellScoped_success
example := @Solcore.SourceSemantics.validateTypeAdmissible
example := @Solcore.SourceSemantics.validateTypeAdmissible_success
example := @Solcore.SourceSemantics.validateSchemeWellFormed
example := @Solcore.SourceSemantics.validateSchemeWellFormed_success
example := @Solcore.SourceSemantics.validateSchemeGeneralizesExcept
example := @Solcore.SourceSemantics.validateSchemeGeneralizesExcept_success
example := @Solcore.SourceSemantics.validateSchemeGeneralizes
example := @Solcore.SourceSemantics.validateSchemeGeneralizes_success
example := @Solcore.SourceSemantics.PredicateWellFormed
example := @Solcore.SourceSemantics.localSchemeTemplateIds
example := @Solcore.SourceSemantics.forItemLocalSchemeTemplateIds_eq_carrier
example :=
  @Solcore.SourceSemantics.statementLocalSchemeTemplateIds_eq_carrier
example := @Solcore.SourceSemantics.nodeLocalSchemeTemplateIds_eq_carrier
example :=
  @Solcore.SourceSemantics.typedSourceLocalSchemeTemplateIds_eq_carrier
example :=
  @Solcore.SourceSemantics.typedSourceLocalSchemeTemplateSites_eq_carrier
example := @Solcore.SourceSemantics.typedSourceLocalSchemeTemplateIds_eq_sites
example := @Solcore.SourceSemantics.instantiateLocalSchemePredicates
example := @Solcore.SourceSemantics.localSchemeInitializerContext
example := @Solcore.SourceSemantics.LocalSchemeRequirementWellFormed
example := @Solcore.SourceSemantics.LocalSchemeRequirementsWellFormed
example := @Solcore.SourceSemantics.LocalSchemeRequirementsWellFormed.empty
example := @Solcore.SourceSemantics.LocalSchemeInstantiationValid
example := @Solcore.SourceSemantics.LocalSchemeInstantiationValid.actual_requirements_nodup
example := @Solcore.SourceSemantics.LocalSchemeInstantiationValid.actual_templates_disjoint
example := @Solcore.SourceSemantics.LocalSchemeInstantiationValid.actual_requirements_valid
example := @Solcore.SourceSemantics.LocalSchemeInstantiationValid.has_shared_substitution
example := @Solcore.SourceSemantics.LocalSchemeInstantiationValid.requirements_length_eq
example := @Solcore.SourceSemantics.LocalSchemeInstantiationValid.toSchemeInstantiatesAt
example := @Solcore.SourceSemantics.LocalSchemeInstantiationValid.type_admissible
example := @Solcore.SourceSemantics.ReferenceUseValid
example := @Solcore.SourceSemantics.ReferenceUseValid.raw_type
example := @Solcore.SourceSemantics.ReferenceUseValid.type_admissible
example := @Solcore.SourceSemantics.CoercionPathValid
example := @Solcore.SourceSemantics.CoercionPathValid.of_isValid
example := @Solcore.SourceSemantics.CoercionPathValid.expressionNode_rawType
example := @Solcore.SourceSemantics.CoercionPathValid.foldl_target
example := @Solcore.SourceSemantics.IntegerLiteralValid
example := @Solcore.SourceSemantics.IntegerLiteralValid.target_type_admissible
example := @Solcore.SourceSemantics.IntegerLiteralValid.transportContext
example := @Solcore.SourceSemantics.WordLiteralValid
example :=
  @Solcore.SourceSemantics.OperatorProfileInstantiates.return_types_admissible
example := @Solcore.SourceSemantics.UnaryOperatorHasType
example := @Solcore.SourceSemantics.UnaryOperatorHasType.result_type_admissible
example := @Solcore.SourceSemantics.BinaryOperatorHasType
example := @Solcore.SourceSemantics.BinaryOperatorHasType.result_type_admissible
example := @Solcore.SourceSemantics.DeclarationApplicationValid
example :=
  @Solcore.SourceSemantics.DeclarationApplicationValid.parameter_types_admissible
example :=
  @Solcore.SourceSemantics.DeclarationApplicationValid.result_type_admissible
example := @Solcore.SourceSemantics.UniformMemberProjection.base_type_admissible
example := @Solcore.SourceSemantics.UniformMemberProjection.member_type_admissible
example := @Solcore.SourceSemantics.TypedMatchPatternHasType
example := @Solcore.SourceSemantics.PlaceHasType
example := @Solcore.SourceSemantics.ExpressionHasType
example := @Solcore.SourceSemantics.ExpressionHasType.ofOrdinary
example := @Solcore.SourceSemantics.ExpressionHasType.ofAppendedOutput
example :=
  @Solcore.SourceSemantics.ExpressionHasType.lambda_annotation_of_uncoerced
example := @Solcore.SourceSemantics.ExpressionsHaveTypes.each_type_admissible
example := @Solcore.SourceSemantics.ExpressionsHaveTypes.product_type_admissible
example := @Solcore.SourceSemantics.StatementHasType
example := @Solcore.SourceSemantics.StatementHasType.letInitializedGeneralized
example := @Solcore.SourceSemantics.StatementsHaveType
example := @Solcore.SourceSemantics.BindersExtend.signatures_eq
example := @Solcore.SourceSemantics.BindersExtend.locals_eq
example := @Solcore.SourceSemantics.BindersExtend.localSchemeRequirements_eq
example := @Solcore.SourceSemantics.MonoBindersExtend.assumptions_eq
example := @Solcore.SourceSemantics.MonoBindersExtend.locals_eq
example :=
  @Solcore.SourceSemantics.MonoBindersExtend.localSchemeRequirements_eq
example := @Solcore.SourceSemantics.MonoBindersExtend.functional
example := @Solcore.SourceSemantics.MonoBindersExtend.bodyTypes_eq
example := @Solcore.SourceSemantics.MonoBindersExtend.each_type_admissible
example := @Solcore.SourceSemantics.MonoBindersExtend.product_type_admissible
example := @Solcore.SourceSemantics.MonomorphicBinders
example := @Solcore.SourceSemantics.MonoBindersExtend.exists_of_monomorphic
example := @Solcore.SourceSemantics.MonoBindersExtend.initialInputIds_nodup
example := @Solcore.SourceSemantics.MonoBindersExtend.initialInputs
example := @Solcore.SourceSemantics.BinderExtends.fresh
example := @Solcore.SourceSemantics.BinderExtends.local_fresh
example := @Solcore.SourceSemantics.BinderExtends.local_scheme_requirements_fresh
example := @Solcore.SourceSemantics.SchemeQuantifiersFresh
example := @Solcore.SourceSemantics.ForItemHasType
example := @Solcore.SourceSemantics.ForItemHasType.letInitializedGeneralized
example := @Solcore.SourceSemantics.ForItemsHaveType
example := @Solcore.SourceSemantics.MatchCaseHasType
example := @Solcore.SourceSemantics.MatchCasesHaveType
example := @Solcore.SourceSemantics.MatchCasesHaveType.pattern_type_of_mem
example := @Solcore.SourceSemantics.TypingSourceExtends
example := @Solcore.SourceSemantics.TypingSourceExtends.refl
example := @Solcore.SourceSemantics.TypingSourceExtends.trans
example := @Solcore.SourceSemantics.TypingSourceExtends.applySubstitution
example := @Solcore.SourceSemantics.TypingSourceExtends.containsExpression
example := @Solcore.SourceSemantics.TypingSourceExtends.containsStatement
example := @Solcore.SourceSemantics.ContainsStatement.initializedLetBinder_mem
example :=
  @Solcore.SourceSemantics.TypingSourceExtends.initializedLetBinders_subset
example :=
  @Solcore.SourceSemantics.TypingSourceExtends.primaryRequirementOccursAt
example := @Solcore.SourceSemantics.ExpressionHasType.weakenSource
example := @Solcore.SourceSemantics.ExpressionFormHasRawType.weakenSource
example := @Solcore.SourceSemantics.ExpressionsHaveTypes.weakenSource
example := @Solcore.SourceSemantics.SourceProjectionsHaveType.weakenSource
example := @Solcore.SourceSemantics.SourcePlaceHasType.weakenSource
example := @Solcore.SourceSemantics.SourceAssignmentHasType.weakenSource
example := @Solcore.SourceSemantics.SourceBitNotAssignmentValid.weakenSource
example := @Solcore.SourceSemantics.StatementHasType.weakenSource
example := @Solcore.SourceSemantics.StatementsHaveType.weakenSource
example := @Solcore.SourceSemantics.ForItemHasType.weakenSource
example := @Solcore.SourceSemantics.ForItemsHaveType.weakenSource
example := @Solcore.SourceSemantics.MatchCaseHasType.weakenSource
example := @Solcore.SourceSemantics.MatchCasesHaveType.weakenSource
example := @Solcore.SourceSemantics.BodyHasType
example := @Solcore.SourceSemantics.BodyDefinition
example := @Solcore.SourceSemantics.BodyDefinitionHasType
example := @Solcore.SourceSemantics.FunctionDefinition

example
    {source : Solcore.Frontend.SourceInference.TypedSource}
    {context : Solcore.SourceSemantics.Context}
    {id : Solcore.Frontend.SourceInference.ExpressionId}
    {type : Solcore.TypeSystem.Ty}
    (unique : Solcore.SourceSemantics.NodeOccurrencesUnique source)
    (typing : Solcore.SourceSemantics.ExpressionHasType source context id type)
    {node : Solcore.Frontend.SourceInference.ExpressionNode}
    (contains : Solcore.SourceSemantics.ContainsExpression source id node)
    {parameters : List Solcore.Frontend.SourceInference.TypedBinder}
    {resultType : Solcore.TypeSystem.Ty}
    {body : List Solcore.Frontend.SourceInference.StatementId}
    (shape : node.form = .lambda parameters resultType body)
    (uncoerced : node.coercions = []) :
    node.type = .function
      (Solcore.TypeSystem.Ty.productMany
        (parameters.map (·.scheme.body))) resultType :=
  Solcore.SourceSemantics.ExpressionHasType.lambda_annotation_of_uncoerced
    unique typing contains shape uncoerced

example := @Solcore.SourceSemantics.FunctionDefinition.Valid
example := @Solcore.SourceSemantics.MethodDefinition
example := @Solcore.SourceSemantics.MethodDefinition.Valid
example := @Solcore.SourceSemantics.ContractSignatureWellFormed
example := @Solcore.SourceSemantics.SignatureCatalogWellFormed
example := @Solcore.SourceSemantics.SignatureCatalogWellFormed.data_contract_ids_ne
example := @Solcore.SourceSemantics.Program
example := @Solcore.SourceSemantics.ProgramWellFormed
example := @Solcore.SourceSemantics.FunctionDefinition.ofChecked
example := @Solcore.SourceSemantics.MethodDefinition.ofChecked
example := @Solcore.SourceSemantics.Program.ofChecked
example := @Solcore.SourceSemantics.checkedBodyContext
example := @Solcore.SourceSemantics.CheckedBodyHeaderWellFormed
example :=
  @Solcore.SourceSemantics.CheckedBodyHeaderWellFormed.ofCheckFunctionBody
example :=
  @Solcore.SourceSemantics.CheckedBodyHeaderWellFormed.ofCheckImplementationMethod
example := @Solcore.SourceSemantics.signatureDeclarationIds_nodup_ofCheckProgram
example :=
  @Solcore.SourceSemantics.SignatureTypeFormationValidated.typeWellScoped
example :=
  @Solcore.SourceSemantics.InferenceTypeFormationValidated.typeWellScoped
example :=
  @Solcore.SourceSemantics.InferenceTypeFormationValidated.typeAdmissible
example :=
  @Solcore.SourceSemantics.InferenceSubstitutionRangeFormationValidated.rangeAdmissible
example :=
  @Solcore.SourceSemantics.SignatureTypesFormationValidated.typesWellScoped
example :=
  @Solcore.SourceSemantics.SignatureTypeFormationValidated.typeWellFormed
example :=
  @Solcore.SourceSemantics.resolveSourceType_success_typeWellFormed
example :=
  @Solcore.SourceSemantics.resolveSourceType_success_signatureTypeWellFormed
example :=
  @Solcore.SourceSemantics.resolveSourceType_success_declarationTypeWellFormed
example :=
  @Solcore.SourceSemantics.SignatureTypesFormationValidated.typesWellFormed
example :=
  @Solcore.SourceSemantics.SignatureTypesFormationValidated.declarationTypesWellFormed
example :=
  @Solcore.SourceSemantics.SignatureParametersWellFormed.declarationContextBinders
example :=
  @Solcore.SourceSemantics.DeclarationInstantiation.instantiate_parameterSubstitution_exact
example :=
  @Solcore.SourceSemantics.DeclarationInstantiation.instantiate_parameterSubstitution_rangeAdmissible
example :=
  @Solcore.SourceSemantics.DeclarationInstantiation.Admissible.type_admissible
example :=
  @Solcore.SourceSemantics.DeclarationInstantiation.ofInstantiated_admissible
example :=
  @Solcore.SourceSemantics.DeclarationInstantiation.ofInstantiated_declarationAdmissible
example :=
  @Solcore.SourceSemantics.SignaturePredicateFormationValidated.predicateWellFormed
example :=
  @Solcore.SourceSemantics.SignaturePredicatesFormationValidated.predicatesWellFormed
example := @Solcore.SourceSemantics.checkFunctionBody_success_result_type_eq
example := @Solcore.SourceSemantics.checkFunctionBody_success_inputs_extend
example :=
  @Solcore.SourceSemantics.checkFunctionBody_success_substitutionRangeAdmissible
example :=
  @Solcore.SourceSemantics.checkedFunctionHeaderWellFormed_ofCheckLoadedProgram
example :=
  @Solcore.SourceSemantics.checkedFunctionHeaderWellFormed_ofCheckProgram
example :=
  @Solcore.SourceSemantics.checkedMethodHeaderWellFormed_ofCheckLoadedProgram
example :=
  @Solcore.SourceSemantics.checkedMethodHeaderWellFormed_ofCheckProgram
example := @Solcore.SourceSemantics.CheckedSignatureCatalogFacts
example := @Solcore.SourceSemantics.CheckedSignatureCatalogFacts.formation
example :=
  @Solcore.SourceSemantics.CheckedSignatureCatalogFacts.function_shapes
example :=
  @Solcore.SourceSemantics.CheckedSignatureCatalogFacts.data_structures
example :=
  @Solcore.SourceSemantics.CheckedSignatureCatalogFacts.constructor_ids
example :=
  @Solcore.SourceSemantics.CheckedSignatureCatalogFacts.trait_structures
example :=
  @Solcore.SourceSemantics.CheckedSignatureCatalogFacts.trait_method_ids
example :=
  @Solcore.SourceSemantics.CheckedSignatureCatalogFacts.implementation_method_ids
example :=
  @Solcore.SourceSemantics.CheckedSignatureCatalogFacts.implementation_structures
example :=
  @Solcore.SourceSemantics.CheckedSignatureCatalogFacts.implementation_heads
example :=
  @Solcore.SourceSemantics.CheckedSignatureCatalogFacts.implementation_method_catalogs
example :=
  @Solcore.SourceSemantics.ImplementationSignatureHeadValidated.semantic_parameters_in_head
example :=
  @Solcore.SourceSemantics.ImplementationSignatureHeadValidated.semantic_trait_catalog
example :=
  @Solcore.SourceSemantics.ImplementationSignatureMethodCatalogValidated.semantic_method
example :=
  @Solcore.SourceSemantics.ImplementationSignatureMethodCatalogValidated.semantic_methods_complete
example :=
  @Solcore.SourceSemantics.ProgramSignatureFormationValidated.functionWellFormed
example :=
  @Solcore.SourceSemantics.ProgramSignatureFormationValidated.dataWellFormed
example :=
  @Solcore.SourceSemantics.ProgramSignatureFormationValidated.traitWellFormed
example :=
  @Solcore.SourceSemantics.ProgramSignatureFormationValidated.implementationWellFormed
example :=
  @Solcore.SourceSemantics.checkedSignatureCatalogFacts_ofCheckLoadedProgram
example :=
  @Solcore.SourceSemantics.checkedSignatureCatalogFacts_ofCheckProgram
example :=
  @Solcore.SourceSemantics.CheckedSignatureCatalogFacts.complete
example :=
  @Solcore.SourceSemantics.SignatureCatalogWellFormed.ofCheckLoadedProgram
example := @Solcore.SourceSemantics.SignatureCatalogWellFormed.ofCheckProgram
example := @Solcore.SourceSemantics.CheckedProgramWellFormedConditions
example :=
  @Solcore.SourceSemantics.CheckedProgramWellFormedConditions.ofCheckLoadedProgram
example :=
  @Solcore.SourceSemantics.CheckedProgramWellFormedConditions.ofCheckProgram
example :=
  @Solcore.SourceSemantics.CheckedProgramWellFormedConditions.programWellFormed
example :=
  @Solcore.SourceSemantics.CheckedProgramWellFormedConditions.programWellFormedOfCheckLoadedProgram
example :=
  @Solcore.SourceSemantics.CheckedProgramWellFormedConditions.programWellFormedOfCheckProgram

example := @Solcore.SourceSemantics.Dynamic.Value
example := @Solcore.SourceSemantics.Dynamic.GeneralizedClosure
example := @Solcore.SourceSemantics.Dynamic.GeneralizedClosure.instantiate
example := @Solcore.SourceSemantics.Dynamic.GeneralizedClosure.instantiate_context
example := @Solcore.SourceSemantics.Dynamic.GeneralizedClosure.instantiate_evidence
example := @Solcore.SourceSemantics.Dynamic.RuntimeContextFields
example := @Solcore.SourceSemantics.Dynamic.RuntimeContextFields.symm
example := @Solcore.SourceSemantics.Dynamic.GeneralizedClosureCaptures
example := @Solcore.SourceSemantics.Dynamic.GeneralizedClosureCaptures.wellTyped
example := @Solcore.SourceSemantics.Dynamic.GeneralizedInitializerMalformed
example := @Solcore.SourceSemantics.Dynamic.GeneralizedInitializerUnsupported
example := @Solcore.SourceSemantics.Dynamic.GeneralizedInitializerUnsupported.captures_or_unsupported
example := @Solcore.SourceSemantics.Dynamic.GeneralizedInitializerUnsupported.not_captures
example := @Solcore.SourceSemantics.Dynamic.Cell.generalized
example := @Solcore.SourceSemantics.Dynamic.Heap
example := @Solcore.SourceSemantics.Dynamic.BodyInstance
example := @Solcore.SourceSemantics.Dynamic.SemanticFault
example := @Solcore.SourceSemantics.Dynamic.SemanticFault.unsupportedPolymorphicBinder
example := @Solcore.SourceSemantics.Dynamic.ControlOutcome
example := @Solcore.SourceSemantics.Dynamic.Environment.LooksUp
example := @Solcore.SourceSemantics.Dynamic.Heap.Reads
example := @Solcore.SourceSemantics.Dynamic.Heap.Allocates
example := @Solcore.SourceSemantics.Dynamic.Heap.AllocatesGeneralized
example := @Solcore.SourceSemantics.Dynamic.Heap.Writes
example := @Solcore.SourceSemantics.Dynamic.HeapMetadataExtend
example := @Solcore.SourceSemantics.Dynamic.HeapMetadataExtend.of_generalized_allocation
example := @Solcore.SourceSemantics.Dynamic.HeapMetadataExtend.toTypes
example := @Solcore.SourceSemantics.Dynamic.ValueHasType
example := @Solcore.SourceSemantics.Dynamic.ClosureCodeValid.residual_variables_open
example := @Solcore.SourceSemantics.Dynamic.GeneralizedClosureCodeValid
example := @Solcore.SourceSemantics.Dynamic.GeneralizedClosureCodeValid.functionType_eq
example := @Solcore.SourceSemantics.Dynamic.GeneralizedClosureCodeValid.instantiateCode
example := @Solcore.SourceSemantics.Dynamic.GeneralizedClosureWellTyped
example := @Solcore.SourceSemantics.Dynamic.GeneralizedClosureWellTyped.instantiateHasType
example := @Solcore.SourceSemantics.Dynamic.OptionalGeneralizedClosureWellTyped
example := @Solcore.SourceSemantics.Dynamic.CellWellTyped.generalized_inv
example := @Solcore.SourceSemantics.Dynamic.TypeContextSupports
example := @Solcore.SourceSemantics.Dynamic.TypeContextSupports.admissibleVariables
example := @Solcore.SourceSemantics.Dynamic.TypeAdmissible.transportContext
example := @Solcore.SourceSemantics.Dynamic.ValuesHaveTypes
example := @Solcore.SourceSemantics.Dynamic.HeapWellTyped
example := @Solcore.SourceSemantics.Dynamic.HeapWellTyped.allocateGeneralized
example := @Solcore.SourceSemantics.Dynamic.LocalCellStorage
example := @Solcore.SourceSemantics.Dynamic.EnvironmentAgrees
example := @Solcore.SourceSemantics.Dynamic.EnvironmentAgrees.lookup
example := @Solcore.SourceSemantics.Dynamic.EnvironmentAgrees.lookup_monomorphic_of_descriptor_empty
example := @Solcore.SourceSemantics.Dynamic.EnvironmentAgrees.lookup_generalized
example := @Solcore.SourceSemantics.Dynamic.HeapTypesExtend
example := @Solcore.SourceSemantics.Dynamic.HeapTypesExtend.of_generalized_allocation
example := @Solcore.SourceSemantics.Dynamic.DefaultValue
example := @Solcore.SourceSemantics.Dynamic.LiteralConstructs
example := @Solcore.SourceSemantics.Dynamic.UnaryPrimitiveApplies
example := @Solcore.SourceSemantics.Dynamic.BinaryPrimitiveApplies
example := @Solcore.SourceSemantics.Dynamic.CoercionPathApplies
example := @Solcore.SourceSemantics.Dynamic.PatternMatches
example := @Solcore.SourceSemantics.Dynamic.ConstructorInstantiationsAgree
example := @Solcore.SourceSemantics.Dynamic.PlaceResolves
example := @Solcore.SourceSemantics.Dynamic.EvidenceEnvironment.applySubstitution
example := @Solcore.SourceSemantics.Dynamic.EvidenceEnvironment.applySubstitution_keys
example := @Solcore.SourceSemantics.Dynamic.EvidenceEnvironment.key_mem_applySubstitution
example := @Solcore.SourceSemantics.Dynamic.EvidenceEnvironment.Supplies
example := @Solcore.SourceSemantics.Dynamic.EvidenceEnvironment.LooksUp.split_append
example := @Solcore.SourceSemantics.Dynamic.EvidenceEnvironment.LooksUp.key_mem
example := @Solcore.SourceSemantics.Dynamic.EvidenceEnvironment.LooksUp.of_applySubstitution
example := @Solcore.SourceSemantics.Dynamic.EvidenceEnvironment.Valid.append
example := @Solcore.SourceSemantics.Dynamic.EvidenceEnvironment.Valid.applySubstitution
example := @Solcore.SourceSemantics.Dynamic.EvidenceEnvironment.Covers.applySubstitution
example := @Solcore.SourceSemantics.Dynamic.EvidenceEnvironment.Supplies.append
example := @Solcore.SourceSemantics.Dynamic.EvidenceCloses.preserves_valid
example := @Solcore.SourceSemantics.Dynamic.Forall₂EvidenceCloses.preserves_valid
example := @Solcore.SourceSemantics.Dynamic.EvidenceValid.close
example := @Solcore.SourceSemantics.Dynamic.EvidenceValid.close_of_covers
example := @Solcore.SourceSemantics.Dynamic.RequirementsProduceEnvironment
example := @Solcore.SourceSemantics.Dynamic.RequirementProves.produces_of_covers
example := @Solcore.SourceSemantics.Dynamic.RequirementSequenceProves.produces_of_covers
example := @Solcore.SourceSemantics.Dynamic.RequirementsProduceEnvironment.supplies
example := @Solcore.SourceSemantics.Dynamic.RequirementsProduceEnvironment.toRequirementSequenceProves
example := @Solcore.SourceSemantics.Dynamic.LocalSchemeRuntimeSelection
example := @Solcore.SourceSemantics.Dynamic.LocalSchemeRuntimeSelection.toLocalSchemeInstantiationValid
example := @Solcore.SourceSemantics.Dynamic.LocalSchemeRuntimeSelection.toSchemeInstantiatesAt
example := @Solcore.SourceSemantics.Dynamic.LocalSchemeRuntimeInstantiation
example := @Solcore.SourceSemantics.Dynamic.LocalSchemeRuntimeInstantiation.toSelection
example := @Solcore.SourceSemantics.Dynamic.LocalSchemeRuntimeInstantiation.toLocalSchemeInstantiationValid
example := @Solcore.SourceSemantics.Dynamic.LocalSchemeRuntimeInstantiation.substitution_range_well_formed
example := @Solcore.SourceSemantics.Dynamic.LocalSchemeRuntimeInstantiation.actual_requirements_length_eq
example := @Solcore.SourceSemantics.Dynamic.LocalSchemeRuntimeInstantiation.produced_evidence_valid
example := @Solcore.SourceSemantics.Dynamic.LocalSchemeRuntimeInstantiation.combined_evidence_covers
example := @Solcore.SourceSemantics.Dynamic.LocalSchemeRuntimeInstantiation.materializedEvidenceCovers
example := @Solcore.SourceSemantics.Dynamic.EvidenceSubtree
example := @Solcore.SourceSemantics.Dynamic.EvidenceEnvironment.DerivedFrom
example := @Solcore.SourceSemantics.Dynamic.EvidenceEntryOriginates
example := @Solcore.SourceSemantics.Dynamic.EvidenceEnvironment.AssembledFrom
example := @Solcore.SourceSemantics.Dynamic.FunctionInstantiates
example := @Solcore.SourceSemantics.Dynamic.TraitMethodInstantiates
example := @Solcore.SourceSemantics.Dynamic.BodyInstanceTypingCertificate
example := @Solcore.SourceSemantics.Dynamic.BodyInstanceTypingCertificate.locals_empty
example := @Solcore.SourceSemantics.Dynamic.BodyInstanceTypingCertificate.type_variables_empty
example := @Solcore.SourceSemantics.Dynamic.BodyInstanceTypingCertificate.residual_type_variables_open
example := @Solcore.SourceSemantics.Dynamic.FunctionInstanceTypingCertificate
example := @Solcore.SourceSemantics.Dynamic.TraitMethodInstanceTypingCertificate
example := @Solcore.SourceSemantics.Dynamic.FunctionInstantiates.certificate
example := @Solcore.SourceSemantics.Dynamic.TraitMethodInstantiates.certificate
example := @Solcore.SourceSemantics.Dynamic.OperatorMethodSelected.certificateOfProfile
example := @Solcore.SourceSemantics.Dynamic.OperatorMethodSelected.coercionCertificateOfProfile
example := @Solcore.SourceSemantics.Dynamic.FunctionInstantiates.hasType
example := @Solcore.SourceSemantics.Dynamic.TraitMethodInstantiates.hasType
example := @Solcore.SourceSemantics.Dynamic.ValuesPack
example := @Solcore.SourceSemantics.Dynamic.MatchCasesSelect
example := @Solcore.SourceSemantics.Dynamic.StatementRoots
example := @Solcore.SourceSemantics.Dynamic.BindersAllocate
example := @Solcore.SourceSemantics.Dynamic.ExpressionEvaluates
example := @Solcore.SourceSemantics.Dynamic.ExpressionEvaluates.generalizedLocal
example := @Solcore.SourceSemantics.Dynamic.ExpressionEvaluates.contains
example := @Solcore.SourceSemantics.Dynamic.ExpressionEvaluates.preservesOfForm
example := @Solcore.SourceSemantics.Dynamic.ExpressionFormEvaluates
example := @Solcore.SourceSemantics.Dynamic.ExpressionFormEvaluates.local
example := @Solcore.SourceSemantics.Dynamic.ExpressionFormEvaluates.localEmptyMapping
example := @Solcore.SourceSemantics.Dynamic.ExpressionsEvaluate
example := @Solcore.SourceSemantics.Dynamic.CoercionPathExecutes
example := @Solcore.SourceSemantics.Dynamic.CallableApplies
example := @Solcore.SourceSemantics.Dynamic.BodyInvokes
example := @Solcore.SourceSemantics.Dynamic.StatementExecutes
example :=
  @Solcore.SourceSemantics.Dynamic.StatementExecutes.letInitializedGeneralized
example := @Solcore.SourceSemantics.Dynamic.StatementsExecute
example := @Solcore.SourceSemantics.Dynamic.FunctionStatementsExecute
example := @Solcore.SourceSemantics.Dynamic.ForItemExecutes
example :=
  @Solcore.SourceSemantics.Dynamic.ForItemExecutes.letInitializedGeneralized
example := @Solcore.SourceSemantics.Dynamic.ForItemsExecute
example := @Solcore.SourceSemantics.Dynamic.WhileExecutes
example := @Solcore.SourceSemantics.Dynamic.ForLoopExecutes
example := @Solcore.SourceSemantics.Dynamic.MatchCasesSelect.arm_preserves_typing
example := @Solcore.SourceSemantics.Dynamic.MatchCasesSelect.noBranch_impossible_of_exhaustive
example := @Solcore.SourceSemantics.Dynamic.StatementExecutes.controlCanFallthrough
example := @Solcore.SourceSemantics.Dynamic.StatementsExecute.controlCanFallthrough
example := @Solcore.SourceSemantics.ControlSummary.HasOutcome
example := @Solcore.SourceSemantics.BodyCompletes.tail_of_cons_of_hasOutcome
example := @Solcore.SourceSemantics.StatementsHaveType.controlHasOutcome
example := @Solcore.SourceSemantics.StatementsHaveType.bodyCompletes_of_closed
example := @Solcore.SourceSemantics.Dynamic.ProgramEntry
example := @Solcore.SourceSemantics.Dynamic.ProgramEntryValid
example := @Solcore.SourceSemantics.Dynamic.ProgramEvaluates
example := @Solcore.SourceSemantics.Dynamic.ProgramEvaluates.preservesWith
example := @Solcore.SourceSemantics.Dynamic.ProgramEvaluates.preserves
example := @Solcore.SourceSemantics.Dynamic.ClosedProgramEvaluates
example := @Solcore.SourceSemantics.Dynamic.ExpressionFaults
example := @Solcore.SourceSemantics.Dynamic.EvidenceEnvironment.lookup_or_unbound
example := @Solcore.SourceSemantics.Dynamic.EvidenceCloses.exists_or_fault
example := @Solcore.SourceSemantics.Dynamic.Forall₂EvidenceCloses.exists_or_fault
example := @Solcore.SourceSemantics.Dynamic.EvidenceCloses.excludes_fault
example := @Solcore.SourceSemantics.Dynamic.EvidenceClosuresFault.excludes_closure
example := @Solcore.SourceSemantics.Dynamic.RequirementProducesEvidence.excludes_unavailable
example := @Solcore.SourceSemantics.Dynamic.RequirementsProduceEnvironment.excludes_fault
example := @Solcore.SourceSemantics.Dynamic.RequirementsProduceEnvironment.excludes_list_fault
example := @Solcore.SourceSemantics.Dynamic.requirement_contains_or_missing
example := @Solcore.SourceSemantics.Dynamic.requirement_produces_or_unavailable
example := @Solcore.SourceSemantics.Dynamic.requirements_produce_or_list_fault
example := @Solcore.SourceSemantics.Dynamic.requirements_produce_or_fault
example := @Solcore.SourceSemantics.Dynamic.ExpressionFaults.generalizedLocalRequirement
example := @Solcore.SourceSemantics.Dynamic.ExpressionFaults.generalizedLocalCoercion
example := @Solcore.SourceSemantics.Dynamic.ExpressionEvaluates.excludes_missing
example := @Solcore.SourceSemantics.Dynamic.ExpressionFormFaults
example := @Solcore.SourceSemantics.Dynamic.ExpressionFormFaults.localUnbound
example := @Solcore.SourceSemantics.Dynamic.ExpressionFormFaults.localDangling
example := @Solcore.SourceSemantics.Dynamic.ExpressionFormFaults.localUninitialized
example := @Solcore.SourceSemantics.Dynamic.ExpressionsFault
example := @Solcore.SourceSemantics.Dynamic.CoercionStepFaults
example := @Solcore.SourceSemantics.Dynamic.CoercionPathFaults
example := @Solcore.SourceSemantics.Dynamic.SourcePlaceFaults
example := @Solcore.SourceSemantics.Dynamic.CallableFaults
example := @Solcore.SourceSemantics.Dynamic.BodyFaults
example := @Solcore.SourceSemantics.Dynamic.StatementFaults
example := @Solcore.SourceSemantics.Dynamic.StatementsFault
example := @Solcore.SourceSemantics.Dynamic.FunctionStatementsFault
example := @Solcore.SourceSemantics.Dynamic.ForItemFaults
example := @Solcore.SourceSemantics.Dynamic.ForItemsFault
example := @Solcore.SourceSemantics.Dynamic.WhileFaults
example := @Solcore.SourceSemantics.Dynamic.ForLoopFaults
example := @Solcore.SourceSemantics.Dynamic.RuntimeBoundaryAccepts
example := @Solcore.SourceSemantics.Dynamic.RuntimeBoundaryRejects
example := @Solcore.SourceSemantics.Dynamic.ExpressionEvaluatesOutcome
example := @Solcore.SourceSemantics.Dynamic.RuntimeExpressionEvaluatesOutcome
example := @Solcore.SourceSemantics.Dynamic.StatementExecutesOutcome
example := @Solcore.SourceSemantics.Dynamic.StatementsExecuteOutcome
example := @Solcore.SourceSemantics.Dynamic.FunctionStatementsExecuteOutcome
example := @Solcore.SourceSemantics.Dynamic.ExpressionEvaluationPreserved
example := @Solcore.SourceSemantics.Dynamic.StatementEvaluationPreserved
example := @Solcore.SourceSemantics.Dynamic.BodyInvocationPreserved
example := @Solcore.SourceSemantics.Dynamic.SourceRuntimeValid
example := @Solcore.SourceSemantics.Dynamic.SourceRuntimeValid.requirements
example := @Solcore.SourceSemantics.Dynamic.SourceRuntimeValid.variables_closed
example := @Solcore.SourceSemantics.Dynamic.SourceRuntimeValid.residual_variables_open
example := @Solcore.SourceSemantics.Dynamic.WholeLanguagePreservation
example := @Solcore.SourceSemantics.ProgramWellFormed.wholeLanguagePreservation

example := @Solcore.SourceSemantics.Staging.Stage
example := @Solcore.SourceSemantics.Staging.StagesJoin
example := @Solcore.SourceSemantics.Staging.HasStage
example := @Solcore.SourceSemantics.Staging.StatementStages
example := @Solcore.SourceSemantics.Staging.ForItemStages
example := @Solcore.SourceSemantics.Staging.ForItemsStage
example := @Solcore.SourceSemantics.Staging.MatchCaseStages
example := @Solcore.SourceSemantics.Staging.MatchCasesStage
example := @Solcore.SourceSemantics.Staging.RootStages
example := @Solcore.SourceSemantics.Staging.RootsStage
example := @Solcore.SourceSemantics.Staging.BodyDefinitionHasStages
example := @Solcore.SourceSemantics.Staging.ProgramHasStages
example := @Solcore.SourceSemantics.Staging.MaterializedValue
example := @Solcore.SourceSemantics.Staging.Materializable
example := @Solcore.SourceSemantics.Staging.Materializes
example := @Solcore.SourceSemantics.Staging.FrontendValueRepresents
example := @Solcore.SourceSemantics.Staging.ComptimeEvaluationBoundary
example := @Solcore.SourceSemantics.Staging.ComptimeParameterInputs
example := @Solcore.SourceSemantics.Staging.ComptimeInvocationBoundary
example := @Solcore.SourceSemantics.Staging.Materializes.frontend_exists_unique
example := @Solcore.SourceSemantics.Staging.ComptimeExpressionMaterializes
example := @Solcore.SourceSemantics.Staging.SourceComptimeExpressionMaterializes

end Tests
end

section
-- leanmerge: from Solcore.Test.SourceSemanticsScopedRequirements
/-!
Boundary examples for the whole-body scoped requirement ledger.

Qualified local-scheme assumptions are admitted only when a source-owned
initialized binder names the exact retained row and that row has a primary
use in the binder's initializer subtree.  Ordinary declaration assumptions
continue to use the declaration-wide evidence judgment.
-/

set_option autoImplicit false

namespace Solcore.Test.SourceSemanticsScopedRequirements

open Frontend
open Frontend.SourceInference
open SourceSemantics
open TypeSystem

private def testModule : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"scoped_requirements", by decide⟩], by decide⟩⟩

private def testOwner : Resolved.DeclarationId := ⟨testModule, 0⟩

private def testSourceId : Syntax.SourceId := {
  origin := .main
  path := "scoped_requirements.sol"
}

private def testSpan : Syntax.SourceSpan := {
  source := testSourceId
  startByte := 0
  endByte := 0
}

private def emptySignatures : ProgramSignatures := {
  functions := []
  implRules := []
  traits := []
  implementations := []
  dataTypes := []
}

private def templateVariable : TypeVarId := ⟨400⟩

private def templateId : RequirementId := ⟨0⟩

private def ordinaryId : RequirementId := ⟨401⟩

private def templatePredicate : ProgramPredicate :=
  ProgramSignatures.builtinIntPredicate (.variable templateVariable)

private def ordinaryPredicate : ProgramPredicate :=
  ProgramSignatures.builtinIntPredicate .word

private def templateRequirement : LocalSchemeRequirement := {
  templateRequirement := templateId
  predicate := templatePredicate
}

private def templateRow : SolvedRequirement := {
  id := templateId
  predicate := templatePredicate
  evidence := .assumption templatePredicate
}

private def ordinaryRow : SolvedRequirement := {
  id := ordinaryId
  predicate := ordinaryPredicate
  evidence := .assumption ordinaryPredicate
}

private def templateBinder (index : Nat) : TypedBinder := {
  id := ⟨testOwner, index⟩
  name := s!"template{index}"
  scheme := {
    quantified := [templateVariable]
    body := .variable templateVariable
  }
  schemeRequirements := [templateRequirement]
  span := some testSpan
}

private def expressionId (index : Nat) : ExpressionId :=
  ⟨⟨testOwner, index⟩⟩

private def statementId (index : Nat) : StatementId :=
  ⟨⟨testOwner, index⟩⟩

private def expressionNode (index : Nat)
    (requirements : List RequirementId) : ExpressionNode := {
  id := expressionId index
  span := testSpan
  type := .variable templateVariable
  form := .proxy (.variable templateVariable)
  requirements
}

private def letNode (index binderIndex initializerIndex : Nat) :
    StatementNode := {
  id := statementId index
  span := testSpan
  type := .unit
  form := .letDecl (templateBinder binderIndex)
    (some (expressionId initializerIndex))
}

private def scopedTemplateSource : TypedSource := {
  owner := testOwner
  inputs := []
  roots := [.statement (statementId 1)]
  nodes := [
    .expression (expressionNode 0 [templateId]),
    .statement (letNode 1 0 0)
  ]
}

private def scopedTemplateOwner : LocalSchemeTemplateOwner := {
  binder := templateBinder 0
  initializer := .expression (expressionId 0)
  requirement := templateRequirement
}

private def orphanSource : TypedSource := {
  owner := testOwner
  inputs := []
  roots := [.expression (expressionId 0)]
  nodes := [.expression (expressionNode 0 [templateId])]
}

private def duplicateOwnerSource : TypedSource := {
  owner := testOwner
  inputs := []
  roots := [.statement (statementId 1), .statement (statementId 3)]
  nodes := [
    .expression (expressionNode 0 [templateId]),
    .statement (letNode 1 0 0),
    .expression (expressionNode 2 []),
    .statement (letNode 3 1 2)
  ]
}

private def wrongScopeSource : TypedSource := {
  owner := testOwner
  inputs := []
  roots := [
    .statement (statementId 1),
    .expression (expressionId 2)
  ]
  nodes := [
    .expression (expressionNode 0 []),
    .statement (letNode 1 0 0),
    .expression (expressionNode 2 [templateId])
  ]
}

private def ordinarySource : TypedSource := {
  owner := testOwner
  inputs := []
  roots := [.expression (expressionId 0)]
  nodes := [.expression (expressionNode 0 [ordinaryId])]
}

private def templateContext : SourceSemantics.Context :=
  (Context.ofSignatures emptySignatures).withSolvedRequirements [templateRow]

private def orphanContext : SourceSemantics.Context := templateContext

private def ordinaryContextWithoutAssumption : SourceSemantics.Context :=
  (Context.ofSignatures emptySignatures).withSolvedRequirements [ordinaryRow]

private def ordinaryContextWithAssumption : SourceSemantics.Context :=
  ((Context.ofSignatures emptySignatures).withAssumptions [ordinaryPredicate])
    |>.withSolvedRequirements [ordinaryRow]

private def templateInferenceContext : SourceInference.Context := {
  environment := { modules := [], declarations := [] }
  signatures := emptySignatures
  scope := {
    currentModule := testModule
    genericOwner := testOwner
    genericParameters := []
  }
}

private def templateInputRequirement : Requirement := {
  id := templateId
  predicate := templatePredicate
}

private def templateSolverState : SourceInference.State := {
  SourceInference.State.initial testOwner with
  nextRequirement := 1
  requirements := [templateInputRequirement]
  localSchemeAssumptions := [templateId]
}

private def templateTrackingBaseState : SourceInference.State := {
  SourceInference.State.initial testOwner with
  nextRequirement := 1
  requirements := [templateInputRequirement]
}

private def templateTrackingAllocatedState : SourceInference.State :=
  (templateTrackingBaseState.allocateBinder "template0"
    (templateBinder 0).scheme (some testSpan) false
    [templateRequirement]).2

private def reversedLocalEnvironmentState : SourceInference.State := {
  SourceInference.State.initial testOwner with
  localBinders := [templateBinder 0, templateBinder 1]
  nextLocal := 2
  localSchemeAssumptions := [templateId]
}

private def reversedLocalEnvironmentContext : SourceSemantics.Context :=
  ((Context.ofSignatures emptySignatures).withLocal
      (templateBinder 0).id (templateBinder 0).scheme
      (templateBinder 0).schemeRequirements)
    |>.withLocal (templateBinder 1).id (templateBinder 1).scheme
      (templateBinder 1).schemeRequirements

private theorem emptySubstitution_without
    (variables : List TypeVarId) :
    TypeSystem.Substitution.without [] variables = [] := by
  induction variables with
  | nil => rfl
  | cons head tail ih =>
      simpa [TypeSystem.Substitution.without,
        TypeSystem.Substitution.erase] using ih

private theorem substitution_apply_empty (type : Ty) :
    TypeSystem.Substitution.apply [] type = type := by
  exact TypeSystem.Substitution.empty_apply type

private theorem types_map_apply_empty (types : List Ty) :
    types.map (TypeSystem.Substitution.apply []) = types := by
  induction types with
  | nil => rfl
  | cons head tail induction =>
      simp [substitution_apply_empty, induction]

private theorem scheme_apply_empty (scheme : Scheme) :
    Scheme.apply [] scheme = scheme := by
  cases scheme
  simp [Scheme.apply, emptySubstitution_without, substitution_apply_empty]

private theorem predicate_apply_empty (predicate : ProgramPredicate) :
    TypedTraitResolution.applySubstitution [] predicate = predicate := by
  cases predicate with
  | mk trait subject arguments =>
      simp [TypedTraitResolution.applySubstitution,
        substitution_apply_empty, types_map_apply_empty]

private theorem localSchemeRequirement_apply_empty
    (requirement : LocalSchemeRequirement) :
    requirement.applySubstitution [] = requirement := by
  cases requirement
  simp [LocalSchemeRequirement.applySubstitution,
    predicate_apply_empty]

private theorem localSchemeRequirements_map_apply_empty
    (requirements : List LocalSchemeRequirement) :
    requirements.map (LocalSchemeRequirement.applySubstitution []) =
      requirements := by
  induction requirements with
  | nil => rfl
  | cons requirement rest induction =>
      simp [localSchemeRequirement_apply_empty, induction]

/-- Semantic binder extension reverses the source-ordered input list, while
the alignment invariant deliberately retains both scopes by permutation. -/
private theorem reversedLocalEnvironmentAligned :
    SourceInferenceSoundness.LocalEnvironmentAligned
      reversedLocalEnvironmentState [] reversedLocalEnvironmentContext := by
  constructor
  · simp [reversedLocalEnvironmentState, templateBinder]
  · simpa [SourceInferenceSoundness.closedBinderLocals,
      reversedLocalEnvironmentState, reversedLocalEnvironmentContext,
      Context.withLocal, Context.ofSignatures,
      emptySubstitution_without, scheme_apply_empty] using
      (List.Perm.swap
        ((templateBinder 0).id, (templateBinder 0).scheme)
        ((templateBinder 1).id, (templateBinder 1).scheme) []).symm
  · simpa [SourceInferenceSoundness.closedBinderRequirements,
      reversedLocalEnvironmentState, reversedLocalEnvironmentContext,
      Context.withLocal, Context.ofSignatures,
      emptySubstitution_without,
      localSchemeRequirement_apply_empty,
      localSchemeRequirements_map_apply_empty] using
      (List.Perm.swap
        ((templateBinder 0).id, (templateBinder 0).schemeRequirements)
        ((templateBinder 1).id, (templateBinder 1).schemeRequirements) []).symm

/-- Replacing stale compatibility locals leaves stable-binder alignment
unchanged. -/
example :
    SourceInferenceSoundness.LocalEnvironmentAligned
      (reversedLocalEnvironmentState.withLocals
        [("stale", .mono .word)])
      [] reversedLocalEnvironmentContext :=
  reversedLocalEnvironmentAligned.withLocals [("stale", .mono .word)]

private def alignedLifecycleAllocation : TypedBinder × SourceInference.State :=
  reversedLocalEnvironmentState.allocateBinder "fresh" (.mono .unit)

private def alignedLifecycleContext : SourceSemantics.Context :=
  reversedLocalEnvironmentContext.withLocal
    alignedLifecycleAllocation.1.id
    (alignedLifecycleAllocation.1.applySubstitution []).scheme
    (alignedLifecycleAllocation.1.applySubstitution []).schemeRequirements

/-- A genuinely fresh stable identity extends both paired semantic scopes in
lockstep with executable binder allocation. -/
example :
    SourceInferenceSoundness.LocalEnvironmentAligned
      alignedLifecycleAllocation.2 [] alignedLifecycleContext := by
  exact
    reversedLocalEnvironmentAligned.allocateBinder_of_localBindersBelowNextLocal
      "fresh" (.mono .unit) none false [] rfl (by
        intro binder member
        change binder ∈ [templateBinder 0, templateBinder 1] at member
        change binder.id.binderIndex < 2
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl <;> simp [templateBinder])

/-- A name selected by executable first-match lookup yields both paired
stable-ID lookups even though the semantic list order is reversed. -/
example :
    reversedLocalEnvironmentContext.LocalLookup (templateBinder 0).id
        (templateBinder 0).scheme ∧
      reversedLocalEnvironmentContext.LocalSchemeRequirementsLookup
        (templateBinder 0).id (templateBinder 0).schemeRequirements := by
  exact reversedLocalEnvironmentAligned.lookup_of_lookupBinder?
    (name := "template0") (by decide)

/-- The order-independent alignment also identifies the local-scheme free
variables used as the lexical barrier for value generalization. -/
example :
    templateVariable ∈
        (reversedLocalEnvironmentState.binderEnvironment.apply []).freeVariables ↔
      templateVariable ∈ reversedLocalEnvironmentContext.locals.flatMap
        (fun entry => entry.2.freeVariables) :=
  reversedLocalEnvironmentAligned.mem_local_freeVariables_iff templateVariable

private def templateTrackingForNode : StatementNode := {
  id := statementId 2
  span := testSpan
  type := .unit
  form := .forLoop
    [.letDecl (templateBinder 0) (some (expressionId 0))]
    (expressionId 1) [] []
}

private theorem templateTrackingBase :
    SourceInferenceSoundness.TemplateTracking templateTrackingBaseState [] := by
  constructor <;>
    simp [templateTrackingBaseState, SourceInference.State.initial,
      SourceInference.State.toTypedSource, sourceLocalSchemeTemplateIds,
      localSchemeTemplateOwners, initializedLetBindings]

private def templateGeneralizationState : SourceInference.State := {
  templateTrackingBaseState with
  directCallRequirements := [templateId]
}

private theorem templateGeneralizationTracking :
    SourceInferenceSoundness.TemplateTracking templateGeneralizationState [] := by
  constructor <;>
    simp [templateGeneralizationState, templateTrackingBaseState,
      SourceInference.State.initial, SourceInference.State.toTypedSource,
      sourceLocalSchemeTemplateIds, localSchemeTemplateOwners,
      initializedLetBindings]

/-- The real generalizer supplies allocation's uniqueness, freshness, and
ledger-coverage premises in one step, including a nonempty template set. -/
example :
    let generalized := SourceInference.Detail.generalizeValue
      templateGeneralizationState [] 0 (.variable templateVariable)
    SourceInferenceSoundness.TemplateTracking
      (({ templateGeneralizationState with locals := [] }).allocateBinder
        "template0" generalized.scheme (some testSpan) false
        generalized.requirements).2
      (generalized.requirements.map fun requirement =>
        requirement.templateRequirement) := by
  exact templateGeneralizationTracking.allocateGeneralizedValue (by rfl)
    [] 0 (.variable templateVariable) "template0" (some testSpan)

/-- Once the executable and declarative barriers agree on the initializer
type's candidate variable, the real nonempty template exemption yields the
declarative qualified-generalization judgment. -/
example :
    let generalized := SourceInference.Detail.generalizeValue
      templateGeneralizationState [] 0 (.variable templateVariable)
    SchemeGeneralizesExcept templateContext
      (generalized.requirements.map fun requirement =>
        requirement.templateRequirement)
      generalized.scheme := by
  dsimp only
  apply
    SourceInferenceSoundness.generalizeValue_schemeGeneralizesExcept_of_barrier
  intro metavariable member
  simp only [Ty.freeVariables] at member
  have variableEq : metavariable = templateVariable := by
    simpa using member
  subst metavariable
  have executableEmpty :
      SourceInference.Detail.generalizeValueBlockedVariables
        templateGeneralizationState [] 0 = [] := by
    decide
  have templateIds :
      ((SourceInference.Detail.generalizeValue templateGeneralizationState [] 0
          (.variable templateVariable)).requirements.map fun requirement =>
        requirement.templateRequirement) = [templateId] := by
    decide
  have semanticEmpty :
      GeneralizationBlockedVariablesExcept templateContext [templateId] = [] := by
    decide
  rw [executableEmpty, templateIds, semanticEmpty]

/-- The locals-only update used by both ordinary lets and for-loop items does
not disturb pending template ownership. -/
example : SourceInferenceSoundness.TemplateTracking
    { templateTrackingBaseState with
      locals := [("replacement", .mono .word)] } [] := by
  exact templateTrackingBase.replaceLocals [("replacement", .mono .word)]

private theorem templateTrackingAllocated :
    SourceInferenceSoundness.TemplateTracking templateTrackingAllocatedState
      [templateId] := by
  apply SourceInferenceSoundness.TemplateTracking.allocateBinder
      templateTrackingBase "template0" (templateBinder 0).scheme
      (some testSpan) false [templateRequirement]
  · simp [templateRequirement]
  · intro id member
    have id_eq : id = templateId := by
      simpa [templateRequirement] using member
    subst id
    change templateId ∉ []
    simp
  · simp [templateRequirement, templateTrackingBaseState,
      templateInputRequirement]

/-- A regular initialized let discharges the binder's pending template ID
when its owner node is recorded. -/
example : SourceInferenceSoundness.TemplateTracking
    (templateTrackingAllocatedState.recordNode
      (.statement (letNode 1 0 0))) [] := by
  apply SourceInferenceSoundness.TemplateTracking.recordNode
  simpa [SourceInferenceSoundness.nodeLocalSchemeTemplateIds,
    statementInitializedLetBindings, InitializedLetBinding.templateOwners,
    letNode, templateBinder, templateRequirement] using
    templateTrackingAllocated

/-- A for-loop node discharges the initialized header item's pending template
ID by the same node-local collector used for ordinary lets. -/
example : SourceInferenceSoundness.TemplateTracking
    (templateTrackingAllocatedState.recordNode
      (.statement templateTrackingForNode)) [] := by
  apply SourceInferenceSoundness.TemplateTracking.recordNode
  simpa [SourceInferenceSoundness.nodeLocalSchemeTemplateIds,
    templateTrackingForNode, statementInitializedLetBindings,
    forItemInitializedLetBindings, InitializedLetBinding.templateOwners,
    templateBinder, templateRequirement] using templateTrackingAllocated

private def templateFinalizeState : SourceInference.State := {
  templateSolverState with
  nodes := scopedTemplateSource.nodes
}

private def templateFinalizedResult : SourceInference.Result := {
  type := .variable templateVariable
  substitution := templateFinalizeState.inference.substitution
  solvedRequirements := [templateRow]
  typedSource := scopedTemplateSource.applySubstitution
    templateFinalizeState.inference.substitution
}

private theorem templateFinalizeStateAligned :
    SourceInferenceSoundness.TemplateIdsAligned templateFinalizeState
      scopedTemplateSource.roots := by
  intro id
  change id ∈ sourceLocalSchemeTemplateIds scopedTemplateSource ↔
    id ∈ [templateId]
  simp [sourceLocalSchemeTemplateIds, localSchemeTemplateOwners,
    initializedLetBindings, statementInitializedLetBindings,
    InitializedLetBinding.templateOwners, scopedTemplateSource, letNode,
    templateBinder, templateRequirement]

private theorem templateFinalizeSuccess :
    SourceInference.Detail.finalize templateInferenceContext
      (.variable templateVariable) templateFinalizeState
      scopedTemplateSource.roots = .ok templateFinalizedResult := by
  rfl

/-- Finalization now reconstructs the complete source/state template tracker
directly from its executable boundary validation. -/
example : SourceInferenceSoundness.TemplateTracking templateFinalizeState [] :=
  SourceInferenceSoundness.finalize_templateTracking templateFinalizeSuccess

/-- The same successful boundary establishes globally unique ownership after
the final flexible substitution. -/
example : LocalSchemeTemplateOwnership templateFinalizedResult.typedSource :=
  SourceInferenceSoundness.finalize_localSchemeTemplateOwnership
    templateFinalizeSuccess

/-- Successful finalization supplies the complete scoped ledger for the
finalized source. -/
example : ScopedRequirementLedgerWellFormed
    (SourceInferenceSoundness.finalizedRequirementContext
      templateInferenceContext templateFinalizedResult)
    templateFinalizedResult.typedSource :=
  SourceInferenceSoundness.finalize_scopedRequirementLedgerWellFormed
    templateFinalizeSuccess

/-- The finalization bridge consumes structural closure separately and fills
the implementation-evidence component from this concrete nonempty template
fixture's finalized scoped ledger. -/
example {sourceContext : SourceSemantics.Context}
    {closedVariables : List TypeVarId}
    (closes : FlexibleSubstitution.ContextCloses
      templateFinalizedResult.substitution closedVariables sourceContext
      (SourceInferenceSoundness.finalizedRequirementContext
        templateInferenceContext templateFinalizedResult))
    (schemesFresh : FlexibleSubstitution.LocalSchemesFreshFor sourceContext
      templateFinalizedResult.substitution) :
    FlexibleSubstitution.ContextSubstitutionValid
      templateFinalizedResult.substitution closedVariables sourceContext
      (SourceInferenceSoundness.finalizedRequirementContext
        templateInferenceContext templateFinalizedResult) :=
  SourceInferenceSoundness.finalize_contextSubstitutionValid
    templateFinalizeSuccess closes schemesFresh

/-- Finalization preserves the exact source/state template-ID alignment of a
nonempty qualified-local fixture. -/
example : ∀ id,
    id ∈ sourceLocalSchemeTemplateIds templateFinalizedResult.typedSource ↔
      id ∈ templateFinalizeState.localSchemeAssumptions := by
  exact SourceInferenceSoundness.finalize_templateIdsAligned
    templateFinalizeStateAligned templateFinalizeSuccess

/-- The executable validator supplies the alignment premise automatically. -/
example : ∀ id,
    id ∈ sourceLocalSchemeTemplateIds templateFinalizedResult.typedSource ↔
      id ∈ templateFinalizeState.localSchemeAssumptions := by
  exact SourceInferenceSoundness.finalize_templateIdsAligned_validated
    templateFinalizeSuccess

/-- A source-classified template emitted by finalization retains canonical
assumption evidence for its normalized predicate. -/
example : ∀ row, row ∈ templateFinalizedResult.solvedRequirements →
    row.id ∈ sourceLocalSchemeTemplateIds templateFinalizedResult.typedSource →
    row.evidence = .assumption row.predicate := by
  exact SourceInferenceSoundness.finalize_template_evidence
    templateFinalizeStateAligned templateFinalizeSuccess

/-- Assumption evidence is also available without an external alignment
premise once finalization succeeds. -/
example : ∀ row, row ∈ templateFinalizedResult.solvedRequirements →
    row.id ∈ sourceLocalSchemeTemplateIds templateFinalizedResult.typedSource →
    row.evidence = .assumption row.predicate := by
  exact SourceInferenceSoundness.finalize_template_evidence_validated
    templateFinalizeSuccess

private theorem templateOwnerContained :
    ContainsLocalSchemeTemplate scopedTemplateSource scopedTemplateOwner := by
  simp [ContainsLocalSchemeTemplate, localSchemeTemplateOwners,
    initializedLetBindings, statementInitializedLetBindings,
    InitializedLetBinding.templateOwners,
    scopedTemplateSource, scopedTemplateOwner, letNode, templateBinder,
    templateRequirement]

private theorem templateOccursAtInitializer :
    PrimaryRequirementOccursAt scopedTemplateSource
      (.expression (expressionId 0)) templateId := by
  simp [PrimaryRequirementOccursAt, primaryRequirementOccurrences,
    nodePrimaryRequirementOccurrences,
    expressionPrimaryRequirementOccurrences,
    statementPrimaryRequirementOccurrences, scopedTemplateSource,
    expressionNode, letNode]

/-- Executable template solving is accepted through scoped source ownership,
not through declaration-wide retained-evidence validity. -/
theorem templateSolverProducesScopedEntry :
    ScopedRequirementEntryValid templateContext scopedTemplateSource
      templateRow := by
  apply
    SourceInferenceSoundness.solveRequirements_scoped_entries_sound
      (inferenceContext := templateInferenceContext)
      (state := templateSolverState)
      (requirements := [templateInputRequirement])
      (solved := [templateRow])
  · rfl
  · rfl
  · intro requirement member
    have requirement_eq : requirement = templateInputRequirement := by
      simpa using member
    subst requirement
    constructor
    · intro _
      exact sourceLocalSchemeTemplateIds_mem_iff.mpr
        ⟨scopedTemplateOwner, templateOwnerContained, rfl⟩
    · intro _
      simp [templateInputRequirement, templateSolverState]
  · intro requirement member template
    have requirement_eq : requirement = templateInputRequirement := by
      simpa using member
    subst requirement
    simpa [templateInputRequirement, templateSolverState,
      SourceInference.Detail.applyPredicate, SourceInference.State.initial,
      TypedTraitResolution.applySubstitution] using
      (LocalSchemeTemplateRowScoped.intro scopedTemplateOwner
        templateOwnerContained rfl rfl rfl (.expression (expressionId 0))
        templateOccursAtInitializer
        (scopedTemplateOwner.scopes_initializer templateOwnerContained))
  · rfl
  · simp

/-- A nonempty canonical inference ledger containing a qualified-local
template becomes a complete scoped semantic ledger after solving. -/
theorem templateSolverProducesScopedLedger :
    ScopedRequirementLedgerWellFormed templateContext
      scopedTemplateSource := by
  apply
    SourceInferenceSoundness.solveRequirements_scoped_ledger_sound
      (inferenceContext := templateInferenceContext)
      (state := templateSolverState)
      (solved := [templateRow])
      (baseContext := Context.ofSignatures emptySignatures)
  · rfl
  · rfl
  · rfl
  · constructor
    simp [sourceLocalSchemeTemplateIds, localSchemeTemplateOwners,
      initializedLetBindings, statementInitializedLetBindings,
      InitializedLetBinding.templateOwners, scopedTemplateSource, letNode,
      templateBinder, templateRequirement]
  · intro requirement member
    have requirement_eq : requirement = templateInputRequirement := by
      simpa [templateSolverState] using member
    subst requirement
    constructor
    · intro _
      exact sourceLocalSchemeTemplateIds_mem_iff.mpr
        ⟨scopedTemplateOwner, templateOwnerContained, rfl⟩
    · intro _
      simp [templateInputRequirement, templateSolverState]
  · intro id member
    simp [sourceLocalSchemeTemplateIds, localSchemeTemplateOwners,
      initializedLetBindings, statementInitializedLetBindings,
      InitializedLetBinding.templateOwners, scopedTemplateSource, letNode,
      templateBinder, templateRequirement, templateSolverState] at member ⊢
    exact member
  · intro requirement member template
    have requirement_eq : requirement = templateInputRequirement := by
      simpa [templateSolverState] using member
    subst requirement
    simpa [templateInputRequirement, templateSolverState,
      SourceInference.Detail.applyPredicate, SourceInference.State.initial,
      TypedTraitResolution.applySubstitution] using
      (LocalSchemeTemplateRowScoped.intro scopedTemplateOwner
        templateOwnerContained rfl rfl rfl (.expression (expressionId 0))
        templateOccursAtInitializer
        (scopedTemplateOwner.scopes_initializer templateOwnerContained))
  · rfl

/-- A template assumption attached at the root of its exact initializer is a
valid scoped ledger entry even though it is not a declaration assumption. -/
theorem initializerRootTemplateAccepted :
    ScopedRequirementLedgerWellFormed templateContext
      scopedTemplateSource := by
  refine {
    idsUnique := ?_
    templateOwnership := ?_
    entriesValid := ?_
    templatesComplete := ?_
  }
  · simp [RequirementIdsUnique, templateContext, templateRow,
      Context.withSolvedRequirements, Context.ofSignatures]
  · constructor
    simp [sourceLocalSchemeTemplateIds, localSchemeTemplateOwners,
      initializedLetBindings, statementInitializedLetBindings,
      InitializedLetBinding.templateOwners,
      scopedTemplateSource, letNode, templateBinder, templateRequirement]
  · intro row member
    have rowEq : row = templateRow := by
      simpa [templateContext, Context.withSolvedRequirements,
        Context.ofSignatures] using member
    subst row
    apply ScopedRequirementEntryValid.template
    exact .intro scopedTemplateOwner templateOwnerContained rfl rfl rfl
      (.expression (expressionId 0)) templateOccursAtInitializer
      (scopedTemplateOwner.scopes_initializer templateOwnerContained)
  · intro owner contains
    have ownerEq : owner = scopedTemplateOwner := by
      simpa [ContainsLocalSchemeTemplate, localSchemeTemplateOwners,
        initializedLetBindings, statementInitializedLetBindings,
        InitializedLetBinding.templateOwners,
        scopedTemplateSource, scopedTemplateOwner, letNode, templateBinder,
        templateRequirement] using contains
    subst owner
    exact ⟨templateRow, by
      simp [templateContext, Context.withSolvedRequirements,
        Context.ofSignatures], rfl⟩

/-- The scoped ledger recovers the exact singleton row needed by local-scheme
formation, not merely a row with the same identity. -/
example : ∃ row,
    templateContext.solvedRequirements.filter (fun candidate =>
      candidate.id == templateRequirement.templateRequirement) = [row] ∧
    row.id = templateRequirement.templateRequirement ∧
    row.predicate = templateRequirement.predicate ∧
    row.evidence = .assumption templateRequirement.predicate :=
  initializerRootTemplateAccepted.template_exact templateOwnerContained

private theorem templatePredicateAdmissible :
    PredicateAdmissible
      (localSchemeInitializerContext templateContext (templateBinder 0))
      templatePredicate := by
  refine {
    subject := ?_
    arguments := ?_
    trait := rfl
  }
  · refine {
      binders := ?_
      typeWellScoped := .variable ?_
    }
    · simp [TypeParameterBindersWellFormed, localSchemeInitializerContext,
        Context.withTypeVariables, Context.withAssumptions, templateContext,
        Context.withSolvedRequirements, Context.ofSignatures]
    · simp [admissibleTypeVariables, localSchemeInitializerContext,
        Context.withTypeVariables, Context.withAssumptions, templateContext,
        Context.withSolvedRequirements, Context.ofSignatures, templateBinder]
  · intro argument member
    simp [templatePredicate, ProgramSignatures.builtinIntPredicate] at member

/-- Source ownership plus the scoped ledger discharges the complete qualified
requirement formation judgment once predicate admissibility and quantified
dependency are supplied. -/
example : LocalSchemeRequirementsWellFormed templateContext
    (templateBinder 0) := by
  apply initializerRootTemplateAccepted.localSchemeRequirementsWellFormed
    (initializer := .expression (expressionId 0))
  · intro requirement member
    have requirementEq : requirement = templateRequirement := by
      simpa [templateBinder] using member
    subst requirement
    exact templateOwnerContained
  · intro requirement member
    have requirementEq : requirement = templateRequirement := by
      simpa [templateBinder] using member
    subst requirement
    exact templatePredicateAdmissible
  · intro requirement member
    have requirementEq : requirement = templateRequirement := by
      simpa [templateBinder] using member
    subst requirement
    exact ⟨templateVariable, by simp [templateBinder], by
      simp [templateRequirement, templatePredicate,
        ProgramSignatures.builtinIntPredicate,
        TypedTraitResolution.predicateVariables, Ty.freeVariables]⟩

private theorem assumptionRowInvalid
    (context : SourceSemantics.Context) (row : SolvedRequirement)
    (evidenceEq : row.evidence = .assumption row.predicate)
    (absent : row.predicate ∉ context.assumptions) :
    ¬ SolvedRequirementValid context row := by
  intro valid
  cases valid with
  | intro retainedValid =>
      cases retainedValid with
      | intro represents semanticValid =>
          rw [evidenceEq] at represents
          cases represents with
          | assumption =>
              cases semanticValid with
              | assumption member => exact absent member

/-- An assumption row without a source local-scheme owner cannot acquire
initializer scope merely by being attached to an expression. -/
theorem orphanTemplateAssumptionRejected :
    ¬ ScopedRequirementLedgerWellFormed orphanContext orphanSource := by
  intro wellFormed
  have member : templateRow ∈ orphanContext.solvedRequirements := by
    simp [orphanContext, templateContext, Context.withSolvedRequirements,
      Context.ofSignatures]
  have notTemplate : templateRow.id ∉
      sourceLocalSchemeTemplateIds orphanSource := by
    simp [sourceLocalSchemeTemplateIds, localSchemeTemplateOwners,
      initializedLetBindings, orphanSource]
  have valid := wellFormed.ordinary_valid member notTemplate
  exact assumptionRowInvalid orphanContext templateRow rfl (by
    simp [orphanContext, templateContext, Context.withSolvedRequirements,
      Context.ofSignatures]) valid

/-- Two initialized local schemes cannot claim the same template identity,
even when the flat solved ledger itself contains only one row. -/
theorem duplicateTemplateOwnersRejected :
    ¬ ScopedRequirementLedgerWellFormed templateContext
      duplicateOwnerSource := by
  intro wellFormed
  have unique := wellFormed.templateOwnership.ids_unique
  simp [sourceLocalSchemeTemplateIds, localSchemeTemplateOwners,
    initializedLetBindings, statementInitializedLetBindings,
    InitializedLetBinding.templateOwners,
    duplicateOwnerSource, letNode, templateBinder, templateRequirement]
    at unique

private theorem initializerHasNoChildren
    (child : NodeId) :
    ¬ DirectChild wrongScopeSource (.expression (expressionId 0)) child := by
  rintro ⟨node, contains, childMem⟩
  rcases contains with ⟨nodeMem, nodeId⟩
  simp [wrongScopeSource, expressionNode, letNode] at nodeMem
  rcases nodeMem with rfl | rfl | rfl
  · simp [nodeChildIds, Node.references, ExpressionForm.references]
      at childMem
  · simp [Node.id, statementId, expressionId] at nodeId
  · simp [Node.id, expressionId] at nodeId

private theorem outsideNotInInitializer :
    ¬ InReflexiveSubtree wrongScopeSource
      (.expression (expressionId 0)) (.expression (expressionId 2)) := by
  rintro (same | descends)
  · simp [expressionId] at same
  · cases descends with
    | direct edge => exact initializerHasNoChildren _ edge
    | step edge _ => exact initializerHasNoChildren _ edge

/-- A source-owned template row is rejected when its sole primary attachment
is outside the owning initializer subtree. -/
theorem templateUseOutsideInitializerRejected :
    ¬ ScopedRequirementLedgerWellFormed templateContext wrongScopeSource := by
  intro wellFormed
  have member : templateRow ∈ templateContext.solvedRequirements := by
    simp [templateContext, Context.withSolvedRequirements,
      Context.ofSignatures]
  have templateMem : templateRow.id ∈
      sourceLocalSchemeTemplateIds wrongScopeSource := by
    simp [sourceLocalSchemeTemplateIds, localSchemeTemplateOwners,
      initializedLetBindings, statementInitializedLetBindings,
      InitializedLetBinding.templateOwners,
      wrongScopeSource, letNode, templateBinder, templateRequirement,
      templateRow]
  have rowScoped := wellFormed.template_scoped member templateMem
  rcases rowScoped.exact_owner with
    ⟨owner, occurrence, contains, _, _, _, occurs, inScope⟩
  have ownerEq : owner = {
      binder := templateBinder 0
      initializer := .expression (expressionId 0)
      requirement := templateRequirement
    } := by
    simpa [ContainsLocalSchemeTemplate, localSchemeTemplateOwners,
      initializedLetBindings, statementInitializedLetBindings,
      InitializedLetBinding.templateOwners,
      wrongScopeSource, letNode, templateBinder, templateRequirement] using
      contains
  subst owner
  have occurrenceEq : occurrence = .expression (expressionId 2) := by
    simpa [PrimaryRequirementOccursAt, primaryRequirementOccurrences,
      nodePrimaryRequirementOccurrences,
      expressionPrimaryRequirementOccurrences,
      statementPrimaryRequirementOccurrences, statementPrimaryRequirementIds,
      wrongScopeSource,
      expressionNode, letNode, templateRow] using occurs
  subst occurrence
  exact outsideNotInInitializer inScope.2

/-- A non-template assumption row remains invalid when its predicate is absent
from the declaration assumption context. -/
theorem ordinaryAssumptionWithoutDeclarationRejected :
    ¬ ScopedRequirementLedgerWellFormed ordinaryContextWithoutAssumption
      ordinarySource := by
  intro wellFormed
  have member : ordinaryRow ∈
      ordinaryContextWithoutAssumption.solvedRequirements := by
    simp [ordinaryContextWithoutAssumption, Context.withSolvedRequirements,
      Context.ofSignatures]
  have notTemplate : ordinaryRow.id ∉
      sourceLocalSchemeTemplateIds ordinarySource := by
    simp [sourceLocalSchemeTemplateIds, localSchemeTemplateOwners,
      initializedLetBindings, ordinarySource]
  have valid := wellFormed.ordinary_valid member notTemplate
  exact assumptionRowInvalid ordinaryContextWithoutAssumption ordinaryRow rfl
    (by simp [ordinaryContextWithoutAssumption,
      Context.withSolvedRequirements, Context.ofSignatures]) valid

/-- Declaration-wide assumption evidence is still accepted through the
ordinary branch when its predicate is explicitly present. -/
theorem ordinaryDeclarationAssumptionAccepted :
    ScopedRequirementLedgerWellFormed ordinaryContextWithAssumption
      ordinarySource := by
  apply ScopedRequirementLedgerWellFormed.ofRequirementLedger
  · constructor
    · simp [RequirementIdsUnique, ordinaryContextWithAssumption,
        Context.withSolvedRequirements, Context.withAssumptions,
        Context.ofSignatures]
    · intro row member
      have rowEq : row = ordinaryRow := by
        simpa [ordinaryContextWithAssumption, Context.withSolvedRequirements,
          Context.withAssumptions, Context.ofSignatures] using member
      subst row
      unfold ordinaryRow
      apply SolvedRequirementValid.intro
      apply RetainedEvidenceValid.intro (.assumption ordinaryPredicate)
      exact .assumption (by
        simp [ordinaryContextWithAssumption, Context.withSolvedRequirements,
          Context.withAssumptions, Context.ofSignatures])
  · simp [sourceLocalSchemeTemplateIds, localSchemeTemplateOwners,
      initializedLetBindings, ordinarySource]

private theorem ordinaryRequirementOwnership :
    RequirementOwnership ordinaryContextWithAssumption ordinarySource := by
  constructor <;>
    simp [primaryRequirementIds, statementPrimaryRequirementIds,
      ordinaryContextWithAssumption, Context.withSolvedRequirements,
      Context.withAssumptions, Context.ofSignatures, ordinarySource,
      expressionNode, ordinaryRow]

private theorem ordinaryExpressionContained :
    ContainsExpression ordinarySource (expressionId 0)
      (expressionNode 0 [ordinaryId]) := by
  simp [ContainsExpression, ordinarySource, expressionNode]

private theorem ordinaryRootsHaveNoParent :
    RootsHaveNoParent ordinarySource := by
  intro root parent rootMem edge
  rcases edge with ⟨node, contains, childMem⟩
  have nodeEq : node = .expression (expressionNode 0 [ordinaryId]) := by
    simpa [ordinarySource] using contains.1
  subst node
  simp [nodeChildIds, Node.references, expressionNode,
    ExpressionForm.references] at childMem

private theorem ordinaryRootScopeCovered :
    TemplateScopeCovered ordinarySource ordinaryContextWithAssumption
      (.expression (expressionId 0)) :=
  TemplateScopeCovered.root ordinaryRootsHaveNoParent (by
    simp [ordinarySource])

/-- The occurrence-sensitive bridge retains the ordinary ledger branch when
the active context is the declaration context itself. -/
example : RequirementValid ordinaryContextWithAssumption ordinaryId := by
  apply ordinaryDeclarationAssumptionAccepted.requirementValidAt
    ordinaryRequirementOwnership rfl rfl (fun _ member => member)
    ordinaryRootScopeCovered
  exact ordinaryExpressionContained.primaryRequirementOccursAt
    (by simp [expressionNode])

private theorem scopedTemplateRequirementOwnership :
    RequirementOwnership templateContext scopedTemplateSource := by
  constructor <;>
    simp [primaryRequirementIds, statementPrimaryRequirementIds,
      templateContext, Context.withSolvedRequirements, Context.ofSignatures,
      scopedTemplateSource, expressionNode, letNode, templateRow]

/-- The concrete initialized-let fixture has no incoming edge to its statement
root. -/
private theorem scopedTemplateRootsHaveNoParent :
    RootsHaveNoParent scopedTemplateSource := by
  intro root parent rootMem edge
  have rootEq : root = .statement (statementId 1) := by
    simpa [scopedTemplateSource] using rootMem
  subst root
  rcases edge with ⟨node, contains, childMem⟩
  have nodeCases :
      node = .expression (expressionNode 0 [templateId]) ∨
        node = .statement (letNode 1 0 0) := by
    simpa [scopedTemplateSource] using contains.1
  rcases nodeCases with rfl | rfl <;>
    simp [nodeChildIds, Node.references, expressionNode, letNode,
      ExpressionForm.references, StatementForm.references] at childMem

/-- The initializer occurrence in the fixture has the retained let statement
as its only possible parent. -/
private theorem scopedTemplateChildHasUniqueParent :
    ChildHasUniqueParent scopedTemplateSource := by
  have parentEq : ∀ {parent child},
      DirectChild scopedTemplateSource parent child →
      parent = .statement (statementId 1) := by
    intro parent child edge
    rcases edge with ⟨node, contains, childMem⟩
    have nodeCases :
        node = .expression (expressionNode 0 [templateId]) ∨
          node = .statement (letNode 1 0 0) := by
      simpa [scopedTemplateSource] using contains.1
    rcases nodeCases with rfl | rfl
    · simp [nodeChildIds, Node.references, expressionNode,
        ExpressionForm.references] at childMem
    · simpa [Node.id, letNode] using contains.2.symm
  intro left right child leftEdge rightEdge
  exact (parentEq leftEdge).trans (parentEq rightEdge).symm

private theorem scopedTemplateInitializerEdge :
    DirectChild scopedTemplateSource (.statement (statementId 1))
      (.expression (expressionId 0)) := by
  refine ⟨.statement (letNode 1 0 0), ?_, ?_⟩
  · exact ⟨by simp [scopedTemplateSource], rfl⟩
  · simp [nodeChildIds, Node.references, letNode, StatementForm.references]

private theorem scopedTemplateParentCovered :
    TemplateScopeCovered scopedTemplateSource templateContext
      (.statement (statementId 1)) :=
  TemplateScopeCovered.root scopedTemplateRootsHaveNoParent (by
    simp [scopedTemplateSource])

private theorem templateInitializerScopeCovered :
    TemplateScopeCovered scopedTemplateSource
      (localSchemeInitializerContext templateContext (templateBinder 0))
      (.expression (expressionId 0)) := by
  apply TemplateScopeCovered.localSchemeInitializer_of_newRoots
    scopedTemplateParentCovered scopedTemplateChildHasUniqueParent
    scopedTemplateInitializerEdge
  intro owner contains initializerEq
  have ownerEq : owner = scopedTemplateOwner := by
    simpa [ContainsLocalSchemeTemplate, localSchemeTemplateOwners,
      initializedLetBindings, statementInitializedLetBindings,
      InitializedLetBinding.templateOwners, scopedTemplateSource,
      scopedTemplateOwner, letNode, templateBinder, templateRequirement] using
      contains
  subst owner
  simp [scopedTemplateOwner, templateBinder, templateRequirement]

private def groupExpressionNode (index innerIndex : Nat) : ExpressionNode := {
  id := expressionId index
  span := testSpan
  type := .variable templateVariable
  form := .group (expressionId innerIndex)
}

/-- A two-level initializer fixture separates entry into a new template root
from ordinary descent within that already covered initializer. -/
private def nestedTemplateSource : TypedSource := {
  owner := testOwner
  inputs := []
  roots := [.statement (statementId 2)]
  nodes := [
    .expression (expressionNode 0 []),
    .expression (groupExpressionNode 1 0),
    .statement (letNode 2 0 1)
  ]
}

private def nestedTemplateOwner : LocalSchemeTemplateOwner := {
  binder := templateBinder 0
  initializer := .expression (expressionId 1)
  requirement := templateRequirement
}

private theorem nestedTemplateParentCovered :
    TemplateScopeCovered nestedTemplateSource
      (localSchemeInitializerContext templateContext (templateBinder 0))
      (.expression (expressionId 1)) := by
  intro owner scopes
  have ownerEq : owner = nestedTemplateOwner := by
    simpa [ContainsLocalSchemeTemplate, localSchemeTemplateOwners,
      initializedLetBindings, statementInitializedLetBindings,
      InitializedLetBinding.templateOwners, nestedTemplateSource,
      nestedTemplateOwner, letNode, templateBinder, templateRequirement] using
      scopes.1
  subst owner
  simp [localSchemeInitializerContext, Context.withTypeVariables,
    Context.withAssumptions, templateContext, Context.withSolvedRequirements,
    Context.ofSignatures, nestedTemplateOwner, templateBinder,
    templateRequirement]

private theorem nestedTemplateEdgeClassification
    {parent child : NodeId}
    (edge : DirectChild nestedTemplateSource parent child) :
    (parent = .expression (expressionId 1) ∧
        child = .expression (expressionId 0)) ∨
      (parent = .statement (statementId 2) ∧
        child = .expression (expressionId 1)) := by
  rcases edge with ⟨node, contains, childMem⟩
  have nodeCases :
      node = .expression (expressionNode 0 []) ∨
        node = .expression (groupExpressionNode 1 0) ∨
        node = .statement (letNode 2 0 1) := by
    simpa [nestedTemplateSource] using contains.1
  rcases nodeCases with rfl | rfl | rfl
  · simp [nodeChildIds, Node.references, expressionNode,
      ExpressionForm.references] at childMem
  · exact Or.inl ⟨by
      simpa [Node.id, groupExpressionNode] using contains.2.symm, by
      simpa [nodeChildIds, Node.references, groupExpressionNode,
        ExpressionForm.references] using childMem⟩
  · exact Or.inr ⟨by
      simpa [Node.id, letNode] using contains.2.symm, by
      simpa [nodeChildIds, Node.references, letNode,
        StatementForm.references] using childMem⟩

private theorem nestedTemplateChildHasUniqueParent :
    ChildHasUniqueParent nestedTemplateSource := by
  intro left right child leftEdge rightEdge
  rcases nestedTemplateEdgeClassification leftEdge with
    ⟨leftParent, leftChild⟩ | ⟨leftParent, leftChild⟩
  · rcases nestedTemplateEdgeClassification rightEdge with
      ⟨rightParent, rightChild⟩ | ⟨rightParent, rightChild⟩
    · exact leftParent.trans rightParent.symm
    · exfalso
      have childEq := leftChild.symm.trans rightChild
      simp [expressionId] at childEq
  · rcases nestedTemplateEdgeClassification rightEdge with
      ⟨rightParent, rightChild⟩ | ⟨rightParent, rightChild⟩
    · exfalso
      have childEq := leftChild.symm.trans rightChild
      simp [expressionId] at childEq
    · exact leftParent.trans rightParent.symm

private theorem nestedTemplateInnerEdge :
    DirectChild nestedTemplateSource (.expression (expressionId 1))
      (.expression (expressionId 0)) := by
  refine ⟨.expression (groupExpressionNode 1 0), ?_, ?_⟩
  · exact ⟨by simp [nestedTemplateSource], rfl⟩
  · simp [nodeChildIds, Node.references, groupExpressionNode,
      ExpressionForm.references]

/-- Ordinary descent inside an initializer inherits the parent's template
coverage without adding another assumption. -/
example : TemplateScopeCovered nestedTemplateSource
    (localSchemeInitializerContext templateContext (templateBinder 0))
    (.expression (expressionId 0)) := by
  apply TemplateScopeCovered.child nestedTemplateParentCovered
    nestedTemplateChildHasUniqueParent nestedTemplateInnerEdge
    (fun _ member => member)
  intro owner contains initializerEq
  have ownerEq : owner = nestedTemplateOwner := by
    simpa [ContainsLocalSchemeTemplate, localSchemeTemplateOwners,
      initializedLetBindings, statementInitializedLetBindings,
      InitializedLetBinding.templateOwners, nestedTemplateSource,
      nestedTemplateOwner, letNode, templateBinder, templateRequirement] using
      contains
  subst owner
  simp [nestedTemplateOwner, expressionId] at initializerEq

/-- The same bridge accepts a template row only inside its covered
initializer context, where the retained assumption evidence is active. -/
example : RequirementIdsValid
    (localSchemeInitializerContext templateContext (templateBinder 0))
    [templateId] := by
  apply initializerRootTemplateAccepted.requirementIdsValidAt
    (active := localSchemeInitializerContext templateContext (templateBinder 0))
    (occurrence := .expression (expressionId 0))
    (ids := [templateId])
    scopedTemplateRequirementOwnership rfl rfl
  · intro predicate member
    simp [templateContext, Context.withSolvedRequirements,
      Context.ofSignatures] at member
  · exact templateInitializerScopeCovered
  · intro id member
    have idEq : id = templateId := by simpa using member
    subst id
    exact templateOccursAtInitializer

/-- Solving a qualified-local template preserves its exact normalized
predicate and source order at the covered initializer occurrence; no global
`SolvedRequirementsValid` premise is needed for the assumption row. -/
example : RequirementSequenceProves
    (localSchemeInitializerContext templateContext (templateBinder 0))
    [templateId] [templatePredicate] := by
  have corresponds : RequirementPredicatesCorrespond
      [templateInputRequirement] [templatePredicate] [templateId] := by
    apply RequirementPredicatesCorrespond.cons
    · simp [templateInputRequirement]
    · exact .nil
  have proves :=
    SourceInferenceSoundness.solveRequirements_correspondingSequenceProvesAt
      (inferenceContext := templateInferenceContext)
      (state := templateSolverState)
      (requirements := [templateInputRequirement])
      (solved := [templateRow])
      (base := templateContext)
      (active := localSchemeInitializerContext templateContext
        (templateBinder 0))
      (source := scopedTemplateSource)
      (occurrence := .expression (expressionId 0))
      corresponds rfl rfl initializerRootTemplateAccepted
      scopedTemplateRequirementOwnership rfl rfl
      (by
        intro predicate member
        simp [templateContext, Context.withSolvedRequirements,
          Context.ofSignatures] at member)
      templateInitializerScopeCovered
      (by
        intro id member
        have idEq : id = templateId := by simpa using member
        subst id
        exact templateOccursAtInitializer)
  simpa [SourceInference.Detail.applyPredicate, templateSolverState,
    SourceInference.State.initial, TypeSystem.InferState.initial,
    predicate_apply_empty] using proves

end Solcore.Test.SourceSemanticsScopedRequirements
end

section
-- leanmerge: from Solcore.Test.SourceSemanticsStaticValidation
/-! Focused executable tests for source-level type-formation validation. -/

set_option autoImplicit false

namespace Solcore.Test.SourceSemanticsStaticValidation

open Frontend
open SourceSemantics
open TypeSystem

private def emptySignatures : ProgramSignatures := {
  functions := []
  implRules := []
  traits := []
  implementations := []
  dataTypes := []
  contracts := []
}

private def emptyContext : Context :=
  Context.ofSignatures emptySignatures

private def flexible : TypeVarId := ⟨0⟩

/-- Explicitly opened flexible variables are accepted. -/
example :
    validateTypeWellScoped emptyContext [flexible] (.variable flexible) =
      .ok () := by
  rfl

/-- Residual admission accepts a retained open occurrence type. -/
example :
    validateTypeAdmissible emptyContext.withResidualTypeVariables
        (.variable flexible) = .ok () := by
  rfl

private def testModule : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"source_semantics_static_validation", by decide⟩], by decide⟩⟩

private def contractOwner : Resolved.DeclarationId :=
  ⟨testModule, 0⟩

private def unknownOwner : Resolved.DeclarationId :=
  ⟨testModule, 1⟩

private def sourceId : Syntax.SourceId := {
  origin := .main
  path := "source_semantics_static_validation.sol"
}

private def sourceSpan : Syntax.SourceSpan := {
  source := sourceId
  startByte := 0
  endByte := 0
}

private def contractSyntax : Syntax.ContractDecl := {
  span := sourceSpan
  value := {
    name := ⟨sourceSpan, "Box"⟩
    genericParameters := some
      ⟨sourceSpan, ⟨⟨sourceSpan, "T"⟩, []⟩⟩
    bodySpan := sourceSpan
    members := []
  }
}

private def contractSignature : ProgramContractSignature := {
  id := contractOwner
  name := "Box"
  parameters := [{ owner := contractOwner, index := 0 }]
  source := contractSyntax
}

private def nominalSignatures : ProgramSignatures := {
  functions := []
  implRules := []
  traits := []
  implementations := []
  dataTypes := []
  contracts := [contractSignature]
}

private def nominalContext : Context :=
  Context.ofSignatures nominalSignatures

/-- A cataloged nominal at its declared arity is accepted. -/
example :
    validateTypeWellScoped nominalContext []
        (Ty.nominal contractOwner [.word]) = .ok () := by
  rfl

/-- A cataloged nominal at the wrong arity is rejected precisely. -/
example :
    validateTypeWellScoped nominalContext [] (Ty.nominal contractOwner []) =
      .error (.nominalArityMismatch contractOwner 1 0) := by
  rfl

/-- A declaration absent from both nominal catalogs is rejected. -/
example :
    validateTypeWellScoped nominalContext [] (Ty.nominal unknownOwner []) =
      .error (.unknownNominal unknownOwner) := by
  rfl

private def duplicateScheme : Scheme := {
  quantified := [flexible, flexible]
  body := .variable flexible
}

/-- Duplicate quantified variables are rejected before body validation. -/
example :
    validateSchemeWellFormed emptyContext duplicateScheme =
      .error .duplicateSchemeVariables := by
  rfl

private def underGeneralizedScheme : Scheme := {
  quantified := []
  body := .variable flexible
}

/-- Exact generalization rejects a scheme that omits a generalizable variable. -/
example :
    validateSchemeGeneralizes emptyContext underGeneralizedScheme =
      .error .schemeGeneralizationMismatch := by
  rfl

private def generalizedScheme : Scheme := {
  quantified := [flexible]
  body := .variable flexible
}

/-- Exact generalization accepts the stable free-variable order. -/
example :
    validateSchemeGeneralizes emptyContext generalizedScheme = .ok () := by
  rfl

end Solcore.Test.SourceSemanticsStaticValidation
end
