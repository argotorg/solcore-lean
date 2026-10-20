import Solcore.SourceSemantics.SourceCompiledBodySelectionFormation
import Solcore.SourceSemantics.SourceInferenceGeneralizedLambdaPrefix
import Solcore.SourceSemantics.SourceCompiledGeneralizedStatementsContracts
import Solcore.SourceSemantics.SourceInferenceSelectedOrdinaryRecorder
import Solcore.SourceSemantics.SourceInferenceSelectedChildSoundness

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend Frontend.SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization

private theorem bindLambdaParameters_owner_eq
    {inferenceContext : Frontend.SourceInference.Context}
    {parameters : List Syntax.LambdaParameter}
    {index : Nat} {seen : List String}
    {state : Frontend.SourceInference.State}
    {result : List TypedBinder × List TypeSystem.Ty ×
      Frontend.SourceInference.State}
    (success : Detail.bindLambdaParameters inferenceContext parameters index
      seen state = .ok result) :
    result.2.2.owner = state.owner := by
  induction parameters generalizing index seen state result with
  | nil =>
      simp only [Detail.bindLambdaParameters] at success
      injection success with resultEq
      subst result
      rfl
  | cons parameter rest induction =>
      cases parameterValue : parameter.value with
      | error =>
          simp [Detail.bindLambdaParameters, parameterValue, bind,
            Except.bind] at success
      | inferred name =>
          simp only [Detail.bindLambdaParameters, parameterValue] at success
          simp only [bind, Except.bind] at success
          repeat' first | split at success
          all_goals try simp_all
          all_goals
            subst result
            subst_vars
            have tailOwner := induction _ _ _ (by assumption)
            exact tailOwner.trans (by
              simp_all [Frontend.SourceInference.State.fresh,
                Frontend.SourceInference.State.allocateBinder])
      | typed marker name sourceType =>
          simp only [Detail.bindLambdaParameters, parameterValue] at success
          cases typeResult : Detail.resolveSourceType inferenceContext
              sourceType with
          | error error =>
              simp [typeResult, bind, Except.bind] at success
          | ok type =>
              simp only [typeResult, bind, Except.bind] at success
              repeat' first | split at success
              all_goals try simp_all
              all_goals
                subst result
                subst_vars
                have tailOwner := induction _ _ _ (by assumption)
                exact tailOwner.trans (by
                  simp_all [Frontend.SourceInference.State.allocateBinder])

private theorem lambdaPrefixFacts_owner_eq
    {inferenceContext : Frontend.SourceInference.Context}
    {expected : Option TypeSystem.Ty}
    {returnAnnotation : Option Syntax.TypeExpr}
    {parameterTypes : List TypeSystem.Ty}
    {parameterState resultState : Frontend.SourceInference.State}
    {resultType : TypeSystem.Ty}
    (facts : Detail.LambdaPrefixFacts inferenceContext expected
      returnAnnotation parameterTypes parameterState resultType resultState) :
    resultState.owner = parameterState.owner := by
  cases facts with
  | noExpectedPartsAnnotated => rfl
  | noExpectedPartsFresh _ _ freshEq =>
      have finalEq : parameterState.fresh.2 = resultState :=
        congrArg Prod.snd freshEq
      rw [← finalEq]
      rfl
  | expectedPartsAnnotated _ parameterUnify =>
      exact congrArg (fun header : Frontend.SourceInference.State.Header =>
        header.owner) (Detail.unify_state_header parameterUnify)
  | expectedPartsInferred _ parameterUnify =>
      exact congrArg (fun header : Frontend.SourceInference.State.Header =>
        header.owner) (Detail.unify_state_header parameterUnify)

private theorem monoBinders_ambientFields
    {owner : Resolved.DeclarationId} {context final : SourceSemantics.Context}
    {binders : List TypedBinder} {types : List Ty}
    (extension : MonoBindersExtend owner context binders types final) :
    final.signatures = context.signatures ∧ final.typeParameters = context.typeParameters ∧
      final.currentDeclaration = context.currentDeclaration ∧
      final.residualTypeVariables = context.residualTypeVariables ∧
      final.solvedRequirements = context.solvedRequirements ∧ final.assumptions = context.assumptions := by
  induction extension with
  | nil => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | cons _ head _ induction =>
    cases head
    exact induction

theorem expressionRetained_lambda
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {inferenceContext : SourceInference.Context} {expression : Syntax.Expr} {keyword : Syntax.SourceSpan}
    {sourceParameters : Syntax.DelimitedList Syntax.LambdaParameter}
    {returnAnnotation : Option Syntax.TypeExpr} {body : Syntax.Block} {expected : Option Ty}
    {initial resultState : State} {inferred : InferredExpression}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (expressionEq : expression.value = .lambda keyword sourceParameters returnAnnotation body)
    (boundary : RetainedExpressionBoundary selected (childFuel + 1) inferenceContext
      expression expected initial inferred resultState frames target)
    (bodySound : ∀ {expectedReturn : Ty} {entry : State} {result : Detail.BlockResult}
        {lambdaTarget : SourceSemantics.Context},
      (∀ binder ∈ entry.localBinders,
        ProtectedVariables.Safe binder.scheme.quantified entry expectedReturn) →
      TypeAdmissible lambdaTarget (selected.body.finalized.substitution.apply expectedReturn) →
      StatementsBoundary selected childFuel { inferenceContext with loopDepth := 0 }
        body.value expectedReturn entry result frames lambdaTarget →
      StatementsConclusion selected { inferenceContext with loopDepth := 0 }
        expectedReturn result frames lambdaTarget) :
    ExpressionTypingBase (resultState.toTypedSource (bodyRoots selected))
      selected.body.finalized.typedSource target selected.body.finalized.substitution inferred := by
  let wholeContext := checkingContext selected
  let finalized := selected.body.finalized
  let roots := bodyRoots selected
  let evidenceState := selected.body.returned
  let semanticSource := selected.body.finalized.typedSource
  let semanticContext := target
  have resources := selected.body.resources
  have interfaces := boundary.interfaces
  have resultSubstitutionExtension := boundary.extension
  have signaturesEq := boundary.scope.signatures
  have ownerEq := boundary.scope.owner
  have typeParametersEq := boundary.scope.parameters
  have signatureFormation := boundary.scope.formation checked
  have functionsCanonical := boundary.scope.functionsCanonical checked
  have catalog := boundary.scope.catalog checked
  have canonical := boundary.scope.canonical checked
  have integerPatternsSubset := boundary.integerPatterns
  have integerLiteralsSubset := boundary.integerLiterals
  have requirementsSubset := boundary.requirements
  have covered := boundary.covered
  have invariant := boundary.invariant
  have expectedBelow := boundary.expectedBelow
  have success := boundary.accepted
  have expectedAdmissible := boundary.expectedAdmissible
  have actual := boundary.actual
  have semanticPreserved := boundary.proper
  have rawProper := boundary.rawProper
  have actualCovered := boundary.actualCovered
  generalize allocationEq : initial.allocateExpressionId = allocatedPair
  rcases allocatedPair with ⟨id, allocated⟩
  have allocatedInvariant := invariant.allocateExpressionId allocationEq
  have allocatedOperational : GeneralizedActualStateInvariant allocated (evidenceSource selected) := by
    rw [← show initial.allocateExpressionId.2 = allocated from congrArg Prod.snd allocationEq]
    exact boundary.operational.allocateExpressionId
  have activeBinders := invariant.typeParameterBinders (by simpa [ownerEq, typeParametersEq] using canonical)
  have activeSignaturesEq := invariant.signatures_eq_whole.trans signaturesEq.symm
  have activeParametersEq := invariant.typeParametersEq.trans typeParametersEq.symm
  have activeOwnerEq : semanticContext.currentDeclaration = some inferenceContext.scope.genericOwner := by
    rw [ownerEq]; exact invariant.declarationEq
  have activeRange := resources.substitutionRangeAdmissible activeBinders
    invariant.signatures_eq_whole invariant.typeParametersEq invariant.declarationEq invariant.residual
  obtain ⟨boundParameters, parameterTypes, parameterState, resultType,
      prefixState, bodyResult, unifiedState, restoredState, parametersSuccess,
      prefixFacts, bodySuccess, unifySuccess, restoredEq, recordSuccess⟩ :=
    Detail.inferExprFuel_success_lambda_facts expressionEq allocationEq success
  have allocationProgress : initial.InferenceProgress allocated := by
    have progress :=
      Frontend.SourceInference.State.InferenceProgress.allocateExpressionId
        initial invariant.ready.solved
    rw [allocationEq] at progress
    exact progress
  have allocatedReady : allocated.InferenceReady := by
    have nextReady :=
      Frontend.SourceInference.State.InferenceReady.allocateExpressionId invariant.ready
    rw [allocationEq] at nextReady
    exact nextReady
  have parameterProperties :=
    Detail.bindLambdaParameters_inferenceProperties allocatedReady
      parametersSuccess
  have parameterTypeBelow :
      (TypeSystem.Ty.productMany parameterTypes).VariablesBelow
        parameterState.inference.next :=
    TypeSystem.Ty.variablesBelow_productMany parameterProperties.2.2
  have expectedAtParameter : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow parameterState.inference.next := by
    intro expectedType member
    exact (expectedBelow expectedType member).weaken
      (allocationProgress.trans parameterProperties.1).next_le
  have prefixProperties := lambdaPrefixFacts_inferenceProperties prefixFacts
    parameterProperties.2.1 parameterTypeBelow expectedAtParameter
  have lambdaSignatureFormation : ProgramSignatureFormationValidated
      ({ inferenceContext with loopDepth := 0 } :
        Frontend.SourceInference.Context).signatures := by
    simpa using signatureFormation
  have lambdaFunctionsCanonical : ∀ signature ∈
      ({ inferenceContext with loopDepth := 0 } :
        Frontend.SourceInference.Context).signatures.functions,
      signature.scheme.body = .function
        (TypeSystem.Ty.productMany signature.parameterTypes)
        (TypeSystem.Ty.productMany signature.returnTypes) := by
    simpa using functionsCanonical
  have bodyProperties := Detail.inferStatementsFuel_inferenceProperties
    (context := { inferenceContext with loopDepth := 0 })
    prefixProperties.2.1 lambdaSignatureFormation lambdaFunctionsCanonical
      prefixProperties.2.2 bodySuccess
  have resultAtBody : resultType.VariablesBelow
      bodyResult.state.inference.next :=
    prefixProperties.2.2.weaken bodyProperties.1.next_le
  have unifiedProgress := Detail.unify_inferenceProgress
    bodyProperties.2.1.solved bodyProperties.2.2 resultAtBody unifySuccess
  have unifiedReady := Detail.unify_preserves_inferenceReady
    bodyProperties.2.1 bodyProperties.2.2 resultAtBody unifySuccess
  have restoreStep : unifiedState.InferenceProgress restoredState := by
    rw [restoredEq]
    exact Frontend.SourceInference.State.InferenceProgress.restoreLexicalScope
      unifiedState allocated.lexicalScope unifiedReady.solved
  have throughUnified : allocated.InferenceProgress unifiedState :=
    parameterProperties.1.trans
      (prefixProperties.1.trans
        (bodyProperties.1.trans unifiedProgress))
  have restoredProperties : allocated.InferenceProgress restoredState ∧
      restoredState.InferenceReady := by
    rw [restoredEq]
    exact Frontend.SourceInference.State.restoreLexicalScope_inferenceProperties
      allocatedReady throughUnified
  have parameterToRestored :
      parameterState.InferenceProgress restoredState :=
    prefixProperties.1.trans
      (bodyProperties.1.trans (unifiedProgress.trans restoreStep))
  have resultToRestored : prefixState.InferenceProgress restoredState :=
    bodyProperties.1.trans (unifiedProgress.trans restoreStep)
  have resolvedParameterBelow :
      (restoredState.resolve
        (TypeSystem.Ty.productMany parameterTypes)).VariablesBelow
          restoredState.inference.next :=
    parameterToRestored.resolve_variablesBelow parameterTypeBelow
  have resolvedResultBelow :
      (restoredState.resolve resultType).VariablesBelow
        restoredState.inference.next :=
    resultToRestored.resolve_variablesBelow prefixProperties.2.2
  have functionBelow :
      (TypeSystem.Ty.function
        (restoredState.resolve (TypeSystem.Ty.productMany parameterTypes))
        (restoredState.resolve resultType)).VariablesBelow
          restoredState.inference.next :=
    (TypeSystem.Ty.variablesBelow_function_iff _ _ _).2
      ⟨resolvedParameterBelow, resolvedResultBelow⟩
  have expectedAtRestored : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow restoredState.inference.next := by
    intro expectedType member
    exact (expectedBelow expectedType member).weaken
      (allocationProgress.trans restoredProperties.1).next_le
  have recordProperties :=
    Detail.recordExpressionWithExpected_inferenceProperties
      restoredProperties.2 functionBelow expectedAtRestored recordSuccess
  have restoredExtension : finalized.substitution.SemanticallyExtends restoredState.inference.substitution :=
    resultSubstitutionExtension.trans recordProperties.1.substitution_extends
  have parameterExtension : finalized.substitution.SemanticallyExtends parameterState.inference.substitution :=
    restoredExtension.trans parameterToRestored.substitution_extends
  have parameterTypesAdmissible :=
    bindLambdaParameters_success_typesAdmissible_in_active
      parametersSuccess canonical activeBinders activeSignaturesEq activeParametersEq
      activeOwnerEq invariant.residual activeRange
  obtain ⟨lambdaContext, namesUnique, _, parametersExtend,
      parameterInvariant, parameterBindersBelow⟩ :=
    bindLambdaParameters_success_monoBindersExtend_afterSubstitution
      parametersSuccess allocatedInvariant.active allocatedInvariant.bindersBelow
      parameterTypesAdmissible
  have sourceOwner : semanticSource.owner = allocated.owner := by
    exact semanticPreserved.owner_eq.trans ((Detail.inferExprFuel_preserves_owner success).trans
      (congrArg (fun pair : ExpressionId × State => pair.2.owner) allocationEq))
  have parametersExtendSource : MonoBindersExtend semanticSource.owner semanticContext
      (boundParameters.map
        (TypedBinder.applySubstitution finalized.substitution))
      (parameterTypes.map finalized.substitution.apply)
      lambdaContext := by
    simpa only [sourceOwner] using parametersExtend
  have resultInvariant : ActiveLocalContextInvariant prefixState
      finalized.substitution lambdaContext :=
    lambdaPrefixFacts_activeLocalContextInvariant prefixFacts
      parameterInvariant
  have allocatedNodesBelow : allocated.NodesBelowNextOccurrence := by
    have preserved :=
      Frontend.SourceInference.State.allocateExpressionId_preserves_nodesBelowNextOccurrence
        initial invariant.nodesBelow
    have finalEq : initial.allocateExpressionId.2 = allocated :=
      congrArg Prod.snd allocationEq
    rwa [finalEq] at preserved
  have parameterNodesBelow : parameterState.NodesBelowNextOccurrence :=
    (Detail.bindLambdaParameters_occurrenceBoundExtends parametersSuccess
      ).nodesBelowNextOccurrence allocatedNodesBelow
  have resultNodesBelow : prefixState.NodesBelowNextOccurrence :=
    lambdaPrefixFacts_nodesBelowNextOccurrence prefixFacts parameterNodesBelow
  have resultBindersBelow : prefixState.LocalBindersBelowNextLocal :=
    lambdaPrefixFacts_localBindersBelowNextLocal prefixFacts
      parameterBindersBelow
  have allocatedOwner : allocated.owner = initial.owner := by
    have finalEq : initial.allocateExpressionId.2 = allocated :=
      congrArg Prod.snd allocationEq
    rw [← finalEq]
    rfl
  have parameterOwner : parameterState.owner = allocated.owner :=
    bindLambdaParameters_owner_eq parametersSuccess
  have prefixOwner : prefixState.owner = parameterState.owner :=
    lambdaPrefixFacts_owner_eq prefixFacts
  have bodyOwner : bodyResult.state.owner = prefixState.owner :=
    Detail.inferStatementsFuel_preserves_owner bodySuccess
  have bodyToResultRaw : TypingSourceExtends
      (bodyResult.state.toTypedSource roots)
      (resultState.toTypedSource roots) := by
    constructor
    · exact (Detail.inferExprFuel_preserves_owner success).trans
        (allocatedOwner.symm.trans
          (parameterOwner.symm.trans
            (prefixOwner.symm.trans bodyOwner.symm)))
    · have nodesPrefix :=
        recordExpressionWithExpected_success_nodesPrefix recordSuccess
      have unifyNodes := (Detail.unify_occurrenceState_eq unifySuccess).1
      rw [restoredEq,
        Frontend.SourceInference.State.restoreLexicalScope_nodes,
        unifyNodes] at nodesPrefix
      exact nodesPrefix
  have laterExtendsUnified : finalized.substitution.SemanticallyExtends
      unifiedState.inference.substitution := by
    have extendsRestored := restoredExtension
    rw [restoredEq] at extendsRestored
    exact extendsRestored
  have laterExtendsBody : finalized.substitution.SemanticallyExtends
      bodyResult.state.inference.substitution :=
    TypeSystem.Substitution.SemanticallyExtends.trans laterExtendsUnified
      unifiedProgress.substitution_extends
  have bodyIntegerPatternsToResult :
      bodyResult.state.integerPatterns ⊆ resultState.integerPatterns := by
    intro origin member
    rw [recordExpressionWithExpected_integerPatterns_eq recordSuccess,
      restoredEq]
    change origin ∈ unifiedState.integerPatterns
    rw [Detail.unify_integerPatterns unifySuccess]
    exact member
  have bodyIntegerLiteralsToResult :
      bodyResult.state.integerLiterals ⊆ resultState.integerLiterals := by
    intro origin member
    rw [Detail.recordExpressionWithExpected_integerLiterals_eq recordSuccess,
      restoredEq]
    change origin ∈ unifiedState.integerLiterals
    rw [Detail.unify_integerLiterals unifySuccess]
    exact member
  have bodyRequirementsToResult :
      bodyResult.state.requirements ⊆ resultState.requirements := by
    apply List.Subset.trans ?_
      (Detail.recordExpressionWithExpected_requirements_subset recordSuccess)
    rw [restoredEq]
    change bodyResult.state.requirements ⊆ unifiedState.requirements
    rw [Detail.unify_requirements_eq unifySuccess]
    exact fun _ member => member
  have bodyIntegerPatternsToEvidence :
      bodyResult.state.integerPatterns ⊆ evidenceState.integerPatterns :=
    List.Subset.trans bodyIntegerPatternsToResult integerPatternsSubset
  have bodyIntegerLiteralsToEvidence :
      bodyResult.state.integerLiterals ⊆ evidenceState.integerLiterals :=
    List.Subset.trans bodyIntegerLiteralsToResult integerLiteralsSubset
  have bodyRequirementsToEvidence :
      bodyResult.state.requirements ⊆ evidenceState.requirements :=
    List.Subset.trans bodyRequirementsToResult requirementsSubset
  obtain ⟨coercions, recordedContains⟩ :=
    recordExpressionWithExpected_success_containsExpression recordSuccess roots
  let lambdaNode : ExpressionNode := {
    id := inferred.id
    span := expression.span
    type := inferred.type
    form := .lambda boundParameters (restoredState.resolve resultType)
      bodyResult.statements
    requirements := [] ++ Detail.coercionRequirements coercions
    coercions
  }
  have containsLambda : ContainsExpression (resultState.toTypedSource roots)
      inferred.id lambdaNode := by
    simpa only [lambdaNode] using recordedContains
  have bodyEdge : ∀ statement ∈ bodyResult.statements,
      DirectChild (resultState.toTypedSource roots) (.expression inferred.id) (.statement statement) := by
    intro statement member
    refine ⟨.expression lambdaNode, ⟨containsLambda.1, congrArg NodeId.expression containsLambda.2⟩, ?_⟩
    simpa [lambdaNode, nodeChildIds, Node.references, ExpressionForm.references] using
      (List.mem_map.mpr ⟨statement, member, rfl⟩ : (.statement statement : NodeId) ∈ bodyResult.statements.map NodeId.statement)
  have bodyCovered : ∀ statement ∈ bodyResult.statements,
      TemplateScopeCovered finalized.typedSource lambdaContext (.statement statement) := by
    intro statement member
    apply TemplateScopeCovered.expressionStatementChild covered resources.graph_closed
      (boundary.directChildren (bodyEdge statement member))
    intro predicate predicateMember
    rw [MonoBindersExtend.assumptions_eq parametersExtendSource]
    exact predicateMember
  have parameterScope := bindLambdaParameters_preserves_generalizedScope allocatedReady
    allocatedOperational allocatedInvariant.schemeIsolation parametersSuccess
  have allocatedExpectedSafe : ∀ binder ∈ allocated.localBinders, ∀ type ∈ expected,
      ProtectedVariables.Safe binder.scheme.quantified allocated type := by
    rw [← show initial.allocateExpressionId.2 = allocated from congrArg Prod.snd allocationEq]
    exact boundary.expectedSafe
  have parameterPrivacy : ∀ binder ∈ parameterState.localBinders,
      ProtectedVariables.Safe binder.scheme.quantified parameterState (Ty.productMany parameterTypes) ∧
      (∀ type ∈ expected, ProtectedVariables.Safe binder.scheme.quantified parameterState type) := by
    intro binder member
    rcases bindLambdaParameters_quantified_origin parametersSuccess binder member with old | empty
    · have privateTypes := ProtectedVariables.bindLambdaParameters_private allocatedReady
        (allocatedOperational.quantifiersBelow binder old) (allocatedOperational.privacy binder old)
        parametersSuccess
      exact ⟨ProtectedVariables.safe_productMany _ _ _ privateTypes.2.1,
        fun type present => privateTypes.1 type (allocatedExpectedSafe binder old type present)⟩
    · rw [empty]
      simp [ProtectedVariables.Safe, ProtectedVariables.Avoids]
  have prefixScope := lambdaPrefixFacts_preserves_generalizedScope parameterProperties.2.1
    parameterScope.1 parameterScope.2 parameterTypeBelow
    (fun binder member => (parameterPrivacy binder member).1) expectedAtParameter
    (fun binder member => (parameterPrivacy binder member).2) prefixFacts
  have lambdaFields : lambdaContext.signatures = semanticContext.signatures ∧
      lambdaContext.typeParameters = semanticContext.typeParameters ∧
      lambdaContext.currentDeclaration = semanticContext.currentDeclaration ∧
      lambdaContext.residualTypeVariables = semanticContext.residualTypeVariables ∧
      lambdaContext.solvedRequirements = semanticContext.solvedRequirements ∧
      lambdaContext.assumptions = semanticContext.assumptions := monoBinders_ambientFields parametersExtend
  have prefixInvariant : RecursiveStatementInvariant wholeContext resultType finalized prefixState lambdaContext := {
    active := resultInvariant
    ready := prefixProperties.2.1
    returnBelow := prefixProperties.2.2
    bindersBelow := resultBindersBelow
    nodesBelow := resultNodesBelow
    schemeIsolation := prefixScope.2.1
    substitutionExtension := laterExtendsBody.trans bodyProperties.1.substitution_extends
    signaturesEq := lambdaFields.1.trans invariant.signaturesEq
    typeParametersEq := lambdaFields.2.1.trans invariant.typeParametersEq
    declarationEq := lambdaFields.2.2.1.trans invariant.declarationEq
    residual := lambdaFields.2.2.2.1.trans invariant.residual
    solvedRequirementsEq := lambdaFields.2.2.2.2.1.trans invariant.solvedRequirementsEq
    assumptionsMono := by rw [lambdaFields.2.2.2.2.2]; exact invariant.assumptionsMono
  }
  have resultAdmissible : TypeAdmissible semanticContext (finalized.substitution.apply resultType) :=
    lambdaPrefixFacts_resultTypeAdmissible_in_active prefixFacts canonical activeBinders
      activeSignaturesEq activeParametersEq activeOwnerEq invariant.residual activeRange
      parameterExtension expectedAdmissible
  have lambdaReturnAdmissible : TypeAdmissible lambdaContext (finalized.substitution.apply resultType) := by
    apply StructuralSubstitution.TypeAdmissible.transportContext (source := semanticContext)
    · exact lambdaFields.1
    · exact lambdaFields.2.1
    · exact lambdaFields.2.2.1
    · exact (actual.monoBinders parametersExtend).variables_eq.trans actual.variables_eq.symm
    · exact lambdaFields.2.2.2.1
    · exact resultAdmissible
  obtain ⟨bodyFinal, bodyFacts, _, _, _, bodyType, bodyAgreement⟩ :=
    bodySound prefixScope.2.2 lambdaReturnAdmissible ({
      accepted := bodySuccess
      interfaces := boundary.interfaces
      extension := laterExtendsBody
      scope := boundary.scope.withLoopDepth 0
      invariant := prefixInvariant
      actual := actual.monoBinders parametersExtend
      operational := prefixScope.1
      rawSubtrees := fun statement member =>
        (rawProper.childSubtree (bodyEdge statement member)).monoBefore bodyToResultRaw
      integerPatterns := bodyIntegerPatternsToEvidence
      integerLiterals := bodyIntegerLiteralsToEvidence
      requirements := bodyRequirementsToEvidence
      covered := bodyCovered
      actualCovered := fun statement member =>
        actualCovered.directChild (boundary.directChildren (bodyEdge statement member)) } :
      StatementsBoundary selected childFuel { inferenceContext with loopDepth := 0 }
        body.value resultType prefixState bodyResult frames lambdaContext)
  have unifiedTypesEq : finalized.substitution.apply bodyResult.type =
      finalized.substitution.apply resultType := by
    calc
      finalized.substitution.apply bodyResult.type =
          finalized.substitution.apply
            (unifiedState.resolve bodyResult.type) := by
        simpa [Frontend.SourceInference.State.resolve,
          TypeSystem.InferState.resolve] using
            (laterExtendsUnified bodyResult.type).symm
      _ = finalized.substitution.apply
          (unifiedState.resolve resultType) :=
        congrArg finalized.substitution.apply
          (Detail.unify_resolve_eq unifySuccess)
      _ = finalized.substitution.apply resultType := by
        simpa [Frontend.SourceInference.State.resolve,
          TypeSystem.InferState.resolve] using
            laterExtendsUnified resultType
  have bodyFactsType : bodyFacts.type =
      finalized.substitution.apply resultType :=
    bodyAgreement.type_eq.trans unifiedTypesEq
  have bodyCompletes : BodyCompletes
      (finalized.substitution.apply resultType) bodyFacts :=
    bodyType.bodyCompletes_of_closed rfl bodyFactsType
  have parameterResolved :
      finalized.substitution.apply
          (restoredState.resolve (TypeSystem.Ty.productMany parameterTypes)) =
        TypeSystem.Ty.productMany
          (parameterTypes.map finalized.substitution.apply) := by
    calc
      finalized.substitution.apply
          (restoredState.resolve (TypeSystem.Ty.productMany parameterTypes)) =
          finalized.substitution.apply
            (TypeSystem.Ty.productMany parameterTypes) := by
        simpa [Frontend.SourceInference.State.resolve,
          TypeSystem.InferState.resolve] using
            restoredExtension
              (TypeSystem.Ty.productMany parameterTypes)
      _ = TypeSystem.Ty.productMany
          (parameterTypes.map finalized.substitution.apply) := by
        exact FlexibleSubstitution.apply_productMany _ _
  have resultResolved :
      finalized.substitution.apply (restoredState.resolve resultType) =
        finalized.substitution.apply resultType := by
    simpa [Frontend.SourceInference.State.resolve,
      TypeSystem.InferState.resolve] using
        restoredExtension resultType
  have formType : ExpressionFormHasRawType semanticSource semanticContext
      ((ExpressionForm.lambda boundParameters (restoredState.resolve resultType)
        bodyResult.statements).applySubstitution finalized.substitution)
      (finalized.substitution.apply
        (.function
          (restoredState.resolve (TypeSystem.Ty.productMany parameterTypes))
          (restoredState.resolve resultType)))
      (.ordinary []) := by
    rw [show finalized.substitution.apply
          (.function
            (restoredState.resolve (TypeSystem.Ty.productMany parameterTypes))
            (restoredState.resolve resultType)) =
        .function
          (TypeSystem.Ty.productMany
            (parameterTypes.map finalized.substitution.apply))
          (finalized.substitution.apply resultType) by
      simp only [FlexibleSubstitution.apply_function, parameterResolved,
        resultResolved]]
    simpa [ExpressionForm.applySubstitution, resultResolved] using
      (ExpressionFormHasRawType.lambda
        (source := semanticSource)
        (by simpa [List.map_map, Function.comp_def,
          TypedBinder.applySubstitution] using namesUnique)
        parametersExtendSource bodyType bodyCompletes)
  have rawAdmissible : TypeAdmissible semanticContext
      (finalized.substitution.apply
        (.function
          (restoredState.resolve (TypeSystem.Ty.productMany parameterTypes))
          (restoredState.resolve resultType))) := by
    rw [show finalized.substitution.apply
          (.function
            (restoredState.resolve (TypeSystem.Ty.productMany parameterTypes))
            (restoredState.resolve resultType)) =
        .function
          (TypeSystem.Ty.productMany
            (parameterTypes.map finalized.substitution.apply))
          (finalized.substitution.apply resultType) by
      simp only [FlexibleSubstitution.apply_function, parameterResolved,
        resultResolved]]
    exact TypeAdmissible.function
      (parametersExtendSource.product_type_admissible activeBinders)
      resultAdmissible
  exact recordExpressionWithExpected_success_expressionTypingBase_actual resources interfaces
    recordSuccess resultSubstitutionExtension requirementsSubset boundary.expressionRequirements boundary.coercionPrimaries
    catalog signaturesEq invariant formType rawAdmissible covered

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
