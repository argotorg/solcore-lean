import Solcore.SourceSemantics.SourceInferenceStatementForLoopResources
import Solcore.SourceSemantics.SourceInferenceExpressionRecursiveSoundness

/-!
The actual `for` condition is inferred after the initializer header has
established its loop-local lexical context.  This bridge uses the completed
parent's provenance and the unique condition slot to type that expression
without attributing header-let template scopes to it.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.SourceInferenceSoundness

open Frontend Frontend.SourceInference TypeSystem

/-- A successful `for` condition is typed under the initializer-produced
context in the completed parent statement source. -/
theorem inferStatementFuel_success_forLoop_condition_scoped
    {fuel : Nat}
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn expectedReturn : Ty}
    {statement : Syntax.Statement} {headerSpan : Syntax.SourceSpan}
    {initializer post : List Syntax.ForItem} {condition : Syntax.Expr}
    {body : Syntax.Block}
    {initial allocated evidenceState : State}
    {id : StatementId} {result : Detail.StatementResult}
    {initializerResult : Detail.InferredForItems}
    {inferredCondition : InferredExpression} {conditionState : State}
    {roots : List NodeId} {finalized : Frontend.SourceInference.Result}
    {semanticContext loopContext : SourceSemantics.Context}
    (statementEq : statement.value =
      .forLoop headerSpan initializer condition post body)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext
      statement expectedReturn initial = .ok result)
    (initializerSuccess : Detail.inferForItemsFuel fuel inferenceContext
      initializer allocated = .ok initializerResult)
    (conditionSuccess : Detail.inferExprFuel fuel inferenceContext condition
      (some .bool) initializerResult.state =
        .ok (inferredCondition, conditionState))
    (resources : FinalInferenceResources wholeContext wholeReturn
      evidenceState roots finalized)
    (signaturesEq : inferenceContext.signatures = wholeContext.signatures)
    (ownerEq : inferenceContext.scope.genericOwner =
      wholeContext.scope.genericOwner)
    (parametersEq : inferenceContext.typeParameters =
      wholeContext.typeParameters)
    (assumptionsEq : inferenceContext.assumptions = wholeContext.assumptions)
    (signatureFormation : ProgramSignatureFormationValidated
      inferenceContext.signatures)
    (functionsCanonical : ∀ candidate ∈ inferenceContext.signatures.functions,
      candidate.scheme.body = .function
        (Ty.productMany candidate.parameterTypes)
        (Ty.productMany candidate.returnTypes))
    (catalog : SignatureCatalogWellFormed inferenceContext.signatures)
    (signatureParameters : SignatureParametersWellFormed
      inferenceContext.scope.genericOwner inferenceContext.typeParameters)
    (initialInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized initial semanticContext)
    (initializerInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized initializerResult.state loopContext)
    (resultSubstitutionExtension : finalized.substitution.SemanticallyExtends
      result.state.inference.substitution)
    (resultExtension : TypingSourceExtends
      ((result.state.toTypedSource roots).applySubstitution
        finalized.substitution) finalized.typedSource)
    (rawResultExtension : TypingSourceExtends
      (result.state.toTypedSource roots)
      (evidenceState.toTypedSource roots))
    (integerPatternsSubset : result.state.integerPatterns ⊆
      evidenceState.integerPatterns)
    (integerLiteralsSubset : result.state.integerLiterals ⊆
      evidenceState.integerLiterals)
    (requirementsSubset : result.state.requirements ⊆
      evidenceState.requirements)
    (parentCovered : TemplateScopeCovered finalized.typedSource
      semanticContext (.statement result.id))
    (loopAssumptionsEq : loopContext.assumptions =
      semanticContext.assumptions)
    (expressionSound : InferExprFuelScopedSoundness fuel) :
    ExpressionHasType
      ((result.state.toTypedSource roots).applySubstitution
        finalized.substitution)
      loopContext inferredCondition.id .bool := by
  obtain ⟨actualInitializer, actualCondition, actualConditionState,
      bodyResult, postResult, actualInitializerSuccess,
      actualConditionSuccess, bodySuccess, postSuccess, initializerBelow,
      conditionSubstitutionExtension, conditionToParent,
      conditionPatternsSubset, conditionLiteralsSubset,
      conditionRequirementsSubset⟩ :=
    inferStatementFuel_success_forLoop_condition_resources statementEq
      allocationEq success signatureFormation functionsCanonical
      initialInvariant resultSubstitutionExtension integerPatternsSubset
      integerLiteralsSubset requirementsSubset
  rw [initializerSuccess] at actualInitializerSuccess
  have initializerEq := (Except.ok.inj actualInitializerSuccess).symm
  subst actualInitializer
  rw [conditionSuccess] at actualConditionSuccess
  obtain ⟨rfl, rfl⟩ := (Except.ok.inj actualConditionSuccess).symm
  obtain ⟨factInitializer, factCondition, factConditionState,
      factBody, factPost, factInitializerSuccess, factConditionSuccess,
      factBodySuccess, factPostSuccess, resultEq, containsRaw⟩ :=
    inferStatementFuel_success_forLoop_facts statementEq allocationEq
      success roots
  rw [initializerSuccess] at factInitializerSuccess
  have factInitializerEq := (Except.ok.inj factInitializerSuccess).symm
  subst factInitializer
  rw [conditionSuccess] at factConditionSuccess
  obtain ⟨rfl, rfl⟩ := (Except.ok.inj factConditionSuccess).symm
  have containsFinal : ContainsStatement finalized.typedSource result.id
      (({
        id := result.id
        span := statement.span
        type := result.type
        form := .forLoop initializerResult.items inferredCondition.id
          factPost.items factBody.statements
      } : StatementNode).applySubstitution finalized.substitution) :=
    resultExtension.containsStatement
      (FlexibleSubstitution.ContainsStatement.applySubstitution
        finalized.substitution containsRaw)
  have conditionCovered : TemplateScopeCovered finalized.typedSource
      loopContext (.expression inferredCondition.id) := by
    apply TemplateScopeCovered.forLoopCondition parentCovered
      resources.graph_closed
    · simpa [StatementNode.applySubstitution,
        StatementForm.applySubstitution] using containsFinal
    · exact loopAssumptionsEq
  have conditionTyped : ExpressionHasType
      ((result.state.toTypedSource roots).applySubstitution
        finalized.substitution)
      loopContext inferredCondition.id
      (finalized.substitution.apply inferredCondition.type) :=
    expressionSound conditionSuccess resources
      conditionSubstitutionExtension signaturesEq ownerEq parametersEq
      assumptionsEq signatureFormation functionsCanonical catalog
      signatureParameters (RecursiveExpressionInvariant.ofStatement
        initializerInvariant) (by
          intro expected member
          simp only [Option.mem_def] at member
          injection member with expectedEq
          subst expected
          simp [Ty.bool])
      (conditionToParent.applySubstitution finalized.substitution)
      resultExtension (conditionToParent.trans rawResultExtension)
      conditionPatternsSubset conditionLiteralsSubset
      conditionRequirementsSubset conditionCovered
  have conditionTypeEq :
      finalized.substitution.apply inferredCondition.type = .bool := by
    simpa using Detail.inferExprFuel_expected_type_apply_eq
      conditionSuccess conditionSubstitutionExtension
  simpa [conditionTypeEq] using conditionTyped

end Solcore.SourceSemantics.SourceInferenceSoundness
