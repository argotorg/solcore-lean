import Solcore.SourceSemantics.SourceInferenceActualRecursiveContracts
import Solcore.SourceSemantics.SourceInferenceActualLocalExpression
import Solcore.SourceSemantics.SourceInferenceSelectedDeclaration

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

theorem actualInferExprFuelRetainedSoundness_literal {fuel : Nat}
    :
  ∀ {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn : Ty} {expression : Syntax.Expr} {literal : Syntax.CoreLiteral} {expected : Option Ty}
    {initial resultState evidenceState : State}
    {inferred : InferredExpression} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource}
    {frames : List InitializedLetBinding}
    {semanticContext : SourceSemantics.Context},
    expression.value = .literal literal →
    Detail.inferExprFuel (fuel + 1) inferenceContext expression expected initial =
        .ok (inferred, resultState) →
    FinalInferenceResources wholeContext wholeReturn evidenceState roots
      finalized →
    ExecutableCoercionInterfaces.SourceInterfaces wholeContext.signatures
      finalized.solvedRequirements finalized.typedSource →
    finalized.substitution.SemanticallyExtends
      resultState.inference.substitution →
    inferenceContext.signatures = wholeContext.signatures →
    inferenceContext.scope.genericOwner = wholeContext.scope.genericOwner →
    inferenceContext.typeParameters = wholeContext.typeParameters →
    inferenceContext.assumptions = wholeContext.assumptions →
    ProgramSignatureFormationValidated inferenceContext.signatures →
    (∀ candidate ∈ inferenceContext.signatures.functions,
      candidate.scheme.body = .function
        (Ty.productMany candidate.parameterTypes)
        (Ty.productMany candidate.returnTypes)) →
    SignatureCatalogWellFormed inferenceContext.signatures →
    SignatureParametersWellFormed inferenceContext.scope.genericOwner
      inferenceContext.typeParameters →
    RecursiveExpressionInvariant wholeContext finalized initial
      semanticContext →
    ActualContext wholeContext finalized frames semanticContext →
    ActualStateInvariant initial (evidenceState.toTypedSource roots) →
    (∀ expectedType ∈ expected,
      expectedType.VariablesBelow initial.inference.next) →
    (∀ expectedType ∈ expected,
      TypeAdmissible semanticContext (finalized.substitution.apply expectedType)) →
    ProperDescendantsPreserved finalized.substitution
      (resultState.toTypedSource roots) finalized.typedSource
      (.expression inferred.id) →
    RawProperDescendantsPreserved (resultState.toTypedSource roots)
      (evidenceState.toTypedSource roots) (.expression inferred.id) →
    resultState.integerPatterns ⊆ evidenceState.integerPatterns →
    resultState.integerLiterals ⊆ evidenceState.integerLiterals →
    resultState.requirements ⊆ evidenceState.requirements →
    ExpressionRequirementsRetainedAt
      (resultState.toTypedSource roots) finalized.typedSource inferred.id →
    ExpressionCoercionPrimariesRetainedAt
      (resultState.toTypedSource roots) finalized.typedSource inferred.id →
    ExpressionOperatorSiteRetainedAt
      (resultState.toTypedSource roots) finalized.typedSource inferred.id →
    ExpressionDirectChildrenRetainedAt
      (resultState.toTypedSource roots) finalized.typedSource inferred.id →
    TemplateScopeCovered finalized.typedSource semanticContext
      (.expression inferred.id) →
    ProperDescendantsPreserved finalized.substitution (resultState.toTypedSource roots)
      semanticSource (.expression inferred.id) →
    ActualContext.Covers finalized frames (.expression inferred.id) →
    ExpressionTypingBase (resultState.toTypedSource roots) semanticSource
      semanticContext finalized.substitution inferred := by
  intro wholeContext inferenceContext wholeReturn expression literal expected initial
    resultState evidenceState inferred roots finalized semanticSource
    frames semanticContext expressionEq success resources interfaces resultSubstitutionExtension signaturesEq
    ownerEq typeParametersEq assumptionsEq signatureFormation
    functionsCanonical catalog canonical invariant actual operational expectedBelow expectedAdmissible
    finalPreserved rawProper integerPatternsSubset integerLiteralsSubset requirementsSubset
    retained coercionsRetained _operatorsRetained childrenRetained covered semanticPreserved actualCovered
  generalize allocationEq : initial.allocateExpressionId = allocatedPair
  rcases allocatedPair with ⟨id, allocated⟩
  have canonicalWhole : SignatureParametersWellFormed wholeContext.scope.genericOwner wholeContext.typeParameters := by
    simpa [ownerEq, typeParametersEq] using canonical
  cases literalForm : literal.value with
  | string _ => simp [Detail.inferExprFuel, expressionEq, literalForm] at success
  | decimal spelling | hexadecimal spelling =>
    cases decoded : numericLiteralValue? literal.value with
    | none =>
      unfold Detail.inferExprFuel at success
      simp only [allocationEq, expressionEq] at success
      rw [literalForm] at decoded
      simp [literalForm, decoded, bind, Except.bind] at success
    | some rawValue =>
      exact inferExprFuel_success_numericLiteral_expressionTypingBase_selected
        resources interfaces expressionEq rfl decoded allocationEq success resultSubstitutionExtension
        requirementsSubset integerLiteralsSubset retained coercionsRetained catalog signaturesEq
        canonicalWhole invariant covered

theorem actualInferExprFuelRetainedSoundness_identifier {fuel : Nat}
    :
  ∀ {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn : Ty} {expression : Syntax.Expr} {name : Syntax.Identifier} {expected : Option Ty}
    {initial resultState evidenceState : State}
    {inferred : InferredExpression} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource}
    {frames : List InitializedLetBinding}
    {semanticContext : SourceSemantics.Context},
    expression.value = .identifier name →
    Detail.inferExprFuel (fuel + 1) inferenceContext expression expected initial =
        .ok (inferred, resultState) →
    FinalInferenceResources wholeContext wholeReturn evidenceState roots
      finalized →
    ExecutableCoercionInterfaces.SourceInterfaces wholeContext.signatures
      finalized.solvedRequirements finalized.typedSource →
    finalized.substitution.SemanticallyExtends
      resultState.inference.substitution →
    inferenceContext.signatures = wholeContext.signatures →
    inferenceContext.scope.genericOwner = wholeContext.scope.genericOwner →
    inferenceContext.typeParameters = wholeContext.typeParameters →
    inferenceContext.assumptions = wholeContext.assumptions →
    ProgramSignatureFormationValidated inferenceContext.signatures →
    (∀ candidate ∈ inferenceContext.signatures.functions,
      candidate.scheme.body = .function
        (Ty.productMany candidate.parameterTypes)
        (Ty.productMany candidate.returnTypes)) →
    SignatureCatalogWellFormed inferenceContext.signatures →
    SignatureParametersWellFormed inferenceContext.scope.genericOwner
      inferenceContext.typeParameters →
    RecursiveExpressionInvariant wholeContext finalized initial
      semanticContext →
    ActualContext wholeContext finalized frames semanticContext →
    ActualStateInvariant initial (evidenceState.toTypedSource roots) →
    (∀ expectedType ∈ expected,
      expectedType.VariablesBelow initial.inference.next) →
    (∀ expectedType ∈ expected,
      TypeAdmissible semanticContext (finalized.substitution.apply expectedType)) →
    ProperDescendantsPreserved finalized.substitution
      (resultState.toTypedSource roots) finalized.typedSource
      (.expression inferred.id) →
    RawProperDescendantsPreserved (resultState.toTypedSource roots)
      (evidenceState.toTypedSource roots) (.expression inferred.id) →
    resultState.integerPatterns ⊆ evidenceState.integerPatterns →
    resultState.integerLiterals ⊆ evidenceState.integerLiterals →
    resultState.requirements ⊆ evidenceState.requirements →
    ExpressionRequirementsRetainedAt
      (resultState.toTypedSource roots) finalized.typedSource inferred.id →
    ExpressionCoercionPrimariesRetainedAt
      (resultState.toTypedSource roots) finalized.typedSource inferred.id →
    ExpressionOperatorSiteRetainedAt
      (resultState.toTypedSource roots) finalized.typedSource inferred.id →
    ExpressionDirectChildrenRetainedAt
      (resultState.toTypedSource roots) finalized.typedSource inferred.id →
    TemplateScopeCovered finalized.typedSource semanticContext
      (.expression inferred.id) →
    ProperDescendantsPreserved finalized.substitution (resultState.toTypedSource roots)
      semanticSource (.expression inferred.id) →
    ActualContext.Covers finalized frames (.expression inferred.id) →
    ExpressionTypingBase (resultState.toTypedSource roots) semanticSource
      semanticContext finalized.substitution inferred := by
  intro wholeContext inferenceContext wholeReturn expression name expected initial
    resultState evidenceState inferred roots finalized semanticSource
    frames semanticContext expressionEq success resources interfaces resultSubstitutionExtension signaturesEq
    ownerEq typeParametersEq assumptionsEq signatureFormation
    functionsCanonical catalog canonical invariant actual operational expectedBelow expectedAdmissible
    finalPreserved rawProper integerPatternsSubset integerLiteralsSubset requirementsSubset
    retained coercionsRetained _operatorsRetained childrenRetained covered semanticPreserved actualCovered
  generalize allocationEq : initial.allocateExpressionId = allocatedPair
  rcases allocatedPair with ⟨id, allocated⟩
  have canonicalWhole : SignatureParametersWellFormed wholeContext.scope.genericOwner wholeContext.typeParameters := by
    simpa [ownerEq, typeParametersEq] using canonical
  cases found : allocated.lookupBinder? name.value with
  | some binder =>
    obtain ⟨pending, ledger⟩ := operational.ledger
    exact inferExprFuel_success_localIdentifier_expressionTypingBase_actual
      resources interfaces expressionEq allocationEq found success ledger operational.origins
      resultSubstitutionExtension requirementsSubset retained coercionsRetained catalog signaturesEq
      canonicalWhole invariant covered
  | none =>
    cases boolean : (name.value == "true" || name.value == "false") with
    | true =>
      exact inferExprFuel_success_builtinBooleanIdentifier_expressionTypingBase_selected
        resources interfaces expressionEq allocationEq found boolean success resultSubstitutionExtension
        requirementsSubset retained coercionsRetained catalog signaturesEq canonicalWhole invariant covered
    | false =>
      cases functions : Detail.functionsNamed inferenceContext name.value with
      | error error =>
        simp [Detail.inferExprFuel, allocationEq, expressionEq, found, boolean,
          functions, bind, Except.bind] at success
      | ok candidates =>
        cases candidates with
        | nil =>
          cases builtin : builtinFunctionNamed? name.value with
          | none =>
            simp [Detail.inferExprFuel, allocationEq, expressionEq, found, boolean,
              functions, builtin, bind, Except.bind] at success
          | some function =>
            exact inferExprFuel_success_builtinFunctionIdentifier_expressionTypingBase_selected
              resources interfaces expressionEq allocationEq found boolean functions builtin success
              resultSubstitutionExtension requirementsSubset retained coercionsRetained catalog signaturesEq
              canonicalWhole invariant covered
        | cons signature rest =>
          cases rest with
          | nil =>
            exact inferExprFuel_success_declarationIdentifier_expressionTypingBase_actual
              resources interfaces expressionEq allocationEq found boolean functions success
              resultSubstitutionExtension requirementsSubset retained coercionsRetained catalog signaturesEq
              canonicalWhole invariant covered
          | cons next rest =>
            simp [Detail.inferExprFuel, allocationEq, expressionEq, found, boolean,
              functions, bind, Except.bind] at success

theorem actualInferExprFuelRetainedSoundness_proxy {fuel : Nat}
    :
  ∀ {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn : Ty} {expression : Syntax.Expr} {marker : Syntax.SourceSpan} {sourceType : Syntax.TypeExpr} {expected : Option Ty}
    {initial resultState evidenceState : State}
    {inferred : InferredExpression} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource}
    {frames : List InitializedLetBinding}
    {semanticContext : SourceSemantics.Context},
    expression.value = .proxy marker sourceType →
    Detail.inferExprFuel (fuel + 1) inferenceContext expression expected initial =
        .ok (inferred, resultState) →
    FinalInferenceResources wholeContext wholeReturn evidenceState roots
      finalized →
    ExecutableCoercionInterfaces.SourceInterfaces wholeContext.signatures
      finalized.solvedRequirements finalized.typedSource →
    finalized.substitution.SemanticallyExtends
      resultState.inference.substitution →
    inferenceContext.signatures = wholeContext.signatures →
    inferenceContext.scope.genericOwner = wholeContext.scope.genericOwner →
    inferenceContext.typeParameters = wholeContext.typeParameters →
    inferenceContext.assumptions = wholeContext.assumptions →
    ProgramSignatureFormationValidated inferenceContext.signatures →
    (∀ candidate ∈ inferenceContext.signatures.functions,
      candidate.scheme.body = .function
        (Ty.productMany candidate.parameterTypes)
        (Ty.productMany candidate.returnTypes)) →
    SignatureCatalogWellFormed inferenceContext.signatures →
    SignatureParametersWellFormed inferenceContext.scope.genericOwner
      inferenceContext.typeParameters →
    RecursiveExpressionInvariant wholeContext finalized initial
      semanticContext →
    ActualContext wholeContext finalized frames semanticContext →
    ActualStateInvariant initial (evidenceState.toTypedSource roots) →
    (∀ expectedType ∈ expected,
      expectedType.VariablesBelow initial.inference.next) →
    (∀ expectedType ∈ expected,
      TypeAdmissible semanticContext (finalized.substitution.apply expectedType)) →
    ProperDescendantsPreserved finalized.substitution
      (resultState.toTypedSource roots) finalized.typedSource
      (.expression inferred.id) →
    RawProperDescendantsPreserved (resultState.toTypedSource roots)
      (evidenceState.toTypedSource roots) (.expression inferred.id) →
    resultState.integerPatterns ⊆ evidenceState.integerPatterns →
    resultState.integerLiterals ⊆ evidenceState.integerLiterals →
    resultState.requirements ⊆ evidenceState.requirements →
    ExpressionRequirementsRetainedAt
      (resultState.toTypedSource roots) finalized.typedSource inferred.id →
    ExpressionCoercionPrimariesRetainedAt
      (resultState.toTypedSource roots) finalized.typedSource inferred.id →
    ExpressionOperatorSiteRetainedAt
      (resultState.toTypedSource roots) finalized.typedSource inferred.id →
    ExpressionDirectChildrenRetainedAt
      (resultState.toTypedSource roots) finalized.typedSource inferred.id →
    TemplateScopeCovered finalized.typedSource semanticContext
      (.expression inferred.id) →
    ProperDescendantsPreserved finalized.substitution (resultState.toTypedSource roots)
      semanticSource (.expression inferred.id) →
    ActualContext.Covers finalized frames (.expression inferred.id) →
    ExpressionTypingBase (resultState.toTypedSource roots) semanticSource
      semanticContext finalized.substitution inferred := by
  intro wholeContext inferenceContext wholeReturn expression marker sourceType expected initial
    resultState evidenceState inferred roots finalized semanticSource
    frames semanticContext expressionEq success resources interfaces resultSubstitutionExtension signaturesEq
    ownerEq typeParametersEq assumptionsEq signatureFormation
    functionsCanonical catalog canonical invariant actual operational expectedBelow expectedAdmissible
    finalPreserved rawProper integerPatternsSubset integerLiteralsSubset requirementsSubset
    retained coercionsRetained _operatorsRetained childrenRetained covered semanticPreserved actualCovered
  generalize allocationEq : initial.allocateExpressionId = allocatedPair
  rcases allocatedPair with ⟨id, allocated⟩
  have canonicalWhole : SignatureParametersWellFormed wholeContext.scope.genericOwner wholeContext.typeParameters := by
    simpa [ownerEq, typeParametersEq] using canonical
  exact inferExprFuel_success_proxy_expressionTypingBase_selected
    resources interfaces expressionEq allocationEq success resultSubstitutionExtension requirementsSubset
    retained coercionsRetained catalog signaturesEq ownerEq typeParametersEq canonicalWhole invariant covered

end Solcore.SourceSemantics.SourceInferenceSoundness
