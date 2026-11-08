import Solcore.SourceSemantics.Internal.Selected.Operators
import Solcore.SourceSemantics.Internal.Inference.ExpressionLedgers
import Solcore.SourceSemantics.Internal.Inference.ExpressionCalls
import Solcore.SourceSemantics.Internal.Inference.RootedContracts
import Solcore.SourceSemantics.Internal.Selected.Children
import Solcore.SourceSemantics.Internal.Selected.State

/-!
# Selected expressions

Atomic, conditional, group, index, lambda and tuple forms.
-/

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActualLocalExpression
/-! Actual local calls obtain allocation and capture evidence from the live
checker ledger and the retained lexical binder inventory. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

/-- A retained local expression uses its actual selected binder, its actual
fresh obligation allocation, and finalization's binder-local capture check. -/
theorem
    inferExprFuel_success_localIdentifier_expressionTypingBase_actual
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn : Ty} {evidenceState : State} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    (resources : FinalInferenceResources wholeContext wholeReturn
      evidenceState roots finalized)
    (interfaces : ExecutableCoercionInterfaces.SourceInterfaces
      wholeContext.signatures finalized.solvedRequirements finalized.typedSource)
    {fuel : Nat} {expression : Syntax.Expr} {expected : Option Ty}
    {initial allocated resultState : State}
    {id : ExpressionId} {name : Syntax.Identifier} {binder : TypedBinder}
    {inferred : InferredExpression}
    {semanticSource : TypedSource} {active : SourceSemantics.Context}
    (expressionEq : expression.value = .identifier name)
    (allocationEq : initial.allocateExpressionId = (id, allocated))
    (lookupEq : allocated.lookupBinder? name.value = some binder)
    (success : Detail.inferExprFuel (fuel + 1) inferenceContext expression
      expected initial = .ok (inferred, resultState))
    {pending : List RequirementId}
    (ledger : RecursiveLedgerInvariant initial pending)
    (origins : ActiveBinderCaptureOrigins initial (evidenceState.toTypedSource roots))
    (resultSubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        resultState.inference.substitution)
    (requirementsSubset : resultState.requirements ⊆
      evidenceState.requirements)
    (retained : ExpressionRequirementsRetainedAt
      (resultState.toTypedSource roots) finalized.typedSource inferred.id)
    (coercionsRetained : ExpressionCoercionPrimariesRetainedAt
      (resultState.toTypedSource roots) finalized.typedSource inferred.id)
    (catalog : SignatureCatalogWellFormed inferenceContext.signatures)
    (signaturesEq : inferenceContext.signatures = wholeContext.signatures)
    (canonical : SignatureParametersWellFormed
      wholeContext.scope.genericOwner wholeContext.typeParameters)
    (invariant : RecursiveExpressionInvariant wholeContext finalized initial
      active)
    (covered : TemplateScopeCovered finalized.typedSource active
      (.expression inferred.id)) :
    ExpressionTypingBase (resultState.toTypedSource roots) semanticSource
      active finalized.substitution inferred := by
  have allocatedEq : initial.allocateExpressionId.2 = allocated := congrArg Prod.snd allocationEq
  have allocatedLedger : RecursiveLedgerInvariant allocated pending := by
    rw [← allocatedEq]
    exact ledger.allocateExpressionId
  have allocatedOrigins : ActiveBinderCaptureOrigins allocated
      (evidenceState.toTypedSource roots) := by
    apply origins.congr_localBinders
    rw [← allocatedEq]
    rfl
  let instantiated := binder.scheme.instantiateWithSubstitution allocated.inference.next
  let advanced : State := { allocated with inference := {
    allocated.inference with next := instantiated.next } }
  let predicates := binder.schemeRequirements.map fun requirement =>
    Detail.applyPredicate advanced
      (TypedTraitResolution.applySubstitution instantiated.substitution requirement.predicate)
  have advancedLedger : RecursiveLedgerInvariant advanced pending := allocatedLedger.withInference
  have found : advanced.lookupBinder? name.value = some binder := lookupEq
  have certificate := advancedLedger.templates.lookupBinderRequirementAllocationCertificate
    advancedLedger.requirements name.value binder predicates found
  have noCapture := resources.noCapture_of_lookupBinder? allocatedOrigins lookupEq
  exact inferExprFuel_success_localIdentifier_expressionTypingBase_selected
    resources interfaces expressionEq allocationEq lookupEq success certificate noCapture
    resultSubstitutionExtension requirementsSubset retained coercionsRetained catalog signaturesEq
    canonical invariant covered

end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedAtomicSoundness
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
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedConditionalSoundness
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

theorem actualInferExprFuelRetainedSoundness_conditional {fuel : Nat}
    (recursive : ActualInferExprFuelRetainedSoundness fuel) :
  ∀ {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn : Ty} {expression condition thenBranch elseBranch : Syntax.Expr}
    {question colon : Syntax.SourceSpan} {expected : Option Ty}
    {initial resultState evidenceState : State}
    {inferred : InferredExpression} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource}
    {frames : List InitializedLetBinding}
    {semanticContext : SourceSemantics.Context},
    expression.value = .conditional condition question thenBranch colon elseBranch →
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
  intro wholeContext inferenceContext wholeReturn expression condition thenBranch elseBranch question colon expected initial
    resultState evidenceState inferred roots finalized semanticSource
    frames semanticContext expressionEq success resources interfaces resultSubstitutionExtension signaturesEq
    ownerEq typeParametersEq assumptionsEq signatureFormation
    functionsCanonical catalog canonical invariant actual operational expectedBelow expectedAdmissible
    finalPreserved rawProper integerPatternsSubset integerLiteralsSubset requirementsSubset
    retained coercionsRetained _operatorsRetained childrenRetained covered semanticPreserved actualCovered
  generalize allocationEq : initial.allocateExpressionId = allocatedPair
  rcases allocatedPair with ⟨id, allocated⟩
  have allocatedInvariant := invariant.allocateExpressionId allocationEq
  have allocatedOperational : ActualStateInvariant allocated (evidenceState.toTypedSource roots) := by
    obtain ⟨pending, ledger⟩ := operational.ledger
    have stateEq : initial.allocateExpressionId.2 = allocated := congrArg Prod.snd allocationEq
    refine ⟨⟨pending, ?_⟩, ?_, ?_, operational.sourceMonomorphic⟩
    · rw [← stateEq]
      exact ledger.allocateExpressionId
    · apply operational.origins.congr_localBinders
      rw [← stateEq]
      rfl
    · apply activeQuantifiersBelowNext_transport operational.quantifiersBelow
      · rw [← stateEq]; rfl
      · rw [← stateEq]; exact Nat.le_refl _
  have allocatedExpected : ∀ type ∈ expected, type.VariablesBelow allocated.inference.next := by
    rw [allocateExpressionId_inferenceNext_eq allocationEq]
    exact expectedBelow
  obtain ⟨conditionResult, conditionState, thenResult, thenState, elseResult,
      elseState, unifiedState, conditionSuccess, thenSuccess, elseSuccess,
      unifySuccess, recorded⟩ :=
    Detail.inferExprFuel_success_conditional_facts expressionEq allocationEq
      success
  have conditionProperties := Detail.inferExprFuel_inferenceProperties
    allocatedInvariant.ready signatureFormation functionsCanonical (by
      intro expectedType member
      simp only [Option.mem_def] at member
      have expectedTypeEq : expectedType = .bool :=
        (Option.some.inj member).symm
      rw [expectedTypeEq]
      change TypeSystem.Ty.VariablesBelow allocated.inference.next
        (.constructor (.builtin .bool))
      exact TypeSystem.Ty.variablesBelow_constructor _ _) conditionSuccess
  have expectedAtCondition : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow conditionState.inference.next := by
    intro expectedType member
    exact (allocatedExpected expectedType member).weaken
      conditionProperties.1.next_le
  have thenProperties := Detail.inferExprFuel_inferenceProperties
    conditionProperties.2.1 signatureFormation functionsCanonical
      expectedAtCondition thenSuccess
  have expectedAtThen : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow thenState.inference.next := by
    intro expectedType member
    exact (expectedAtCondition expectedType member).weaken
      thenProperties.1.next_le
  have elseProperties := Detail.inferExprFuel_inferenceProperties
    thenProperties.2.1 signatureFormation functionsCanonical expectedAtThen
      elseSuccess
  have thenAtElse : thenResult.type.VariablesBelow
      elseState.inference.next :=
    thenProperties.2.2.weaken elseProperties.1.next_le
  have unifyProgress := Detail.unify_inferenceProgress
    elseProperties.2.1.solved thenAtElse elseProperties.2.2 unifySuccess
  have unifiedReady := Detail.unify_preserves_inferenceReady
    elseProperties.2.1 thenAtElse elseProperties.2.2 unifySuccess
  have allocatedToUnified : allocated.InferenceProgress unifiedState :=
    conditionProperties.1.trans
      (thenProperties.1.trans (elseProperties.1.trans unifyProgress))
  have expectedAtUnified : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow unifiedState.inference.next := by
    intro expectedType member
    exact (allocatedExpected expectedType member).weaken
      allocatedToUnified.next_le
  have thenAtUnified : thenResult.type.VariablesBelow
      unifiedState.inference.next :=
    thenAtElse.weaken unifyProgress.next_le
  have resolvedThenBelow :
      (unifiedState.resolve thenResult.type).VariablesBelow
        unifiedState.inference.next :=
    unifiedReady.solved.variablesBelow_apply thenAtUnified
  have recordedProperties :=
    Detail.recordExpressionWithExpected_inferenceProperties unifiedReady
      resolvedThenBelow expectedAtUnified recorded
  have laterUnified : finalized.substitution.SemanticallyExtends
      unifiedState.inference.substitution :=
    TypeSystem.Substitution.SemanticallyExtends.trans resultSubstitutionExtension
      recordedProperties.1.substitution_extends
  have laterElse : finalized.substitution.SemanticallyExtends
      elseState.inference.substitution :=
    TypeSystem.Substitution.SemanticallyExtends.trans laterUnified
      unifyProgress.substitution_extends
  have laterThen : finalized.substitution.SemanticallyExtends
      thenState.inference.substitution :=
    TypeSystem.Substitution.SemanticallyExtends.trans laterElse
      elseProperties.1.substitution_extends
  have laterCondition : finalized.substitution.SemanticallyExtends
      conditionState.inference.substitution :=
    TypeSystem.Substitution.SemanticallyExtends.trans laterThen
      thenProperties.1.substitution_extends
  have allocatedBelow := allocatedInvariant.nodesBelow
  have conditionBelow : conditionState.NodesBelowNextOccurrence :=
    (Detail.inferExprFuel_occurrenceBoundExtends conditionSuccess
      ).nodesBelowNextOccurrence allocatedBelow
  have thenBelow : thenState.NodesBelowNextOccurrence :=
    (Detail.inferExprFuel_occurrenceBoundExtends thenSuccess
      ).nodesBelowNextOccurrence conditionBelow
  have elseBelow : elseState.NodesBelowNextOccurrence :=
    (Detail.inferExprFuel_occurrenceBoundExtends elseSuccess
      ).nodesBelowNextOccurrence thenBelow
  have unifiedBelow : unifiedState.NodesBelowNextOccurrence :=
    (Detail.unify_occurrenceBoundExtends unifySuccess
      ).nodesBelowNextOccurrence elseBelow
  have conditionToThen :=
    inferExprFuel_success_typingSourceExtends thenSuccess conditionBelow roots
  have thenToElse :=
    inferExprFuel_success_typingSourceExtends elseSuccess thenBelow roots
  have elseToUnified : TypingSourceExtends
      (elseState.toTypedSource roots) (unifiedState.toTypedSource roots) := by
    constructor
    · change unifiedState.owner = elseState.owner
      have headerEq := Detail.unify_state_header unifySuccess
      simpa [Frontend.SourceInference.State.header] using
        congrArg Frontend.SourceInference.State.Header.owner headerEq
    · change elseState.nodes <+: unifiedState.nodes
      rw [(Detail.unify_occurrenceState_eq unifySuccess).1]
      exact List.prefix_rfl
  have allocatedOwner : allocated.owner = initial.owner := by
    have stateEq : initial.allocateExpressionId.2 = allocated :=
      congrArg Prod.snd allocationEq
    rw [← stateEq]
    rfl
  have conditionOwner : conditionState.owner = allocated.owner :=
    Detail.inferExprFuel_preserves_owner conditionSuccess
  have thenOwner : thenState.owner = conditionState.owner :=
    Detail.inferExprFuel_preserves_owner thenSuccess
  have elseOwner : elseState.owner = thenState.owner :=
    Detail.inferExprFuel_preserves_owner elseSuccess
  have unifiedOwner : unifiedState.owner = elseState.owner := by
    have headerEq := Detail.unify_state_header unifySuccess
    simpa [Frontend.SourceInference.State.header] using
      congrArg Frontend.SourceInference.State.Header.owner headerEq
  have parentOwner : resultState.owner = initial.owner :=
    Detail.inferExprFuel_preserves_owner success
  have unifiedToParent : TypingSourceExtends
      (unifiedState.toTypedSource roots) (resultState.toTypedSource roots) := by
    constructor
    · exact parentOwner.trans
        (allocatedOwner.symm.trans
          (conditionOwner.symm.trans
            (thenOwner.symm.trans
              (elseOwner.symm.trans unifiedOwner.symm))))
    · exact recordExpressionWithExpected_success_nodesPrefix recorded
  have conditionToParent :=
    TypingSourceExtends.trans conditionToThen
      (TypingSourceExtends.trans thenToElse
        (TypingSourceExtends.trans elseToUnified unifiedToParent))
  have thenToParent :=
    TypingSourceExtends.trans thenToElse
      (TypingSourceExtends.trans elseToUnified unifiedToParent)
  have elseToParent :=
    TypingSourceExtends.trans elseToUnified unifiedToParent
  have unifiedIntegerLiteralsSubset :
      unifiedState.integerLiterals ⊆ resultState.integerLiterals := by
    intro origin member
    rw [Detail.recordExpressionWithExpected_integerLiterals_eq recorded]
    exact member
  have elseIntegerLiteralsSubset :
      elseState.integerLiterals ⊆ resultState.integerLiterals := by
    intro origin member
    apply unifiedIntegerLiteralsSubset
    rw [Detail.unify_integerLiterals unifySuccess]
    exact member
  have thenIntegerLiteralsSubset :
      thenState.integerLiterals ⊆ resultState.integerLiterals :=
    List.Subset.trans
      (Detail.inferExprFuel_integerLiterals_subset elseSuccess)
      elseIntegerLiteralsSubset
  have conditionIntegerLiteralsSubset :
      conditionState.integerLiterals ⊆ resultState.integerLiterals :=
    List.Subset.trans
      (Detail.inferExprFuel_integerLiterals_subset thenSuccess)
      thenIntegerLiteralsSubset
  have unifiedIntegerPatternsSubset :
      unifiedState.integerPatterns ⊆ resultState.integerPatterns := by
    intro origin member
    rw [recordExpressionWithExpected_integerPatterns_eq recorded]
    exact member
  have elseIntegerPatternsSubset :
      elseState.integerPatterns ⊆ resultState.integerPatterns := by
    intro origin member
    apply unifiedIntegerPatternsSubset
    rw [(Detail.unify_integerPatternMetadata_eq unifySuccess).1]
    exact member
  have thenIntegerPatternsSubset :
      thenState.integerPatterns ⊆ resultState.integerPatterns :=
    List.Subset.trans
      (Detail.inferExprFuel_integerPatterns_subset elseSuccess)
      elseIntegerPatternsSubset
  have conditionIntegerPatternsSubset :
      conditionState.integerPatterns ⊆ resultState.integerPatterns :=
    List.Subset.trans
      (Detail.inferExprFuel_integerPatterns_subset thenSuccess)
      thenIntegerPatternsSubset
  have unifiedRequirementsSubset :
      unifiedState.requirements ⊆ resultState.requirements :=
    Detail.recordExpressionWithExpected_requirements_subset recorded
  have elseRequirementsSubset :
      elseState.requirements ⊆ resultState.requirements := by
    intro requirement member
    apply unifiedRequirementsSubset
    rw [Detail.unify_requirements_eq unifySuccess]
    exact member
  have thenRequirementsSubset :
      thenState.requirements ⊆ resultState.requirements :=
    List.Subset.trans
      (Detail.inferExprFuel_requirements_subset elseSuccess)
      elseRequirementsSubset
  have conditionRequirementsSubset :
      conditionState.requirements ⊆ resultState.requirements :=
    List.Subset.trans
      (Detail.inferExprFuel_requirements_subset thenSuccess)
      thenRequirementsSubset
  have conditionExpected : ∀ type ∈ (some Ty.bool : Option Ty), type.VariablesBelow allocated.inference.next := by
    intro type member
    have same : type = Ty.bool := (Option.some.inj member).symm
    subst type
    exact Ty.variablesBelow_constructor _ _
  have conditionInvariant := allocatedInvariant.ofExpression signatureFormation functionsCanonical
    conditionExpected laterCondition conditionSuccess
  have thenInvariant := conditionInvariant.ofExpression signatureFormation functionsCanonical
    expectedAtCondition laterThen thenSuccess
  have conditionOperational := allocatedOperational.ofExpression conditionSuccess conditionProperties.1.next_le
  have thenOperational := conditionOperational.ofExpression thenSuccess thenProperties.1.next_le
  obtain ⟨coercions, contains⟩ := recordExpressionWithExpected_success_containsExpression recorded roots
  have edge : ∀ child ∈ [conditionResult.id, thenResult.id, elseResult.id],
      DirectChild (resultState.toTypedSource roots) (.expression inferred.id) (.expression child) := by
    intro child member
    refine ⟨.expression _, ⟨contains.1, rfl⟩, ?_⟩
    simpa [nodeChildIds, Node.references, ExpressionForm.references] using
      (List.mem_map.mpr ⟨child, member, rfl⟩ : NodeId.expression child ∈
        [conditionResult.id, thenResult.id, elseResult.id].map NodeId.expression)
  have conditionEdge := edge conditionResult.id (by simp)
  have conditionTypeRaw := actualInferExprFuelFinalSubtreeSoundness_of_retainedSoundness recursive
    conditionSuccess resources interfaces laterCondition signaturesEq ownerEq typeParametersEq assumptionsEq
    signatureFormation functionsCanonical catalog canonical allocatedInvariant actual allocatedOperational conditionExpected
    (by
      intro type member
      have same : type = .bool := (Option.some.inj member).symm
      subst type
      exact TypeAdmissible.bool (invariant.typeParameterBinders (by simpa [ownerEq, typeParametersEq] using canonical)))
    ((semanticPreserved.childSubtree conditionEdge).monoBefore conditionToParent)
    ((finalPreserved.childSubtree conditionEdge).monoBefore conditionToParent)
    ((rawProper.childSubtree conditionEdge).monoBefore conditionToParent).proper
    (List.Subset.trans conditionIntegerPatternsSubset integerPatternsSubset)
    (List.Subset.trans conditionIntegerLiteralsSubset integerLiteralsSubset)
    (List.Subset.trans conditionRequirementsSubset requirementsSubset)
    (covered.expressionChild resources.graph_closed (childrenRetained conditionEdge))
    (actualCovered.directChild (childrenRetained conditionEdge))
  have thenEdge := edge thenResult.id (by simp)
  have thenTypeRaw := actualInferExprFuelFinalSubtreeSoundness_of_retainedSoundness recursive
    thenSuccess resources interfaces laterThen signaturesEq ownerEq typeParametersEq assumptionsEq
    signatureFormation functionsCanonical catalog canonical conditionInvariant actual conditionOperational expectedAtCondition expectedAdmissible
    ((semanticPreserved.childSubtree thenEdge).monoBefore thenToParent)
    ((finalPreserved.childSubtree thenEdge).monoBefore thenToParent)
    ((rawProper.childSubtree thenEdge).monoBefore thenToParent).proper
    (List.Subset.trans thenIntegerPatternsSubset integerPatternsSubset)
    (List.Subset.trans thenIntegerLiteralsSubset integerLiteralsSubset)
    (List.Subset.trans thenRequirementsSubset requirementsSubset)
    (covered.expressionChild resources.graph_closed (childrenRetained thenEdge))
    (actualCovered.directChild (childrenRetained thenEdge))
  have elseEdge := edge elseResult.id (by simp)
  have elseTypeRaw := actualInferExprFuelFinalSubtreeSoundness_of_retainedSoundness recursive
    elseSuccess resources interfaces laterElse signaturesEq ownerEq typeParametersEq assumptionsEq
    signatureFormation functionsCanonical catalog canonical thenInvariant actual thenOperational expectedAtThen expectedAdmissible
    ((semanticPreserved.childSubtree elseEdge).monoBefore elseToParent)
    ((finalPreserved.childSubtree elseEdge).monoBefore elseToParent)
    ((rawProper.childSubtree elseEdge).monoBefore elseToParent).proper
    (List.Subset.trans elseIntegerPatternsSubset integerPatternsSubset)
    (List.Subset.trans elseIntegerLiteralsSubset integerLiteralsSubset)
    (List.Subset.trans elseRequirementsSubset requirementsSubset)
    (covered.expressionChild resources.graph_closed (childrenRetained elseEdge))
    (actualCovered.directChild (childrenRetained elseEdge))
  have conditionEq : finalized.substitution.apply conditionResult.type =
      .bool := by
    simpa using Detail.inferExprFuel_expected_type_apply_eq conditionSuccess
      laterCondition
  have conditionType : ExpressionHasType semanticSource semanticContext
      conditionResult.id .bool := by
    rw [← conditionEq]
    exact conditionTypeRaw
  have resolvedThenEq :
      finalized.substitution.apply
          (unifiedState.resolve thenResult.type) =
        finalized.substitution.apply thenResult.type := by
    simpa [Frontend.SourceInference.State.resolve,
      TypeSystem.InferState.resolve] using laterUnified thenResult.type
  have resolvedElseEq :
      finalized.substitution.apply
          (unifiedState.resolve elseResult.type) =
        finalized.substitution.apply elseResult.type := by
    simpa [Frontend.SourceInference.State.resolve,
      TypeSystem.InferState.resolve] using laterUnified elseResult.type
  have unifiedEq : unifiedState.resolve thenResult.type =
      unifiedState.resolve elseResult.type := by
    simpa [Frontend.SourceInference.State.resolve] using
      Detail.unify_resolve_eq unifySuccess
  have branchEq : finalized.substitution.apply thenResult.type =
      finalized.substitution.apply elseResult.type := by
    calc
      finalized.substitution.apply thenResult.type =
          finalized.substitution.apply
            (unifiedState.resolve thenResult.type) := resolvedThenEq.symm
      _ = finalized.substitution.apply
          (unifiedState.resolve elseResult.type) :=
        congrArg finalized.substitution.apply unifiedEq
      _ = finalized.substitution.apply elseResult.type := resolvedElseEq
  have thenType : ExpressionHasType semanticSource semanticContext thenResult.id
      (finalized.substitution.apply
        (unifiedState.resolve thenResult.type)) := by
    rw [resolvedThenEq]
    exact thenTypeRaw
  have elseType : ExpressionHasType semanticSource semanticContext elseResult.id
      (finalized.substitution.apply
        (unifiedState.resolve thenResult.type)) := by
    rw [resolvedThenEq, branchEq]
    exact elseTypeRaw
  have formType : ExpressionFormHasRawType semanticSource semanticContext
      ((ExpressionForm.conditional conditionResult.id thenResult.id
        elseResult.id).applySubstitution finalized.substitution)
      (finalized.substitution.apply
        (unifiedState.resolve thenResult.type)) (.ordinary []) := by
    simpa [ExpressionForm.applySubstitution] using
      ExpressionFormHasRawType.conditional conditionType thenType elseType
  exact recordExpressionWithExpected_success_expressionTypingBase_actual resources interfaces
    recorded resultSubstitutionExtension requirementsSubset retained coercionsRetained
    catalog signaturesEq invariant formType thenType.type_admissible covered

end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedGroupSoundness
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

theorem actualInferExprFuelRetainedSoundness_group {fuel : Nat}
    (recursive : ActualInferExprFuelRetainedSoundness fuel) :
  ∀ {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn : Ty} {expression inner : Syntax.Expr} {expected : Option Ty}
    {initial resultState evidenceState : State}
    {inferred : InferredExpression} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource}
    {frames : List InitializedLetBinding}
    {semanticContext : SourceSemantics.Context},
    expression.value = .group inner →
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
  intro wholeContext inferenceContext wholeReturn expression inner expected initial
    resultState evidenceState inferred roots finalized semanticSource
    frames semanticContext expressionEq success resources interfaces resultSubstitutionExtension signaturesEq
    ownerEq typeParametersEq assumptionsEq signatureFormation
    functionsCanonical catalog canonical invariant actual operational expectedBelow expectedAdmissible
    finalPreserved rawProper integerPatternsSubset integerLiteralsSubset requirementsSubset
    retained coercionsRetained _operatorsRetained childrenRetained covered semanticPreserved actualCovered
  generalize allocationEq : initial.allocateExpressionId = allocatedPair
  rcases allocatedPair with ⟨id, allocated⟩
  have allocatedInvariant := invariant.allocateExpressionId allocationEq
  have allocatedOperational : ActualStateInvariant allocated (evidenceState.toTypedSource roots) := by
    obtain ⟨pending, ledger⟩ := operational.ledger
    have stateEq : initial.allocateExpressionId.2 = allocated := congrArg Prod.snd allocationEq
    refine ⟨⟨pending, ?_⟩, ?_, ?_, operational.sourceMonomorphic⟩
    · rw [← stateEq]
      exact ledger.allocateExpressionId
    · apply operational.origins.congr_localBinders
      rw [← stateEq]
      rfl
    · apply activeQuantifiersBelowNext_transport operational.quantifiersBelow
      · rw [← stateEq]; rfl
      · rw [← stateEq]; exact Nat.le_refl _
  have allocatedExpected : ∀ type ∈ expected, type.VariablesBelow allocated.inference.next := by
    rw [allocateExpressionId_inferenceNext_eq allocationEq]
    exact expectedBelow
  obtain ⟨innerResult, innerState, innerSuccess, recorded⟩ :=
    Detail.inferExprFuel_success_group_facts expressionEq allocationEq success
  have properties := Detail.inferExprFuel_inferenceProperties allocatedInvariant.ready
    signatureFormation functionsCanonical allocatedExpected innerSuccess
  have innerExpected : ∀ type ∈ expected, type.VariablesBelow innerState.inference.next := by
    intro type member
    exact (allocatedExpected type member).weaken properties.1.next_le
  have recording := Detail.recordExpressionWithExpected_inferenceProperties
    properties.2.1 properties.2.2 innerExpected recorded
  have innerExtension := resultSubstitutionExtension.trans recording.1.substitution_extends
  have allocatedOwner : allocated.owner = initial.owner := by
    have stateEq : initial.allocateExpressionId.2 = allocated := congrArg Prod.snd allocationEq
    rw [← stateEq]
    rfl
  have innerToParent : TypingSourceExtends (innerState.toTypedSource roots)
      (resultState.toTypedSource roots) := by
    refine ⟨?_, recordExpressionWithExpected_success_nodesPrefix recorded⟩
    exact (Detail.inferExprFuel_preserves_owner success).trans
      (allocatedOwner.symm.trans (Detail.inferExprFuel_preserves_owner innerSuccess).symm)
  obtain ⟨coercions, contains⟩ := recordExpressionWithExpected_success_containsExpression recorded roots
  have edge : DirectChild (resultState.toTypedSource roots)
      (.expression inferred.id) (.expression innerResult.id) := by
    refine ⟨.expression _, ⟨contains.1, rfl⟩, ?_⟩
    simp [nodeChildIds, Node.references, ExpressionForm.references]
  have finalEdge := childrenRetained edge
  have childFinal := (finalPreserved.childSubtree edge).monoBefore innerToParent
  have childSemantic := (semanticPreserved.childSubtree edge).monoBefore innerToParent
  have childPatterns : innerState.integerPatterns ⊆ evidenceState.integerPatterns := by
    rw [← recordExpressionWithExpected_integerPatterns_eq recorded]
    exact integerPatternsSubset
  have childLiterals : innerState.integerLiterals ⊆ evidenceState.integerLiterals := by
    rw [← Detail.recordExpressionWithExpected_integerLiterals_eq recorded]
    exact integerLiteralsSubset
  have childRequirements := List.Subset.trans
    (Detail.recordExpressionWithExpected_requirements_subset recorded) requirementsSubset
  have typed := actualInferExprFuelFinalSubtreeSoundness_of_retainedSoundness recursive
    innerSuccess resources interfaces innerExtension signaturesEq ownerEq typeParametersEq assumptionsEq
    signatureFormation functionsCanonical catalog canonical allocatedInvariant actual allocatedOperational
    allocatedExpected expectedAdmissible childSemantic childFinal
    ((rawProper.childSubtree edge).monoBefore innerToParent).proper childPatterns childLiterals childRequirements
    (covered.expressionChild resources.graph_closed finalEdge) (actualCovered.directChild finalEdge)
  have formType : ExpressionFormHasRawType semanticSource semanticContext
      ((ExpressionForm.group innerResult.id).applySubstitution finalized.substitution)
      (finalized.substitution.apply innerResult.type) (.ordinary []) := by
    simpa [ExpressionForm.applySubstitution] using ExpressionFormHasRawType.group typed
  exact recordExpressionWithExpected_success_expressionTypingBase_actual resources interfaces
    recorded resultSubstitutionExtension requirementsSubset retained coercionsRetained
    catalog signaturesEq invariant formType typed.type_admissible covered

end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedIndexSoundness
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

private theorem fresh_eq_typingSourceExtends
    {initial final : Frontend.SourceInference.State}
    {type : TypeSystem.Ty}
    (success : initial.fresh = (type, final))
    (roots : List NodeId := []) :
    TypingSourceExtends (initial.toTypedSource roots)
      (final.toTypedSource roots) := by
  have finalEq : initial.fresh.2 = final := congrArg Prod.snd success
  rw [← finalEq]
  exact .refl _

private theorem fresh_eq_integerLiterals_eq
    {initial final : Frontend.SourceInference.State}
    {type : TypeSystem.Ty}
    (success : initial.fresh = (type, final)) :
    final.integerLiterals = initial.integerLiterals := by
  have finalEq : initial.fresh.2 = final := congrArg Prod.snd success
  rw [← finalEq]
  rfl

private theorem fresh_eq_integerPatterns_eq
    {initial final : Frontend.SourceInference.State}
    {type : TypeSystem.Ty}
    (success : initial.fresh = (type, final)) :
    final.integerPatterns = initial.integerPatterns := by
  have finalEq : initial.fresh.2 = final := congrArg Prod.snd success
  rw [← finalEq]
  rfl

private theorem fresh_eq_requirements_eq
    {initial final : Frontend.SourceInference.State}
    {type : TypeSystem.Ty}
    (success : initial.fresh = (type, final)) :
    final.requirements = initial.requirements := by
  have finalEq : initial.fresh.2 = final := congrArg Prod.snd success
  rw [← finalEq]
  rfl

private theorem unify_success_typingSourceExtends
    {initial final : Frontend.SourceInference.State}
    {left right : TypeSystem.Ty}
    (success : Detail.unify initial left right = .ok final)
    (roots : List NodeId := []) :
    TypingSourceExtends (initial.toTypedSource roots)
      (final.toTypedSource roots) := by
  constructor
  · change final.owner = initial.owner
    have headerEq := Detail.unify_state_header success
    simpa [Frontend.SourceInference.State.header] using
      congrArg Frontend.SourceInference.State.Header.owner headerEq
  · change initial.nodes <+: final.nodes
    rw [(Detail.unify_occurrenceState_eq success).1]
    exact List.prefix_rfl

theorem actualInferExprFuelRetainedSoundness_index {fuel : Nat}
    (recursive : ActualInferExprFuelRetainedSoundness fuel) :
  ∀ {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn : Ty} {expression baseExpression indexExpression : Syntax.Expr}
    {brackets : Syntax.SourceSpan} {expected : Option Ty}
    {initial resultState evidenceState : State}
    {inferred : InferredExpression} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource}
    {frames : List InitializedLetBinding}
    {semanticContext : SourceSemantics.Context},
    expression.value = .index baseExpression brackets indexExpression →
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
  intro wholeContext inferenceContext wholeReturn expression baseExpression indexExpression brackets expected initial
    resultState evidenceState inferred roots finalized semanticSource
    frames semanticContext expressionEq success resources interfaces resultSubstitutionExtension signaturesEq
    ownerEq typeParametersEq assumptionsEq signatureFormation
    functionsCanonical catalog canonical invariant actual operational expectedBelow expectedAdmissible
    finalPreserved rawProper integerPatternsSubset integerLiteralsSubset requirementsSubset
    retained coercionsRetained _operatorsRetained childrenRetained covered semanticPreserved actualCovered
  generalize allocationEq : initial.allocateExpressionId = allocatedPair
  rcases allocatedPair with ⟨id, allocated⟩
  have allocatedInvariant := invariant.allocateExpressionId allocationEq
  have allocatedOperational : ActualStateInvariant allocated (evidenceState.toTypedSource roots) := by
    obtain ⟨pending, ledger⟩ := operational.ledger
    have stateEq : initial.allocateExpressionId.2 = allocated := congrArg Prod.snd allocationEq
    refine ⟨⟨pending, ?_⟩, ?_, ?_, operational.sourceMonomorphic⟩
    · rw [← stateEq]
      exact ledger.allocateExpressionId
    · apply operational.origins.congr_localBinders
      rw [← stateEq]
      rfl
    · apply activeQuantifiersBelowNext_transport operational.quantifiersBelow
      · rw [← stateEq]; rfl
      · rw [← stateEq]; exact Nat.le_refl _
  have allocatedExpected : ∀ type ∈ expected, type.VariablesBelow allocated.inference.next := by
    rw [allocateExpressionId_inferenceNext_eq allocationEq]
    exact expectedBelow
  obtain ⟨baseResult, baseState, keyType, keyState, valueType, valueState,
      mappingState, indexResult, indexState, baseSuccess, keyFresh, valueFresh,
      mappingSuccess, indexSuccess, recorded⟩ :=
    Detail.inferExprFuel_success_index_facts expressionEq allocationEq success
  have baseProperties := Detail.inferExprFuel_inferenceProperties
    allocatedInvariant.ready signatureFormation functionsCanonical (by
      intro expectedType member
      simp at member) baseSuccess
  have keyProperties := Detail.fresh_eq_inferenceProperties
    baseProperties.2.1 keyFresh
  have valueProperties := Detail.fresh_eq_inferenceProperties
    keyProperties.2.1 valueFresh
  have baseAtValue : baseResult.type.VariablesBelow
      valueState.inference.next :=
    baseProperties.2.2.weaken
      (keyProperties.1.trans valueProperties.1).next_le
  have keyAtValue : keyType.VariablesBelow valueState.inference.next :=
    keyProperties.2.2.weaken valueProperties.1.next_le
  have mappingBelow : (TypeSystem.Ty.mapping keyType valueType).VariablesBelow
      valueState.inference.next :=
    (TypeSystem.Ty.variablesBelow_mapping_iff _ _ _).2
      ⟨keyAtValue, valueProperties.2.2⟩
  have unifyProgress := Detail.unify_inferenceProgress
    valueProperties.2.1.solved baseAtValue mappingBelow mappingSuccess
  have mappingReady := Detail.unify_preserves_inferenceReady
    valueProperties.2.1 baseAtValue mappingBelow mappingSuccess
  have keyAtMapping : keyType.VariablesBelow mappingState.inference.next :=
    keyAtValue.weaken unifyProgress.next_le
  have resolvedKeyBelow :
      (mappingState.resolve keyType).VariablesBelow
        mappingState.inference.next :=
    mappingReady.solved.variablesBelow_apply keyAtMapping
  have indexProperties := Detail.inferExprFuel_inferenceProperties
    mappingReady signatureFormation functionsCanonical (by
      intro expectedType member
      simp only [Option.mem_def] at member
      have expectedTypeEq : expectedType = mappingState.resolve keyType :=
        (Option.some.inj member).symm
      rw [expectedTypeEq]
      exact resolvedKeyBelow) indexSuccess
  have allocatedToIndex : allocated.InferenceProgress indexState :=
    baseProperties.1.trans
      (keyProperties.1.trans
        (valueProperties.1.trans
          (unifyProgress.trans indexProperties.1)))
  have expectedAtIndex : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow indexState.inference.next := by
    intro expectedType member
    exact (allocatedExpected expectedType member).weaken allocatedToIndex.next_le
  have valueAtIndex : valueType.VariablesBelow indexState.inference.next :=
    valueProperties.2.2.weaken
      (unifyProgress.trans indexProperties.1).next_le
  have resolvedValueBelow :
      (indexState.resolve valueType).VariablesBelow
        indexState.inference.next :=
    indexProperties.2.1.solved.variablesBelow_apply valueAtIndex
  have recordedProperties :=
    Detail.recordExpressionWithExpected_inferenceProperties
      indexProperties.2.1 resolvedValueBelow expectedAtIndex recorded
  have laterIndex : finalized.substitution.SemanticallyExtends
      indexState.inference.substitution :=
    TypeSystem.Substitution.SemanticallyExtends.trans resultSubstitutionExtension
      recordedProperties.1.substitution_extends
  have laterMapping : finalized.substitution.SemanticallyExtends
      mappingState.inference.substitution :=
    TypeSystem.Substitution.SemanticallyExtends.trans laterIndex
      indexProperties.1.substitution_extends
  have allocatedBelow := allocatedInvariant.nodesBelow
  have baseBelow : baseState.NodesBelowNextOccurrence :=
    (Detail.inferExprFuel_occurrenceBoundExtends baseSuccess
      ).nodesBelowNextOccurrence allocatedBelow
  have keyBelow : keyState.NodesBelowNextOccurrence := by
    have below :=
      Frontend.SourceInference.State.fresh_preserves_nodesBelowNextOccurrence
        baseState baseBelow
    have stateEq : baseState.fresh.2 = keyState := congrArg Prod.snd keyFresh
    simpa [stateEq] using below
  have valueBelow : valueState.NodesBelowNextOccurrence := by
    have below :=
      Frontend.SourceInference.State.fresh_preserves_nodesBelowNextOccurrence
        keyState keyBelow
    have stateEq : keyState.fresh.2 = valueState :=
      congrArg Prod.snd valueFresh
    simpa [stateEq] using below
  have mappingNodesBelow : mappingState.NodesBelowNextOccurrence :=
    (Detail.unify_occurrenceBoundExtends mappingSuccess
      ).nodesBelowNextOccurrence valueBelow
  have indexBelow : indexState.NodesBelowNextOccurrence :=
    (Detail.inferExprFuel_occurrenceBoundExtends indexSuccess
      ).nodesBelowNextOccurrence mappingNodesBelow
  have baseToKey := fresh_eq_typingSourceExtends keyFresh roots
  have keyToValue := fresh_eq_typingSourceExtends valueFresh roots
  have valueToMapping := unify_success_typingSourceExtends mappingSuccess roots
  have mappingToIndex :=
    inferExprFuel_success_typingSourceExtends indexSuccess mappingNodesBelow roots
  have allocatedOwner : allocated.owner = initial.owner := by
    have stateEq : initial.allocateExpressionId.2 = allocated :=
      congrArg Prod.snd allocationEq
    rw [← stateEq]
    rfl
  have baseOwner : baseState.owner = allocated.owner :=
    Detail.inferExprFuel_preserves_owner baseSuccess
  have parentOwner : resultState.owner = initial.owner :=
    Detail.inferExprFuel_preserves_owner success
  have indexToParent : TypingSourceExtends
      (indexState.toTypedSource roots) (resultState.toTypedSource roots) := by
    constructor
    · exact parentOwner.trans
        (allocatedOwner.symm.trans
          (baseOwner.symm.trans
            (baseToKey.owner_eq.symm.trans
              (keyToValue.owner_eq.symm.trans
                (valueToMapping.owner_eq.symm.trans
                  mappingToIndex.owner_eq.symm)))))
    · exact recordExpressionWithExpected_success_nodesPrefix recorded
  have baseToParent :=
    TypingSourceExtends.trans baseToKey
      (TypingSourceExtends.trans keyToValue
        (TypingSourceExtends.trans valueToMapping
          (TypingSourceExtends.trans mappingToIndex indexToParent)))
  have indexIntegerLiteralsSubset :
      indexState.integerLiterals ⊆ resultState.integerLiterals := by
    intro origin member
    rw [Detail.recordExpressionWithExpected_integerLiterals_eq recorded]
    exact member
  have mappingIntegerLiteralsSubset :
      mappingState.integerLiterals ⊆ resultState.integerLiterals :=
    List.Subset.trans
      (Detail.inferExprFuel_integerLiterals_subset indexSuccess)
      indexIntegerLiteralsSubset
  have valueIntegerLiteralsSubset :
      valueState.integerLiterals ⊆ resultState.integerLiterals := by
    intro origin member
    apply mappingIntegerLiteralsSubset
    rw [Detail.unify_integerLiterals mappingSuccess]
    exact member
  have keyIntegerLiteralsSubset :
      keyState.integerLiterals ⊆ resultState.integerLiterals := by
    intro origin member
    apply valueIntegerLiteralsSubset
    rw [fresh_eq_integerLiterals_eq valueFresh]
    exact member
  have baseIntegerLiteralsSubset :
      baseState.integerLiterals ⊆ resultState.integerLiterals := by
    intro origin member
    apply keyIntegerLiteralsSubset
    rw [fresh_eq_integerLiterals_eq keyFresh]
    exact member
  have indexIntegerPatternsSubset :
      indexState.integerPatterns ⊆ resultState.integerPatterns := by
    intro origin member
    rw [recordExpressionWithExpected_integerPatterns_eq recorded]
    exact member
  have mappingIntegerPatternsSubset :
      mappingState.integerPatterns ⊆ resultState.integerPatterns :=
    List.Subset.trans
      (Detail.inferExprFuel_integerPatterns_subset indexSuccess)
      indexIntegerPatternsSubset
  have valueIntegerPatternsSubset :
      valueState.integerPatterns ⊆ resultState.integerPatterns := by
    intro origin member
    apply mappingIntegerPatternsSubset
    rw [(Detail.unify_integerPatternMetadata_eq mappingSuccess).1]
    exact member
  have keyIntegerPatternsSubset :
      keyState.integerPatterns ⊆ resultState.integerPatterns := by
    intro origin member
    apply valueIntegerPatternsSubset
    rw [fresh_eq_integerPatterns_eq valueFresh]
    exact member
  have baseIntegerPatternsSubset :
      baseState.integerPatterns ⊆ resultState.integerPatterns := by
    intro origin member
    apply keyIntegerPatternsSubset
    rw [fresh_eq_integerPatterns_eq keyFresh]
    exact member
  have indexRequirementsSubset :
      indexState.requirements ⊆ resultState.requirements :=
    Detail.recordExpressionWithExpected_requirements_subset recorded
  have mappingRequirementsSubset :
      mappingState.requirements ⊆ resultState.requirements :=
    List.Subset.trans
      (Detail.inferExprFuel_requirements_subset indexSuccess)
      indexRequirementsSubset
  have valueRequirementsSubset :
      valueState.requirements ⊆ resultState.requirements := by
    intro requirement member
    apply mappingRequirementsSubset
    rw [Detail.unify_requirements_eq mappingSuccess]
    exact member
  have keyRequirementsSubset :
      keyState.requirements ⊆ resultState.requirements := by
    intro requirement member
    apply valueRequirementsSubset
    rw [fresh_eq_requirements_eq valueFresh]
    exact member
  have baseRequirementsSubset :
      baseState.requirements ⊆ resultState.requirements := by
    intro requirement member
    apply keyRequirementsSubset
    rw [fresh_eq_requirements_eq keyFresh]
    exact member
  have laterValue := laterMapping.trans unifyProgress.substitution_extends
  have laterKey := laterValue.trans valueProperties.1.substitution_extends
  have laterBase := laterKey.trans keyProperties.1.substitution_extends
  have baseInvariant := allocatedInvariant.ofExpression signatureFormation functionsCanonical
    (by simp) laterBase baseSuccess
  have keyEq : baseState.fresh.2 = keyState := congrArg Prod.snd keyFresh
  have valueEq : keyState.fresh.2 = valueState := congrArg Prod.snd valueFresh
  have keyInvariant : RecursiveExpressionInvariant wholeContext finalized keyState semanticContext := by
    simpa only [keyEq] using baseInvariant.fresh (by simpa only [keyEq] using laterKey)
  have valueInvariant : RecursiveExpressionInvariant wholeContext finalized valueState semanticContext := by
    simpa only [valueEq] using keyInvariant.fresh (by simpa only [valueEq] using laterValue)
  have mappingInvariant := valueInvariant.unify baseAtValue mappingBelow laterMapping mappingSuccess
  have baseOperational := allocatedOperational.ofExpression baseSuccess baseProperties.1.next_le
  have keyOperational : ActualStateInvariant keyState (evidenceState.toTypedSource roots) := by
    simpa only [keyEq] using baseOperational.fresh
  have valueOperational : ActualStateInvariant valueState (evidenceState.toTypedSource roots) := by
    simpa only [valueEq] using keyOperational.fresh
  have mappingOperational := valueOperational.unify mappingSuccess
  have indexExpected : ∀ type ∈ (some (mappingState.resolve keyType) : Option Ty),
      type.VariablesBelow mappingState.inference.next := by
    intro type member
    have same : type = mappingState.resolve keyType := (Option.some.inj member).symm
    subst type
    exact resolvedKeyBelow
  obtain ⟨coercions, contains⟩ := recordExpressionWithExpected_success_containsExpression recorded roots
  have edge : ∀ child ∈ [baseResult.id, indexResult.id],
      DirectChild (resultState.toTypedSource roots) (.expression inferred.id) (.expression child) := by
    intro child member
    refine ⟨.expression _, ⟨contains.1, rfl⟩, ?_⟩
    simpa [nodeChildIds, Node.references, ExpressionForm.references] using
      (List.mem_map.mpr ⟨child, member, rfl⟩ : NodeId.expression child ∈
        [baseResult.id, indexResult.id].map NodeId.expression)
  have baseEdge := edge baseResult.id (by simp)
  have baseTypeRaw := actualInferExprFuelFinalSubtreeSoundness_of_retainedSoundness recursive
    baseSuccess resources interfaces laterBase signaturesEq ownerEq typeParametersEq assumptionsEq
    signatureFormation functionsCanonical catalog canonical allocatedInvariant actual allocatedOperational (by simp) (by simp)
    ((semanticPreserved.childSubtree baseEdge).monoBefore baseToParent)
    ((finalPreserved.childSubtree baseEdge).monoBefore baseToParent)
    ((rawProper.childSubtree baseEdge).monoBefore baseToParent).proper
    (List.Subset.trans baseIntegerPatternsSubset integerPatternsSubset)
    (List.Subset.trans baseIntegerLiteralsSubset integerLiteralsSubset)
    (List.Subset.trans baseRequirementsSubset requirementsSubset)
    (covered.expressionChild resources.graph_closed (childrenRetained baseEdge))
    (actualCovered.directChild (childrenRetained baseEdge))
  have unifiedEq : mappingState.resolve baseResult.type =
      mappingState.resolve (.mapping keyType valueType) := by
    simpa [Frontend.SourceInference.State.resolve] using
      Detail.unify_resolve_eq mappingSuccess
  have resolvedBaseEq :
      finalized.substitution.apply
          (mappingState.resolve baseResult.type) =
        finalized.substitution.apply baseResult.type := by
    simpa [Frontend.SourceInference.State.resolve,
      TypeSystem.InferState.resolve] using laterMapping baseResult.type
  have resolvedMappingEq :
      finalized.substitution.apply
          (mappingState.resolve (.mapping keyType valueType)) =
        finalized.substitution.apply (.mapping keyType valueType) := by
    simpa [Frontend.SourceInference.State.resolve,
      TypeSystem.InferState.resolve] using
        laterMapping (.mapping keyType valueType)
  have baseEq : finalized.substitution.apply baseResult.type =
      .mapping (finalized.substitution.apply keyType)
        (finalized.substitution.apply valueType) := by
    calc
      finalized.substitution.apply baseResult.type =
          finalized.substitution.apply
            (mappingState.resolve baseResult.type) := resolvedBaseEq.symm
      _ = finalized.substitution.apply
          (mappingState.resolve (.mapping keyType valueType)) :=
        congrArg finalized.substitution.apply unifiedEq
      _ = finalized.substitution.apply
          (.mapping keyType valueType) := resolvedMappingEq
      _ = .mapping (finalized.substitution.apply keyType)
          (finalized.substitution.apply valueType) := rfl
  have resolvedKeyEq :
      finalized.substitution.apply (mappingState.resolve keyType) =
        finalized.substitution.apply keyType := by
    simpa [Frontend.SourceInference.State.resolve,
      TypeSystem.InferState.resolve] using laterMapping keyType
  have indexEdge := edge indexResult.id (by simp)
  have indexTypeRaw := actualInferExprFuelFinalSubtreeSoundness_of_retainedSoundness recursive
    indexSuccess resources interfaces laterIndex signaturesEq ownerEq typeParametersEq assumptionsEq
    signatureFormation functionsCanonical catalog canonical mappingInvariant actual mappingOperational indexExpected
    (by
      intro type member
      have same : type = mappingState.resolve keyType := (Option.some.inj member).symm
      subst type
      rw [resolvedKeyEq]
      have baseAdmissible := baseTypeRaw.type_admissible
      rw [baseEq] at baseAdmissible
      exact TypeAdmissible.mapping_key baseAdmissible)
    ((semanticPreserved.childSubtree indexEdge).monoBefore indexToParent)
    ((finalPreserved.childSubtree indexEdge).monoBefore indexToParent)
    ((rawProper.childSubtree indexEdge).monoBefore indexToParent).proper
    (List.Subset.trans indexIntegerPatternsSubset integerPatternsSubset)
    (List.Subset.trans indexIntegerLiteralsSubset integerLiteralsSubset)
    (List.Subset.trans indexRequirementsSubset requirementsSubset)
    (covered.expressionChild resources.graph_closed (childrenRetained indexEdge))
    (actualCovered.directChild (childrenRetained indexEdge))
  have indexExpectedEq :
      finalized.substitution.apply indexResult.type =
        finalized.substitution.apply
          (mappingState.resolve keyType) :=
    Detail.inferExprFuel_expected_type_apply_eq indexSuccess laterIndex
  have resolvedValueEq :
      finalized.substitution.apply (indexState.resolve valueType) =
        finalized.substitution.apply valueType := by
    simpa [Frontend.SourceInference.State.resolve,
      TypeSystem.InferState.resolve] using laterIndex valueType
  have baseType : ExpressionHasType semanticSource semanticContext baseResult.id
      (.mapping (finalized.substitution.apply keyType)
        (finalized.substitution.apply valueType)) := by
    rw [← baseEq]
    exact baseTypeRaw
  have indexType : ExpressionHasType semanticSource semanticContext indexResult.id
      (finalized.substitution.apply keyType) := by
    rw [← resolvedKeyEq, ← indexExpectedEq]
    exact indexTypeRaw
  have formType : ExpressionFormHasRawType semanticSource semanticContext
      ((ExpressionForm.index baseResult.id indexResult.id).applySubstitution
        finalized.substitution)
      (finalized.substitution.apply (indexState.resolve valueType))
      (.ordinary []) := by
    rw [resolvedValueEq]
    simpa [ExpressionForm.applySubstitution] using
      ExpressionFormHasRawType.index baseType indexType
  have rawAdmissible : TypeAdmissible semanticContext
      (finalized.substitution.apply (indexState.resolve valueType)) := by
    rw [resolvedValueEq]
    exact TypeAdmissible.mapping_value baseType.type_admissible
  exact recordExpressionWithExpected_success_expressionTypingBase_actual resources interfaces
    recorded resultSubstitutionExtension requirementsSubset retained coercionsRetained
    catalog signaturesEq invariant formType rawAdmissible covered

end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedLambdaSoundness
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

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

theorem actualInferExprFuelRetainedSoundness_lambda {fuel : Nat}
    (bodySound : ActualInferStatementsFuelRootedSoundness fuel) :
  ∀ {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn : Ty} {expression : Syntax.Expr} {keyword : Syntax.SourceSpan}
    {sourceParameters : Syntax.DelimitedList Syntax.LambdaParameter}
    {returnAnnotation : Option Syntax.TypeExpr} {body : Syntax.Block} {expected : Option Ty}
    {initial resultState evidenceState : State}
    {inferred : InferredExpression} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource}
    {frames : List InitializedLetBinding}
    {semanticContext : SourceSemantics.Context},
    expression.value = .lambda keyword sourceParameters returnAnnotation body →
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
  intro wholeContext inferenceContext wholeReturn expression keyword sourceParameters returnAnnotation body expected initial
    resultState evidenceState inferred roots finalized semanticSource
    frames semanticContext expressionEq success resources interfaces resultSubstitutionExtension signaturesEq
    ownerEq typeParametersEq assumptionsEq signatureFormation
    functionsCanonical catalog canonical invariant actual operational expectedBelow expectedAdmissible
    finalPreserved rawProper integerPatternsSubset integerLiteralsSubset requirementsSubset
    retained coercionsRetained _operatorsRetained childrenRetained covered semanticPreserved actualCovered
  generalize allocationEq : initial.allocateExpressionId = allocatedPair
  rcases allocatedPair with ⟨id, allocated⟩
  have allocatedInvariant := invariant.allocateExpressionId allocationEq
  have allocatedOperational := operational.allocateExpressionId allocationEq
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
      (childrenRetained (bodyEdge statement member))
    intro predicate predicateMember
    rw [MonoBindersExtend.assumptions_eq parametersExtendSource]
    exact predicateMember
  have parameterScope := bindLambdaParameters_preserves_actualScope allocatedOperational
    allocatedInvariant.schemeIsolation parametersSuccess
  have prefixScope := lambdaPrefixFacts_preserves_actualScope parameterScope.1 parameterScope.2 prefixFacts
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
    schemeIsolation := prefixScope.2
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
  obtain ⟨bodyFinal, bodyFacts, _, _, _, bodyType, bodyAgreement⟩ :=
    bodySound bodySuccess resources interfaces signaturesEq ownerEq typeParametersEq assumptionsEq
      signatureFormation functionsCanonical catalog canonical prefixInvariant
      (actual.monoBinders parametersExtend) prefixScope.1
      (by
        apply StructuralSubstitution.TypeAdmissible.transportContext (source := semanticContext)
        · exact lambdaFields.1
        · exact lambdaFields.2.1
        · exact lambdaFields.2.2.1
        · exact (actual.monoBinders parametersExtend).variables_eq.trans actual.variables_eq.symm
        · exact lambdaFields.2.2.2.1
        · exact resultAdmissible)
      laterExtendsBody
      (fun statement member => ((semanticPreserved.childSubtree (bodyEdge statement member)).monoBefore bodyToResultRaw))
      (fun statement member => ((rawProper.childSubtree (bodyEdge statement member)).monoBefore bodyToResultRaw))
      bodyIntegerPatternsToEvidence bodyIntegerLiteralsToEvidence bodyRequirementsToEvidence bodyCovered
      (fun statement member => actualCovered.directChild (childrenRetained (bodyEdge statement member)))
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
    recordSuccess resultSubstitutionExtension requirementsSubset retained coercionsRetained
    catalog signaturesEq invariant formType rawAdmissible covered

end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedTupleSoundness
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

theorem actualInferExprFuelRetainedSoundness_tuple {fuel : Nat}
    (recursive : ∀ smaller, smaller < fuel + 1 → ActualInferExprFuelRetainedSoundness smaller) :
  ∀ {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn : Ty} {expression : Syntax.Expr} {elements : Syntax.DelimitedList Syntax.Expr} {expected : Option Ty}
    {initial resultState evidenceState : State}
    {inferred : InferredExpression} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource}
    {frames : List InitializedLetBinding}
    {semanticContext : SourceSemantics.Context},
    expression.value = .tuple elements →
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
  intro wholeContext inferenceContext wholeReturn expression elements expected initial
    resultState evidenceState inferred roots finalized semanticSource
    frames semanticContext expressionEq success resources interfaces resultSubstitutionExtension signaturesEq
    ownerEq typeParametersEq assumptionsEq signatureFormation
    functionsCanonical catalog canonical invariant actual operational expectedBelow expectedAdmissible
    finalPreserved rawProper integerPatternsSubset integerLiteralsSubset requirementsSubset
    retained coercionsRetained _operatorsRetained childrenRetained covered semanticPreserved actualCovered
  generalize allocationEq : initial.allocateExpressionId = allocatedPair
  rcases allocatedPair with ⟨id, allocated⟩
  have allocatedInvariant := invariant.allocateExpressionId allocationEq
  have allocatedOperational : ActualStateInvariant allocated (evidenceState.toTypedSource roots) := by
    obtain ⟨pending, ledger⟩ := operational.ledger
    have stateEq : initial.allocateExpressionId.2 = allocated := congrArg Prod.snd allocationEq
    refine ⟨⟨pending, ?_⟩, ?_, ?_, operational.sourceMonomorphic⟩
    · rw [← stateEq]
      exact ledger.allocateExpressionId
    · apply operational.origins.congr_localBinders
      rw [← stateEq]
      rfl
    · apply activeQuantifiersBelowNext_transport operational.quantifiersBelow
      · rw [← stateEq]; rfl
      · rw [← stateEq]; exact Nat.le_refl _
  have allocatedExpected : ∀ type ∈ expected, type.VariablesBelow allocated.inference.next := by
    rw [allocateExpressionId_inferenceNext_eq allocationEq]
    exact expectedBelow
  obtain ⟨elementsResult, elementsState, elementsSuccess, recorded⟩ :=
    Detail.inferExprFuel_success_tuple_facts expressionEq allocationEq success
  have properties := Detail.inferExprsFuel_inferenceProperties allocatedInvariant.ready
    signatureFormation functionsCanonical elementsSuccess
  have elementsExpected : ∀ type ∈ expected, type.VariablesBelow elementsState.inference.next := by
    intro type member
    exact (allocatedExpected type member).weaken properties.1.next_le
  have rawBelow : (Ty.productMany (elementsResult.map (·.type))).VariablesBelow elementsState.inference.next :=
    Ty.variablesBelow_productMany (by
      intro type member
      obtain ⟨element, elementMember, rfl⟩ := List.mem_map.mp member
      exact properties.2.2 element elementMember)
  have recording := Detail.recordExpressionWithExpected_inferenceProperties
    properties.2.1 rawBelow elementsExpected recorded
  have elementsExtension := resultSubstitutionExtension.trans recording.1.substitution_extends
  have allocatedOwner : allocated.owner = initial.owner := by
    have stateEq : initial.allocateExpressionId.2 = allocated := congrArg Prod.snd allocationEq
    rw [← stateEq]
    rfl
  have allocatedToElements := inferExprsFuel_success_typingSourceExtends_under_bound
    elementsSuccess allocatedInvariant.nodesBelow roots
  have elementsToParent : TypingSourceExtends (elementsState.toTypedSource roots)
      (resultState.toTypedSource roots) := by
    refine ⟨?_, recordExpressionWithExpected_success_nodesPrefix recorded⟩
    exact (Detail.inferExprFuel_preserves_owner success).trans
      (allocatedOwner.symm.trans allocatedToElements.owner_eq.symm)
  obtain ⟨coercions, contains⟩ := recordExpressionWithExpected_success_containsExpression recorded roots
  have edge : ∀ element ∈ elementsResult, DirectChild (resultState.toTypedSource roots)
      (.expression inferred.id) (.expression element.id) := by
    intro element member
    refine ⟨.expression _, ⟨contains.1, rfl⟩, ?_⟩
    simpa [nodeChildIds, Node.references, ExpressionForm.references] using
      (List.mem_map.mpr ⟨element.id, List.mem_map.mpr ⟨element, member, rfl⟩, rfl⟩ :
        NodeId.expression element.id ∈ (elementsResult.map (·.id)).map NodeId.expression)
  have childPatterns : elementsState.integerPatterns ⊆ evidenceState.integerPatterns := by
    rw [← recordExpressionWithExpected_integerPatterns_eq recorded]
    exact integerPatternsSubset
  have childLiterals : elementsState.integerLiterals ⊆ evidenceState.integerLiterals := by
    rw [← Detail.recordExpressionWithExpected_integerLiterals_eq recorded]
    exact integerLiteralsSubset
  have childRequirements := List.Subset.trans
    (Detail.recordExpressionWithExpected_requirements_subset recorded) requirementsSubset
  have typed := actualInferExprsFuelFinalSubtreeSoundness fuel
    (fun smaller less => recursive smaller (Nat.lt_trans less (Nat.lt_succ_self fuel)))
    elementsSuccess resources interfaces elementsExtension signaturesEq ownerEq typeParametersEq assumptionsEq
    signatureFormation functionsCanonical catalog canonical allocatedInvariant actual allocatedOperational
    (fun element member => (semanticPreserved.childSubtree (edge element member)).monoBefore elementsToParent)
    (fun element member => (finalPreserved.childSubtree (edge element member)).monoBefore elementsToParent)
    (fun element member => ((rawProper.childSubtree (edge element member)).monoBefore elementsToParent).proper)
    childPatterns childLiterals childRequirements
    (fun element member => covered.expressionChild resources.graph_closed (childrenRetained (edge element member)))
    (fun element member => actualCovered.directChild (childrenRetained (edge element member)))
  have formType : ExpressionFormHasRawType semanticSource semanticContext
      ((ExpressionForm.tuple (elementsResult.map (·.id))).applySubstitution finalized.substitution)
      (finalized.substitution.apply (Ty.productMany (elementsResult.map (·.type)))) (.ordinary []) := by
    simpa [ExpressionForm.applySubstitution, FlexibleSubstitution.apply_productMany,
      List.map_map, Function.comp_def] using ExpressionFormHasRawType.tuple typed
  have rawAdmissible : TypeAdmissible semanticContext
      (finalized.substitution.apply (Ty.productMany (elementsResult.map (·.type)))) := by
    simpa [FlexibleSubstitution.apply_productMany, List.map_map, Function.comp_def] using
      typed.product_type_admissible (invariant.typeParameterBinders (by
        simpa [ownerEq, typeParametersEq] using canonical))
  exact recordExpressionWithExpected_success_expressionTypingBase_actual resources interfaces
    recorded resultSubstitutionExtension requirementsSubset retained coercionsRetained
    catalog signaturesEq invariant formType rawAdmissible covered

end Solcore.SourceSemantics.SourceInferenceSoundness
end
