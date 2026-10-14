import Solcore.SourceSemantics.SourceInferenceSelectedFreshConstructor

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

theorem actualInferExprFuelRetainedSoundness_call_constructor {fuel : Nat}
    (recursive : ActualInferExprFuelRetainedSoundness fuel) :
  ∀ {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn : Ty} {dataType : ProgramDataSignature} {constructor : ProgramDataConstructorSignature} {expression callee : Syntax.Expr} {arguments : Syntax.DelimitedList Syntax.Expr} {expected : Option Ty}
    {initial resultState evidenceState : State}
    {inferred : InferredExpression} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource}
    {frames : List InitializedLetBinding}
    {semanticContext : SourceSemantics.Context},
    expression.value = .call callee arguments →
    Detail.constructorCalleeCandidates inferenceContext initial.allocateExpressionId.2 callee = .ok [(dataType, constructor)] →
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
  intro wholeContext inferenceContext wholeReturn dataType constructor expression callee arguments expected initial
    resultState evidenceState inferred roots finalized semanticSource frames semanticContext expressionEq discovery success
    resources interfaces extension signaturesEq ownerEq typeParametersEq assumptionsEq formation functions catalog canonical
    invariant actual operational expectedBelow _expectedAdmissible final raw patterns literals requirements retained
    coercionsRetained _operatorsRetained childrenRetained covered semantic actualCovered
  generalize allocationEq : initial.allocateExpressionId = allocatedPair
  obtain ⟨id, allocated⟩ := allocatedPair
  have allocatedInvariant := invariant.allocateExpressionId allocationEq
  have allocatedOperational := operational.allocateExpressionId allocationEq
  have allocatedExpected : ∀ type ∈ expected, type.VariablesBelow allocated.inference.next := by
    rw [allocateExpressionId_inferenceNext_eq allocationEq]; exact expectedBelow
  have found : Detail.constructorCalleeCandidates inferenceContext allocated callee = .ok [(dataType, constructor)] := by
    simpa only [allocationEq] using discovery
  have members := Detail.constructorCalleeCandidates_success_members found dataType constructor (by simp)
  unfold Detail.inferExprFuel at success
  simp only [allocationEq, expressionEq, found, bind, Except.bind] at success
  generalize fresh : Detail.freshDataConstructorInstantiation dataType constructor allocated = pair at success
  obtain ⟨instantiation, constructorState⟩ := pair
  exact actualFreshConstructorApplication_typing recursive members.1 members.2 fresh success resources interfaces
    extension signaturesEq ownerEq typeParametersEq assumptionsEq formation functions catalog canonical allocatedInvariant actual
    allocatedOperational allocatedExpected semantic final raw patterns literals requirements retained coercionsRetained
    childrenRetained covered actualCovered

theorem actualInferExprFuelRetainedSoundness_dotConstructor {fuel : Nat}
    (recursive : ActualInferExprFuelRetainedSoundness fuel) :
  ∀ {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn : Ty} {expression : Syntax.Expr} {dot : Syntax.SourceSpan} {name : Syntax.Identifier}
    {arguments : Option (Syntax.DelimitedList Syntax.Expr)} {expected : Option Ty}
    {initial resultState evidenceState : State}
    {inferred : InferredExpression} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource}
    {frames : List InitializedLetBinding}
    {semanticContext : SourceSemantics.Context},
    expression.value = .dotConstructor dot name arguments →
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
  intro wholeContext inferenceContext wholeReturn expression dot name arguments expected initial
    resultState evidenceState inferred roots finalized semanticSource frames semanticContext expressionEq success
    resources interfaces extension signaturesEq ownerEq typeParametersEq assumptionsEq formation functions catalog canonical
    invariant actual operational expectedBelow expectedAdmissible final raw patterns literals requirements retained
    coercionsRetained _operatorsRetained childrenRetained covered semantic actualCovered
  generalize allocationEq : initial.allocateExpressionId = allocatedPair
  obtain ⟨id, allocated⟩ := allocatedPair
  have allocatedInvariant := invariant.allocateExpressionId allocationEq
  have allocatedOperational := operational.allocateExpressionId allocationEq
  have allocatedExpected : ∀ type ∈ expected, type.VariablesBelow allocated.inference.next := by
    rw [allocateExpressionId_inferenceNext_eq allocationEq]; exact expectedBelow
  unfold Detail.inferExprFuel at success
  simp only [allocationEq, expressionEq, bind, Except.bind] at success
  cases selected : Detail.contextualConstructorCandidate inferenceContext allocated expected name.value with
  | error error => simp [selected] at success
  | ok selectedPair =>
    obtain ⟨dataType, constructor, typeArguments⟩ := selectedPair
    simp only [selected] at success
    obtain ⟨dataMember, constructorMember, expectedType, expectedEq, nominalEq⟩ :=
      Detail.contextualConstructorCandidate_success_facts selected
    have bounded := Detail.contextualConstructorCandidate_success_instantiation_variablesBelow
      allocatedInvariant.ready allocatedExpected formation selected
    have activeCatalog : SignatureCatalogWellFormed semanticContext.signatures := by
      rw [invariant.signatures_eq_whole, ← signaturesEq]; exact catalog
    have activeData : dataType ∈ semanticContext.signatures.dataTypes := by
      rw [invariant.signatures_eq_whole, ← signaturesEq]; exact dataMember
    have resultAdmissible : TypeAdmissible semanticContext
        (finalized.substitution.apply (Detail.instantiateDataConstructor dataType constructor typeArguments).resultType) := by
      have expectedTyped := expectedAdmissible expectedType (by simp [expectedEq])
      have resolved : finalized.substitution.apply (allocated.resolve expectedType) =
          finalized.substitution.apply expectedType := by
        simpa only [State.resolve, InferState.resolve] using allocatedInvariant.substitutionExtension expectedType
      rw [← resolved, nominalEq] at expectedTyped
      exact expectedTyped
    have valid := SourceSemantics.DataConstructorInstantiation.Admissible.instantiateDataConstructor_applySubstitution
      activeCatalog activeData constructorMember finalized.substitution resultAdmissible
    exact actualConstructorApplication_typing recursive success resources interfaces extension signaturesEq ownerEq typeParametersEq
      assumptionsEq formation functions catalog canonical allocatedInvariant actual allocatedOperational bounded.1 bounded.2
      allocatedExpected valid semantic final raw patterns literals requirements retained coercionsRetained childrenRetained
      covered actualCovered

theorem actualInferExprFuelRetainedSoundness_field_constructor {fuel : Nat}
    (recursive : ActualInferExprFuelRetainedSoundness fuel) :
  ∀ {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn : Ty} {expression base : Syntax.Expr} {dot : Syntax.SourceSpan} {name : Syntax.Identifier} {expected : Option Ty}
    {initial resultState evidenceState : State}
    {inferred : InferredExpression} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource}
    {frames : List InitializedLetBinding}
    {semanticContext : SourceSemantics.Context},
    expression.value = .field base dot name →
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
  intro wholeContext inferenceContext wholeReturn expression base dot name expected initial
    resultState evidenceState inferred roots finalized semanticSource frames semanticContext expressionEq success
    resources interfaces extension signaturesEq ownerEq typeParametersEq assumptionsEq formation functions catalog canonical
    invariant actual operational expectedBelow _expectedAdmissible final raw patterns literals requirements retained
    coercionsRetained _operatorsRetained childrenRetained covered semantic actualCovered
  generalize allocationEq : initial.allocateExpressionId = allocatedPair
  obtain ⟨id, allocated⟩ := allocatedPair
  have allocatedInvariant := invariant.allocateExpressionId allocationEq
  have allocatedOperational := operational.allocateExpressionId allocationEq
  have allocatedExpected : ∀ type ∈ expected, type.VariablesBelow allocated.inference.next := by
    rw [allocateExpressionId_inferenceNext_eq allocationEq]; exact expectedBelow
  unfold Detail.inferExprFuel at success
  simp only [allocationEq, expressionEq, bind, Except.bind] at success
  cases discovery : Detail.constructorCalleeCandidates inferenceContext allocated expression with
  | error error => simp [discovery] at success
  | ok candidates =>
    cases candidates with
    | nil =>
      simp only [discovery] at success
      repeat' split at success
      all_goals simp_all [throw]
    | cons first rest =>
      obtain ⟨dataType, constructor⟩ := first
      cases rest with
      | cons second tail => simp [discovery] at success
      | nil =>
        simp only [discovery] at success
        have members := Detail.constructorCalleeCandidates_success_members discovery dataType constructor (by simp)
        generalize fresh : Detail.freshDataConstructorInstantiation dataType constructor allocated = pair at success
        obtain ⟨instantiation, constructorState⟩ := pair
        exact actualFreshConstructorApplication_typing recursive members.1 members.2 fresh success resources interfaces
          extension signaturesEq ownerEq typeParametersEq assumptionsEq formation functions catalog canonical allocatedInvariant actual
          allocatedOperational allocatedExpected semantic final raw patterns literals requirements retained coercionsRetained
          childrenRetained covered actualCovered

end Solcore.SourceSemantics.SourceInferenceSoundness
