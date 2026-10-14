import Solcore.SourceSemantics.SourceInferenceSelectedNamedCall
import Solcore.SourceSemantics.SourceInferenceSelectedBuiltinCall
import Solcore.SourceSemantics.SourceInferenceSelectedIndirectCall

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

theorem actualInferExprFuelRetainedSoundness_call_nonConstructor {fuel : Nat}
    (recursive : ∀ smaller, smaller < fuel + 1 → ActualInferExprFuelRetainedSoundness smaller) :
  ∀ {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn : Ty} {expression callee : Syntax.Expr} {arguments : Syntax.DelimitedList Syntax.Expr} {expected : Option Ty}
    {initial resultState evidenceState : State}
    {inferred : InferredExpression} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource}
    {frames : List InitializedLetBinding}
    {semanticContext : SourceSemantics.Context},
    expression.value = .call callee arguments →
    Detail.constructorCalleeCandidates inferenceContext initial.allocateExpressionId.2 callee = .ok [] →
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
  intro wholeContext inferenceContext wholeReturn expression callee arguments expected initial
    resultState evidenceState inferred roots finalized semanticSource
    frames semanticContext expressionEq nonConstructor success resources interfaces resultSubstitutionExtension signaturesEq
    ownerEq typeParametersEq assumptionsEq signatureFormation
    functionsCanonical catalog canonical invariant actual operational expectedBelow expectedAdmissible
    finalPreserved rawProper integerPatternsSubset integerLiteralsSubset requirementsSubset
    retained coercionsRetained _operatorsRetained childrenRetained covered semanticPreserved actualCovered
  generalize allocationEq : initial.allocateExpressionId = allocatedPair
  rcases allocatedPair with ⟨id, allocated⟩
  have allocatedInvariant := invariant.allocateExpressionId allocationEq
  have allocatedOperational := operational.allocateExpressionId allocationEq
  have allocatedExpected : ∀ type ∈ expected, type.VariablesBelow allocated.inference.next := by
    rw [allocateExpressionId_inferenceNext_eq allocationEq]
    exact expectedBelow
  have noConstructor : Detail.constructorCalleeCandidates inferenceContext allocated callee = .ok [] := by
    simpa only [allocationEq] using nonConstructor
  cases inferExprFuel_success_call_dispatch_facts expressionEq allocationEq success with
  | constructor discovery fresh application =>
    rw [noConstructor] at discovery
    cases discovery
  | selected argumentsSuccess origin selection recording =>
    exact actualSelectedCall_typing
      (fun smaller less => recursive smaller (Nat.lt_trans less (Nat.lt_succ_self fuel)))
      argumentsSuccess selection recording origin.candidatesSubset
      resources interfaces resultSubstitutionExtension signaturesEq ownerEq typeParametersEq assumptionsEq
      signatureFormation functionsCanonical catalog canonical allocatedInvariant actual allocatedOperational
      allocatedExpected expectedAdmissible finalPreserved rawProper integerPatternsSubset integerLiteralsSubset
      requirementsSubset retained coercionsRetained _operatorsRetained childrenRetained covered semanticPreserved actualCovered
  | builtin argumentsSuccess recording =>
    exact actualBuiltinCall_typing
      (fun smaller less => recursive smaller (Nat.lt_trans less (Nat.lt_succ_self fuel)))
      argumentsSuccess recording resources interfaces resultSubstitutionExtension
      signaturesEq ownerEq typeParametersEq assumptionsEq signatureFormation functionsCanonical catalog canonical
      allocatedInvariant actual allocatedOperational allocatedExpected expectedAdmissible finalPreserved rawProper
      integerPatternsSubset integerLiteralsSubset requirementsSubset retained coercionsRetained _operatorsRetained
      childrenRetained covered semanticPreserved actualCovered
  | indirect argumentsSuccess calleeSuccess applicationSuccess recording =>
    exact actualIndirectCall_typing recursive argumentsSuccess calleeSuccess applicationSuccess recording
      resources interfaces resultSubstitutionExtension signaturesEq ownerEq typeParametersEq assumptionsEq
      signatureFormation functionsCanonical catalog canonical allocatedInvariant actual allocatedOperational
      allocatedExpected expectedAdmissible finalPreserved rawProper integerPatternsSubset integerLiteralsSubset
      requirementsSubset retained coercionsRetained _operatorsRetained childrenRetained covered semanticPreserved actualCovered

end Solcore.SourceSemantics.SourceInferenceSoundness
