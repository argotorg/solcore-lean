import Solcore.SourceSemantics.SourceInferenceSelectedChildSoundness
import Solcore.SourceSemantics.SourceInferenceSelectedExpressionState
import Solcore.SourceSemantics.SourceInferenceExpressionDispatchSoundness

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

theorem actualInferExprsFuelFinalSubtreeSoundness : ∀ fuel : Nat,
    (∀ smaller, smaller < fuel → ActualInferExprFuelRetainedSoundness smaller) →
  ∀ {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn : Ty} {expressions : List Syntax.Expr}
    {initial resultState evidenceState : State}
    {inferred : List InferredExpression} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource}
    {frames : List InitializedLetBinding}
    {semanticContext : SourceSemantics.Context},
    Detail.inferExprsFuel fuel inferenceContext expressions initial =
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
    (∀ argument ∈ inferred, SubtreePreserved finalized.substitution
      (resultState.toTypedSource roots) semanticSource (.expression argument.id)) →
    (∀ argument ∈ inferred, SubtreePreserved finalized.substitution (resultState.toTypedSource roots)
      finalized.typedSource (.expression argument.id)) →
    (∀ argument ∈ inferred, RawProperDescendantsPreserved (resultState.toTypedSource roots)
      (evidenceState.toTypedSource roots) (.expression argument.id)) →
    resultState.integerPatterns ⊆ evidenceState.integerPatterns →
    resultState.integerLiterals ⊆ evidenceState.integerLiterals →
    resultState.requirements ⊆ evidenceState.requirements →
    (∀ argument ∈ inferred, TemplateScopeCovered finalized.typedSource semanticContext
      (.expression argument.id)) →
    (∀ argument ∈ inferred, ActualContext.Covers finalized frames (.expression argument.id)) →
    ExpressionsHaveTypes semanticSource semanticContext (inferred.map (·.id))
      (inferred.map fun argument => finalized.substitution.apply argument.type) := by
  intro fuel
  induction fuel with
  | zero =>
    intro recursive wholeContext inferenceContext wholeReturn expressions initial
      resultState evidenceState inferred roots finalized semanticSource frames semanticContext success
    simp [Detail.inferExprsFuel] at success
  | succ fuel induction =>
    intro recursive wholeContext inferenceContext wholeReturn expressions initial
      resultState evidenceState inferred roots finalized semanticSource frames semanticContext success
      resources interfaces extension signaturesEq ownerEq typeParametersEq assumptionsEq
      signatureFormation functionsCanonical catalog canonical invariant actual operational
      semanticPreserved finalPreserved rawProper integerPatternsSubset integerLiteralsSubset requirementsSubset
      covered actualCovered
    cases expressions with
    | nil =>
      simp only [Detail.inferExprsFuel, Except.ok.injEq, Prod.mk.injEq] at success
      cases success.1
      exact .nil semanticContext
    | cons expression rest =>
      unfold Detail.inferExprsFuel at success
      cases headSuccess : Detail.inferExprFuel fuel inferenceContext expression none initial with
      | error error => simp [headSuccess, bind, Except.bind] at success
      | ok pair =>
        rcases pair with ⟨head, headState⟩
        simp only [headSuccess, bind, Except.bind] at success
        cases tailSuccess : Detail.inferExprsFuel fuel inferenceContext rest headState with
        | error error => simp [tailSuccess] at success
        | ok pair =>
          rcases pair with ⟨tail, tailState⟩
          simp only [tailSuccess, pure, Pure.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at success
          rcases success with ⟨rfl, rfl⟩
          have headProperties := Detail.inferExprFuel_inferenceProperties invariant.ready
            signatureFormation functionsCanonical (by simp) headSuccess
          have tailProperties := Detail.inferExprsFuel_inferenceProperties headProperties.2.1
            signatureFormation functionsCanonical tailSuccess
          have headExtension := extension.trans tailProperties.1.substitution_extends
          have headInvariant := invariant.ofExpression signatureFormation functionsCanonical
            (by simp) headExtension headSuccess
          have headOperational := operational.ofExpression headSuccess headProperties.1.next_le
          have headToFinal := inferExprsFuel_success_typingSourceExtends_under_bound
            tailSuccess headInvariant.nodesBelow roots
          have headTyped := actualInferExprFuelFinalSubtreeSoundness_of_retainedSoundness
            (recursive fuel (Nat.lt_succ_self fuel)) headSuccess resources interfaces headExtension
            signaturesEq ownerEq typeParametersEq assumptionsEq signatureFormation functionsCanonical
            catalog canonical invariant actual operational (by simp) (by simp)
            ((semanticPreserved head (by simp)).monoBefore headToFinal)
            ((finalPreserved head (by simp)).monoBefore headToFinal)
            ((rawProper head (by simp)).monoBefore headToFinal)
            (List.Subset.trans (Detail.inferExprsFuel_integerPatterns_subset tailSuccess) integerPatternsSubset)
            (List.Subset.trans (Detail.inferExprsFuel_integerLiterals_subset tailSuccess) integerLiteralsSubset)
            (List.Subset.trans (Detail.inferExprsFuel_requirements_subset tailSuccess) requirementsSubset)
            (covered head (by simp)) (actualCovered head (by simp))
          have tailTyped := induction
            (fun smaller less => recursive smaller (Nat.lt_trans less (Nat.lt_succ_self fuel)))
            tailSuccess resources interfaces extension signaturesEq ownerEq typeParametersEq assumptionsEq
            signatureFormation functionsCanonical catalog canonical headInvariant actual headOperational
            (fun argument member => semanticPreserved argument (List.mem_cons_of_mem _ member))
            (fun argument member => finalPreserved argument (List.mem_cons_of_mem _ member))
            (fun argument member => rawProper argument (List.mem_cons_of_mem _ member))
            integerPatternsSubset integerLiteralsSubset requirementsSubset
            (fun argument member => covered argument (List.mem_cons_of_mem _ member))
            (fun argument member => actualCovered argument (List.mem_cons_of_mem _ member))
          exact .cons headTyped tailTyped

end Solcore.SourceSemantics.SourceInferenceSoundness
