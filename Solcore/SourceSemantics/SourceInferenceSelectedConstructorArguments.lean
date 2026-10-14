import Solcore.SourceSemantics.SourceInferenceSelectedAttachedChild
import Solcore.SourceSemantics.SourceInferenceSelectedExpressionState

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

theorem actualInferConstructorArgumentsFuelTypes {fuel : Nat}
    (recursive : ActualInferExprFuelRetainedSoundness fuel) :
  ∀ {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn : Ty} {sources : List Syntax.Expr} {expectedTypes : List Ty}
    {initial resultState evidenceState : State} {inferred : List InferredExpression}
    {roots : List NodeId} {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource} {frames : List InitializedLetBinding} {semanticContext : SourceSemantics.Context},
    Detail.inferConstructorArgumentsFuel fuel inferenceContext sources expectedTypes initial = .ok (inferred, resultState) →
    FinalInferenceResources wholeContext wholeReturn evidenceState roots finalized →
    ExecutableCoercionInterfaces.SourceInterfaces wholeContext.signatures finalized.solvedRequirements finalized.typedSource →
    finalized.substitution.SemanticallyExtends resultState.inference.substitution →
    inferenceContext.signatures = wholeContext.signatures →
    inferenceContext.scope.genericOwner = wholeContext.scope.genericOwner →
    inferenceContext.typeParameters = wholeContext.typeParameters →
    inferenceContext.assumptions = wholeContext.assumptions →
    ProgramSignatureFormationValidated inferenceContext.signatures →
    (∀ candidate ∈ inferenceContext.signatures.functions,
      candidate.scheme.body = .function (Ty.productMany candidate.parameterTypes) (Ty.productMany candidate.returnTypes)) →
    SignatureCatalogWellFormed inferenceContext.signatures →
    SignatureParametersWellFormed inferenceContext.scope.genericOwner inferenceContext.typeParameters →
    RecursiveExpressionInvariant wholeContext finalized initial semanticContext →
    ActualContext wholeContext finalized frames semanticContext →
    ActualStateInvariant initial (evidenceState.toTypedSource roots) →
    (∀ type ∈ expectedTypes, type.VariablesBelow initial.inference.next) →
    (∀ type ∈ expectedTypes, TypeAdmissible semanticContext (finalized.substitution.apply type)) →
    (∀ argument ∈ inferred, SubtreePreserved finalized.substitution
      (resultState.toTypedSource roots) semanticSource (.expression argument.id)) →
    (∀ argument ∈ inferred, SubtreePreserved finalized.substitution
      (resultState.toTypedSource roots) finalized.typedSource (.expression argument.id)) →
    (∀ argument ∈ inferred, RawProperDescendantsPreserved
      (resultState.toTypedSource roots) (evidenceState.toTypedSource roots) (.expression argument.id)) →
    resultState.integerPatterns ⊆ evidenceState.integerPatterns →
    resultState.integerLiterals ⊆ evidenceState.integerLiterals →
    resultState.requirements ⊆ evidenceState.requirements →
    (∀ argument ∈ inferred, TemplateScopeCovered finalized.typedSource semanticContext (.expression argument.id)) →
    (∀ argument ∈ inferred, ActualContext.Covers finalized frames (.expression argument.id)) →
    ExpressionsHaveTypes semanticSource semanticContext (inferred.map (·.id))
      (expectedTypes.map finalized.substitution.apply) := by
  intro wholeContext inferenceContext wholeReturn sources
  induction sources with
  | nil =>
    intro expectedTypes initial resultState evidenceState inferred roots finalized semanticSource frames semanticContext
      success resources interfaces extension signaturesEq ownerEq typeParametersEq assumptionsEq formation functions
      catalog canonical invariant actual operational expectedBelow expectedAdmissible semantic final raw patterns literals
      requirements covered actualCovered
    cases expectedTypes with
    | nil =>
      simp only [Detail.inferConstructorArgumentsFuel, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at success
      obtain ⟨rfl, rfl⟩ := success
      exact .nil _
    | cons _ _ => simp [Detail.inferConstructorArgumentsFuel] at success
  | cons source sources induction =>
    intro expectedTypes initial resultState evidenceState inferred roots finalized semanticSource frames semanticContext
      success resources interfaces extension signaturesEq ownerEq typeParametersEq assumptionsEq formation functions
      catalog canonical invariant actual operational expectedBelow expectedAdmissible semantic final raw patterns literals
      requirements covered actualCovered
    cases expectedTypes with
    | nil => simp [Detail.inferConstructorArgumentsFuel] at success
    | cons expected expectedTypes =>
      unfold Detail.inferConstructorArgumentsFuel at success
      cases headSuccess : Detail.inferExprFuel fuel inferenceContext source
          (some (initial.resolve expected)) initial with
      | error error => simp [headSuccess, bind, Except.bind] at success
      | ok headPair =>
        obtain ⟨head, headState⟩ := headPair
        simp only [headSuccess, bind, Except.bind] at success
        cases tailSuccess : Detail.inferConstructorArgumentsFuel fuel inferenceContext sources expectedTypes headState with
        | error error => simp [tailSuccess] at success
        | ok tailPair =>
          obtain ⟨tail, tailState⟩ := tailPair
          simp only [tailSuccess, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at success
          obtain ⟨rfl, rfl⟩ := success
          have expectedHeadBelow := expectedBelow expected (by simp)
          have headExpectedBelow : ∀ type ∈ some (initial.resolve expected), type.VariablesBelow initial.inference.next := by
            intro type member
            have same : type = initial.resolve expected := by
              simpa only [Option.mem_def, Option.some.injEq] using member.symm
            subst type
            exact invariant.ready.solved.variablesBelow_apply expectedHeadBelow
          have headProperties := Detail.inferExprFuel_inferenceProperties invariant.ready formation functions
            headExpectedBelow headSuccess
          have tailExpectedBelow : ∀ type ∈ expectedTypes, type.VariablesBelow headState.inference.next :=
            fun type member => (expectedBelow type (by simp [member])).weaken headProperties.1.next_le
          have tailProperties := Detail.inferConstructorArgumentsFuel_inferenceProperties
            headProperties.2.1 formation functions tailExpectedBelow tailSuccess
          have headExtension := extension.trans tailProperties.1.substitution_extends
          have initialExtension := headExtension.trans headProperties.1.substitution_extends
          have initialResolved : finalized.substitution.apply (initial.resolve expected) =
              finalized.substitution.apply expected := by
            simpa only [State.resolve, InferState.resolve] using initialExtension expected
          have headExpectedAdmissible : ∀ type ∈ some (initial.resolve expected),
              TypeAdmissible semanticContext (finalized.substitution.apply type) := by
            intro type member
            have same : type = initial.resolve expected := by
              simpa only [Option.mem_def, Option.some.injEq] using member.symm
            rw [same, initialResolved]
            exact expectedAdmissible expected (by simp)
          have headInvariant := invariant.ofExpression formation functions headExpectedBelow headExtension headSuccess
          have headOperational := operational.ofExpression headSuccess headProperties.1.next_le
          have headToFinal := inferConstructorArgumentsFuel_success_typingSourceExtends
            tailSuccess headInvariant.nodesBelow roots
          have headTyped := actualInferExprFuelFinalSubtreeSoundness_of_retainedSoundness recursive
            headSuccess resources interfaces headExtension signaturesEq ownerEq typeParametersEq assumptionsEq
            formation functions catalog canonical invariant actual operational headExpectedBelow headExpectedAdmissible
            ((semantic head (by simp)).monoBefore headToFinal)
            ((final head (by simp)).monoBefore headToFinal)
            ((raw head (by simp)).monoBefore headToFinal)
            ((Detail.inferConstructorArgumentsFuel_integerPatterns_subset tailSuccess).trans patterns)
            ((Detail.inferConstructorArgumentsFuel_integerLiterals_subset tailSuccess).trans literals)
            ((Detail.inferConstructorArgumentsFuel_requirements_subset tailSuccess).trans requirements)
            (covered head (by simp)) (actualCovered head (by simp))
          have headTypeEq : finalized.substitution.apply head.type = finalized.substitution.apply expected := by
            exact (Detail.inferExprFuel_expected_type_apply_eq headSuccess headExtension).trans initialResolved
          have tailTyped := induction tailSuccess resources interfaces extension signaturesEq ownerEq typeParametersEq
            assumptionsEq formation functions catalog canonical headInvariant actual headOperational tailExpectedBelow
            (fun type member => expectedAdmissible type (by simp [member]))
            (fun argument member => semantic argument (by simp [member]))
            (fun argument member => final argument (by simp [member]))
            (fun argument member => raw argument (by simp [member])) patterns literals requirements
            (fun argument member => covered argument (by simp [member]))
            (fun argument member => actualCovered argument (by simp [member]))
          exact .cons (by simpa only [headTypeEq] using headTyped) tailTyped

end Solcore.SourceSemantics.SourceInferenceSoundness
