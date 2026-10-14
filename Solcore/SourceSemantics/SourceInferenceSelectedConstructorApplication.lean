import Solcore.SourceSemantics.SourceInferenceSelectedConstructorArguments
import Solcore.SourceSemantics.SourceInferenceSelectedOrdinaryRecorder
import Solcore.SourceSemantics.SourceInferenceSelectedOperatorMetadata

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

theorem actualConstructorApplication_typing {fuel : Nat}
    (recursive : ActualInferExprFuelRetainedSoundness fuel) :
  ∀ {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn : Ty} {source : Syntax.Expr} {id : ExpressionId}
    {arguments : List Syntax.Expr} {instantiation : DataConstructorInstantiation} {expected : Option Ty}
    {initial resultState evidenceState : State} {inferred : InferredExpression}
    {roots : List NodeId} {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource} {frames : List InitializedLetBinding} {semanticContext : SourceSemantics.Context},
    Detail.inferConstructorApplicationFuel fuel inferenceContext source id instantiation arguments expected initial = .ok (inferred, resultState) →
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
    (∀ type ∈ instantiation.payloadTypes, type.VariablesBelow initial.inference.next) →
    instantiation.resultType.VariablesBelow initial.inference.next →
    (∀ type ∈ expected, type.VariablesBelow initial.inference.next) →
    SourceSemantics.DataConstructorInstantiation.Admissible semanticContext
      (instantiation.applySubstitution finalized.substitution) →
    ProperDescendantsPreserved finalized.substitution (resultState.toTypedSource roots)
      semanticSource (.expression inferred.id) →
    ProperDescendantsPreserved finalized.substitution (resultState.toTypedSource roots)
      finalized.typedSource (.expression inferred.id) →
    RawProperDescendantsPreserved (resultState.toTypedSource roots)
      (evidenceState.toTypedSource roots) (.expression inferred.id) →
    resultState.integerPatterns ⊆ evidenceState.integerPatterns →
    resultState.integerLiterals ⊆ evidenceState.integerLiterals →
    resultState.requirements ⊆ evidenceState.requirements →
    ExpressionRequirementsRetainedAt (resultState.toTypedSource roots) finalized.typedSource inferred.id →
    ExpressionCoercionPrimariesRetainedAt (resultState.toTypedSource roots) finalized.typedSource inferred.id →
    ExpressionDirectChildrenRetainedAt (resultState.toTypedSource roots) finalized.typedSource inferred.id →
    TemplateScopeCovered finalized.typedSource semanticContext (.expression inferred.id) →
    ActualContext.Covers finalized frames (.expression inferred.id) →
    ExpressionTypingBase (resultState.toTypedSource roots) semanticSource semanticContext finalized.substitution inferred := by
  intro wholeContext inferenceContext wholeReturn source id arguments instantiation expected initial resultState evidenceState
    inferred roots finalized semanticSource frames semanticContext success resources interfaces extension signaturesEq ownerEq
    typeParametersEq assumptionsEq formation functions catalog canonical invariant actual operational payloadBelow resultBelow
    expectedBelow instantiationValid semantic final raw patterns literals requirements retained coercionsRetained childrenRetained
    covered actualCovered
  have activeCatalog : SignatureCatalogWellFormed semanticContext.signatures := by
    rw [invariant.signatures_eq_whole, ← signaturesEq]; exact catalog
  have binders := invariant.typeParameterBinders (by simpa only [ownerEq, typeParametersEq] using canonical)
  have finish {argumentInitial argumentsState : State} {inferredArguments : List InferredExpression}
      (argumentInvariant : RecursiveExpressionInvariant wholeContext finalized argumentInitial semanticContext)
      (argumentOperational : ActualStateInvariant argumentInitial (evidenceState.toTypedSource roots))
      (payloadAt : ∀ type ∈ instantiation.payloadTypes, type.VariablesBelow argumentInitial.inference.next)
      (resultAt : instantiation.resultType.VariablesBelow argumentInitial.inference.next)
      (expectedAt : ∀ type ∈ expected, type.VariablesBelow argumentInitial.inference.next)
      (argumentsSuccess : Detail.inferConstructorArgumentsFuel fuel inferenceContext arguments instantiation.payloadTypes
        argumentInitial = .ok (inferredArguments, argumentsState))
      (recorded : Detail.recordExpressionWithExpected inferenceContext source id
        (argumentsState.resolve instantiation.resultType) (.constructor instantiation (inferredArguments.map (·.id))) []
        expected argumentsState = .ok (inferred, resultState)) :
      ExpressionTypingBase (resultState.toTypedSource roots) semanticSource semanticContext finalized.substitution inferred := by
    have properties := Detail.inferConstructorArgumentsFuel_inferenceProperties argumentInvariant.ready formation functions
      payloadAt argumentsSuccess
    have recording := Detail.recordExpressionWithExpected_inferenceProperties properties.2.1
      (properties.2.1.solved.variablesBelow_apply (resultAt.weaken properties.1.next_le))
      (fun type member => (expectedAt type member).weaken properties.1.next_le) recorded
    have argumentExtension := extension.trans recording.1.substitution_extends
    have argumentToParent : TypingSourceExtends (argumentsState.toTypedSource roots) (resultState.toTypedSource roots) := by
      constructor
      · obtain ⟨fitted, fittedSuccess, _, stateEq⟩ := Detail.recordExpressionWithExpected_success_record recorded
        change resultState.owner = argumentsState.owner
        dsimp only at stateEq
        rw [stateEq]
        exact congrArg State.Header.owner (Detail.SelectedMetadata.withExpected_state_header fittedSuccess)
      · exact recordExpressionWithExpected_success_nodesPrefix recorded
    obtain ⟨coercions, contains⟩ := recordExpressionWithExpected_success_containsExpression recorded roots
    have edge : ∀ argument ∈ inferredArguments, DirectChild (resultState.toTypedSource roots)
        (.expression inferred.id) (.expression argument.id) := by
      intro argument member
      refine ⟨.expression _, ⟨contains.1, rfl⟩, ?_⟩
      simp only [nodeChildIds, Node.references, ExpressionForm.references]
      exact List.mem_map.mpr ⟨argument.id, List.mem_map.mpr ⟨argument, member, rfl⟩, rfl⟩
    have payloadAdmissible : ∀ type ∈ instantiation.payloadTypes,
        TypeAdmissible semanticContext (finalized.substitution.apply type) := by
      intro type member
      apply SourceSemantics.DataConstructorInstantiation.Admissible.payload_type_admissible
        activeCatalog binders instantiationValid
      exact List.mem_map.mpr ⟨type, member, rfl⟩
    have typed := actualInferConstructorArgumentsFuelTypes recursive argumentsSuccess resources interfaces argumentExtension
      signaturesEq ownerEq typeParametersEq assumptionsEq formation functions catalog canonical argumentInvariant actual
      argumentOperational payloadAt payloadAdmissible
      (fun argument member => (semantic.childSubtree (edge argument member)).monoBefore argumentToParent)
      (fun argument member => (final.childSubtree (edge argument member)).monoBefore argumentToParent)
      (fun argument member => ((raw.childSubtree (edge argument member)).monoBefore argumentToParent).proper)
      (by rw [← recordExpressionWithExpected_integerPatterns_eq recorded]; exact patterns)
      (by rw [← Detail.recordExpressionWithExpected_integerLiterals_eq recorded]; exact literals)
      ((Detail.recordExpressionWithExpected_requirements_subset recorded).trans requirements)
      (fun argument member => covered.expressionChild resources.graph_closed (childrenRetained (edge argument member)))
      (fun argument member => actualCovered.directChild (childrenRetained (edge argument member)))
    have rawEq : finalized.substitution.apply (argumentsState.resolve instantiation.resultType) =
        finalized.substitution.apply instantiation.resultType := by
      simpa only [State.resolve, InferState.resolve] using argumentExtension instantiation.resultType
    have rawAdmissible : TypeAdmissible semanticContext
        (finalized.substitution.apply (argumentsState.resolve instantiation.resultType)) := by
      rw [rawEq]
      exact SourceSemantics.DataConstructorInstantiation.Admissible.result_type_admissible
        binders instantiationValid
    have formType : ExpressionFormHasRawType semanticSource semanticContext
        ((.constructor instantiation (inferredArguments.map (·.id)) : ExpressionForm).applySubstitution finalized.substitution)
        (finalized.substitution.apply (argumentsState.resolve instantiation.resultType)) (.ordinary []) := by
      rw [rawEq]
      exact .constructor instantiationValid typed
    exact recordExpressionWithExpected_success_expressionTypingBase_actual resources interfaces recorded extension
      requirements retained coercionsRetained catalog signaturesEq invariant formType rawAdmissible covered
  unfold Detail.inferConstructorApplicationFuel at success
  by_cases arity : arguments.length = instantiation.payloadTypes.length
  · simp only [arity] at success
    cases expected with
    | none =>
      simp only [pure, Pure.pure, Except.pure, bind, Except.bind] at success
      cases args : Detail.inferConstructorArgumentsFuel fuel inferenceContext arguments instantiation.payloadTypes initial with
      | error error => simp [args] at success
      | ok pair =>
        obtain ⟨inferredArguments, argumentsState⟩ := pair
        simp only [args] at success
        exact finish invariant operational payloadBelow resultBelow expectedBelow args success
    | some expectedType =>
      cases unified : Detail.unify initial instantiation.resultType expectedType with
      | error error => simp [unified, bind, Except.bind] at success
      | ok argumentInitial =>
        simp only [unified, bind, Except.bind] at success
        have expectedTypeBelow := expectedBelow expectedType (by simp)
        have progress := Detail.unify_inferenceProgress invariant.ready.solved resultBelow expectedTypeBelow unified
        cases args : Detail.inferConstructorArgumentsFuel fuel inferenceContext arguments instantiation.payloadTypes argumentInitial with
        | error error => simp [args] at success
        | ok pair =>
          obtain ⟨inferredArguments, argumentsState⟩ := pair
          simp only [args] at success
          have argumentReady := Detail.unify_preserves_inferenceReady invariant.ready resultBelow expectedTypeBelow unified
          have argsProperties := Detail.inferConstructorArgumentsFuel_inferenceProperties argumentReady formation functions
            (fun type member => (payloadBelow type member).weaken progress.next_le) args
          have recordProperties := Detail.recordExpressionWithExpected_inferenceProperties argsProperties.2.1
            (argsProperties.2.1.solved.variablesBelow_apply
              (resultBelow.weaken (Nat.le_trans progress.next_le argsProperties.1.next_le)))
            (fun type member => (expectedBelow type member).weaken (Nat.le_trans progress.next_le argsProperties.1.next_le)) success
          have argumentExtension := extension.trans (recordProperties.1.substitution_extends.trans argsProperties.1.substitution_extends)
          exact finish (invariant.unify resultBelow expectedTypeBelow argumentExtension unified)
            (operational.unify unified)
            (fun type member => (payloadBelow type member).weaken progress.next_le)
            (resultBelow.weaken progress.next_le)
            (fun type member => (expectedBelow type member).weaken progress.next_le) args success
  · simp [arity, bind, Except.bind] at success

end Solcore.SourceSemantics.SourceInferenceSoundness
