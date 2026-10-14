import Solcore.SourceSemantics.SourceInferenceSelectedOperatorTyping

/-! Argument and result fitting use only interfaces of actual retained coercion
steps. Every empty path is checked by its real inference trace. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

theorem argumentFitTrace_argumentCoercionsValid_from_interfaces
    {inferenceContext solverContext : Frontend.SourceInference.Context}
    {initial later : Frontend.SourceInference.State}
    {arguments : List InferredExpression}
    {parameters : List TypeSystem.Ty}
    {result : Detail.ArgumentFitResult}
    {solved : List SolvedRequirement}
    {base semanticContext : SourceSemantics.Context}
    {ledgerSource : TypedSource}
    (trace : Detail.ArgumentFitTrace inferenceContext initial arguments
      parameters result)
    (ready : initial.InferenceReady)
    (argumentsBelow : ∀ argument ∈ arguments,
      argument.type.VariablesBelow initial.inference.next)
    (parametersBelow : ∀ parameter ∈ parameters,
      parameter.VariablesBelow initial.inference.next)
    (substitutionExtends :
      later.inference.substitution.SemanticallyExtends
        result.state.inference.substitution)
    (requirementsSubset : result.state.requirements ⊆ later.requirements)
    (interfaces : ExecutableCoercionInterfaces.SourceInterfaces inferenceContext.signatures solved ledgerSource)
    (present : ∀ entry ∈ result.coercions, CoercionPrimariesPresent ledgerSource entry.coercions)
    (parametersAdmissible : ∀ parameter ∈ parameters,
      TypeAdmissible semanticContext
        (later.inference.substitution.apply parameter))
    (catalog : SignatureCatalogWellFormed semanticContext.signatures)
    (signaturesEq : semanticContext.signatures = inferenceContext.signatures)
    (solveSuccess : Detail.solveRequirements solverContext later
      later.requirements = .ok solved)
    (solvedEq : base.solvedRequirements = solved)
    (ledger : ScopedRequirementLedgerWellFormed base ledgerSource)
    (ownership : RequirementOwnership base ledgerSource)
    (activeSignaturesEq : semanticContext.signatures = base.signatures)
    (activeRequirementsEq :
      semanticContext.solvedRequirements = base.solvedRequirements)
    (assumptionsMono : base.assumptions ⊆ semanticContext.assumptions)
    (covered : ∀ entry ∈ result.coercions,
      TemplateScopeCovered ledgerSource semanticContext
        (.expression entry.expression))
    (occurs : ∀ entry ∈ result.coercions, ∀ requirement,
      requirement ∈ coercionRequirementIds entry.coercions →
        PrimaryRequirementOccursAt ledgerSource
          (.expression entry.expression) requirement) :
    ArgumentCoercionsValid semanticContext later.inference.substitution
      arguments parameters result.coercions := by
  induction trace with
  | nil => exact .nil
  | @cons state argument arguments parameter parameters fitted tail
      head rest induction =>
      have argumentBelow :
          argument.type.VariablesBelow state.inference.next :=
        argumentsBelow argument (by simp)
      have parameterBelow :
          parameter.VariablesBelow state.inference.next :=
        parametersBelow parameter (by simp)
      have fittedProperties :=
        Detail.candidateWithExpected_some_inferenceProperties ready
          argumentBelow (by
            intro expectedType member
            simp only [Option.mem_def] at member
            have expectedTypeEq : expectedType = parameter :=
              Option.some.inj member.symm
            simpa only [expectedTypeEq] using parameterBelow) head
      have tailArgumentsBelow : ∀ tailArgument ∈ arguments,
          tailArgument.type.VariablesBelow fitted.state.inference.next := by
        intro tailArgument member
        exact (argumentsBelow tailArgument (by simp [member])).weaken
          fittedProperties.1.next_le
      have tailParametersBelow : ∀ tailParameter ∈ parameters,
          tailParameter.VariablesBelow fitted.state.inference.next := by
        intro tailParameter member
        exact (parametersBelow tailParameter (by simp [member])).weaken
          fittedProperties.1.next_le
      have tailProperties := rest.inferenceProperties
        fittedProperties.2.1 tailArgumentsBelow tailParametersBelow
      have outerFitted : later.inference.substitution.SemanticallyExtends
          fitted.state.inference.substitution :=
        TypeSystem.Substitution.SemanticallyExtends.trans substitutionExtends
          tailProperties.1.substitution_extends
      have fittedRequirementsSubset :
          fitted.state.requirements ⊆ later.requirements :=
        List.Subset.trans rest.requirements_subset requirementsSubset
      let entry : Detail.ExpressionCoercions := {
        expression := argument.id
        coercions := fitted.coercions
      }
      have entryMember : entry ∈ entry :: tail.coercions := by simp
      have path :=
        withExpected_success_coercionPathValid_from_interfaces
          (Detail.candidateWithExpected_some_withExpected head)
          interfaces (present entry entryMember) fittedRequirementsSubset catalog
          signaturesEq solveSuccess solvedEq ledger
          ownership activeSignaturesEq activeRequirementsEq assumptionsMono
          (covered entry entryMember)
          (fun requirement member => occurs entry entryMember requirement member)
      have rawEndpointEq :
          later.inference.substitution.apply
              (fitted.state.resolve argument.type) =
            later.inference.substitution.apply argument.type :=
        TypeSystem.InferState.apply_resolve_eq_apply outerFitted argument.type
      have targetEndpointEq :
          later.inference.substitution.apply fitted.expression.type =
            later.inference.substitution.apply parameter :=
        Detail.candidateWithExpected_some_apply_eq head outerFitted
      refine .cons (parametersAdmissible parameter (by simp)) ?_ ?_
      · simpa only [rawEndpointEq, targetEndpointEq] using path
      · apply induction fittedProperties.2.1 tailArgumentsBelow
          tailParametersBelow substitutionExtends requirementsSubset
        · intro tailEntry member
          exact present tailEntry (by simp [member])
        · intro tailParameter member
          exact parametersAdmissible tailParameter (by simp [member])
        · intro tailEntry member
          exact covered tailEntry (by simp [member])
        · intro tailEntry entryMember requirement requirementMember
          exact occurs tailEntry (by simp [entryMember]) requirement
            requirementMember


theorem tryFunctionCandidate_some_argumentCoercionsValid_from_interfaces
    {inferenceContext solverContext : Frontend.SourceInference.Context}
    {arguments : List InferredExpression}
    {integerLiteralOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected : Option TypeSystem.Ty}
    {state later : Frontend.SourceInference.State}
    {signature : ProgramFunctionSignature}
    {result : Detail.CandidateAttemptResult}
    {solved : List SolvedRequirement}
    {base semanticContext : SourceSemantics.Context}
    {ledgerSource : TypedSource}
    (canonical : signature.scheme.body = .function
      (TypeSystem.Ty.productMany signature.parameterTypes)
      (TypeSystem.Ty.productMany signature.returnTypes))
    (success : Detail.tryFunctionCandidate inferenceContext arguments
      integerLiteralOrigins call expected state signature = .ok (some result))
    (ready : state.InferenceReady)
    (argumentsBelow : ∀ argument ∈ arguments,
      argument.type.VariablesBelow state.inference.next)
    (schemeBodyBelow : signature.scheme.body.VariablesBelow
      state.inference.next)
    (expectedBelow : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow state.inference.next)
    (substitutionExtends :
      later.inference.substitution.SemanticallyExtends
        result.state.inference.substitution)
    (requirementsSubset : result.state.requirements ⊆ later.requirements)
    (interfaces : ExecutableCoercionInterfaces.SourceInterfaces inferenceContext.signatures solved ledgerSource)
    (present : ∀ entry ∈ result.argumentCoercions, CoercionPrimariesPresent ledgerSource entry.coercions)
    (parametersAdmissible : ∀ parameter ∈ signature.parameterTypes.map
      (signature.scheme.instantiate state.inference.next).parameterSubstitution.apply,
      TypeAdmissible semanticContext (later.inference.substitution.apply parameter))
    (catalog : SignatureCatalogWellFormed semanticContext.signatures)
    (signaturesEq : semanticContext.signatures = inferenceContext.signatures)
    (solveSuccess : Detail.solveRequirements solverContext later
      later.requirements = .ok solved)
    (solvedEq : base.solvedRequirements = solved)
    (ledger : ScopedRequirementLedgerWellFormed base ledgerSource)
    (ownership : RequirementOwnership base ledgerSource)
    (activeSignaturesEq : semanticContext.signatures = base.signatures)
    (activeRequirementsEq :
      semanticContext.solvedRequirements = base.solvedRequirements)
    (assumptionsMono : base.assumptions ⊆ semanticContext.assumptions)
    (covered : ∀ entry ∈ result.argumentCoercions,
      TemplateScopeCovered ledgerSource semanticContext
        (.expression entry.expression))
    (occurs : ∀ entry ∈ result.argumentCoercions, ∀ requirement,
      requirement ∈ coercionRequirementIds entry.coercions →
        PrimaryRequirementOccursAt ledgerSource
          (.expression entry.expression) requirement) :
    ArgumentCoercionsValid semanticContext later.inference.substitution
      arguments
      (signature.parameterTypes.map
        (signature.scheme.instantiate state.inference.next
          |>.parameterSubstitution.apply))
      result.argumentCoercions := by
  let instantiated := signature.scheme.instantiate state.inference.next
  let advancedState : Frontend.SourceInference.State := {
    state with inference := {
      state.inference with next := instantiated.next
    }
  }
  obtain ⟨fittedArguments, fittedResult, trace, fittedResultSuccess,
    coercionsEq, resultInferenceEq, fittedRequirementsSubset⟩ :=
    Detail.tryFunctionCandidate_some_argumentFitWitness canonical success
  have instantiatedNextLe :
      state.inference.next ≤ instantiated.next := by
    simpa only [instantiated] using
      ConstrainedDeclarationScheme.instantiate_next_le signature.scheme
        state.inference.next
  have advanceProgress : state.InferenceProgress advancedState := by
    refine Frontend.SourceInference.State.InferenceProgress.of_substitution_eq
      ready.solved ?_ ?_
    · simpa only [advancedState] using instantiatedNextLe
    · rfl
  have advancedReady : advancedState.InferenceReady :=
    Frontend.SourceInference.State.InferenceReady.of_progress_of_binderEnvironment_eq
      ready advanceProgress rfl
  have argumentsAtAdvanced : ∀ argument ∈ arguments,
      argument.type.VariablesBelow advancedState.inference.next := by
    intro argument member
    exact (argumentsBelow argument member).weaken advanceProgress.next_le
  have instantiatedBodyBelow :
      instantiated.body.VariablesBelow instantiated.next := by
    simpa only [instantiated] using
      ConstrainedDeclarationScheme.instantiate_body_variablesBelow
        signature.scheme state.inference.next schemeBodyBelow
  have partsResult : Detail.functionParts? instantiated.body =
      some
        (instantiated.parameterSubstitution.apply
            (TypeSystem.Ty.productMany signature.parameterTypes),
          instantiated.parameterSubstitution.apply
            (TypeSystem.Ty.productMany signature.returnTypes)) := by
    rw [ConstrainedDeclarationScheme.instantiate_body, canonical]
    rfl
  have partsBelow := Detail.functionParts?_success_variablesBelow
    instantiatedBodyBelow partsResult
  have parametersResult := Detail.parameterTypesForArity?_apply_productMany
    instantiated.parameterSubstitution signature.parameterTypes
  have parametersBelowAtInstantiation :=
    Detail.parameterTypesForArity?_success_variablesBelow partsBelow.1
      parametersResult
  have parametersBelow : ∀ parameter ∈
      signature.parameterTypes.map instantiated.parameterSubstitution.apply,
      parameter.VariablesBelow advancedState.inference.next := by
    simpa only [advancedState] using parametersBelowAtInstantiation
  have traceProperties := trace.inferenceProperties advancedReady
    argumentsAtAdvanced parametersBelow
  have resultTypeAtAdvanced :
      (instantiated.parameterSubstitution.apply
        (TypeSystem.Ty.productMany signature.returnTypes)).VariablesBelow
          advancedState.inference.next := by
    simpa only [advancedState] using partsBelow.2
  have resultTypeAtArguments :
      (instantiated.parameterSubstitution.apply
        (TypeSystem.Ty.productMany signature.returnTypes)).VariablesBelow
          fittedArguments.state.inference.next :=
    resultTypeAtAdvanced.weaken traceProperties.1.next_le
  have expectedAtArguments : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow
        fittedArguments.state.inference.next := by
    intro expectedType member
    exact (expectedBelow expectedType member).weaken
      (Nat.le_trans advanceProgress.next_le traceProperties.1.next_le)
  have fittedResultProperties :=
    Detail.candidateWithExpected_some_inferenceProperties
      traceProperties.2 resultTypeAtArguments expectedAtArguments
        fittedResultSuccess
  have laterExtendsFittedResult :
      later.inference.substitution.SemanticallyExtends
        fittedResult.state.inference.substitution := by
    rw [← resultInferenceEq]
    exact substitutionExtends
  have laterExtendsFittedArguments :
      later.inference.substitution.SemanticallyExtends
        fittedArguments.state.inference.substitution :=
    TypeSystem.Substitution.SemanticallyExtends.trans
      laterExtendsFittedResult
      fittedResultProperties.1.substitution_extends
  have fittedRequirementsAtLater :
      fittedArguments.state.requirements ⊆ later.requirements :=
    List.Subset.trans fittedRequirementsSubset requirementsSubset
  have fittedCovered : ∀ entry ∈ fittedArguments.coercions,
      TemplateScopeCovered ledgerSource semanticContext
        (.expression entry.expression) := by
    intro entry member
    apply covered entry
    rw [coercionsEq]
    exact member
  have fittedOccurs : ∀ entry ∈ fittedArguments.coercions,
      ∀ requirement,
        requirement ∈ coercionRequirementIds entry.coercions →
          PrimaryRequirementOccursAt ledgerSource
            (.expression entry.expression) requirement := by
    intro entry member requirement requirementMember
    apply occurs entry
    · rw [coercionsEq]
      exact member
    · exact requirementMember
  rw [coercionsEq]
  exact argumentFitTrace_argumentCoercionsValid_from_interfaces
    trace advancedReady argumentsAtAdvanced parametersBelow
    laterExtendsFittedArguments fittedRequirementsAtLater interfaces
    (by simpa only [← coercionsEq] using present) parametersAdmissible catalog
    signaturesEq solveSuccess solvedEq ledger ownership
    activeSignaturesEq activeRequirementsEq assumptionsMono fittedCovered
    fittedOccurs


theorem tryFunctionCandidate_some_directCallRequirementsValid_from_interfaces
    {inferenceContext solverContext : Frontend.SourceInference.Context}
    {arguments : List InferredExpression}
    {integerLiteralOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected : Option TypeSystem.Ty}
    {state later : Frontend.SourceInference.State}
    {signature : ProgramFunctionSignature}
    {result : Detail.CandidateAttemptResult}
    {solved : List SolvedRequirement}
    {base semanticContext : SourceSemantics.Context}
    {ledgerSource : TypedSource}
    (canonical : signature.scheme.body = .function
      (TypeSystem.Ty.productMany signature.parameterTypes)
      (TypeSystem.Ty.productMany signature.returnTypes))
    (success : Detail.tryFunctionCandidate inferenceContext arguments
      integerLiteralOrigins call expected state signature = .ok (some result))
    (ready : state.InferenceReady)
    (argumentsBelow : ∀ argument ∈ arguments,
      argument.type.VariablesBelow state.inference.next)
    (schemeBodyBelow : signature.scheme.body.VariablesBelow
      state.inference.next)
    (expectedBelow : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow state.inference.next)
    (substitutionExtends :
      later.inference.substitution.SemanticallyExtends
        result.state.inference.substitution)
    (requirementsSubset : result.state.requirements ⊆ later.requirements)
    (interfaces : ExecutableCoercionInterfaces.SourceInterfaces inferenceContext.signatures solved ledgerSource)
    (present : CoercionPrimariesPresent ledgerSource result.callCoercions)
    (catalog : SignatureCatalogWellFormed semanticContext.signatures)
    (signaturesEq : semanticContext.signatures = inferenceContext.signatures)
    (solveSuccess : Detail.solveRequirements solverContext later
      later.requirements = .ok solved)
    (solvedEq : base.solvedRequirements = solved)
    (ledger : ScopedRequirementLedgerWellFormed base ledgerSource)
    (ownership : RequirementOwnership base ledgerSource)
    (activeSignaturesEq : semanticContext.signatures = base.signatures)
    (activeRequirementsEq :
      semanticContext.solvedRequirements = base.solvedRequirements)
    (assumptionsMono : base.assumptions ⊆ semanticContext.assumptions)
    (covered : TemplateScopeCovered ledgerSource semanticContext
      (.expression result.result.id))
    (occurs : ∀ requirement,
      requirement ∈ Detail.coercionRequirements result.callCoercions ++
          result.signatureRequirements →
        PrimaryRequirementOccursAt ledgerSource
          (.expression result.result.id) requirement) :
    let instantiated := signature.scheme.instantiate state.inference.next
    DirectCallRequirementsValid semanticContext
      (later.inference.substitution.apply
        (instantiated.parameterSubstitution.apply
          (TypeSystem.Ty.productMany signature.returnTypes)))
      (later.inference.substitution.apply result.result.type)
      (result.instantiation.predicates.map
        (TypedTraitResolution.applySubstitution
          later.inference.substitution))
      (Detail.coercionRequirements result.callCoercions ++
        result.signatureRequirements)
      (result.callCoercions.map
        (CoercionStep.applySubstitution
          later.inference.substitution)) := by
  let instantiated := signature.scheme.instantiate state.inference.next
  let advancedState : Frontend.SourceInference.State := {
    state with inference := {
      state.inference with next := instantiated.next
    }
  }
  obtain ⟨fittedArguments, fittedResult, trace, fittedResultSuccess,
    instantiationEq, resultExpressionEq, _, callCoercionsEq,
    signatureRequirementsEq, resultStateEq⟩ :=
    Detail.tryFunctionCandidate_some_resultFitAllocationWitness canonical
      success
  let allocation := fittedResult.state.addRequirementsWithIds
    instantiated.predicates
  let finalState := allocation.2.markDirectCallRequirements allocation.1
  have normalizedResultExpressionEq : result.result = {
      fittedResult.expression with
      type := finalState.resolve fittedResult.expression.type
    } := by
    simpa only [allocation, finalState] using resultExpressionEq
  have normalizedSignatureRequirementsEq :
      result.signatureRequirements = allocation.1 := by
    simpa only [allocation] using signatureRequirementsEq
  have normalizedResultStateEq : result.state = finalState := by
    simpa only [allocation, finalState] using resultStateEq
  have instantiatedNextLe :
      state.inference.next ≤ instantiated.next := by
    simpa only [instantiated] using
      ConstrainedDeclarationScheme.instantiate_next_le signature.scheme
        state.inference.next
  have advanceProgress : state.InferenceProgress advancedState := by
    refine Frontend.SourceInference.State.InferenceProgress.of_substitution_eq
      ready.solved ?_ ?_
    · simpa only [advancedState] using instantiatedNextLe
    · rfl
  have advancedReady : advancedState.InferenceReady :=
    Frontend.SourceInference.State.InferenceReady.of_progress_of_binderEnvironment_eq
      ready advanceProgress rfl
  have argumentsAtAdvanced : ∀ argument ∈ arguments,
      argument.type.VariablesBelow advancedState.inference.next := by
    intro argument member
    exact (argumentsBelow argument member).weaken advanceProgress.next_le
  have instantiatedBodyBelow :
      instantiated.body.VariablesBelow instantiated.next := by
    simpa only [instantiated] using
      ConstrainedDeclarationScheme.instantiate_body_variablesBelow
        signature.scheme state.inference.next schemeBodyBelow
  have partsResult : Detail.functionParts? instantiated.body =
      some
        (instantiated.parameterSubstitution.apply
            (TypeSystem.Ty.productMany signature.parameterTypes),
          instantiated.parameterSubstitution.apply
            (TypeSystem.Ty.productMany signature.returnTypes)) := by
    rw [ConstrainedDeclarationScheme.instantiate_body, canonical]
    rfl
  have partsBelow := Detail.functionParts?_success_variablesBelow
    instantiatedBodyBelow partsResult
  have parametersResult := Detail.parameterTypesForArity?_apply_productMany
    instantiated.parameterSubstitution signature.parameterTypes
  have parametersBelowAtInstantiation :=
    Detail.parameterTypesForArity?_success_variablesBelow partsBelow.1
      parametersResult
  have parametersBelow : ∀ parameter ∈
      signature.parameterTypes.map instantiated.parameterSubstitution.apply,
      parameter.VariablesBelow advancedState.inference.next := by
    simpa only [advancedState] using parametersBelowAtInstantiation
  have traceProperties := trace.inferenceProperties advancedReady
    argumentsAtAdvanced parametersBelow
  have resultTypeAtAdvanced :
      (instantiated.parameterSubstitution.apply
        (TypeSystem.Ty.productMany signature.returnTypes)).VariablesBelow
          advancedState.inference.next := by
    simpa only [advancedState] using partsBelow.2
  have resultTypeAtArguments :
      (instantiated.parameterSubstitution.apply
        (TypeSystem.Ty.productMany signature.returnTypes)).VariablesBelow
          fittedArguments.state.inference.next :=
    resultTypeAtAdvanced.weaken traceProperties.1.next_le
  have expectedAtArguments : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow
        fittedArguments.state.inference.next := by
    intro expectedType member
    exact (expectedBelow expectedType member).weaken
      (Nat.le_trans advanceProgress.next_le traceProperties.1.next_le)
  have fittedResultProperties :=
    Detail.candidateWithExpected_some_inferenceProperties
      traceProperties.2 resultTypeAtArguments expectedAtArguments
        fittedResultSuccess
  have allocationProgress :
      fittedResult.state.InferenceProgress allocation.2 := by
    simpa only [allocation] using
      (Frontend.SourceInference.State.InferenceProgress.addRequirementsWithIds
        fittedResult.state instantiated.predicates
        fittedResultProperties.2.1.solved)
  have markProgress : allocation.2.InferenceProgress finalState := by
    simpa only [finalState] using
      (Frontend.SourceInference.State.InferenceProgress.markDirectCallRequirements
        allocation.2 allocation.1 allocationProgress.solved)
  have finalProgress :
      fittedResult.state.InferenceProgress finalState :=
    allocationProgress.trans markProgress
  have laterExtendsFinal :
      later.inference.substitution.SemanticallyExtends
        finalState.inference.substitution := by
    rw [← normalizedResultStateEq]
    exact substitutionExtends
  have laterExtendsFittedResult :
      later.inference.substitution.SemanticallyExtends
        fittedResult.state.inference.substitution :=
    TypeSystem.Substitution.SemanticallyExtends.trans laterExtendsFinal
      finalProgress.substitution_extends
  have allocationRequirementsAtFinal :
      allocation.2.requirements ⊆ finalState.requirements := by
    simpa only [finalState] using
      Frontend.SourceInference.State.markDirectCallRequirements_requirements_subset
        allocation.2 allocation.1
  have finalRequirementsAtLater :
      finalState.requirements ⊆ later.requirements := by
    rw [← normalizedResultStateEq]
    exact requirementsSubset
  have allocationRequirementsAtLater :
      allocation.2.requirements ⊆ later.requirements :=
    List.Subset.trans allocationRequirementsAtFinal finalRequirementsAtLater
  have fittedRequirementsAtAllocation :
      fittedResult.state.requirements ⊆ allocation.2.requirements := by
    simpa only [allocation] using
      Frontend.SourceInference.State.addRequirementsWithIds_requirements_subset
        fittedResult.state instantiated.predicates
  have fittedRequirementsAtLater :
      fittedResult.state.requirements ⊆ later.requirements :=
    List.Subset.trans fittedRequirementsAtAllocation
      allocationRequirementsAtLater
  have selectedPath :=
    withExpected_success_coercionPathValid_from_interfaces
      (Detail.candidateWithExpected_some_withExpected fittedResultSuccess)
      interfaces (by simpa only [← callCoercionsEq] using present) fittedRequirementsAtLater catalog
      signaturesEq solveSuccess solvedEq ledger
      ownership activeSignaturesEq activeRequirementsEq assumptionsMono
      covered (by
        intro requirement member
        apply occurs requirement
        apply List.mem_append_left
        rw [callCoercionsEq]
        simpa [Detail.coercionRequirements, coercionRequirementIds] using
          member)
  have rawEndpointEq :
      later.inference.substitution.apply
          (fittedResult.state.resolve
            (instantiated.parameterSubstitution.apply
              (TypeSystem.Ty.productMany signature.returnTypes))) =
        later.inference.substitution.apply
          (instantiated.parameterSubstitution.apply
            (TypeSystem.Ty.productMany signature.returnTypes)) :=
    TypeSystem.InferState.apply_resolve_eq_apply laterExtendsFittedResult _
  have resultTypeEq : result.result.type =
      finalState.resolve fittedResult.expression.type := by
    exact congrArg InferredExpression.type normalizedResultExpressionEq
  have finalEndpointEq :
      later.inference.substitution.apply result.result.type =
        later.inference.substitution.apply fittedResult.expression.type := by
    rw [resultTypeEq]
    exact TypeSystem.InferState.apply_resolve_eq_apply laterExtendsFinal _
  have selectedPathValid : CoercionPathValid semanticContext
      (later.inference.substitution.apply
        (instantiated.parameterSubstitution.apply
          (TypeSystem.Ty.productMany signature.returnTypes)))
      (later.inference.substitution.apply result.result.type)
      (result.callCoercions.map
        (CoercionStep.applySubstitution
          later.inference.substitution)) := by
    simpa only [instantiated, rawEndpointEq, finalEndpointEq,
      callCoercionsEq] using
      selectedPath
  have allocationCorresponds : RequirementPredicatesCorrespond
      allocation.2.requirements instantiated.predicates allocation.1 := by
    simpa only [allocation] using
      Frontend.SourceInference.State.addRequirementsWithIds_correspond
        fittedResult.state instantiated.predicates
  have laterCorresponds : RequirementPredicatesCorrespond
      later.requirements instantiated.predicates allocation.1 :=
    allocationCorresponds.mono allocationRequirementsAtLater
  have allocatedSignatureValid : RequirementSequenceProves semanticContext
      allocation.1 (instantiated.predicates.map (Detail.applyPredicate later)) :=
    solveRequirements_correspondingSequenceProvesAt laterCorresponds
      solveSuccess solvedEq ledger ownership activeSignaturesEq
      activeRequirementsEq assumptionsMono covered (by
        intro requirement member
        apply occurs requirement
        apply List.mem_append_right
        rw [normalizedSignatureRequirementsEq]
        exact member)
  have predicateMapEq :
      instantiated.predicates.map (Detail.applyPredicate later) =
        instantiated.predicates.map
          (TypedTraitResolution.applySubstitution
            later.inference.substitution) := by
    apply List.map_congr_left
    intro predicate _
    rfl
  have signatureValid : RequirementSequenceProves semanticContext
      result.signatureRequirements
      (result.instantiation.predicates.map
        (TypedTraitResolution.applySubstitution
          later.inference.substitution)) := by
    simpa only [instantiated, normalizedSignatureRequirementsEq,
      instantiationEq,
      Frontend.SourceInference.DeclarationInstantiation.ofInstantiated,
      predicateMapEq] using allocatedSignatureValid
  apply DirectCallRequirementsValid.intro selectedPathValid (.nil _)
    signatureValid
  · simp only [List.append_nil]
  · rw [FlexibleSubstitution.coercionRequirementIds_applySubstitution]
    simp [Detail.coercionRequirements, coercionRequirementIds]


end Solcore.SourceSemantics.SourceInferenceSoundness
