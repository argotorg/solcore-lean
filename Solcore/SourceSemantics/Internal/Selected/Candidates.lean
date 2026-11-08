import Solcore.SourceSemantics.Internal.Selected.Operators

/-!
# Candidates of a call

Argument and result fitting use only interfaces of retained coercion steps, and the selected call
keeps every attached operand.
-/

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedCandidateFitting
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
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedCandidateApplication
/-! The selected declaration keeps its full canonical substitution while
parameter and result formation are proved directly in the active context. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

theorem declarationApplication_afterSubstitution
    {context : SourceSemantics.Context} {substitution : Substitution}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (binders : TypeParameterBindersWellFormed context)
    (residual : context.residualTypeVariables = true)
    (range : SubstitutionRangeAdmissible context substitution)
    {signature : ProgramFunctionSignature}
    (member : signature ∈ context.signatures.functions) (next : Nat) :
    let instantiated := signature.scheme.instantiate next
    DeclarationApplicationValid context
      ((Frontend.SourceInference.DeclarationInstantiation.ofInstantiated signature instantiated).applySubstitution substitution)
      ((signature.parameterTypes.map instantiated.parameterSubstitution.apply).map substitution.apply)
      (substitution.apply (instantiated.parameterSubstitution.apply (Ty.productMany signature.returnTypes)))
      (instantiated.predicates.map (TypedTraitResolution.applySubstitution substitution)) := by
  let instantiated := signature.scheme.instantiate next
  have valid := declarationInstantiation_afterSubstitution catalog binders residual range member next
  have formed := catalog.functions_semantic signature member
  have exactDomain := DeclarationInstantiation.instantiate_parameterSubstitution_exact
    signature.scheme next (catalog.function_parameters signature member).1
  have parameters := FlexibleSubstitution.TypesWellScoped.applyFlexible_composeParameters
    (context := signatureContext context.signatures signature.id signature.scheme.parameters signature.scheme.predicates)
    substitution instantiated.parameterSubstitution exactDomain
    (StructuralSubstitution.TypesWellFormed.toTypesWellScoped formed.parameter_types)
  have returns := FlexibleSubstitution.TypeWellScoped.applyFlexible_composeParameters
    (context := signatureContext context.signatures signature.id signature.scheme.parameters signature.scheme.predicates)
    substitution instantiated.parameterSubstitution exactDomain
    (StructuralSubstitution.TypesWellScoped.productMany
      (StructuralSubstitution.TypesWellFormed.toTypesWellScoped formed.return_types))
  refine .intro member valid rfl ?_ ?_ ?_ rfl
  · exact parameters.symm
  · exact returns.symm
  · change substitution.apply instantiated.body = _
    rw [ConstrainedDeclarationScheme.instantiate_body, formed.scheme_body,
      StructuralSubstitution.apply_function, StructuralSubstitution.apply_productMany,
      FlexibleSubstitution.apply_function, FlexibleSubstitution.apply_productMany]

theorem tryFunctionCandidate_application_afterSubstitution
    {inferenceContext : Frontend.SourceInference.Context}
    {arguments : List InferredExpression} {integerLiteralOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected : Option Ty} {state : State}
    {signature : ProgramFunctionSignature} {attempt : Detail.CandidateAttemptResult}
    {active : SourceSemantics.Context} {substitution : Substitution}
    (catalog : SignatureCatalogWellFormed active.signatures)
    (binders : TypeParameterBindersWellFormed active)
    (residual : active.residualTypeVariables = true)
    (range : SubstitutionRangeAdmissible active substitution)
    (member : signature ∈ active.signatures.functions)
    (success : Detail.tryFunctionCandidate inferenceContext arguments integerLiteralOrigins
      call expected state signature = .ok (some attempt)) :
    let instantiated := signature.scheme.instantiate state.inference.next
    DeclarationApplicationValid active (attempt.instantiation.applySubstitution substitution)
      ((signature.parameterTypes.map instantiated.parameterSubstitution.apply).map substitution.apply)
      (substitution.apply (instantiated.parameterSubstitution.apply (Ty.productMany signature.returnTypes)))
      (instantiated.predicates.map (TypedTraitResolution.applySubstitution substitution)) := by
  rw [Detail.tryFunctionCandidate_some_instantiation success]
  exact declarationApplication_afterSubstitution catalog binders residual range member state.inference.next

end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedCandidateCall
/-! The actual selected call retains every attached operand and synthetic
callee node. Only genuine retained coercion sites supply method interfaces. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

theorem tryFunctionCandidate_recordSelectedCallResult_typing_from_interfaces
    {inferenceContext solverContext : Frontend.SourceInference.Context}
    {source callee : Syntax.Expr} {name : String}
    {arguments : List InferredExpression}
    {integerLiteralOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected : Option TypeSystem.Ty}
    {state recordState later : Frontend.SourceInference.State}
    {signature : ProgramFunctionSignature}
    {attempt : Detail.CandidateAttemptResult}
    {result : InferredExpression}
    {trailingCoercions : List CoercionStep}
    {recorded : InferredExpression × Frontend.SourceInference.State}
    {roots : List NodeId}
    {solved : List SolvedRequirement}
    {base active : SourceSemantics.Context}
    {semanticSource evidenceSource : TypedSource}
    (canonical : signature.scheme.body = .function
      (TypeSystem.Ty.productMany signature.parameterTypes)
      (TypeSystem.Ty.productMany signature.returnTypes))
    (candidateSuccess : Detail.tryFunctionCandidate inferenceContext arguments
      integerLiteralOrigins call expected state signature = .ok (some attempt))
    (recordSuccess : Detail.recordSelectedCallResult source callee name
      arguments attempt result trailingCoercions recordState = recorded)
    (recordNodesEq : recordState.nodes = attempt.state.nodes)
    (resultIdEq : result.id = attempt.result.id)
    (bases : ArgumentTypingBasesValid (state.toTypedSource roots)
      semanticSource active later.inference.substitution arguments)
    (argumentIdsUnique : (arguments.map (·.id)).Nodup)
    (ready : state.InferenceReady)
    (argumentsBelow : ∀ argument ∈ arguments,
      argument.type.VariablesBelow state.inference.next)
    (schemeBodyBelow : signature.scheme.body.VariablesBelow
      state.inference.next)
    (expectedBelow : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow state.inference.next)
    (candidateSubstitutionExtends :
      later.inference.substitution.SemanticallyExtends
        attempt.state.inference.substitution)
    (recordSubstitutionExtends :
      later.inference.substitution.SemanticallyExtends
        recordState.inference.substitution)
    (candidateRequirementsSubset :
      attempt.state.requirements ⊆ later.requirements)
    (semanticArgumentNodesPreserved : ExpressionNodesPreservedAt
      (arguments.map (·.id))
      ((Detail.attachExpressionCoercions recordState
          attempt.argumentCoercions
        |>.toTypedSource roots).applySubstitution
          later.inference.substitution)
      semanticSource)
    (semanticCalleeNodePreserved : ExpressionNodesPreservedAt
      [((Detail.attachExpressionCoercions recordState
          attempt.argumentCoercions).allocateExpressionId.1)]
      ((recorded.2.toTypedSource roots).applySubstitution
        later.inference.substitution)
      semanticSource)
    (evidenceArgumentNodesPreserved : ExpressionNodesPreservedAt
      (arguments.map (·.id))
      ((Detail.attachExpressionCoercions recordState
          attempt.argumentCoercions
        |>.toTypedSource roots).applySubstitution
          later.inference.substitution)
      evidenceSource)
    (callRequirementsRetained : ExpressionRequirementsRetainedAt
      (recorded.2.toTypedSource roots) evidenceSource result.id)
    (interfaces : ExecutableCoercionInterfaces.SourceInterfaces inferenceContext.signatures solved evidenceSource)
    (coercionsRetained : ExpressionCoercionPrimariesRetainedAt
      (recorded.2.toTypedSource roots) evidenceSource result.id)
    (argumentCovered : ∀ entry ∈ attempt.argumentCoercions,
      TemplateScopeCovered evidenceSource active
        (.expression entry.expression))
    (catalog : SignatureCatalogWellFormed active.signatures)
    (binders : TypeParameterBindersWellFormed active)
    (residual : active.residualTypeVariables = true)
    (range : SubstitutionRangeAdmissible active later.inference.substitution)
    (signatureMember : signature ∈ active.signatures.functions)
    (signaturesEq : active.signatures = inferenceContext.signatures)
    (solveSuccess : Detail.solveRequirements solverContext later
      later.requirements = .ok solved)
    (solvedEq : base.solvedRequirements = solved)
    (ledger : ScopedRequirementLedgerWellFormed base evidenceSource)
    (ownership : RequirementOwnership base evidenceSource)
    (activeSignaturesEq : active.signatures = base.signatures)
    (activeRequirementsEq :
      active.solvedRequirements = base.solvedRequirements)
    (assumptionsMono : base.assumptions ⊆ active.assumptions)
    (callCovered : TemplateScopeCovered evidenceSource active
      (.expression result.id))
    (trailingPath : CoercionPathValid active
      (later.inference.substitution.apply attempt.result.type)
      (later.inference.substitution.apply result.type)
      (trailingCoercions.map
        (CoercionStep.applySubstitution later.inference.substitution))) :
    ExpressionTypingBase (recorded.2.toTypedSource roots) semanticSource active
      later.inference.substitution result := by
  let instantiated := signature.scheme.instantiate state.inference.next
  have mappedApplication := tryFunctionCandidate_application_afterSubstitution
    catalog binders residual range signatureMember candidateSuccess
  have rawAdmissible := DeclarationApplicationValid.result_type_admissible catalog binders mappedApplication
  have parameterAdmissible := DeclarationApplicationValid.parameter_types_admissible catalog binders mappedApplication
  have candidateNodesEq : attempt.state.nodes = state.nodes :=
    (Detail.tryFunctionCandidate_some_occurrenceState_eq candidateSuccess).1
  have nodesPrefix :
      (state.toTypedSource roots).nodes <+:
        (recordState.toTypedSource roots).nodes := by
    change state.nodes <+: recordState.nodes
    rw [recordNodesEq, candidateNodesEq]
    exact List.prefix_rfl
  have recordBases : ArgumentTypingBasesValid
      (recordState.toTypedSource roots) semanticSource active
      later.inference.substitution arguments :=
    bases.weakenNodeSource nodesPrefix
  have argumentExpressionIds :
      attempt.argumentCoercions.map (·.expression) =
        arguments.map (·.id) :=
    Detail.tryFunctionCandidate_some_argumentCoercion_expression_ids
      canonical candidateSuccess
  have entryIdsUnique :
      (attempt.argumentCoercions.map (·.expression)).Nodup := by
    rw [argumentExpressionIds]
    exact argumentIdsUnique
  have argumentOccurs : ∀ entry ∈ attempt.argumentCoercions,
      ∀ requirement,
        requirement ∈ coercionRequirementIds entry.coercions →
          PrimaryRequirementOccursAt evidenceSource
            (.expression entry.expression) requirement := by
    intro entry entryMember requirement requirementMember
    have entryIdMember : entry.expression ∈ arguments.map (·.id) := by
      rw [← argumentExpressionIds]
      exact List.mem_map.mpr ⟨entry, entryMember, rfl⟩
    obtain ⟨argument, argumentMember, argumentIdEq⟩ :=
      List.mem_map.mp entryIdMember
    obtain ⟨node, contains⟩ :=
      recordBases.containsExpression_of_mem argumentMember
    have entryContains : ContainsExpression
        (recordState.toTypedSource roots) entry.expression node := by
      rwa [← argumentIdEq]
    have attachedContains := attachExpressionCoercions_containsExpression
      recordState attempt.argumentCoercions entry node roots entryIdsUnique
      entryMember entryContains
    have substitutedContains :=
      FlexibleSubstitution.ContainsExpression.applySubstitution
        later.inference.substitution attachedContains
    have finalContains :=
      evidenceArgumentNodesPreserved entryIdMember substitutedContains
    apply finalContains.primaryRequirementOccursAt
    change requirement ∈
      node.requirements ++ Detail.coercionRequirements entry.coercions
    apply List.mem_append_right
    simpa [Detail.coercionRequirements, coercionRequirementIds] using
      requirementMember
  have argumentPresent : ∀ entry ∈ attempt.argumentCoercions,
      CoercionPrimariesPresent evidenceSource entry.coercions := by
    intro entry entryMember step stepMember
    have entryIdMember : entry.expression ∈ arguments.map (·.id) := by
      rw [← argumentExpressionIds]
      exact List.mem_map.mpr ⟨entry, entryMember, rfl⟩
    obtain ⟨argument, argumentMember, argumentIdEq⟩ := List.mem_map.mp entryIdMember
    obtain ⟨node, contains⟩ := recordBases.containsExpression_of_mem argumentMember
    have entryContains : ContainsExpression (recordState.toTypedSource roots) entry.expression node := by
      rwa [← argumentIdEq]
    have attached := attachExpressionCoercions_containsExpression
      recordState attempt.argumentCoercions entry node roots entryIdsUnique entryMember entryContains
    have finalFound := evidenceArgumentNodesPreserved entryIdMember
      (FlexibleSubstitution.ContainsExpression.applySubstitution later.inference.substitution attached)
    refine ⟨_, finalFound.1, step.applySubstitution later.inference.substitution, ?_, rfl⟩
    apply List.mem_append_left
    change step.applySubstitution later.inference.substitution ∈
      (node.coercions ++ entry.coercions).map (CoercionStep.applySubstitution later.inference.substitution)
    exact List.mem_map.mpr ⟨step, List.mem_append_right _ stepMember, rfl⟩
  have argumentCoercions : ArgumentCoercionsValid active
      later.inference.substitution arguments
      (signature.parameterTypes.map instantiated.parameterSubstitution.apply)
      attempt.argumentCoercions := by
    simpa only [instantiated] using
      tryFunctionCandidate_some_argumentCoercionsValid_from_interfaces
        canonical candidateSuccess ready argumentsBelow schemeBodyBelow
        expectedBelow candidateSubstitutionExtends
        candidateRequirementsSubset interfaces argumentPresent
        (by intro parameter member; exact parameterAdmissible _ (List.mem_map.mpr ⟨parameter, member, rfl⟩))
        catalog signaturesEq
        solveSuccess solvedEq ledger ownership activeSignaturesEq
        activeRequirementsEq assumptionsMono argumentCovered argumentOccurs
  have selectedCovered : TemplateScopeCovered evidenceSource active
      (.expression attempt.result.id) := by
    simpa only [← resultIdEq] using callCovered
  have selectedOccurs : ∀ requirement,
      requirement ∈ Detail.coercionRequirements attempt.callCoercions ++
          attempt.signatureRequirements →
        PrimaryRequirementOccursAt evidenceSource
          (.expression attempt.result.id) requirement := by
    intro requirement member
    have callContains :=
      recordSelectedCallResult_success_containsExpression recordSuccess roots
    have occurs := callRequirementsRetained callContains
      (List.mem_append_left
        (Detail.coercionRequirements trailingCoercions) member)
    simpa only [← resultIdEq] using occurs
  have instantiationPredicatesEq :
      attempt.instantiation.predicates = instantiated.predicates := by
    rw [Detail.tryFunctionCandidate_some_instantiation candidateSuccess]
    rfl
  have callRequirements : DirectCallRequirementsValid active
      (later.inference.substitution.apply
        (instantiated.parameterSubstitution.apply
          (TypeSystem.Ty.productMany signature.returnTypes)))
      (later.inference.substitution.apply attempt.result.type)
      (instantiated.predicates.map
        (TypedTraitResolution.applySubstitution
          later.inference.substitution))
      (Detail.coercionRequirements attempt.callCoercions ++
        attempt.signatureRequirements)
      (attempt.callCoercions.map
        (CoercionStep.applySubstitution
          later.inference.substitution)) := by
    rw [← instantiationPredicatesEq]
    simpa only [instantiated] using
      tryFunctionCandidate_some_directCallRequirementsValid_from_interfaces
        canonical candidateSuccess ready argumentsBelow schemeBodyBelow
        expectedBelow candidateSubstitutionExtends
        candidateRequirementsSubset interfaces
        (by intro step member
            exact coercionsRetained.present
              (recordSelectedCallResult_success_containsExpression recordSuccess roots) step
              (List.mem_append_left _ (List.mem_append_left _ member))) catalog signaturesEq solveSuccess solvedEq ledger
        ownership activeSignaturesEq activeRequirementsEq assumptionsMono
        selectedCovered selectedOccurs
  let attachedState := Detail.attachExpressionCoercions recordState
    attempt.argumentCoercions
  let allocation := attachedState.allocateExpressionId
  let calleeNode : ExpressionNode := {
    id := allocation.1
    span := callee.span
    type := allocation.2.resolve attempt.instantiation.type
    form := .reference name (.declaration attempt.instantiation)
  }
  let callNode : ExpressionNode := {
    id := result.id
    span := source.span
    type := result.type
    form := .call allocation.1 (arguments.map (·.id))
      (.declaration attempt.instantiation)
    requirements :=
      Detail.coercionRequirements attempt.callCoercions ++
        attempt.signatureRequirements ++
        Detail.coercionRequirements trailingCoercions
    coercions := attempt.callCoercions ++ trailingCoercions
  }
  have rawContains : ContainsExpression (recorded.2.toTypedSource roots)
      result.id callNode := by
    simpa only [attachedState, allocation, callNode] using
      recordSelectedCallResult_success_containsExpression recordSuccess roots
  have argumentsType : ExpressionsHaveTypes semanticSource active
      (arguments.map (·.id))
      ((signature.parameterTypes.map
        instantiated.parameterSubstitution.apply).map
          later.inference.substitution.apply) :=
    argumentTypingBasesValid_attachExpressionCoercions_expressionsHaveTypes
      recordBases argumentCoercions argumentIdsUnique
        semanticArgumentNodesPreserved
  have rawCalleeContains : ContainsExpression
      (recorded.2.toTypedSource roots) allocation.1 calleeNode := by
    have nodes := Detail.recordSelectedCallResult_success_nodes recordSuccess
    refine ⟨?_, rfl⟩
    change .expression calleeNode ∈ recorded.2.nodes
    rw [nodes.2]
    simp [attachedState, allocation, calleeNode]
  have substitutedCalleeContains : ContainsExpression
      ((recorded.2.toTypedSource roots).applySubstitution
        later.inference.substitution)
      allocation.1
      (calleeNode.applySubstitution later.inference.substitution) :=
    FlexibleSubstitution.ContainsExpression.applySubstitution
      later.inference.substitution rawCalleeContains
  have finalCalleeContains : ContainsExpression semanticSource allocation.1
      (calleeNode.applySubstitution later.inference.substitution) :=
    semanticCalleeNodePreserved (by simp [attachedState, allocation])
      substitutedCalleeContains
  have mappedInstantiationValid : SourceSemantics.DeclarationInstantiation.Admissible active
      (attempt.instantiation.applySubstitution later.inference.substitution) := by
    cases mappedApplication with
    | intro _ valid _ _ _ _ _ => exact valid
  have allocationInferenceEq : allocation.2.inference =
      recordState.inference := by
    calc
      allocation.2.inference = attachedState.inference := by rfl
      _ = recordState.inference :=
        Detail.attachExpressionCoercions_inference_eq recordState
          attempt.argumentCoercions
  have allocationExtends :
      later.inference.substitution.SemanticallyExtends
        allocation.2.inference.substitution := by
    rw [allocationInferenceEq]
    exact recordSubstitutionExtends
  have normalizedCalleeType :
      later.inference.substitution.apply
          (allocation.2.resolve attempt.instantiation.type) =
        later.inference.substitution.apply attempt.instantiation.type :=
    TypeSystem.InferState.apply_resolve_eq_apply allocationExtends _
  have calleeValid : DirectDeclarationCalleeValid active semanticSource
      allocation.1
      (attempt.instantiation.applySubstitution
        later.inference.substitution) := by
    refine DirectDeclarationCalleeValid.intro (name := name)
      finalCalleeContains ?_ mappedInstantiationValid ?_ ?_ ?_
    · rfl
    · simpa [calleeNode, ExpressionNode.applySubstitution,
        DeclarationInstantiation.applySubstitution] using normalizedCalleeType
    · rfl
    · rfl
  have formType : ExpressionFormHasRawType semanticSource active
      (callNode.applySubstitution later.inference.substitution).form
      (later.inference.substitution.apply
        (instantiated.parameterSubstitution.apply
          (TypeSystem.Ty.productMany signature.returnTypes)))
      (.directCall
        (instantiated.predicates.map
          (TypedTraitResolution.applySubstitution
            later.inference.substitution))) := by
    simpa [callNode, instantiated, ExpressionNode.applySubstitution,
      ExpressionForm.applySubstitution, CallResolution.applySubstitution] using
        (ExpressionFormHasRawType.directCall calleeValid mappedApplication
          argumentsType)
  refine .intro rawContains (by rfl) formType rawAdmissible ?_
  have requirements :=
    (ExpressionRequirementPlan.Valid.directCall callRequirements).appendOutput
      trailingPath
  rw [FlexibleSubstitution.coercionRequirementIds_applySubstitution]
    at requirements
  simpa [callNode, ExpressionNode.applySubstitution, List.map_append,
    Detail.coercionRequirements, coercionRequirementIds,
    List.append_assoc] using requirements


end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedCallRecording
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

theorem selectFunctionCandidateFrom_recordSelectedCall_typing_from_interfaces
    {inferenceContext solverContext : Frontend.SourceInference.Context}
    {source callee : Syntax.Expr} {name : String}
    {candidates : List ProgramFunctionSignature}
    {arguments : List InferredExpression}
    {integerLiteralOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected : Option TypeSystem.Ty}
    {state later : Frontend.SourceInference.State}
    {attempt : Detail.CandidateAttemptResult}
    {result : InferredExpression}
    {resultState : Frontend.SourceInference.State}
    {roots : List NodeId}
    {solved : List SolvedRequirement}
    {base active : SourceSemantics.Context}
    {semanticSource evidenceSource : TypedSource}
    (selectionSuccess : Detail.selectFunctionCandidateFrom inferenceContext
      name candidates arguments integerLiteralOrigins call expected state =
        .ok attempt)
    (recordEq : Detail.recordSelectedCall source callee name arguments attempt =
      (result, resultState))
    (candidatesSubset : candidates ⊆
      inferenceContext.signatures.functions)
    (bases : ArgumentTypingBasesValid (state.toTypedSource roots)
      semanticSource active later.inference.substitution arguments)
    (argumentIdsUnique : (arguments.map (·.id)).Nodup)
    (ready : state.InferenceReady)
    (argumentsBelow : ∀ argument ∈ arguments,
      argument.type.VariablesBelow state.inference.next)
    (signatureFormation :
      ProgramSignatureFormationValidated inferenceContext.signatures)
    (functionsCanonical : ∀ signature ∈
      inferenceContext.signatures.functions,
      signature.scheme.body = .function
        (TypeSystem.Ty.productMany signature.parameterTypes)
        (TypeSystem.Ty.productMany signature.returnTypes))
    (expectedBelow : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow state.inference.next)
    (substitutionExtends :
      later.inference.substitution.SemanticallyExtends
        resultState.inference.substitution)
    (requirementsSubset : resultState.requirements ⊆ later.requirements)
    (semanticArgumentNodesPreserved : ExpressionNodesPreservedAt
      (arguments.map (·.id))
      ((Detail.attachExpressionCoercions attempt.state
          attempt.argumentCoercions
        |>.toTypedSource roots).applySubstitution
          later.inference.substitution)
      semanticSource)
    (semanticCalleeNodePreserved : ExpressionNodesPreservedAt
      [((Detail.attachExpressionCoercions attempt.state
          attempt.argumentCoercions).allocateExpressionId.1)]
      ((resultState.toTypedSource roots).applySubstitution
        later.inference.substitution)
      semanticSource)
    (evidenceArgumentNodesPreserved : ExpressionNodesPreservedAt
      (arguments.map (·.id))
      ((Detail.attachExpressionCoercions attempt.state
          attempt.argumentCoercions
        |>.toTypedSource roots).applySubstitution
          later.inference.substitution)
      evidenceSource)
    (callRequirementsRetained : ExpressionRequirementsRetainedAt
      (resultState.toTypedSource roots) evidenceSource result.id)
    (interfaces : ExecutableCoercionInterfaces.SourceInterfaces inferenceContext.signatures solved evidenceSource)
    (coercionsRetained : ExpressionCoercionPrimariesRetainedAt
      (resultState.toTypedSource roots) evidenceSource result.id)
    (argumentCovered : ∀ entry ∈ attempt.argumentCoercions,
      TemplateScopeCovered evidenceSource active
        (.expression entry.expression))
    (catalog : SignatureCatalogWellFormed active.signatures)
    (binders : TypeParameterBindersWellFormed active)
    (residual : active.residualTypeVariables = true)
    (range : SubstitutionRangeAdmissible active later.inference.substitution)
    (signaturesEq : active.signatures = inferenceContext.signatures)
    (solveSuccess : Detail.solveRequirements solverContext later
      later.requirements = .ok solved)
    (solvedEq : base.solvedRequirements = solved)
    (ledger : ScopedRequirementLedgerWellFormed base evidenceSource)
    (ownership : RequirementOwnership base evidenceSource)
    (activeSignaturesEq : active.signatures = base.signatures)
    (activeRequirementsEq :
      active.solvedRequirements = base.solvedRequirements)
    (assumptionsMono : base.assumptions ⊆ active.assumptions)
    (callCovered : TemplateScopeCovered evidenceSource active
      (.expression result.id)) :
    ExpressionTypingBase (resultState.toTypedSource roots) semanticSource active
      later.inference.substitution result := by
  obtain ⟨signature, _, signatureMember, canonical, schemeBodyBelow,
      candidateSuccess⟩ :=
    selectFunctionCandidateFrom_success_semanticCandidate signatureFormation
      functionsCanonical signaturesEq candidatesSubset selectionSuccess
  have candidateProperties :=
    Detail.tryFunctionCandidate_some_inferenceProperties ready argumentsBelow
      schemeBodyBelow expectedBelow candidateSuccess
  have recordProperties := Detail.recordSelectedCall_inferenceProperties
    source callee name arguments attempt candidateProperties.2.1
      candidateProperties.2.2
  rw [recordEq] at recordProperties
  have laterExtendsAttempt :
      later.inference.substitution.SemanticallyExtends
        attempt.state.inference.substitution :=
    TypeSystem.Substitution.SemanticallyExtends.trans substitutionExtends
      recordProperties.1.substitution_extends
  have attemptRequirementsAtResult :=
    Detail.recordSelectedCall_requirements_subset source callee name arguments
      attempt
  rw [recordEq] at attemptRequirementsAtResult
  have attemptRequirementsAtLater :
      attempt.state.requirements ⊆ later.requirements :=
    List.Subset.trans attemptRequirementsAtResult requirementsSubset
  have recordSuccess : Detail.recordSelectedCallResult source callee name
      arguments attempt attempt.result [] attempt.state =
        (result, resultState) := by
    simpa only [Detail.recordSelectedCall] using recordEq
  have resultEq : result = attempt.result :=
    (Detail.recordSelectedCallResult_success_nodes recordSuccess).1
  subst result
  exact
    tryFunctionCandidate_recordSelectedCallResult_typing_from_interfaces
      canonical candidateSuccess recordSuccess rfl rfl bases
      argumentIdsUnique ready argumentsBelow schemeBodyBelow expectedBelow
      laterExtendsAttempt laterExtendsAttempt attemptRequirementsAtLater
      semanticArgumentNodesPreserved semanticCalleeNodePreserved
      evidenceArgumentNodesPreserved callRequirementsRetained interfaces coercionsRetained argumentCovered
      catalog binders residual range signatureMember signaturesEq
      solveSuccess solvedEq ledger
      ownership activeSignaturesEq activeRequirementsEq assumptionsMono
      callCovered (.nil _)

end Solcore.SourceSemantics.SourceInferenceSoundness
end
