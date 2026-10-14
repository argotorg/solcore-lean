import Solcore.SourceSemantics.SourceInferenceExecutableCoercionFitting

/-! Indirect calls retain their bundled-argument coercion path in call
metadata. The actual selected interfaces validate both that path and the
output path while child typing remains in its own semantic source. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

private theorem functionParts?_success_eq
    {type parameter result : Ty}
    (success : Detail.functionParts? type = some (parameter, result)) :
    type = .function parameter result := by
  cases type <;> simp_all [Detail.functionParts?]

theorem
    applyFunctionType_recordIndirectCall_typing_from_interfaces
    {inferenceContext solverContext : Frontend.SourceInference.Context}
    {calleeState resultState later : Frontend.SourceInference.State}
    {arguments : List InferredExpression}
    {source : Syntax.Expr}
    {callee : InferredExpression}
    {call : ExpressionId} {expected : Option TypeSystem.Ty}
    {application : Detail.IndirectApplicationResult}
    {result : InferredExpression}
    {roots : List NodeId}
    {solved : List SolvedRequirement}
    {base active : SourceSemantics.Context}
    {semanticSource ledgerSource : TypedSource}
    (applicationSuccess : Detail.applyFunctionType inferenceContext call
      callee.type arguments expected calleeState = .ok application)
    (recordEq : Detail.recordIndirectCall source callee arguments application =
      (result, resultState))
    (applicationReady : calleeState.InferenceReady)
    (calleeBelow : callee.type.VariablesBelow
      calleeState.inference.next)
    (argumentsBelow : ∀ argument ∈ arguments,
      argument.type.VariablesBelow calleeState.inference.next)
    (expectedBelow : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow calleeState.inference.next)
    (substitutionExtends :
      later.inference.substitution.SemanticallyExtends
        resultState.inference.substitution)
    (requirementsSubset : resultState.requirements ⊆ later.requirements)
    (retained : ExpressionRequirementsRetainedAt
      (resultState.toTypedSource roots) ledgerSource result.id)
    (coercionsRetained : ExpressionCoercionPrimariesRetainedAt
      (resultState.toTypedSource roots) ledgerSource result.id)
    (interfaces : ExecutableCoercionInterfaces.SourceInterfaces
      inferenceContext.signatures solved ledgerSource)
    (argumentsType : ExpressionsHaveTypes semanticSource active
      (arguments.map (·.id))
      (arguments.map fun argument =>
        later.inference.substitution.apply argument.type))
    (calleeType : ExpressionHasType semanticSource active callee.id
      (later.inference.substitution.apply callee.type))
    (catalog : SignatureCatalogWellFormed active.signatures)
    (signaturesEq : active.signatures = inferenceContext.signatures)
    (solveSuccess : Detail.solveRequirements solverContext later
      later.requirements = .ok solved)
    (solvedEq : base.solvedRequirements = solved)
    (ledger : ScopedRequirementLedgerWellFormed base ledgerSource)
    (ownership : RequirementOwnership base ledgerSource)
    (activeSignaturesEq : active.signatures = base.signatures)
    (activeRequirementsEq :
      active.solvedRequirements = base.solvedRequirements)
    (assumptionsMono : base.assumptions ⊆ active.assumptions)
    (callCovered : TemplateScopeCovered ledgerSource active
      (.expression result.id)) :
    ExpressionTypingBase (resultState.toTypedSource roots) semanticSource active
      later.inference.substitution result := by
  have resultEq := congrArg Prod.fst recordEq
  have resultStateEq := congrArg Prod.snd recordEq
  simp only at resultEq resultStateEq
  subst result
  subst resultState
  have applicationProperties := Detail.applyFunctionType_inferenceProperties
    applicationReady calleeBelow argumentsBelow expectedBelow
      applicationSuccess
  have recordProperties := Detail.recordIndirectCall_inferenceProperties
    source callee arguments application applicationProperties.2.1
      applicationProperties.2.2
  have outerApplication : later.inference.substitution.SemanticallyExtends
      application.state.inference.substitution :=
    TypeSystem.Substitution.SemanticallyExtends.trans substitutionExtends
      recordProperties.1.substitution_extends
  have outerCalleeState : later.inference.substitution.SemanticallyExtends
      calleeState.inference.substitution :=
    TypeSystem.Substitution.SemanticallyExtends.trans outerApplication
      applicationProperties.1.substitution_extends
  have applicationRequirementsSubset :
      application.state.requirements ⊆ later.requirements :=
    List.Subset.trans
      (Detail.recordIndirectCall_requirements_subset source callee arguments
        application)
      requirementsSubset
  let argumentType := TypeSystem.Ty.productMany (arguments.map (·.type))
  let coercedArgumentType := application.argumentCoercions.foldl
    (fun _ step => step.target) argumentType
  let metadata : IndirectCallResolution := {
    argumentCount := arguments.length
    argumentTypeBeforeCoercion := argumentType
    argumentTypeAfterCoercion := coercedArgumentType
    argumentCoercions := application.argumentCoercions
  }
  let callNode : ExpressionNode := {
    id := application.result.id
    span := source.span
    type := application.result.type
    form := .call callee.id (arguments.map (·.id)) (.indirect metadata)
    requirements :=
      Detail.coercionRequirements application.argumentCoercions ++
        Detail.coercionRequirements application.callCoercions
    coercions := application.callCoercions
  }
  have rawContains : ContainsExpression
      ((Detail.recordIndirectCall source callee arguments application).2
        |>.toTypedSource roots)
      application.result.id callNode := by
    simpa only [Detail.recordIndirectCall, argumentType,
      coercedArgumentType, metadata, callNode] using
        (recordExpression_containsExpression source application.result
          (.call callee.id (arguments.map (·.id)) (.indirect metadata))
          (Detail.coercionRequirements application.argumentCoercions ++
            Detail.coercionRequirements application.callCoercions)
          application.callCoercions application.state roots)
  have covered : TemplateScopeCovered ledgerSource active
      (.expression application.result.id) := by
    simpa only [Detail.recordIndirectCall_fst] using callCovered
  have argumentOccurs : ∀ requirement,
      requirement ∈ coercionRequirementIds application.argumentCoercions →
        PrimaryRequirementOccursAt ledgerSource
          (.expression application.result.id) requirement := by
    intro requirement member
    apply retained rawContains
    change requirement ∈
      Detail.coercionRequirements application.argumentCoercions ++
        Detail.coercionRequirements application.callCoercions
    apply List.mem_append_left
    simpa [Detail.coercionRequirements, coercionRequirementIds] using member
  have outputOccurs : ∀ requirement,
      requirement ∈ coercionRequirementIds application.callCoercions →
        PrimaryRequirementOccursAt ledgerSource
          (.expression application.result.id) requirement := by
    intro requirement member
    apply retained rawContains
    change requirement ∈
      Detail.coercionRequirements application.argumentCoercions ++
        Detail.coercionRequirements application.callCoercions
    apply List.mem_append_right
    simpa [Detail.coercionRequirements, coercionRequirementIds] using member
  have argumentPresent : CoercionPrimariesPresent ledgerSource application.argumentCoercions := by
    intro step member
    exact coercionsRetained.present rawContains step (List.mem_append_right _ member)
  have outputPresent : CoercionPrimariesPresent ledgerSource application.callCoercions := by
    intro step member
    exact coercionsRetained.present rawContains step (List.mem_append_left _ member)
  have argumentTypesBelow : ∀ type ∈ arguments.map (·.type),
      type.VariablesBelow calleeState.inference.next := by
    intro type member
    rcases List.mem_map.mp member with ⟨argument, argumentMember, rfl⟩
    exact argumentsBelow argument argumentMember
  have argumentTypeBelow : argumentType.VariablesBelow
      calleeState.inference.next :=
    TypeSystem.Ty.variablesBelow_productMany argumentTypesBelow
  rcases Detail.applyFunctionType_success_facts applicationSuccess with
      known | fresh
  · rcases known with ⟨parameterType, resultType, fittedArgument,
      fittedResult, partsResult, argumentSuccess, outputSuccess,
      applicationEq⟩
    subst application
    have resolvedCalleeBelow :
        (calleeState.resolve callee.type).VariablesBelow
          calleeState.inference.next :=
      applicationReady.solved.variablesBelow_apply calleeBelow
    have partsBelow := Detail.functionParts?_success_variablesBelow
      resolvedCalleeBelow partsResult
    have argumentProperties := Detail.withExpected_inferenceProperties
      applicationReady argumentTypeBelow (by
        intro expectedType expectedMember
        simp at expectedMember
        subst expectedType
        exact partsBelow.1) argumentSuccess
    have resultTypeBelow : resultType.VariablesBelow
        fittedArgument.state.inference.next :=
      partsBelow.2.weaken argumentProperties.1.next_le
    have expectedAtArgument : ∀ expectedType ∈ expected,
        expectedType.VariablesBelow fittedArgument.state.inference.next := by
      intro expectedType expectedMember
      exact (expectedBelow expectedType expectedMember).weaken
        argumentProperties.1.next_le
    have outputProperties := Detail.withExpected_inferenceProperties
      argumentProperties.2.1 resultTypeBelow expectedAtArgument outputSuccess
    have outerFittedArgument :
        later.inference.substitution.SemanticallyExtends
          fittedArgument.state.inference.substitution :=
      TypeSystem.Substitution.SemanticallyExtends.trans outerApplication
        outputProperties.1.substitution_extends
    have argumentRequirementsSubset :
        fittedArgument.state.requirements ⊆ later.requirements :=
      List.Subset.trans (Detail.withExpected_requirements_subset outputSuccess)
        applicationRequirementsSubset
    have rawArgumentPath :=
      withExpected_success_coercionPathValid_from_interfaces
        argumentSuccess interfaces argumentPresent
        argumentRequirementsSubset catalog signaturesEq
        solveSuccess solvedEq ledger ownership activeSignaturesEq
        activeRequirementsEq assumptionsMono covered argumentOccurs
    have argumentSourceEq : later.inference.substitution.apply
        (fittedArgument.state.resolve argumentType) =
        later.inference.substitution.apply argumentType :=
      TypeSystem.InferState.apply_resolve_eq_apply outerFittedArgument _
    have argumentTargetEq : later.inference.substitution.apply
        fittedArgument.expression.type =
        later.inference.substitution.apply parameterType :=
      Detail.withExpected_some_apply_eq argumentSuccess outerFittedArgument
    have argumentPath : CoercionPathValid active
        (later.inference.substitution.apply argumentType)
        (later.inference.substitution.apply parameterType)
        (fittedArgument.coercions.map
          (CoercionStep.applySubstitution later.inference.substitution)) := by
      rw [← argumentSourceEq, ← argumentTargetEq]
      exact rawArgumentPath
    have rawOutputPath :=
      withExpected_success_coercionPathValid_from_interfaces
        outputSuccess interfaces outputPresent
        applicationRequirementsSubset catalog signaturesEq solveSuccess solvedEq ledger ownership activeSignaturesEq
        activeRequirementsEq assumptionsMono covered outputOccurs
    have outputSourceEq : later.inference.substitution.apply
        (fittedResult.state.resolve resultType) =
        later.inference.substitution.apply resultType :=
      TypeSystem.InferState.apply_resolve_eq_apply outerApplication _
    have outputPath : CoercionPathValid active
        (later.inference.substitution.apply resultType)
        (later.inference.substitution.apply fittedResult.expression.type)
        (fittedResult.coercions.map
          (CoercionStep.applySubstitution later.inference.substitution)) := by
      rw [← outputSourceEq]
      exact rawOutputPath
    have calleeShape : calleeState.resolve callee.type =
        .function parameterType resultType :=
      functionParts?_success_eq partsResult
    have calleeFunctionEq : later.inference.substitution.apply callee.type =
        .function (later.inference.substitution.apply parameterType)
          (later.inference.substitution.apply resultType) := by
      calc
        later.inference.substitution.apply callee.type =
            later.inference.substitution.apply
              (calleeState.resolve callee.type) :=
          (TypeSystem.InferState.apply_resolve_eq_apply outerCalleeState _).symm
        _ = later.inference.substitution.apply
              (.function parameterType resultType) :=
          congrArg later.inference.substitution.apply calleeShape
        _ = .function (later.inference.substitution.apply parameterType)
              (later.inference.substitution.apply resultType) := rfl
    have calleeFunctionType : ExpressionHasType semanticSource active callee.id
        (.function (later.inference.substitution.apply parameterType)
          (later.inference.substitution.apply resultType)) := by
      rw [← calleeFunctionEq]
      exact calleeType
    simpa only [argumentType] using
      (ExpressionTypingBase.ofRecordIndirectCall
        (source := source) (callee := callee) (arguments := arguments)
        (application := {
          result := fittedResult.expression
          argumentCoercions := fittedArgument.coercions
          callCoercions := fittedResult.coercions
          state := fittedResult.state
        }) (roots := roots) calleeFunctionType argumentsType argumentPath
          outputPath)
  · rcases fresh with ⟨resultType, freshState, unifiedState, fittedResult,
      _, freshEq, unifySuccess, outputSuccess, applicationEq⟩
    subst application
    have freshProgress : calleeState.InferenceProgress freshState := by
      have progress := Frontend.SourceInference.State.InferenceProgress.fresh
        calleeState applicationReady.solved
      rw [freshEq] at progress
      exact progress
    have freshReady : freshState.InferenceReady := by
      have ready := Frontend.SourceInference.State.InferenceReady.fresh
        applicationReady
      rw [freshEq] at ready
      exact ready
    have freshTypeBelow : resultType.VariablesBelow
        freshState.inference.next := by
      have below : calleeState.fresh.1.VariablesBelow
          calleeState.fresh.2.inference.next := by
        change TypeSystem.Ty.VariablesBelow
          (calleeState.inference.next + 1)
          (.variable ⟨calleeState.inference.next⟩)
        exact (TypeSystem.Ty.variablesBelow_variable_iff _ _).2
          (Nat.lt_succ_self _)
      rw [freshEq] at below
      exact below
    have calleeAtFresh : callee.type.VariablesBelow
        freshState.inference.next :=
      calleeBelow.weaken freshProgress.next_le
    have argumentTypeAtFresh : argumentType.VariablesBelow
        freshState.inference.next :=
      argumentTypeBelow.weaken freshProgress.next_le
    have functionTypeBelow :
        (TypeSystem.Ty.function argumentType resultType).VariablesBelow
          freshState.inference.next :=
      (TypeSystem.Ty.variablesBelow_function_iff _ _ _).2
        ⟨argumentTypeAtFresh, freshTypeBelow⟩
    have unifyProgress := Detail.unify_inferenceProgress freshReady.solved
      calleeAtFresh functionTypeBelow unifySuccess
    have unifiedReady := Detail.unify_preserves_inferenceReady freshReady
      calleeAtFresh functionTypeBelow unifySuccess
    have resultTypeAtUnified : resultType.VariablesBelow
        unifiedState.inference.next :=
      freshTypeBelow.weaken unifyProgress.next_le
    have expectedAtUnified : ∀ expectedType ∈ expected,
        expectedType.VariablesBelow unifiedState.inference.next := by
      intro expectedType expectedMember
      exact (expectedBelow expectedType expectedMember).weaken
        (freshProgress.trans unifyProgress).next_le
    have outputProperties := Detail.withExpected_inferenceProperties
      unifiedReady resultTypeAtUnified expectedAtUnified outputSuccess
    have outerUnified : later.inference.substitution.SemanticallyExtends
        unifiedState.inference.substitution :=
      TypeSystem.Substitution.SemanticallyExtends.trans outerApplication
        outputProperties.1.substitution_extends
    have rawOutputPath :=
      withExpected_success_coercionPathValid_from_interfaces
        outputSuccess interfaces outputPresent
        applicationRequirementsSubset catalog signaturesEq solveSuccess solvedEq ledger ownership activeSignaturesEq
        activeRequirementsEq assumptionsMono covered outputOccurs
    have outputSourceEq : later.inference.substitution.apply
        (fittedResult.state.resolve resultType) =
        later.inference.substitution.apply resultType :=
      TypeSystem.InferState.apply_resolve_eq_apply outerApplication _
    have outputPath : CoercionPathValid active
        (later.inference.substitution.apply resultType)
        (later.inference.substitution.apply fittedResult.expression.type)
        (fittedResult.coercions.map
          (CoercionStep.applySubstitution later.inference.substitution)) := by
      rw [← outputSourceEq]
      exact rawOutputPath
    have unifiedEq := Detail.unify_resolve_eq unifySuccess
    have calleeFunctionEq : later.inference.substitution.apply callee.type =
        .function (later.inference.substitution.apply argumentType)
          (later.inference.substitution.apply resultType) := by
      calc
        later.inference.substitution.apply callee.type =
            later.inference.substitution.apply
              (unifiedState.resolve callee.type) :=
          (TypeSystem.InferState.apply_resolve_eq_apply outerUnified _).symm
        _ = later.inference.substitution.apply
              (unifiedState.resolve
                (.function argumentType resultType)) :=
          congrArg later.inference.substitution.apply unifiedEq
        _ = later.inference.substitution.apply
              (.function argumentType resultType) :=
          TypeSystem.InferState.apply_resolve_eq_apply outerUnified _
        _ = .function (later.inference.substitution.apply argumentType)
              (later.inference.substitution.apply resultType) := rfl
    have calleeFunctionType : ExpressionHasType semanticSource active callee.id
        (.function (later.inference.substitution.apply argumentType)
          (later.inference.substitution.apply resultType)) := by
      rw [← calleeFunctionEq]
      exact calleeType
    have argumentPath : CoercionPathValid active
        (later.inference.substitution.apply argumentType)
        (later.inference.substitution.apply argumentType) [] := .nil _
    simpa only [argumentType] using
      (ExpressionTypingBase.ofRecordIndirectCall
        (source := source) (callee := callee) (arguments := arguments)
        (application := {
          result := fittedResult.expression
          argumentCoercions := []
          callCoercions := fittedResult.coercions
          state := fittedResult.state
        }) (roots := roots) calleeFunctionType argumentsType argumentPath
          outputPath)

end Solcore.SourceSemantics.SourceInferenceSoundness
