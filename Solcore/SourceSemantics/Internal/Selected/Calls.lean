import Solcore.SourceSemantics.Internal.Selected.Children
import Solcore.SourceSemantics.Internal.Selected.Operators
import Solcore.SourceSemantics.Internal.Selected.OperatorMetadata
import Solcore.SourceSemantics.Internal.Selected.State
import Solcore.SourceSemantics.Internal.Selected.Candidates

/-!
# Selected calls and constructors

Named, indirect and constructor calls keep their typing through the actual selected trace.
-/

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedConstructorApplication
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
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedConstructorInstantiation
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

theorem RecursiveExpressionInvariant.freshConstructor
    {wholeContext : Frontend.SourceInference.Context} {finalized : Frontend.SourceInference.Result}
    {state : State} {context : SourceSemantics.Context}
    (invariant : RecursiveExpressionInvariant wholeContext finalized state context)
    (dataType : ProgramDataSignature) (constructor : ProgramDataConstructorSignature) :
    RecursiveExpressionInvariant wholeContext finalized
      (Detail.freshDataConstructorInstantiation dataType constructor state).2 context := by
  let step : List Ty × State → TypeParameterId → List Ty × State :=
    fun result _ => (result.1 ++ [result.2.fresh.1], result.2.fresh.2)
  have foldPreserves (parameters : List TypeParameterId) (accumulator : List Ty × State)
      (valid : RecursiveExpressionInvariant wholeContext finalized accumulator.2 context) :
      RecursiveExpressionInvariant wholeContext finalized (parameters.foldl step accumulator).2 context := by
    induction parameters generalizing accumulator with
    | nil => exact valid
    | cons parameter parameters induction =>
      exact induction (step accumulator parameter) (valid.fresh valid.substitutionExtension)
  exact foldPreserves dataType.parameters ([], state) invariant

theorem ActualStateInvariant.freshConstructor
    {state : State} {source : TypedSource}
    (invariant : ActualStateInvariant state source)
    (dataType : ProgramDataSignature) (constructor : ProgramDataConstructorSignature) :
    ActualStateInvariant (Detail.freshDataConstructorInstantiation dataType constructor state).2 source := by
  let step : List Ty × State → TypeParameterId → List Ty × State :=
    fun result _ => (result.1 ++ [result.2.fresh.1], result.2.fresh.2)
  have foldPreserves (parameters : List TypeParameterId) (accumulator : List Ty × State)
      (valid : ActualStateInvariant accumulator.2 source) :
      ActualStateInvariant (parameters.foldl step accumulator).2 source := by
    induction parameters generalizing accumulator with
    | nil => exact valid
    | cons parameter parameters induction =>
      exact induction (step accumulator parameter) valid.fresh
  exact foldPreserves dataType.parameters ([], state) invariant

theorem freshConstructor_admissible_afterSubstitution
    {context : SourceSemantics.Context} {outer : Substitution}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (binders : TypeParameterBindersWellFormed context)
    (residual : context.residualTypeVariables = true)
    (range : SubstitutionRangeAdmissible context outer)
    {dataType : ProgramDataSignature} {constructor : ProgramDataConstructorSignature}
    {state next : State} {instantiation : DataConstructorInstantiation}
    (dataType_mem : dataType ∈ context.signatures.dataTypes)
    (constructor_mem : constructor ∈ dataType.constructors)
    (fresh : Detail.freshDataConstructorInstantiation dataType constructor state = (instantiation, next)) :
    SourceSemantics.DataConstructorInstantiation.Admissible context (instantiation.applySubstitution outer) := by
  obtain ⟨arguments, argumentsLength, argumentsVariables, instantiationEq⟩ :=
    Detail.freshDataConstructorInstantiation_success_shape fresh
  subst instantiation
  have dataWellFormed := catalog.data_semantic dataType dataType_mem
  have innerExact : ParameterSubstitution.Exact
      (dataType.parameters.zip arguments) dataType.parameters :=
    ParameterSubstitution.exact_zip dataWellFormed.parameters_nodup
      argumentsLength
  refine .intro dataType constructor dataType_mem constructor_mem
    (dataWellFormed.constructor_owners constructor constructor_mem) rfl ?_ ?_
      ?_ ?_
  · change ParameterSubstitution.Exact
      (FlexibleSubstitution.ParameterSubstitution.mapRange outer
        (dataType.parameters.zip arguments)) dataType.parameters
    exact FlexibleSubstitution.ParameterSubstitution.Exact.mapRange outer
      innerExact
  · change ParameterSubstitution.RangeAdmissible context
      (FlexibleSubstitution.ParameterSubstitution.mapRange outer
        (dataType.parameters.zip arguments))
    intro parameter replacement member
    rcases List.mem_map.mp member with
      ⟨⟨sourceParameter, argument⟩, sourceMember, entryEq⟩
    cases entryEq
    obtain ⟨metavariable, rfl⟩ := argumentsVariables argument (List.of_mem_zip sourceMember).2
    cases found : outer.lookup? metavariable with
    | none =>
      simp only [Substitution.apply, found, Option.getD_none]
      exact TypeAdmissible.variableOfResidual binders residual metavariable
    | some type =>
      simp only [Substitution.apply, found, Option.getD_some]
      exact range metavariable type (Substitution.lookup?_eq_some_mem found)
  · change
      (constructor.payloadTypes.map
          (ParameterSubstitution.apply
            (dataType.parameters.zip arguments))).map outer.apply =
        constructor.payloadTypes.map
          (ParameterSubstitution.apply
            (FlexibleSubstitution.ParameterSubstitution.mapRange outer
              (dataType.parameters.zip arguments)))
    exact FlexibleSubstitution.TypesWellScoped.applyFlexible_composeParameters
      (context := signatureContext context.signatures dataType.id
        dataType.parameters)
      outer (dataType.parameters.zip arguments) innerExact
      (StructuralSubstitution.TypesWellFormed.toTypesWellScoped
        (dataWellFormed.constructor_payloads constructor constructor_mem))
  · change outer.apply (Ty.nominal dataType.id arguments) =
      Ty.nominal dataType.id
        (ParameterSubstitution.orderedArguments
          (FlexibleSubstitution.ParameterSubstitution.mapRange outer
            (dataType.parameters.zip arguments)) dataType.parameters)
    rw [StructuralSubstitution.applyFlexible_nominal,
      FlexibleSubstitution.ParameterSubstitution.orderedArguments_mapRange
        outer innerExact,
      ParameterSubstitution.orderedArguments_zip
        dataWellFormed.parameters_nodup argumentsLength]

end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedFreshConstructor
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

theorem actualFreshConstructorApplication_typing {fuel : Nat}
    (recursive : ActualInferExprFuelRetainedSoundness fuel) :
  ∀ {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn : Ty} {source : Syntax.Expr} {id : ExpressionId}
    {arguments : List Syntax.Expr} {instantiation : DataConstructorInstantiation} {expected : Option Ty}
    {initial constructorState resultState evidenceState : State}
    {dataType : ProgramDataSignature} {constructor : ProgramDataConstructorSignature} {inferred : InferredExpression}
    {roots : List NodeId} {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource} {frames : List InitializedLetBinding} {semanticContext : SourceSemantics.Context},
    dataType ∈ inferenceContext.signatures.dataTypes →
    constructor ∈ dataType.constructors →
    Detail.freshDataConstructorInstantiation dataType constructor initial = (instantiation, constructorState) →
    Detail.inferConstructorApplicationFuel fuel inferenceContext source id instantiation arguments expected constructorState = .ok (inferred, resultState) →
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
    (∀ type ∈ expected, type.VariablesBelow initial.inference.next) →
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
  intro wholeContext inferenceContext wholeReturn source id arguments instantiation expected initial constructorState resultState evidenceState
    dataType constructor inferred roots finalized semanticSource frames semanticContext dataMember constructorMember fresh
    success resources interfaces extension signaturesEq ownerEq typeParametersEq assumptionsEq formation functions catalog canonical
    invariant actual operational expectedBelow semantic final raw patterns literals requirements retained coercionsRetained
    childrenRetained covered actualCovered
  have freshInvariant := invariant.freshConstructor dataType constructor
  have freshOperational := operational.freshConstructor dataType constructor
  rw [fresh] at freshInvariant freshOperational
  have properties := Detail.freshDataConstructorInstantiation_inferenceProperties dataType constructor initial invariant.ready
    (formation.data_constructor_payloadTypes_variablesBelow dataMember constructorMember initial.inference.next)
  rw [fresh] at properties
  have binders := invariant.typeParameterBinders (by simpa only [ownerEq, typeParametersEq] using canonical)
  have activeCatalog : SignatureCatalogWellFormed semanticContext.signatures := by
    rw [invariant.signatures_eq_whole, ← signaturesEq]; exact catalog
  have activeData : dataType ∈ semanticContext.signatures.dataTypes := by
    rw [invariant.signatures_eq_whole, ← signaturesEq]; exact dataMember
  have range := resources.substitutionRangeAdmissible binders invariant.signatures_eq_whole invariant.typeParametersEq
    invariant.declarationEq invariant.residual
  have valid := freshConstructor_admissible_afterSubstitution activeCatalog binders invariant.residual range
    activeData constructorMember fresh
  exact actualConstructorApplication_typing recursive success resources interfaces extension signaturesEq ownerEq typeParametersEq
    assumptionsEq formation functions catalog canonical freshInvariant actual freshOperational properties.2.2.2.1
    properties.2.2.2.2 (fun type member => (expectedBelow type member).weaken properties.1.next_le) valid
    semantic final raw patterns literals requirements retained coercionsRetained childrenRetained covered actualCovered

end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedConstructorSoundness
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
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedIndirectCall
/-! The actual indirect-call trace preserves earlier arguments while inferring
its callee, then records both coercion paths on the call. Each child is typed
from its own retained subtree and the actual scope after argument inference. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

private def indirectMetadata (state : State) :=
  (state.owner, state.integerPatterns, state.integerLiterals)

private theorem unify_indirectMetadata {state next : State} {left right : Ty}
    (success : Detail.unify state left right = .ok next) :
    indirectMetadata next = indirectMetadata state := by
  unfold Detail.unify at success
  cases unified : state.inference.unify left right <;>
    simp [Detail.liftUnification, unified, bind, Except.bind] at success
  cases success
  rfl

private theorem withExpected_indirectMetadata
    {context : Frontend.SourceInference.Context} {state : State} {actual : InferredExpression}
    {expected : Option Ty} {result : Detail.ExpectationResult}
    (success : Detail.withExpected context state actual expected = .ok result) :
    indirectMetadata result.state = indirectMetadata state := by
  apply Prod.ext
  · exact congrArg State.Header.owner (Detail.SelectedMetadata.withExpected_state_header success)
  · exact Prod.ext (Detail.SelectedMetadata.withExpected_integerPatterns_eq success)
      (Detail.SelectedMetadata.withExpected_integerLiterals_eq success)

theorem applyFunctionType_metadata
    {context : Frontend.SourceInference.Context} {call : ExpressionId} {calleeType : Ty}
    {arguments : List InferredExpression} {expected : Option Ty}
    {state : State} {result : Detail.IndirectApplicationResult}
    (success : Detail.applyFunctionType context call calleeType arguments expected state = .ok result) :
    result.state.owner = state.owner ∧ result.state.integerPatterns = state.integerPatterns ∧
      result.state.integerLiterals = state.integerLiterals := by
  have metadata : indirectMetadata result.state = indirectMetadata state := by
    rcases Detail.applyFunctionType_success_facts success with known | fresh
    · obtain ⟨parameter, resultType, fittedArgument, fittedResult, _, argumentSuccess, outputSuccess, rfl⟩ := known
      exact (withExpected_indirectMetadata outputSuccess).trans (withExpected_indirectMetadata argumentSuccess)
    · obtain ⟨resultType, freshState, unifiedState, fittedResult, _, freshEq, unifySuccess, outputSuccess, rfl⟩ := fresh
      have freshMetadata : indirectMetadata freshState = indirectMetadata state := by
        have stateEq : state.fresh.2 = freshState := congrArg Prod.snd freshEq
        rw [← stateEq]
        rfl
      exact (withExpected_indirectMetadata outputSuccess).trans ((unify_indirectMetadata unifySuccess).trans freshMetadata)
  exact ⟨congrArg Prod.fst metadata, congrArg (fun row => row.2.1) metadata,
    congrArg (fun row => row.2.2) metadata⟩

theorem actualIndirectCall_typing {fuel : Nat}
    (recursive : ∀ smaller, smaller < fuel + 1 → ActualInferExprFuelRetainedSoundness smaller) :
  ∀ {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn : Ty} {expression calleeSource : Syntax.Expr} {expected : Option Ty}
    {argumentSources : List Syntax.Expr} {arguments : List InferredExpression}
    {callee : InferredExpression} {call : ExpressionId}
    {application : Detail.IndirectApplicationResult}
    {initial argumentState calleeState resultState evidenceState : State}
    {inferred : InferredExpression} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource}
    {frames : List InitializedLetBinding}
    {semanticContext : SourceSemantics.Context},
    Detail.inferExprsFuel fuel inferenceContext argumentSources initial = .ok (arguments, argumentState) →
    Detail.inferExprFuel fuel inferenceContext calleeSource none argumentState = .ok (callee, calleeState) →
    Detail.applyFunctionType inferenceContext call callee.type arguments expected calleeState = .ok application →
    Detail.recordIndirectCall expression callee arguments application = (inferred, resultState) →
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
  intro wholeContext inferenceContext wholeReturn expression calleeSource expected argumentSources arguments
    callee call application initial argumentState calleeState resultState evidenceState
    inferred roots finalized semanticSource frames semanticContext argumentsSuccess calleeSuccess applicationSuccess
    recording resources interfaces resultSubstitutionExtension signaturesEq ownerEq
    typeParametersEq assumptionsEq signatureFormation functionsCanonical catalog canonical invariant
    actual operational expectedBelow expectedAdmissible finalPreserved rawProper integerPatternsSubset
    integerLiteralsSubset requirementsSubset retained coercionsRetained _operatorsRetained childrenRetained covered
    semanticPreserved actualCovered
  have inferredEq : inferred = application.result := by
    have same := congrArg Prod.fst recording
    simpa only [Detail.recordIndirectCall_fst] using same.symm
  subst inferred
  have argumentProperties := Detail.inferExprsFuel_inferenceProperties invariant.ready
    signatureFormation functionsCanonical argumentsSuccess
  have calleeProperties := Detail.inferExprFuel_inferenceProperties argumentProperties.2.1
    signatureFormation functionsCanonical (by simp) calleeSuccess
  have argumentsBelow : ∀ argument ∈ arguments, argument.type.VariablesBelow calleeState.inference.next :=
    fun argument member => (argumentProperties.2.2 argument member).weaken calleeProperties.1.next_le
  have expectedAtCallee : ∀ type ∈ expected, type.VariablesBelow calleeState.inference.next :=
    fun type member => (expectedBelow type member).weaken (argumentProperties.1.trans calleeProperties.1).next_le
  have applicationProperties := Detail.applyFunctionType_inferenceProperties
    calleeProperties.2.1 calleeProperties.2.2 argumentsBelow expectedAtCallee applicationSuccess
  have recordProperties := Detail.recordIndirectCall_inferenceProperties expression callee arguments application
    applicationProperties.2.1 applicationProperties.2.2
  rw [recording] at recordProperties
  have applicationExtension := resultSubstitutionExtension.trans recordProperties.1.substitution_extends
  have calleeExtension := applicationExtension.trans applicationProperties.1.substitution_extends
  have argumentExtension := calleeExtension.trans calleeProperties.1.substitution_extends
  have argumentInvariant := invariant.ofExpressions signatureFormation functionsCanonical argumentExtension argumentsSuccess
  have argumentOperational := operational.ofExpressions argumentsSuccess argumentProperties.1.next_le
  have argumentToCallee := inferExprFuel_success_typingSourceExtends calleeSuccess argumentInvariant.nodesBelow roots
  have metadata := applyFunctionType_metadata applicationSuccess
  have calleeToApplication : TypingSourceExtends (calleeState.toTypedSource roots)
      (application.state.toTypedSource roots) := by
    refine ⟨metadata.1, ?_⟩
    change calleeState.nodes <+: application.state.nodes
    rw [(Detail.applyFunctionType_occurrenceState_eq applicationSuccess).1]
    exact List.prefix_rfl
  have applicationToParent : TypingSourceExtends (application.state.toTypedSource roots)
      (resultState.toTypedSource roots) := by
    have stateEq : (Detail.recordIndirectCall expression callee arguments application).2 = resultState := congrArg Prod.snd recording
    rw [← stateEq]
    refine ⟨rfl, ?_⟩
    change application.state.nodes <+: application.state.nodes ++ [_]
    exact List.prefix_append _ _
  have calleeToParent := calleeToApplication.trans applicationToParent
  have argumentToParent := argumentToCallee.trans calleeToParent
  let callMetadata : IndirectCallResolution := {
    argumentCount := arguments.length
    argumentTypeBeforeCoercion := Ty.productMany (arguments.map (·.type))
    argumentTypeAfterCoercion := application.argumentCoercions.foldl
      (fun _ step => step.target) (Ty.productMany (arguments.map (·.type)))
    argumentCoercions := application.argumentCoercions
  }
  let callNode : ExpressionNode := {
    id := application.result.id
    span := expression.span
    type := application.result.type
    form := .call callee.id (arguments.map (·.id)) (.indirect callMetadata)
    requirements := Detail.coercionRequirements application.argumentCoercions ++
      Detail.coercionRequirements application.callCoercions
    coercions := application.callCoercions
  }
  have callContains : ContainsExpression (resultState.toTypedSource roots) application.result.id callNode := by
    have stateEq : (Detail.recordIndirectCall expression callee arguments application).2 = resultState := congrArg Prod.snd recording
    rw [← stateEq]
    exact recordExpression_containsExpression expression application.result
      (.call callee.id (arguments.map (·.id)) (.indirect callMetadata))
      (Detail.coercionRequirements application.argumentCoercions ++ Detail.coercionRequirements application.callCoercions)
      application.callCoercions application.state roots
  have calleeEdge : DirectChild (resultState.toTypedSource roots) (.expression application.result.id) (.expression callee.id) := by
    refine ⟨.expression callNode, ⟨callContains.1, rfl⟩, ?_⟩
    simp [callNode, nodeChildIds, Node.references, ExpressionForm.references]
  have argumentEdge : ∀ argument ∈ arguments,
      DirectChild (resultState.toTypedSource roots) (.expression application.result.id) (.expression argument.id) := by
    intro argument member
    refine ⟨.expression callNode, ⟨callContains.1, rfl⟩, ?_⟩
    simp only [callNode, nodeChildIds, Node.references, ExpressionForm.references, List.mem_cons]
    exact Or.inr (List.mem_map.mpr ⟨argument.id, List.mem_map.mpr ⟨argument, member, rfl⟩, rfl⟩)
  have parentPatterns : resultState.integerPatterns = application.state.integerPatterns := by
    have stateEq : (Detail.recordIndirectCall expression callee arguments application).2 = resultState := congrArg Prod.snd recording
    rw [← stateEq]
    rfl
  have parentLiterals : resultState.integerLiterals = application.state.integerLiterals := by
    have stateEq : (Detail.recordIndirectCall expression callee arguments application).2 = resultState := congrArg Prod.snd recording
    rw [← stateEq]
    rfl
  have calleePatterns : calleeState.integerPatterns ⊆ evidenceState.integerPatterns := by
    rw [← metadata.2.1, ← parentPatterns]
    exact integerPatternsSubset
  have calleeLiterals : calleeState.integerLiterals ⊆ evidenceState.integerLiterals := by
    rw [← metadata.2.2, ← parentLiterals]
    exact integerLiteralsSubset
  have calleeRequirements : calleeState.requirements ⊆ evidenceState.requirements := by
    apply List.Subset.trans (Detail.applyFunctionType_requirements_subset applicationSuccess)
    have recorded := Detail.recordIndirectCall_requirements_subset expression callee arguments application
    rw [recording] at recorded
    exact recorded.trans requirementsSubset
  have argumentsTyped := actualInferExprsFuelFinalSubtreeSoundness fuel
    (fun smaller less => recursive smaller (Nat.lt_trans less (Nat.lt_succ_self fuel)))
    argumentsSuccess resources interfaces argumentExtension signaturesEq ownerEq typeParametersEq assumptionsEq
    signatureFormation functionsCanonical catalog canonical invariant actual operational
    (fun argument member => (semanticPreserved.childSubtree (argumentEdge argument member)).monoBefore argumentToParent)
    (fun argument member => (finalPreserved.childSubtree (argumentEdge argument member)).monoBefore argumentToParent)
    (fun argument member => ((rawProper.childSubtree (argumentEdge argument member)).monoBefore argumentToParent).proper)
    ((Detail.inferExprFuel_integerPatterns_subset calleeSuccess).trans calleePatterns)
    ((Detail.inferExprFuel_integerLiterals_subset calleeSuccess).trans calleeLiterals)
    ((Detail.inferExprFuel_requirements_subset calleeSuccess).trans calleeRequirements)
    (fun argument member => covered.expressionChild resources.graph_closed (childrenRetained (argumentEdge argument member)))
    (fun argument member => actualCovered.directChild (childrenRetained (argumentEdge argument member)))
  have calleeTyped := actualInferExprFuelFinalSubtreeSoundness_of_retainedSoundness
    (recursive fuel (Nat.lt_succ_self fuel)) calleeSuccess resources interfaces calleeExtension
    signaturesEq ownerEq typeParametersEq assumptionsEq signatureFormation functionsCanonical catalog canonical
    argumentInvariant actual argumentOperational (by simp) (by simp)
    ((semanticPreserved.childSubtree calleeEdge).monoBefore calleeToParent)
    ((finalPreserved.childSubtree calleeEdge).monoBefore calleeToParent)
    ((rawProper.childSubtree calleeEdge).monoBefore calleeToParent).proper
    calleePatterns calleeLiterals calleeRequirements
    (covered.expressionChild resources.graph_closed (childrenRetained calleeEdge))
    (actualCovered.directChild (childrenRetained calleeEdge))
  have activeSignaturesEq := invariant.signatures_eq_whole.trans signaturesEq.symm
  have activeCatalog : SignatureCatalogWellFormed semanticContext.signatures := by
    rw [activeSignaturesEq]
    exact catalog
  have finalSubstitutionEq := resources.substitution_eq.symm
  have finalRequirements : resultState.requirements ⊆ resources.finalState.requirements := by
    rw [resources.requirements_eq]
    exact requirementsSubset
  simpa only [finalSubstitutionEq] using
    (applyFunctionType_recordIndirectCall_typing_from_interfaces
      (solverContext := wholeContext) (later := resources.finalState)
      (base := finalizedRequirementContext wholeContext finalized)
      applicationSuccess recording calleeProperties.2.1 calleeProperties.2.2 argumentsBelow expectedAtCallee
      (by simpa only [finalSubstitutionEq] using resultSubstitutionExtension)
      finalRequirements retained coercionsRetained (by simpa only [signaturesEq] using interfaces)
      (by simpa only [finalSubstitutionEq] using argumentsTyped)
      (by simpa only [finalSubstitutionEq] using calleeTyped)
      activeCatalog activeSignaturesEq resources.solve_success resources.solved_context_eq
      resources.ledger resources.ownership invariant.signaturesEq invariant.solvedRequirementsEq
      invariant.assumptionsMono covered)

end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedNamedCall
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

theorem actualSelectedCall_typing {fuel : Nat}
    (recursive : ∀ smaller, smaller < fuel → ActualInferExprFuelRetainedSoundness smaller) :
  ∀ {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn : Ty} {expression callee : Syntax.Expr} {expected : Option Ty}
    {argumentSources : List Syntax.Expr} {arguments : List InferredExpression}
    {name : String} {candidates : List ProgramFunctionSignature}
    {integerLiteralOrigins : List IntegerLiteralOrigin} {call : ExpressionId}
    {attempt : Detail.CandidateAttemptResult}
    {initial argumentState resultState evidenceState : State}
    {inferred : InferredExpression} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource}
    {frames : List InitializedLetBinding}
    {semanticContext : SourceSemantics.Context},
    Detail.inferExprsFuel fuel inferenceContext argumentSources initial = .ok (arguments, argumentState) →
    Detail.selectFunctionCandidateFrom inferenceContext name candidates arguments integerLiteralOrigins
      call expected argumentState = .ok attempt →
    Detail.recordSelectedCall expression callee name arguments attempt = (inferred, resultState) →
    candidates ⊆ inferenceContext.signatures.functions →
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
  intro wholeContext inferenceContext wholeReturn expression callee expected argumentSources arguments
    name candidates integerLiteralOrigins call attempt initial argumentState resultState evidenceState
    inferred roots finalized semanticSource frames semanticContext argumentsSuccess selectionSuccess
    recording candidatesSubset resources interfaces resultSubstitutionExtension signaturesEq ownerEq
    typeParametersEq assumptionsEq signatureFormation functionsCanonical catalog canonical invariant
    actual operational expectedBelow expectedAdmissible finalPreserved rawProper integerPatternsSubset
    integerLiteralsSubset requirementsSubset retained coercionsRetained _operatorsRetained childrenRetained covered
    semanticPreserved actualCovered
  have recordSuccess : Detail.recordSelectedCallResult expression callee name arguments attempt
      attempt.result [] attempt.state = (inferred, resultState) := by
    simpa only [Detail.recordSelectedCall] using recording
  have inferredEq : inferred = attempt.result := (Detail.recordSelectedCallResult_success_nodes recordSuccess).1
  subst inferred
  have activeSignaturesEq := invariant.signatures_eq_whole.trans signaturesEq.symm
  obtain ⟨signature, _, signatureMember, signatureCanonical, schemeBelow, candidateSuccess⟩ :=
    selectFunctionCandidateFrom_success_semanticCandidate signatureFormation functionsCanonical
      activeSignaturesEq candidatesSubset selectionSuccess
  have argumentProperties := Detail.inferExprsFuel_inferenceProperties invariant.ready
    signatureFormation functionsCanonical argumentsSuccess
  have expectedAtArguments : ∀ type ∈ expected, type.VariablesBelow argumentState.inference.next :=
    fun type member => (expectedBelow type member).weaken argumentProperties.1.next_le
  have candidateProperties := Detail.tryFunctionCandidate_some_inferenceProperties
    argumentProperties.2.1 argumentProperties.2.2 schemeBelow expectedAtArguments candidateSuccess
  have recordProperties := Detail.recordSelectedCall_inferenceProperties expression callee name arguments
    attempt candidateProperties.2.1 candidateProperties.2.2
  rw [recording] at recordProperties
  have attemptExtension := resultSubstitutionExtension.trans recordProperties.1.substitution_extends
  have argumentExtension := attemptExtension.trans candidateProperties.1.substitution_extends
  have argumentIdsUnique := Detail.inferExprsFuel_success_ids_nodup argumentsSuccess
  have entryIds : attempt.argumentCoercions.map (·.expression) = arguments.map (·.id) :=
    Detail.tryFunctionCandidate_some_argumentCoercion_expression_ids signatureCanonical candidateSuccess
  have entryIdsUnique : (attempt.argumentCoercions.map (·.expression)).Nodup := by
    rw [entryIds]; exact argumentIdsUnique
  have argumentToAttempt : TypingSourceExtends (argumentState.toTypedSource roots)
      (attempt.state.toTypedSource roots) := by
    refine ⟨?_, ?_⟩
    · exact congrArg State.Header.owner (Detail.SelectedMetadata.tryFunctionCandidate_some_state_header candidateSuccess)
    · change argumentState.nodes <+: attempt.state.nodes
      rw [(Detail.tryFunctionCandidate_some_occurrenceState_eq candidateSuccess).1]
      exact List.prefix_rfl
  have attachedExtension := recordSelectedCallResult_success_attachedTypingSourceExtends recordSuccess roots
  have callContains := recordSelectedCallResult_success_containsExpression recordSuccess roots
  have argumentEdge : ∀ argument ∈ arguments,
      DirectChild (resultState.toTypedSource roots) (.expression attempt.result.id) (.expression argument.id) := by
    intro argument member
    refine ⟨.expression _, ⟨callContains.1, rfl⟩, ?_⟩
    simp only [nodeChildIds, Node.references, ExpressionForm.references, List.mem_cons]
    exact Or.inr (List.mem_map.mpr ⟨argument.id, List.mem_map.mpr ⟨argument, member, rfl⟩, rfl⟩)
  have entryEdge : ∀ entry ∈ attempt.argumentCoercions,
      DirectChild (resultState.toTypedSource roots) (.expression attempt.result.id) (.expression entry.expression) := by
    intro entry member
    have idMember : entry.expression ∈ arguments.map (·.id) := by
      rw [← entryIds]; exact List.mem_map.mpr ⟨entry, member, rfl⟩
    obtain ⟨argument, argumentMember, idEq⟩ := List.mem_map.mp idMember
    rw [← idEq]; exact argumentEdge argument argumentMember
  have argumentPreserved : ∀ argument ∈ arguments,
      AttachedChildPreserved finalized.substitution (argumentState.toTypedSource roots)
        semanticSource finalized.typedSource (evidenceState.toTypedSource roots) argument.id := by
    intro argument member
    have idMember : argument.id ∈ attempt.argumentCoercions.map (·.expression) := by
      rw [entryIds]; exact List.mem_map.mpr ⟨argument, member, rfl⟩
    obtain ⟨entry, entryMember, idEq⟩ := List.mem_map.mp idMember
    rw [← idEq]
    exact (AttachedChildPreserved.of_attachment attempt.state attempt.argumentCoercions roots
      attachedExtension entryIdsUnique entryEdge semanticPreserved finalPreserved rawProper
      childrenRetained resources.graph_closed entry entryMember).monoBefore argumentToAttempt
  have attemptRequirements := Detail.recordSelectedCall_requirements_subset expression callee name arguments attempt
  rw [recording] at attemptRequirements
  have argumentRequirements := (Detail.tryFunctionCandidate_requirements_subset candidateSuccess).trans
    (attemptRequirements.trans requirementsSubset)
  have argumentPatterns : argumentState.integerPatterns ⊆ evidenceState.integerPatterns := by
    have recordedPatterns := Detail.SelectedMetadata.recordSelectedCallResult_integerPatterns_eq
      expression callee name arguments attempt attempt.result [] attempt.state
    rw [recordSuccess, Detail.SelectedMetadata.tryFunctionCandidate_integerPatterns_eq candidateSuccess] at recordedPatterns
    rw [← recordedPatterns]
    exact integerPatternsSubset
  have argumentLiterals : argumentState.integerLiterals ⊆ evidenceState.integerLiterals := by
    have recordedLiterals := Detail.SelectedMetadata.recordSelectedCallResult_integerLiterals_eq
      expression callee name arguments attempt attempt.result [] attempt.state
    rw [recordSuccess, Detail.SelectedMetadata.tryFunctionCandidate_integerLiterals_eq candidateSuccess] at recordedLiterals
    rw [← recordedLiterals]
    exact integerLiteralsSubset
  have argumentBases := actualInferExprsFuelRetainedBases fuel recursive argumentsSuccess resources interfaces
    argumentExtension signaturesEq ownerEq typeParametersEq assumptionsEq signatureFormation
    functionsCanonical catalog canonical invariant actual operational argumentPreserved
    argumentPatterns argumentLiterals argumentRequirements
    (fun argument member => covered.expressionChild resources.graph_closed (childrenRetained (argumentEdge argument member)))
    (fun argument member => actualCovered.directChild (childrenRetained (argumentEdge argument member)))
  have argumentSemantic : ExpressionNodesPreservedAt (arguments.map (·.id))
      (((Detail.attachExpressionCoercions attempt.state attempt.argumentCoercions).toTypedSource roots).applySubstitution finalized.substitution)
      semanticSource := by
    intro id node member contains
    obtain ⟨argument, argumentMember, rfl⟩ := List.mem_map.mp member
    exact ((semanticPreserved.childSubtree (argumentEdge argument argumentMember)).monoBefore attachedExtension).expressionNode
      (by simp) contains
  have argumentFinal : ExpressionNodesPreservedAt (arguments.map (·.id))
      (((Detail.attachExpressionCoercions attempt.state attempt.argumentCoercions).toTypedSource roots).applySubstitution finalized.substitution)
      finalized.typedSource := by
    intro id node member contains
    obtain ⟨argument, argumentMember, rfl⟩ := List.mem_map.mp member
    exact ((finalPreserved.childSubtree (argumentEdge argument argumentMember)).monoBefore attachedExtension).expressionNode
      (by simp) contains
  have calleeEdge : DirectChild (resultState.toTypedSource roots) (.expression attempt.result.id)
      (.expression (Detail.attachExpressionCoercions attempt.state attempt.argumentCoercions).allocateExpressionId.1) := by
    refine ⟨.expression _, ⟨callContains.1, rfl⟩, ?_⟩
    simp [nodeChildIds, Node.references, ExpressionForm.references]
  have calleeSemantic : ExpressionNodesPreservedAt
      [(Detail.attachExpressionCoercions attempt.state attempt.argumentCoercions).allocateExpressionId.1]
      ((resultState.toTypedSource roots).applySubstitution finalized.substitution) semanticSource :=
    (semanticPreserved.childSubtree calleeEdge).expressionNode
  have binders := invariant.typeParameterBinders (by simpa [ownerEq, typeParametersEq] using canonical)
  have range := resources.substitutionRangeAdmissible binders invariant.signatures_eq_whole
    invariant.typeParametersEq invariant.declarationEq invariant.residual
  have activeCatalog : SignatureCatalogWellFormed semanticContext.signatures := by
    rw [activeSignaturesEq]; exact catalog
  have finalSubstitutionEq := resources.substitution_eq.symm
  have finalExtension : resources.finalState.inference.substitution.SemanticallyExtends attempt.state.inference.substitution := by
    simpa only [finalSubstitutionEq] using attemptExtension
  have finalRequirements : attempt.state.requirements ⊆ resources.finalState.requirements := by
    rw [resources.requirements_eq]
    exact attemptRequirements.trans requirementsSubset
  simpa only [finalSubstitutionEq] using
    (tryFunctionCandidate_recordSelectedCallResult_typing_from_interfaces
      (solverContext := wholeContext) (later := resources.finalState)
      (base := finalizedRequirementContext wholeContext finalized)
      signatureCanonical candidateSuccess recordSuccess rfl rfl
      (by simpa only [finalSubstitutionEq] using argumentBases) argumentIdsUnique
      argumentProperties.2.1 argumentProperties.2.2 schemeBelow expectedAtArguments
      finalExtension finalExtension finalRequirements
      (by
        intro id node member found
        apply argumentSemantic member
        simpa only [finalSubstitutionEq] using found)
      (by
        intro id node member found
        apply calleeSemantic member
        simpa only [finalSubstitutionEq] using found)
      (by
        intro id node member found
        apply argumentFinal member
        simpa only [finalSubstitutionEq] using found)
      retained (by simpa only [signaturesEq] using interfaces) coercionsRetained
      (fun entry member => covered.expressionChild resources.graph_closed (childrenRetained (entryEdge entry member)))
      activeCatalog binders invariant.residual (by simpa only [finalSubstitutionEq] using range)
      signatureMember activeSignaturesEq resources.solve_success resources.solved_context_eq
      resources.ledger resources.ownership invariant.signaturesEq invariant.solvedRequirementsEq
      invariant.assumptionsMono covered (.nil _))

end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedNonConstructorCall
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
end
