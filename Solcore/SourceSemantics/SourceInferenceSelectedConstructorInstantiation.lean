import Solcore.SourceSemantics.SourceInferenceSelectedConstructorApplication

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
