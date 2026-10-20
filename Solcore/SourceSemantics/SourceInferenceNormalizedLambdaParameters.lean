import Solcore.SourceSemantics.SourceInferenceNormalizedContracts

/-! Actual lambda parameter allocation forms each fresh or annotated type
under the selected final substitution and enters its real monomorphic binder. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
open Frontend SourceInference TypeSystem SourceInferenceRequirementFormation SourceInferenceSoundness

theorem resolved_annotation_normalized_formation
    {semantic : SourceSemantics.Context} {outer : Substitution} {context : SourceInference.Context}
    {source : Syntax.TypeExpr} {type : Ty}
    (formation : InferenceFormationContext semantic context outer)
    (accepted : Detail.resolveSourceType context source = .ok type) :
    TypeAdmissible semantic (outer.apply type) :=
  type_applySubstitution_residual formation.residual formation.range
    (.ofWellFormed (resolveSourceType_success_typeWellFormed formation.canonical
      formation.scope.signatures formation.scope.parameters formation.scope.owner accepted))

/-- Inferred and annotated parameters follow the actual recursive allocator. -/
theorem bindLambdaParameters_normalized_formation
    {semantic : SourceSemantics.Context} {outer : Substitution}
    {context : SourceInference.Context} {parameters : List Syntax.LambdaParameter}
    {index : Nat} {seen : List String} {state : State}
    {result : List TypedBinder × List Ty × State}
    (formation : InferenceFormationContext semantic context outer)
    (formed : NormalizedStateFormation semantic outer state)
    (accepted : Detail.bindLambdaParameters context parameters index seen state = .ok result) :
    (∀ type ∈ result.2.1, TypeAdmissible semantic (outer.apply type)) ∧
      NormalizedStateFormation semantic outer result.2.2 := by
  induction parameters generalizing index seen state result with
  | nil =>
    simp only [Detail.bindLambdaParameters, Except.ok.injEq] at accepted
    subst result
    exact ⟨by simp, formed⟩
  | cons parameter rest ih =>
    cases parameterValue : parameter.value with
    | error =>
      simp [Detail.bindLambdaParameters, parameterValue, bind, Except.bind, pure, Pure.pure, Except.pure] at accepted
    | inferred name =>
      by_cases duplicate : name.value ∈ seen
      · simp [Detail.bindLambdaParameters, parameterValue, duplicate, bind, Except.bind, pure, Pure.pure, Except.pure] at accepted
      · let type := state.fresh.1
        let freshState := state.fresh.2
        let binderState := (freshState.allocateBinder name.value (.mono type) (some parameter.span) false []).2
        cases tailRun : Detail.bindLambdaParameters context rest (index + 1) (name.value :: seen) binderState with
        | error error =>
          simp [Detail.bindLambdaParameters, parameterValue, duplicate, type, freshState,
            binderState, tailRun, bind, Except.bind, pure, Pure.pure, Except.pure] at accepted
        | ok tail =>
          rcases tail with ⟨binders, types, finalState⟩
          have same : ((freshState.allocateBinder name.value (.mono type) (some parameter.span) false []).1 :: binders,
              type :: types, finalState) = result := by
            simpa [Detail.bindLambdaParameters, parameterValue, duplicate, type, freshState,
              binderState, tailRun, bind, Except.bind, pure, Pure.pure, Except.pure] using accepted
          subst result
          have typeFormed : TypeAdmissible semantic (outer.apply type) :=
            type_applySubstitution_residual formation.residual formation.range
              (.variableOfResidual formation.scope.binders formation.residual _)
          have freshFormed : NormalizedStateFormation semantic outer freshState := formed.congr rfl rfl
          have entered : NormalizedStateFormation semantic outer binderState :=
            freshFormed.allocate _ _ _ _ [] (NormalizedBinderFormation.mono _ _ _ _ _ typeFormed)
          have child := ih entered tailRun
          refine ⟨?_,child.2⟩
          intro actual member
          rcases List.mem_cons.mp member with rfl | member
          · exact typeFormed
          · exact child.1 actual member
    | typed marker name sourceType =>
      cases resolved : Detail.resolveSourceType context sourceType with
      | error error =>
        simp [Detail.bindLambdaParameters, parameterValue, resolved, bind, Except.bind] at accepted
      | ok type =>
        by_cases duplicate : name.value ∈ seen
        · simp [Detail.bindLambdaParameters, parameterValue, resolved, duplicate, bind, Except.bind, pure, Pure.pure, Except.pure] at accepted
        · let binderState := (state.allocateBinder name.value (.mono type) (some parameter.span) marker.isSome []).2
          cases tailRun : Detail.bindLambdaParameters context rest (index + 1) (name.value :: seen) binderState with
          | error error =>
            simp [Detail.bindLambdaParameters, parameterValue, resolved, duplicate,
              binderState, tailRun, bind, Except.bind, pure, Pure.pure, Except.pure] at accepted
          | ok tail =>
            rcases tail with ⟨binders, types, finalState⟩
            have same : ((state.allocateBinder name.value (.mono type) (some parameter.span) marker.isSome []).1 :: binders,
                type :: types, finalState) = result := by
              simpa [Detail.bindLambdaParameters, parameterValue, resolved, duplicate,
                binderState, tailRun, bind, Except.bind, pure, Pure.pure, Except.pure] using accepted
            subst result
            have typeFormed := resolved_annotation_normalized_formation formation resolved
            have entered : NormalizedStateFormation semantic outer binderState :=
              formed.allocate _ _ _ _ [] (NormalizedBinderFormation.mono _ _ _ _ _ typeFormed)
            have child := ih entered tailRun
            refine ⟨?_,child.2⟩
            intro actual member
            rcases List.mem_cons.mp member with rfl | member
            · exact typeFormed
            · exact child.1 actual member

end Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
