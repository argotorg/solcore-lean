import Solcore.SourceSemantics.SourceInferenceSelectedExpressionState
import Solcore.SourceSemantics.SourceInferenceExpressionSoundness

/-! Lambda annotations and fresh parameters are admissible in the active
context from the actual catalog and final substitution range. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

theorem substitutedVariable_admissible
    {active : SourceSemantics.Context} {substitution : Substitution}
    (binders : TypeParameterBindersWellFormed active)
    (residual : active.residualTypeVariables = true)
    (range : SubstitutionRangeAdmissible active substitution)
    (metavariable : TypeVarId) :
    TypeAdmissible active (substitution.apply (.variable metavariable)) := by
  cases found : substitution.lookup? metavariable with
  | none =>
    simp only [Substitution.apply, found, Option.getD_none]
    exact TypeAdmissible.variableOfResidual binders residual metavariable
  | some type =>
    simp only [Substitution.apply, found, Option.getD_some]
    exact range metavariable type (Substitution.lookup?_eq_some_mem found)

theorem bindLambdaParameters_success_typesAdmissible_in_active
    {inferenceContext : Frontend.SourceInference.Context}
    {sourceParameters : List Syntax.LambdaParameter}
    {index : Nat} {seen : List String}
    {state : Frontend.SourceInference.State}
    {result : List TypedBinder × List TypeSystem.Ty ×
      Frontend.SourceInference.State}
    {substitution : TypeSystem.Substitution}
    {target : SourceSemantics.Context}
    (success : Detail.bindLambdaParameters inferenceContext sourceParameters
      index seen state = .ok result)
    (canonical : SignatureParametersWellFormed
      inferenceContext.scope.genericOwner inferenceContext.typeParameters)
    (binders : TypeParameterBindersWellFormed target)
    (signatures_eq : target.signatures =
      inferenceContext.signatures)
    (parameters_eq : target.typeParameters =
      inferenceContext.typeParameters)
    (owner_eq : target.currentDeclaration =
      some inferenceContext.scope.genericOwner)
    (residual : target.residualTypeVariables = true)
    (range : SubstitutionRangeAdmissible target substitution) :
    ∀ type ∈ result.2.1,
      TypeAdmissible target (substitution.apply type) := by
  induction sourceParameters generalizing index seen state result with
  | nil =>
      simp only [Detail.bindLambdaParameters] at success
      injection success with resultEq
      subst result
      simp
  | cons parameter rest induction =>
      cases parameterValue : parameter.value with
      | error =>
          simp [Detail.bindLambdaParameters, parameterValue, bind,
            Except.bind, pure, Pure.pure, Except.pure] at success
      | inferred name =>
          by_cases duplicate : name.value ∈ seen
          · simp [Detail.bindLambdaParameters, parameterValue, duplicate,
              bind, Except.bind, pure, Pure.pure, Except.pure] at success
          · let type := state.fresh.1
            let freshState := state.fresh.2
            let binderState :=
              (freshState.allocateBinder name.value (.mono type)
                (some parameter.span) false []).2
            cases tailResult : Detail.bindLambdaParameters inferenceContext rest
                (index + 1) (name.value :: seen) binderState with
            | error error =>
                simp [Detail.bindLambdaParameters, parameterValue, duplicate,
                  type, freshState, binderState, tailResult, bind,
                  Except.bind, pure, Pure.pure, Except.pure] at success
            | ok tail =>
                rcases tail with ⟨tailBinders, tailTypes, finalState⟩
                have resultEq :
                    ((freshState.allocateBinder name.value (.mono type)
                        (some parameter.span) false []).1 :: tailBinders,
                      type :: tailTypes, finalState) = result := by
                  simpa [Detail.bindLambdaParameters, parameterValue,
                    duplicate, type, freshState, binderState, tailResult,
                    bind, Except.bind, pure, Pure.pure, Except.pure] using
                    success
                subst result
                intro candidate member
                rcases List.mem_cons.mp member with rfl | member
                · exact substitutedVariable_admissible binders residual range _
                · exact induction tailResult candidate member
      | typed marker name sourceType =>
          cases typeResult : Detail.resolveSourceType inferenceContext
              sourceType with
          | error error =>
              simp [Detail.bindLambdaParameters, parameterValue, typeResult,
                bind, Except.bind] at success
          | ok resolvedType =>
              by_cases duplicate : name.value ∈ seen
              · simp [Detail.bindLambdaParameters, parameterValue,
                  typeResult, duplicate, bind, Except.bind, pure, Pure.pure,
                  Except.pure] at success
              · let binderState :=
                  (state.allocateBinder name.value (.mono resolvedType)
                    (some parameter.span) marker.isSome []).2
                cases tailResult : Detail.bindLambdaParameters inferenceContext
                    rest (index + 1) (name.value :: seen) binderState with
                | error error =>
                    simp [Detail.bindLambdaParameters, parameterValue,
                      typeResult, duplicate, binderState, tailResult, bind,
                      Except.bind, pure, Pure.pure, Except.pure] at success
                | ok tail =>
                    rcases tail with ⟨tailBinders, tailTypes, finalState⟩
                    have resultEq :
                        ((state.allocateBinder name.value (.mono resolvedType)
                            (some parameter.span) marker.isSome []).1 ::
                            tailBinders,
                          resolvedType :: tailTypes, finalState) = result := by
                      simpa [Detail.bindLambdaParameters, parameterValue,
                        typeResult, duplicate, binderState, tailResult, bind,
                        Except.bind, pure, Pure.pure, Except.pure] using success
                    subst result
                    intro candidate member
                    rcases List.mem_cons.mp member with rfl | member
                    · rw [Detail.resolveSourceType_success_apply_eq_self substitution typeResult]
                      exact TypeAdmissible.ofWellFormed
                        (resolveSourceType_success_typeWellFormed canonical
                          signatures_eq parameters_eq owner_eq typeResult)
                    · exact induction tailResult candidate member

private theorem functionParts?_success_eq
    {type parameter result : Ty}
    (success : Detail.functionParts? type = some (parameter, result)) :
    type = .function parameter result := by
  cases type <;> simp_all [Detail.functionParts?]

theorem lambdaPrefixFacts_resultTypeAdmissible_in_active
    {inferenceContext : Frontend.SourceInference.Context}
    {expected : Option TypeSystem.Ty}
    {returnAnnotation : Option Syntax.TypeExpr}
    {parameterTypes : List TypeSystem.Ty}
    {parameterState resultState : Frontend.SourceInference.State}
    {resultType : TypeSystem.Ty}
    {active : SourceSemantics.Context}
    {substitution : TypeSystem.Substitution}
    (facts : Detail.LambdaPrefixFacts inferenceContext expected
      returnAnnotation parameterTypes parameterState resultType resultState)
    (canonical : SignatureParametersWellFormed
      inferenceContext.scope.genericOwner inferenceContext.typeParameters)
    (binders : TypeParameterBindersWellFormed active)
    (signaturesEq : active.signatures = inferenceContext.signatures)
    (parametersEq : active.typeParameters =
      inferenceContext.typeParameters)
    (ownerEq : active.currentDeclaration =
      some inferenceContext.scope.genericOwner)
    (residual : active.residualTypeVariables = true)
    (range : SubstitutionRangeAdmissible active substitution)
    (substitutionExtends : substitution.SemanticallyExtends
      parameterState.inference.substitution)
    (expectedAdmissible : ∀ expectedType ∈ expected,
      TypeAdmissible active (substitution.apply expectedType)) :
    TypeAdmissible active (substitution.apply resultType) := by
  cases facts with
  | noExpectedPartsAnnotated _ _ resolution =>
      rw [Detail.resolveSourceType_success_apply_eq_self substitution resolution]
      exact TypeAdmissible.ofWellFormed
        (resolveSourceType_success_typeWellFormed canonical signaturesEq
          parametersEq ownerEq resolution)
  | noExpectedPartsFresh _ _ freshEq =>
      have resultEq : parameterState.fresh.1 = resultType :=
        congrArg Prod.fst freshEq
      rw [← resultEq]
      change TypeAdmissible active
        (substitution.apply
          (.variable ⟨parameterState.inference.next⟩))
      exact substitutedVariable_admissible binders residual range _
  | expectedPartsAnnotated _ _ _ resolution =>
      rw [Detail.resolveSourceType_success_apply_eq_self substitution resolution]
      exact TypeAdmissible.ofWellFormed
        (resolveSourceType_success_typeWellFormed canonical signaturesEq
          parametersEq ownerEq resolution)
  | @expectedPartsInferred expectedParameter _ _ partsEq _ _ =>
      simp only [Option.bind_eq_some_iff] at partsEq
      obtain ⟨expectedType, expectedEq, partsSuccess⟩ := partsEq
      have resolvedEq : parameterState.resolve expectedType =
          .function expectedParameter resultType :=
        functionParts?_success_eq partsSuccess
      have endpointEq : substitution.apply
          (parameterState.resolve expectedType) =
          substitution.apply expectedType := by
        simpa [Frontend.SourceInference.State.resolve,
          TypeSystem.InferState.resolve] using
            substitutionExtends expectedType
      have functionAdmissible : TypeAdmissible active
          (.function (substitution.apply expectedParameter)
            (substitution.apply resultType)) := by
        rw [← FlexibleSubstitution.apply_function, ← resolvedEq,
          endpointEq]
        exact expectedAdmissible expectedType (by simp [expectedEq])
      exact functionAdmissible.function_result


private theorem lambdaFreshParameter_isolated
    {state : State} (isolated : ActiveSchemeQuantifierIsolation state)
    (bound : ActiveQuantifiersBelowNext state) (name : String)
    (span : Option Syntax.SourceSpan) :
    ActiveSchemeQuantifierIsolation
      (state.fresh.2.allocateBinder name (.mono state.fresh.1) span false []).2 := by
  apply activeSchemeQuantifierIsolation_allocateMonoBinder
  · exact activeSchemeQuantifierIsolation_transport isolated rfl
  · intro metavariable free quantified
    have same : metavariable = ⟨state.inference.next⟩ := by
      simpa [State.fresh, InferState.fresh, Ty.freeVariables] using free
    subst metavariable
    obtain ⟨binder, member, quantified⟩ := List.mem_flatMap.mp quantified
    have below := bound binder member _ quantified
    exact Nat.lt_irrefl _ below

private theorem lambdaAnnotatedParameter_isolated
    {context : Frontend.SourceInference.Context} {sourceType : Syntax.TypeExpr}
    {state : State} {type : Ty}
    (isolated : ActiveSchemeQuantifierIsolation state)
    (resolved : Detail.resolveSourceType context sourceType = .ok type)
    (name : String) (span : Option Syntax.SourceSpan) (comptime : Bool) :
    ActiveSchemeQuantifierIsolation
      (state.allocateBinder name (.mono type) span comptime []).2 := by
  apply activeSchemeQuantifierIsolation_allocateBinder
  · exact isolated
  · intro metavariable free _
    have freeType : metavariable ∈ type.freeVariables := by
      simpa [Scheme.mono, Scheme.freeVariables] using free
    exact Nat.not_lt_zero _
      (Detail.resolveSourceType_success_variablesBelow resolved 0 metavariable freeType)
  · simp [Scheme.mono]

theorem bindLambdaParameters_preserves_actualScope
    {context : Frontend.SourceInference.Context}
    {parameters : List Syntax.LambdaParameter} {index : Nat}
    {seen : List String} {state : State}
    {result : List TypedBinder × List Ty × State} {source : TypedSource}
    (operational : ActualStateInvariant state source)
    (isolated : ActiveSchemeQuantifierIsolation state)
    (success : Detail.bindLambdaParameters context parameters index seen state = .ok result) :
    ActualStateInvariant result.2.2 source ∧
      ActiveSchemeQuantifierIsolation result.2.2 := by
  induction parameters generalizing index seen state result with
  | nil =>
    simp only [Detail.bindLambdaParameters] at success
    injection success with resultEq
    subst result
    exact ⟨operational, isolated⟩
  | cons parameter rest induction =>
    cases parameterValue : parameter.value with
    | error =>
      simp [Detail.bindLambdaParameters, parameterValue, bind, Except.bind] at success
    | inferred name =>
      simp only [Detail.bindLambdaParameters, parameterValue, bind, Except.bind] at success
      repeat' first | split at success
      all_goals try simp_all only [exceptPure_eq_ok]
      all_goals try simp_all
      all_goals
        subst result
        subst_vars
        exact induction _ _ _
          (operational.fresh.allocateMonoBinder name.value state.fresh.1 (some parameter.span) false)
          (lambdaFreshParameter_isolated isolated operational.quantifiersBelow name.value (some parameter.span))
          (by assumption)
    | typed marker name sourceType =>
      simp only [Detail.bindLambdaParameters, parameterValue] at success
      cases resolution : Detail.resolveSourceType context sourceType with
      | error error => simp [resolution, bind, Except.bind] at success
      | ok parameterType =>
        simp only [resolution, bind, Except.bind] at success
        repeat' first | split at success
        all_goals try simp_all only [exceptPure_eq_ok]
        all_goals try simp_all
        all_goals
          subst result
          subst_vars
          exact induction _ _ _
            (operational.allocateMonoBinder name.value parameterType (some parameter.span) marker.isSome)
            (lambdaAnnotatedParameter_isolated isolated resolution name.value (some parameter.span) marker.isSome)
            (by assumption)

theorem lambdaPrefixFacts_preserves_actualScope
    {context : Frontend.SourceInference.Context} {expected : Option Ty}
    {annotation : Option Syntax.TypeExpr} {types : List Ty}
    {initial final : State} {resultType : Ty} {source : TypedSource}
    (operational : ActualStateInvariant initial source)
    (isolated : ActiveSchemeQuantifierIsolation initial)
    (facts : Detail.LambdaPrefixFacts context expected annotation types initial resultType final) :
    ActualStateInvariant final source ∧ ActiveSchemeQuantifierIsolation final := by
  cases facts with
  | noExpectedPartsAnnotated => exact ⟨operational, isolated⟩
  | noExpectedPartsFresh _ _ fresh =>
    have stateEq : initial.fresh.2 = final := congrArg Prod.snd fresh
    rw [← stateEq]
    exact ⟨operational.fresh, activeSchemeQuantifierIsolation_transport isolated rfl⟩
  | expectedPartsAnnotated _ unified | expectedPartsInferred _ unified =>
    exact ⟨operational.unify unified, activeSchemeQuantifierIsolation_transport isolated
      (congrArg LexicalScope.binders (Detail.unify_preserves_lexicalScope unified))⟩

end Solcore.SourceSemantics.SourceInferenceSoundness
