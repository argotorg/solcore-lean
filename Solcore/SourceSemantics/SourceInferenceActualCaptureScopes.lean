import Solcore.SourceSemantics.SourceInferenceActualCaptureResults
import Solcore.SourceSemantics.SourceInferencePatternActiveState

/-! Real monomorphic parameter and pattern allocations preserve capture origins. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail SourceInferenceSoundness
open SourceInferenceSoundness.ProtectedVariables
namespace ActualCaptureOrigins

theorem of_scope {initial final : State} {whole : TypedSource}
    (origins : ActiveBinderCaptureOrigins initial whole)
    (same : final.lexicalScope = initial.lexicalScope) :
    ActiveBinderCaptureOrigins final whole :=
  origins.congr_localBinders (congrArg LexicalScope.binders same)

theorem freshConstructor {initial final : State} {whole : TypedSource}
    {dataType : ProgramDataSignature} {constructor : ProgramDataConstructorSignature}
    {instantiation : DataConstructorInstantiation}
    (origins : ActiveBinderCaptureOrigins initial whole)
    (accepted : freshDataConstructorInstantiation dataType constructor initial = (instantiation, final)) :
    ActiveBinderCaptureOrigins final whole := by
  have same := freshDataConstructorInstantiation_preserves_lexicalScope dataType constructor initial
  rw [accepted] at same
  exact of_scope origins same

theorem lambdaParameters
    {context : SourceInference.Context} {parameters : List Syntax.LambdaParameter}
    {index : Nat} {seen : List String} {initial : State}
    {result : List TypedBinder × List Ty × State} {whole : TypedSource}
    (accepted : bindLambdaParameters context parameters index seen initial = .ok result)
    (origins : ActiveBinderCaptureOrigins initial whole) :
    ActiveBinderCaptureOrigins result.2.2 whole := by
  induction parameters generalizing index seen initial result with
  | nil =>
    simp only [bindLambdaParameters] at accepted
    cases Except.ok.inj accepted
    exact origins
  | cons parameter rest ih =>
    cases form : parameter.value with
    | error => simp [bindLambdaParameters, form, bind, Except.bind] at accepted
    | inferred name =>
      simp only [bindLambdaParameters, form, bind, Except.bind] at accepted
      repeat' first | split at accepted
      all_goals try simp_all only [exceptPure_eq_ok]
      all_goals try simp_all
      all_goals
        subst result
        subst_vars
        have freshOrigins : ActiveBinderCaptureOrigins initial.fresh.2 whole :=
          origins.congr_localBinders rfl
        have allocatedOrigins : ActiveBinderCaptureOrigins
            (initial.fresh.2.allocateBinder name.value (.mono initial.fresh.1)
              (some parameter.span) false []).2 whole :=
          freshOrigins.allocateBinder rfl (.inl rfl)
        exact ih _ _ _ (by assumption) allocatedOrigins
    | typed marker name sourceType =>
      simp only [bindLambdaParameters, form] at accepted
      cases resolved : resolveSourceType context sourceType with
      | error error => simp [resolved, bind, Except.bind] at accepted
      | ok type =>
        simp only [resolved, bind, Except.bind] at accepted
        repeat' first | split at accepted
        all_goals try simp_all only [exceptPure_eq_ok]
        all_goals try simp_all
        all_goals
          subst result
          subst_vars
          exact ih _ _ _ (by assumption) (origins.allocateBinder rfl (.inl rfl))

theorem lambdaPrefix
    {context : SourceInference.Context} {expected : Option Ty} {annotation : Option Syntax.TypeExpr}
    {types : List Ty} {initial final : State} {resultType : Ty} {whole : TypedSource}
    (facts : LambdaPrefixFacts context expected annotation types initial resultType final)
    (origins : ActiveBinderCaptureOrigins initial whole) :
    ActiveBinderCaptureOrigins final whole := by
  cases facts with
  | noExpectedPartsAnnotated => exact origins
  | noExpectedPartsFresh _ _ fresh =>
    have same : initial.fresh.2 = final := congrArg Prod.snd fresh
    rw [← same]
    exact origins.congr_localBinders rfl
  | expectedPartsAnnotated _ unified => exact origins.unify unified
  | expectedPartsInferred _ unified => exact origins.unify unified

theorem pattern
    {fuel : Nat} {context : SourceInference.Context} {pattern : Syntax.Pattern}
    {expected : Ty} {initial : State} {result : TypedMatchPattern × State} {whole : TypedSource}
    (accepted : inferMatchPatternFuel fuel context pattern expected initial = .ok result)
    (origins : ActiveBinderCaptureOrigins initial whole) :
    ActiveBinderCaptureOrigins result.2 whole :=
  (inferMatchPatternFuel_scope accepted).captureOrigins origins

theorem scrutinee
    {fuel : Nat} {context : SourceInference.Context} {span : Syntax.SourceSpan}
    {sources : List Syntax.Expr} {initial : State} {result : InferredExpression × State}
    {whole : TypedSource}
    (accepted : matchScrutinee fuel context span sources initial = .ok result)
    (origins : ActiveBinderCaptureOrigins initial whole) :
    ActiveBinderCaptureOrigins result.2 whole := by
  unfold matchScrutinee at accepted
  split at accepted
  · exact origins.inferExprFuel accepted
  · cases children : inferExprsFuel fuel context sources initial with
    | error error => simp [children, bind, Except.bind] at accepted
    | ok values =>
      simp only [children, bind, Except.bind, pure, Pure.pure, Except.pure] at accepted
      cases Except.ok.inj accepted
      exact (origins.inferExprsFuel children).congr_localBinders rfl

end ActualCaptureOrigins
end Solcore.SourceSemantics.SourceInferenceExecution
