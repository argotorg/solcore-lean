import Solcore.SourceSemantics.SourceInferenceGeneralizedConstructorState
import Solcore.SourceSemantics.SourceInferenceSelectedLambdaPrefix

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend SourceInference TypeSystem ProtectedVariables

theorem GeneralizedActualStateInvariant.allocateMonoBinder
    {state : State} {source : TypedSource}
    (invariant : GeneralizedActualStateInvariant state source)
    (name : String) (type : Ty) (span : Option Syntax.SourceSpan) (comptime : Bool)
    (safe : ∀ binder ∈ state.localBinders, Safe binder.scheme.quantified state type) :
    GeneralizedActualStateInvariant (state.allocateBinder name (.mono type) span comptime []).2 source := by
  obtain ⟨pending, ledger⟩ := invariant.ledger
  refine ⟨⟨pending, ledger.allocateBinderWithoutRequirements name (.mono type) span comptime⟩,
    invariant.origins.allocateBinder rfl (.inl rfl),
    activeQuantifiersBelowNext_allocateBinder state name (.mono type) span comptime []
      invariant.quantifiersBelow (by simp [Scheme.mono]), ?_, ?_⟩
  · intro binder member
    rcases List.mem_cons.mp member with rfl | member
    · exact liveBindersSafe_nil _
    · exact allocate_mono_private name span comptime (safe binder member) (invariant.privacy binder member)
  · intro binder member requirement retained
    rcases List.mem_cons.mp member with rfl | member
    · cases retained
    · exact invariant.backed binder member requirement retained

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

theorem bindLambdaParameters_preserves_generalizedScope
    {context : Frontend.SourceInference.Context}
    {parameters : List Syntax.LambdaParameter} {index : Nat}
    {seen : List String} {state : State}
    {result : List TypedBinder × List Ty × State} {source : TypedSource}
    (ready : state.InferenceReady)
    (operational : GeneralizedActualStateInvariant state source)
    (isolated : ActiveSchemeQuantifierIsolation state)
    (success : Detail.bindLambdaParameters context parameters index seen state = .ok result) :
    GeneralizedActualStateInvariant result.2.2 source ∧
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
          (State.InferenceReady.allocateBinder name.value (.mono state.fresh.1) (some parameter.span) false [] ready.fresh
            ((Ty.variablesBelow_variable_iff _ _).mpr (Nat.lt_succ_self _)))
          (operational.fresh.allocateMonoBinder name.value state.fresh.1 (some parameter.span) false
            (fun binder member => fresh_type ready (operational.quantifiersBelow binder member)))
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
            (State.InferenceReady.allocateBinder name.value (.mono parameterType) (some parameter.span) marker.isSome [] ready
              (Detail.resolveSourceType_success_variablesBelow resolution _))
            (operational.allocateMonoBinder name.value parameterType (some parameter.span) marker.isSome
              (fun binder _ => safe_closed binder.scheme.quantified state
                (Detail.resolveSourceType_success_variablesBelow resolution 0)))
            (lambdaAnnotatedParameter_isolated isolated resolution name.value (some parameter.span) marker.isSome)
            (by assumption)

theorem bindLambdaParameters_quantified_origin
    {context : SourceInference.Context} {parameters : List Syntax.LambdaParameter}
    {index : Nat} {seen : List String} {state : State}
    {result : List TypedBinder × List Ty × State}
    (success : Detail.bindLambdaParameters context parameters index seen state = .ok result) :
    ∀ binder ∈ result.2.2.localBinders,
      binder ∈ state.localBinders ∨ binder.scheme.quantified = [] := by
  induction parameters generalizing index seen state result with
  | nil =>
    simp only [Detail.bindLambdaParameters] at success
    injection success with resultEq
    subst result
    exact fun _ member => .inl member
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
        intro binder member
        rcases induction _ _ _ (by assumption) binder member with old | empty
        · rcases List.mem_cons.mp old with rfl | old
          · exact .inr rfl
          · exact .inl old
        · exact .inr empty
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
          intro binder member
          rcases induction _ _ _ (by assumption) binder member with old | empty
          · rcases List.mem_cons.mp old with rfl | old
            · exact .inr rfl
            · exact .inl old
          · exact .inr empty

end Solcore.SourceSemantics.SourceInferenceSoundness
