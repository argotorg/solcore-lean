import Solcore.SourceSemantics.SourceInferenceSelectedPrivacyBuiltins

/-! Actual lambda parameter allocation preserves older protected variables. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem

theorem allocate_mono_private {protectedVars : List TypeVarId} {state : State}
    {type : Ty} (name : String) (span : Option Syntax.SourceSpan) (comptime : Bool)
    (safe : Safe protectedVars state type) (live : LiveBindersSafe protectedVars state) :
    LiveBindersSafe protectedVars (state.allocateBinder name (.mono type) span comptime []).2 := by
  have transport : SafeTransport protectedVars state
      (state.allocateBinder name (.mono type) span comptime []).2 := .of_substitution_eq rfl
  intro binder member
  rcases List.mem_cons.mp member with rfl | member
  · constructor
    · intro metavariable occurs
      exact transport _ (safe_variable_member safe (List.mem_filter.mp occurs).1)
    · intro requirement occurs
      cases occurs
  · exact (live binder member).transport transport

theorem LiveBindersSafe.restore {protectedVars : List TypeVarId} {before after : State}
    (live : LiveBindersSafe protectedVars before)
    (transport : SafeTransport protectedVars before after) :
    LiveBindersSafe protectedVars (after.restoreLexicalScope before.lexicalScope) := by
  intro binder member
  exact (live binder member).transport transport

/-- Both inferred and annotated parameters follow the real fresh allocator,
annotation resolver, duplicate check and recursive binder-entry sequence. -/
theorem bindLambdaParameters_private {protectedVars : List TypeVarId}
    {context : SourceInference.Context} {parameters : List Syntax.LambdaParameter}
    {index : Nat} {seen : List String} {state : State}
    {result : List TypedBinder × List Ty × State}
    (ready : state.InferenceReady)
    (bound : ∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next)
    (live : LiveBindersSafe protectedVars state)
    (accepted : Detail.bindLambdaParameters context parameters index seen state = .ok result) :
    SafeTransport protectedVars state result.2.2 ∧
      (∀ type ∈ result.2.1, Safe protectedVars result.2.2 type) ∧
      LiveBindersSafe protectedVars result.2.2 ∧ result.2.2.requirements = state.requirements := by
  induction parameters generalizing index seen state result with
  | nil =>
    simp only [Detail.bindLambdaParameters, Except.ok.injEq] at accepted
    subst result
    exact ⟨.refl _ _, by simp, live, rfl⟩
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
          have typeSafe : Safe protectedVars freshState type := fresh_type ready bound
          have binderReady : binderState.InferenceReady :=
            State.InferenceReady.allocateBinder _ _ _ _ _ ready.fresh
              ((Ty.variablesBelow_variable_iff _ _).mpr (Nat.lt_succ_self _))
          have allocated : SafeTransport protectedVars freshState binderState := .of_substitution_eq rfl
          have entered : LiveBindersSafe protectedVars binderState :=
            allocate_mono_private _ _ _ typeSafe (live.transport rfl fresh)
          have child := ih binderReady
            (by intro metavariable member; exact Nat.lt_trans (bound metavariable member) (Nat.lt_succ_self _))
            entered tailRun
          refine ⟨fresh.trans (allocated.trans child.1), ?_, child.2.2.1, child.2.2.2⟩
          intro actual member
          rcases List.mem_cons.mp member with rfl | member
          · exact child.1 _ (allocated _ typeSafe)
          · exact child.2.1 actual member
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
            have typeSafe : Safe protectedVars state type :=
              safe_closed _ _ (Detail.resolveSourceType_success_variablesBelow resolved 0)
            have binderReady : binderState.InferenceReady :=
              State.InferenceReady.allocateBinder _ _ _ _ _ ready
                (Detail.resolveSourceType_success_variablesBelow resolved _)
            have allocated : SafeTransport protectedVars state binderState := .of_substitution_eq rfl
            have entered : LiveBindersSafe protectedVars binderState := allocate_mono_private _ _ _ typeSafe live
            have child := ih binderReady bound entered tailRun
            refine ⟨allocated.trans child.1, ?_, child.2.2.1, child.2.2.2⟩
            intro actual member
            rcases List.mem_cons.mp member with rfl | member
            · exact child.1 _ (allocated _ typeSafe)
            · exact child.2.1 actual member

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
