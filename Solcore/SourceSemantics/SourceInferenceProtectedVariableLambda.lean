import Solcore.SourceSemantics.SourceInferenceProtectedVariableArguments

/-! Fixed protected variables survive the actual lambda parameter, body,
return-unification and saved-scope continuation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail

/-- Parameter binding only allocates variables and lexical binders. -/
private theorem bindLambdaParameters_substitution
    {context : SourceInference.Context} {parameters : List Syntax.LambdaParameter}
    {index : Nat} {seen : List String} {state : State}
    {result : List TypedBinder × List Ty × State}
    (accepted : Detail.bindLambdaParameters context parameters index seen state = .ok result) :
    result.2.2.inference.substitution = state.inference.substitution := by
  induction parameters generalizing index seen state result with
  | nil =>
    simp only [Detail.bindLambdaParameters, Except.ok.injEq] at accepted
    subst result
    rfl
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
          exact ih (state := binderState) (result := (binders, types, finalState)) tailRun
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
            exact ih (state := binderState) (result := (binders, types, finalState)) tailRun

private theorem functionParts_eq {type parameter result : Ty}
    (found : functionParts? type = some (parameter, result)) :
    type = .function parameter result := by
  cases type <;> simp [functionParts?] at found
  rcases found with ⟨rfl, rfl⟩
  rfl

private theorem expected_parts_private
    {protectedVars : List TypeVarId} {state : State} {expected : Option Ty}
    {parameter result : Ty}
    (ready : state.InferenceReady)
    (below : ∀ type ∈ expected, type.VariablesBelow state.inference.next)
    (safe : ∀ type ∈ expected, Safe protectedVars state type)
    (parts : expected.bind (fun type => functionParts? (state.resolve type)) =
      some (parameter, result)) :
    parameter.VariablesBelow state.inference.next ∧
      result.VariablesBelow state.inference.next ∧
      Safe protectedVars state parameter ∧ Safe protectedVars state result := by
  obtain ⟨type, member, found⟩ := Option.bind_eq_some_iff.mp parts
  have present : type ∈ expected := by simp [member]
  have bounded := functionParts?_success_variablesBelow
    (ready.solved.variablesBelow_apply (below type present)) found
  have resolved := safe_resolved ready (safe type present)
  rw [functionParts_eq found] at resolved
  exact ⟨bounded.1, bounded.2, (safe_function_iff _ _ _ _).mp resolved⟩

private theorem prefix_private
    {protectedVars : List TypeVarId} {context : SourceInference.Context}
    {expected : Option Ty} {annotation : Option Syntax.TypeExpr}
    {parameters : List Ty} {state resultState : State} {resultType : Ty}
    (ready : state.InferenceReady)
    (wellFormed : state.RequirementsWellFormed)
    (bound : ∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next)
    (live : LiveBindersSafe protectedVars state)
    (parameterBelow : (Ty.productMany parameters).VariablesBelow state.inference.next)
    (parameterSafe : Safe protectedVars state (Ty.productMany parameters))
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow state.inference.next)
    (expectedSafe : ∀ type ∈ expected, Safe protectedVars state type)
    (prefixFacts : LambdaPrefixFacts context expected annotation parameters state resultType resultState) :
    state.InferenceProgress resultState ∧ resultState.InferenceReady ∧
      resultState.RequirementsWellFormed ∧
      resultType.VariablesBelow resultState.inference.next ∧
      SafeTransport protectedVars state resultState ∧
      Safe protectedVars resultState resultType ∧
      LiveBindersSafe protectedVars resultState := by
  cases prefixFacts with
  | noExpectedPartsAnnotated parts annotation resolved =>
    exact ⟨.refl ready.solved, ready, wellFormed,
      resolveSourceType_success_variablesBelow resolved _, .refl _ _,
      safe_closed _ _ (resolveSourceType_success_variablesBelow resolved 0), live⟩
  | noExpectedPartsFresh parts annotation allocated =>
    have typeEq : resultType = state.fresh.1 := (congrArg Prod.fst allocated).symm
    have stateEq : resultState = state.fresh.2 := (congrArg Prod.snd allocated).symm
    subst resultType resultState
    exact ⟨.fresh _ ready.solved, ready.fresh,
      State.fresh_preserves_requirementsWellFormed _ wellFormed,
      (Ty.variablesBelow_variable_iff _ _).mpr (Nat.lt_succ_self _),
      fresh, fresh_type ready bound, live.transport rfl fresh⟩
  | expectedPartsAnnotated parts unified annotation resolved =>
    have expected := expected_parts_private ready expectedBelow expectedSafe parts
    have progress := unify_inferenceProgress ready.solved parameterBelow expected.1 unified
    have nextReady := unify_preserves_inferenceReady ready parameterBelow expected.1 unified
    exact ⟨progress, nextReady, unify_preserves_requirementsWellFormed unified wellFormed,
      resolveSourceType_success_variablesBelow resolved _, ProtectedVariables.unify parameterSafe expected.2.2.1 unified,
      safe_closed _ _ (resolveSourceType_success_variablesBelow resolved 0),
      live.unify parameterSafe expected.2.2.1 unified⟩
  | expectedPartsInferred parts unified annotation =>
    have expected := expected_parts_private ready expectedBelow expectedSafe parts
    have progress := unify_inferenceProgress ready.solved parameterBelow expected.1 unified
    have transport := ProtectedVariables.unify parameterSafe expected.2.2.1 unified
    exact ⟨progress, unify_preserves_inferenceReady ready parameterBelow expected.1 unified,
      unify_preserves_requirementsWellFormed unified wellFormed,
      expected.2.1.weaken progress.next_le, transport, transport _ expected.2.2.2,
      live.unify parameterSafe expected.2.2.1 unified⟩

private theorem prefix_fixed
    {protectedVars : List TypeVarId} {context : SourceInference.Context}
    {expected : Option Ty} {annotation : Option Syntax.TypeExpr}
    {parameters : List Ty} {state resultState : State} {resultType : Ty}
    (ready : state.InferenceReady)
    (parameterSafe : Safe protectedVars state (Ty.productMany parameters))
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow state.inference.next)
    (expectedSafe : ∀ type ∈ expected, Safe protectedVars state type)
    (fixed : FixesProtected protectedVars state)
    (prefixFacts : LambdaPrefixFacts context expected annotation parameters state resultType resultState) :
    FixesProtected protectedVars resultState := by
  cases prefixFacts with
  | noExpectedPartsAnnotated parts annotation resolved => exact fixed
  | noExpectedPartsFresh parts annotation allocated =>
    have stateEq : resultState = state.fresh.2 := (congrArg Prod.snd allocated).symm
    subst resultState
    exact fixed.of_substitution_eq rfl
  | expectedPartsAnnotated parts unified annotation resolved =>
    have expected := expected_parts_private ready expectedBelow expectedSafe parts
    exact unify_fixes_protected fixed parameterSafe expected.2.2.1 unified
  | expectedPartsInferred parts unified annotation =>
    have expected := expected_parts_private ready expectedBelow expectedSafe parts
    exact unify_fixes_protected fixed parameterSafe expected.2.2.1 unified

theorem inferExprFuel_lambda_fixes_protected
    {protectedVars : List TypeVarId} {fuel : Nat} {context : SourceInference.Context}
    {expression : Syntax.Expr} {expected : Option Ty} {initial : State}
    {keyword : Syntax.SourceSpan} {parameters : Syntax.DelimitedList Syntax.LambdaParameter}
    {returnType : Option Syntax.TypeExpr} {body : Syntax.Block}
    (form : expression.value = .lambda keyword parameters returnType body)
    (bodyIH : ∀ resultType state,
      InferStatementsFuelFixedness protectedVars fuel {context with loopDepth := 0}
        body.value resultType state) :
    InferExprFuelFixedness protectedVars (fuel + 1) context expression expected initial := by
  intro ready wellFormed bound live fixed catalog validated canonical expectedBelow expectedSafe result accepted
  obtain ⟨boundParameters, parameterTypes, parameterState, resultType, resultState,
    bodyResult, unifiedState, restoredState, parametersRun, prefixFacts, bodyRun,
    unified, restoredEq, recorded⟩ :=
    inferExprFuel_success_lambda_facts form (Prod.eta initial.allocateExpressionId).symm accepted
  let allocated := initial.allocateExpressionId.2
  have allocationProgress : initial.InferenceProgress allocated := .allocateExpressionId _ ready.solved
  have allocatedReady : allocated.InferenceReady := ready.allocateExpressionId
  have allocationPrivacy : SafeTransport protectedVars initial allocated := .of_substitution_eq rfl
  have allocatedLive : LiveBindersSafe protectedVars allocated := live.transport rfl allocationPrivacy
  have parameterFixed : FixesProtected protectedVars parameterState :=
    (fixed.of_substitution_eq (after := allocated) rfl).of_substitution_eq
      (bindLambdaParameters_substitution parametersRun)
  have parameterProperties := bindLambdaParameters_inferenceProperties allocatedReady parametersRun
  have parameterPrivacy := bindLambdaParameters_private allocatedReady bound allocatedLive parametersRun
  have parameterProgress := allocationProgress.trans parameterProperties.1
  have toParameters := allocationPrivacy.trans parameterPrivacy.1
  have parameterBelow := Ty.variablesBelow_productMany parameterProperties.2.2
  have parameterSafe := safe_productMany protectedVars parameterState parameterTypes parameterPrivacy.2.1
  have parameterWellFormed := (bindLambdaParameters_direct_progress parametersRun).wellFormed
    (State.allocateExpressionId_preserves_requirementsWellFormed initial wellFormed)
  have entered := prefix_private parameterProperties.2.1 parameterWellFormed
    (fun metavariable member => Nat.lt_of_lt_of_le (bound metavariable member) parameterProgress.next_le)
    parameterPrivacy.2.2.1 parameterBelow parameterSafe
    (fun type member => (expectedBelow type member).weaken parameterProgress.next_le)
    (fun type member => toParameters _ (expectedSafe type member)) prefixFacts
  rcases entered with ⟨prefixProgress, resultReady, resultWellFormed, resultBelow,
    prefixPrivacy, resultSafe, resultLive⟩
  have resultFixed := prefix_fixed parameterProperties.2.1 parameterSafe
    (fun type member => (expectedBelow type member).weaken parameterProgress.next_le)
    (fun type member => toParameters _ (expectedSafe type member)) parameterFixed prefixFacts
  have toResult := toParameters.trans prefixPrivacy
  have initialToResult := parameterProgress.trans prefixProgress
  have bodyProperties := inferStatementsFuel_inferenceProperties
    (context := {context with loopDepth := 0}) resultReady validated
    (fun signature member => canonical signature member) resultBelow bodyRun
  have bodyPrivacy := inferStatementsFuel_private protectedVars fuel {context with loopDepth := 0}
    body.value resultType resultState resultReady resultWellFormed
    (fun metavariable member => Nat.lt_of_lt_of_le (bound metavariable member) initialToResult.next_le)
    resultLive catalog validated canonical resultBelow resultSafe bodyResult bodyRun
  have bodyFixed := bodyIH resultType resultState resultReady resultWellFormed
    (fun metavariable member => Nat.lt_of_lt_of_le (bound metavariable member) initialToResult.next_le)
    resultLive resultFixed catalog validated canonical resultBelow resultSafe bodyResult bodyRun
  have unifiedFixed := unify_fixes_protected bodyFixed bodyPrivacy.2.1 (bodyPrivacy.1 _ resultSafe) unified
  have unifiedProgress := unify_inferenceProgress bodyProperties.2.1.solved bodyProperties.2.2
    (resultBelow.weaken bodyProperties.1.next_le) unified
  have unifiedReady := unify_preserves_inferenceReady bodyProperties.2.1 bodyProperties.2.2
    (resultBelow.weaken bodyProperties.1.next_le) unified
  have unifyPrivacy := ProtectedVariables.unify bodyPrivacy.2.1 (bodyPrivacy.1 _ resultSafe) unified
  have toUnified := toResult.trans (bodyPrivacy.1.trans unifyPrivacy)
  have parametersToUnified := prefixProgress.trans (bodyProperties.1.trans unifiedProgress)
  have allocatedToUnified := parameterProperties.1.trans parametersToUnified
  have restoredProperties := State.restoreLexicalScope_inferenceProperties allocatedReady allocatedToUnified
  subst restoredState
  let restored := unifiedState.restoreLexicalScope allocated.lexicalScope
  have restoreProgress : unifiedState.InferenceProgress restored :=
    .restoreLexicalScope _ _ unifiedReady.solved
  have restorePrivacy : SafeTransport protectedVars unifiedState restored := .of_substitution_eq rfl
  have restoredReady : restored.InferenceReady := restoredProperties.2
  have toRestored := toUnified.trans restorePrivacy
  have parameterAtRestored : Safe protectedVars restored (Ty.productMany parameterTypes) :=
    (prefixPrivacy.trans (bodyPrivacy.1.trans (unifyPrivacy.trans restorePrivacy))) _ parameterSafe
  have resultAtRestored : Safe protectedVars restored resultType :=
    (bodyPrivacy.1.trans (unifyPrivacy.trans restorePrivacy)) _ resultSafe
  exact recordExpressionWithExpected_fixes_protected (unifiedFixed.of_substitution_eq (after := restored) rfl)
    ((safe_function_iff _ _ _ _).mpr
      ⟨safe_resolved restoredReady parameterAtRestored, safe_resolved restoredReady resultAtRestored⟩)
    (fun type member => toRestored _ (expectedSafe type member)) recorded

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
