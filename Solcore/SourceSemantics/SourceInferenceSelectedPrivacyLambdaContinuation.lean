import Solcore.SourceSemantics.SourceInferenceSelectedPrivacyContracts

/-! The actual lambda branch preserves older scheme quantifiers through its
parameter fit, body inference, return unification and lexical restoration.
The body hypothesis is the smaller-fuel branch of the mutual inference proof. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail

private theorem unify_requirements {state result : State} {left right : Ty}
    (accepted : Detail.unify state left right = .ok result) :
    result.requirements = state.requirements := by
  unfold Detail.unify at accepted
  cases unified : state.inference.unify left right with
  | error error => simp [unified, liftUnification, bind, Except.bind] at accepted
  | ok inference =>
    simp only [unified, liftUnification, bind, Except.bind, pure, Pure.pure, Except.pure] at accepted
    cases accepted
    rfl

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
      LiveBindersSafe protectedVars resultState ∧
      resultState.requirements = state.requirements := by
  cases prefixFacts with
  | noExpectedPartsAnnotated parts annotation resolved =>
    exact ⟨.refl ready.solved, ready, wellFormed,
      resolveSourceType_success_variablesBelow resolved _, .refl _ _,
      safe_closed _ _ (resolveSourceType_success_variablesBelow resolved 0), live, rfl⟩
  | noExpectedPartsFresh parts annotation allocated =>
    have typeEq : resultType = state.fresh.1 := (congrArg Prod.fst allocated).symm
    have stateEq : resultState = state.fresh.2 := (congrArg Prod.snd allocated).symm
    subst resultType resultState
    exact ⟨.fresh _ ready.solved, ready.fresh,
      State.fresh_preserves_requirementsWellFormed _ wellFormed,
      (Ty.variablesBelow_variable_iff _ _).mpr (Nat.lt_succ_self _),
      fresh, fresh_type ready bound, live.transport rfl fresh, rfl⟩
  | expectedPartsAnnotated parts unified annotation resolved =>
    have expected := expected_parts_private ready expectedBelow expectedSafe parts
    have progress := unify_inferenceProgress ready.solved parameterBelow expected.1 unified
    have nextReady := unify_preserves_inferenceReady ready parameterBelow expected.1 unified
    exact ⟨progress, nextReady, unify_preserves_requirementsWellFormed unified wellFormed,
      resolveSourceType_success_variablesBelow resolved _, ProtectedVariables.unify parameterSafe expected.2.2.1 unified,
      safe_closed _ _ (resolveSourceType_success_variablesBelow resolved 0),
      live.unify parameterSafe expected.2.2.1 unified, unify_requirements unified⟩
  | expectedPartsInferred parts unified annotation =>
    have expected := expected_parts_private ready expectedBelow expectedSafe parts
    have progress := unify_inferenceProgress ready.solved parameterBelow expected.1 unified
    have transport := ProtectedVariables.unify parameterSafe expected.2.2.1 unified
    exact ⟨progress, unify_preserves_inferenceReady ready parameterBelow expected.1 unified,
      unify_preserves_requirementsWellFormed unified wellFormed,
      expected.2.1.weaken progress.next_le, transport, transport _ expected.2.2.2,
      live.unify parameterSafe expected.2.2.1 unified, unify_requirements unified⟩

theorem inferExprFuel_lambda_private
    {protectedVars : List TypeVarId} {fuel : Nat} {context : SourceInference.Context}
    {expression : Syntax.Expr} {expected : Option Ty} {initial : State}
    {keyword : Syntax.SourceSpan} {parameters : Syntax.DelimitedList Syntax.LambdaParameter}
    {returnType : Option Syntax.TypeExpr} {body : Syntax.Block}
    (form : expression.value = .lambda keyword parameters returnType body)
    (bodyIH : ∀ resultType state,
      InferStatementsFuelPrivacy protectedVars fuel {context with loopDepth := 0}
        body.value resultType state) :
    InferExprFuelPrivacy protectedVars (fuel + 1) context expression expected initial := by
  intro ready wellFormed bound live catalog validated canonical expectedBelow expectedSafe result accepted
  obtain ⟨boundParameters, parameterTypes, parameterState, resultType, resultState,
    bodyResult, unifiedState, restoredState, parametersRun, prefixFacts, bodyRun,
    unified, restoredEq, recorded⟩ :=
    inferExprFuel_success_lambda_facts form (Prod.eta initial.allocateExpressionId).symm accepted
  let allocated := initial.allocateExpressionId.2
  have allocationProgress : initial.InferenceProgress allocated := .allocateExpressionId _ ready.solved
  have allocatedReady : allocated.InferenceReady := ready.allocateExpressionId
  have allocationPrivacy : SafeTransport protectedVars initial allocated := .of_substitution_eq rfl
  have allocatedLive : LiveBindersSafe protectedVars allocated := live.transport rfl allocationPrivacy
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
    prefixPrivacy, resultSafe, resultLive, prefixRequirements⟩
  have toResult := toParameters.trans prefixPrivacy
  have initialToResult := parameterProgress.trans prefixProgress
  have bodyProperties := inferStatementsFuel_inferenceProperties
    (context := {context with loopDepth := 0}) resultReady validated
    (fun signature member => canonical signature member) resultBelow bodyRun
  have bodyPrivacy := bodyIH resultType resultState resultReady resultWellFormed
    (fun metavariable member => Nat.lt_of_lt_of_le (bound metavariable member) initialToResult.next_le)
    resultLive catalog validated canonical resultBelow resultSafe bodyResult bodyRun
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
  have resultToRestored := bodyProperties.1.trans (unifiedProgress.trans restoreProgress)
  have parametersToRestored := parametersToUnified.trans restoreProgress
  have initialToRestored := allocationProgress.trans restoredProperties.1
  have restoredLive : LiveBindersSafe protectedVars restored :=
    allocatedLive.restore (parameterPrivacy.1.trans (prefixPrivacy.trans (bodyPrivacy.1.trans unifyPrivacy)))
  have parameterAtRestored : Safe protectedVars restored (Ty.productMany parameterTypes) :=
    (prefixPrivacy.trans (bodyPrivacy.1.trans (unifyPrivacy.trans restorePrivacy))) _ parameterSafe
  have resultAtRestored : Safe protectedVars restored resultType :=
    (bodyPrivacy.1.trans (unifyPrivacy.trans restorePrivacy)) _ resultSafe
  have recordPrivacy := recordExpressionWithExpected_private catalog restoredReady
    ((Ty.variablesBelow_function_iff _ _ _).mpr
      ⟨parametersToRestored.resolve_variablesBelow parameterBelow,
        resultToRestored.resolve_variablesBelow resultBelow⟩)
    (fun type member => (expectedBelow type member).weaken initialToRestored.next_le)
    ((safe_function_iff _ _ _ _).mpr
      ⟨safe_resolved restoredReady parameterAtRestored, safe_resolved restoredReady resultAtRestored⟩)
    (fun type member => toRestored _ (expectedSafe type member)) restoredLive recorded
  refine ⟨toRestored.trans recordPrivacy.1, recordPrivacy.2.1, recordPrivacy.2.2.1, ?_⟩
  have resultRequirements : resultState.requirements = initial.requirements :=
    prefixRequirements.trans parameterPrivacy.2.2.2
  have bodyRows : ∀ row ∈ restored.requirements, row ∉ initial.requirements →
      PredicateSafe protectedVars restored row.predicate := by
    intro row member freshRow type typeMember
    have atBody : row ∈ bodyResult.state.requirements := by
      change row ∈ unifiedState.requirements at member
      simpa only [unify_requirements unified] using member
    apply restorePrivacy
    apply unifyPrivacy
    exact bodyPrivacy.2.2.2 row atBody (by simpa only [resultRequirements] using freshRow) type typeMember
  exact new_requirements_trans bodyRows recordPrivacy.2.2.2 recordPrivacy.1

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
