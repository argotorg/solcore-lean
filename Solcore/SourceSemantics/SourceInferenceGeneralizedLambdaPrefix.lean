import Solcore.SourceSemantics.SourceInferenceGeneralizedLambdaParameters

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend SourceInference TypeSystem ProtectedVariables Detail

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

theorem lambdaPrefixFacts_preserves_generalizedScope
    {context : SourceInference.Context} {expected : Option Ty}
    {annotation : Option Syntax.TypeExpr} {types : List Ty}
    {initial final : State} {resultType : Ty} {source : TypedSource}
    (ready : initial.InferenceReady)
    (operational : GeneralizedActualStateInvariant initial source)
    (isolated : ActiveSchemeQuantifierIsolation initial)
    (parameterBelow : (Ty.productMany types).VariablesBelow initial.inference.next)
    (parameterSafe : ∀ binder ∈ initial.localBinders,
      Safe binder.scheme.quantified initial (Ty.productMany types))
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow initial.inference.next)
    (expectedSafe : ∀ binder ∈ initial.localBinders, ∀ type ∈ expected,
      Safe binder.scheme.quantified initial type)
    (facts : Detail.LambdaPrefixFacts context expected annotation types initial resultType final) :
    GeneralizedActualStateInvariant final source ∧ ActiveSchemeQuantifierIsolation final ∧
      (∀ binder ∈ final.localBinders, Safe binder.scheme.quantified final resultType) := by
  have properties := lambdaPrefixFacts_inferenceProperties facts ready parameterBelow expectedBelow
  have binders : final.localBinders = initial.localBinders := by
    cases facts with
    | noExpectedPartsAnnotated => rfl
    | noExpectedPartsFresh _ _ fresh =>
      rw [← show initial.fresh.2 = final from congrArg Prod.snd fresh]
      rfl
    | expectedPartsAnnotated _ unified | expectedPartsInferred _ unified =>
      exact congrArg LexicalScope.binders (Detail.unify_preserves_lexicalScope unified)
  have ledger : ∃ pending, RecursiveLedgerInvariant final pending := by
    obtain ⟨pending, ledger⟩ := operational.ledger
    cases facts with
    | noExpectedPartsAnnotated => exact ⟨pending, ledger⟩
    | noExpectedPartsFresh _ _ fresh =>
      rw [← show initial.fresh.2 = final from congrArg Prod.snd fresh]
      exact ⟨pending, ledger.fresh⟩
    | expectedPartsAnnotated _ unified | expectedPartsInferred _ unified =>
      exact ⟨pending, ledger.unify unified⟩
  have origins := operational.origins.congr_localBinders binders
  have privacy : ∀ binder ∈ final.localBinders,
      Safe binder.scheme.quantified final resultType ∧ LiveBindersSafe binder.scheme.quantified final ∧
      final.requirements = initial.requirements := by
    intro binder member
    have old := binders ▸ member
    obtain ⟨_, _, _, _, _, safe, live, rows⟩ := prefix_private ready operational.requirements
      (operational.quantifiersBelow binder old) (operational.privacy binder old) parameterBelow
      (parameterSafe binder old) expectedBelow (expectedSafe binder old) facts
    exact ⟨safe, live, rows⟩
  have backed : LiveTemplatesBacked final := by
    intro binder member requirement retained
    have old := binders ▸ member
    obtain ⟨raw, present, same⟩ := operational.backed binder old requirement retained
    have rows := (privacy binder member).2.2
    have extension := properties.1.substitution_extends
    refine ⟨raw, rows.symm ▸ present, ?_⟩
    have transported := congrArg (applyPredicate final) same
    simpa only [applyPredicate, TypedTraitResolution.applySubstitution_semanticallyExtends extension] using transported
  exact ⟨⟨ledger, origins,
    activeQuantifiersBelowNext_transport operational.quantifiersBelow binders properties.1.next_le,
    fun binder member => (privacy binder member).2.1, backed⟩,
    activeSchemeQuantifierIsolation_transport isolated binders,
    fun binder member => (privacy binder member).1⟩

end Solcore.SourceSemantics.SourceInferenceSoundness
