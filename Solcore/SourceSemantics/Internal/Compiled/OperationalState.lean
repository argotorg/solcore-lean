import Solcore.SourceSemantics.Internal.Compiled.Calls
import Solcore.SourceSemantics.Internal.Selected.State
import Solcore.SourceSemantics.Internal.Privacy.LifetimeContinuations
import Solcore.SourceSemantics.Internal.Compiled.Contracts
import Solcore.SourceSemantics.Internal.Selected.Children

/-!
# Operational state of generalized checking

State transitions through constructors, loops, lambdas, places and statements. Each keeps the
privacy of the active generalized binders, including through the lambda continuation of a lifetime.
-/

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceGeneralizedConstructorState
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend SourceInference TypeSystem ProtectedVariables

theorem GeneralizedActualStateInvariant.freshConstructor
    {state : State} {source : TypedSource}
    (invariant : GeneralizedActualStateInvariant state source)
    (dataType : ProgramDataSignature) (constructor : ProgramDataConstructorSignature) :
    GeneralizedActualStateInvariant
      (Detail.freshDataConstructorInstantiation dataType constructor state).2 source := by
  let step : List Ty × State → TypeParameterId → List Ty × State :=
    fun result _ => (result.1 ++ [result.2.fresh.1], result.2.fresh.2)
  have foldPreserves (parameters : List TypeParameterId) (accumulator : List Ty × State)
      (valid : GeneralizedActualStateInvariant accumulator.2 source) :
      GeneralizedActualStateInvariant (parameters.foldl step accumulator).2 source := by
    induction parameters generalizing accumulator with
    | nil => exact valid
    | cons parameter parameters induction =>
      exact induction (step accumulator parameter) valid.fresh
  exact foldPreserves dataType.parameters ([], state) invariant

private theorem unify_rows {state after : State} {left right : Ty}
    (accepted : Detail.unify state left right = .ok after) :
    after.requirements = state.requirements := by
  unfold Detail.unify at accepted
  cases unified : state.inference.unify left right with
  | error error => simp [unified, Detail.liftUnification, bind, Except.bind] at accepted
  | ok inference =>
    simp only [unified, Detail.liftUnification, bind, Except.bind, pure, Pure.pure, Except.pure] at accepted
    cases accepted
    rfl

theorem GeneralizedActualStateInvariant.unify
    {state after : State} {source : TypedSource} {left right : Ty}
    (invariant : GeneralizedActualStateInvariant state source)
    (ready : state.InferenceReady)
    (leftBelow : left.VariablesBelow state.inference.next)
    (rightBelow : right.VariablesBelow state.inference.next)
    (leftSafe : ∀ binder ∈ state.localBinders, Safe binder.scheme.quantified state left)
    (rightSafe : ∀ binder ∈ state.localBinders, Safe binder.scheme.quantified state right)
    (accepted : Detail.unify state left right = .ok after) :
    GeneralizedActualStateInvariant after source := by
  have progress := Detail.unify_inferenceProgress ready.solved leftBelow rightBelow accepted
  have binders : after.localBinders = state.localBinders :=
    congrArg LexicalScope.binders (Detail.unify_preserves_lexicalScope accepted)
  obtain ⟨pending, ledger⟩ := invariant.ledger
  refine ⟨⟨pending, ledger.unify accepted⟩, invariant.origins.unify accepted,
    activeQuantifiersBelowNext_transport invariant.quantifiersBelow binders progress.next_le,
    ?_, invariant.backed.transport (fun _ member => binders ▸ member)
      (fun _ member => (unify_rows accepted).symm ▸ member) progress.substitution_extends⟩
  intro binder member
  have old := binders ▸ member
  exact (invariant.privacy binder old).unify (leftSafe binder old) (rightSafe binder old) accepted

end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceGeneralizedLambdaParameters
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
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceGeneralizedLambdaPrefix
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
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceLambdaOperationalPrefix
/-! Lambda entry uses the real parameter and prefix calls. Its operational
privacy proof does not require a declarative body or raw scheme isolation. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend SourceInference TypeSystem ProtectedVariables Detail

theorem bindLambdaParameters_operational
    {context : Frontend.SourceInference.Context}
    {parameters : List Syntax.LambdaParameter} {index : Nat}
    {seen : List String} {state : State}
    {result : List TypedBinder × List Ty × State} {source : TypedSource}
    (ready : state.InferenceReady)
    (operational : GeneralizedActualStateInvariant state source)
    (success : Detail.bindLambdaParameters context parameters index seen state = .ok result) :
    GeneralizedActualStateInvariant result.2.2 source := by
  induction parameters generalizing index seen state result with
  | nil =>
    simp only [Detail.bindLambdaParameters] at success
    injection success with resultEq
    subst result
    exact operational
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
            (by assumption)

theorem lambdaPrefixFacts_operational
    {context : SourceInference.Context} {expected : Option Ty}
    {annotation : Option Syntax.TypeExpr} {types : List Ty}
    {initial final : State} {resultType : Ty} {source : TypedSource}
    (ready : initial.InferenceReady)
    (operational : GeneralizedActualStateInvariant initial source)
    (parameterBelow : (Ty.productMany types).VariablesBelow initial.inference.next)
    (parameterSafe : ∀ binder ∈ initial.localBinders,
      Safe binder.scheme.quantified initial (Ty.productMany types))
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow initial.inference.next)
    (expectedSafe : ∀ binder ∈ initial.localBinders, ∀ type ∈ expected,
      Safe binder.scheme.quantified initial type)
    (facts : Detail.LambdaPrefixFacts context expected annotation types initial resultType final) :
    GeneralizedActualStateInvariant final source ∧
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
    fun binder member => (privacy binder member).1⟩


end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceGeneralizationLifetimeLambda
/-! A lambda continuation transports any actual inner generalization, including
header declarations, through its real return unification and scope restore. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail

private theorem parameter_binders_subset
    {context : SourceInference.Context} {parameters : List Syntax.LambdaParameter}
    {index : Nat} {seen : List String} {initial : State}
    {result : List TypedBinder × List Ty × State}
    (accepted : bindLambdaParameters context parameters index seen initial = .ok result) :
    initial.localBinders ⊆ result.2.2.localBinders := by
  induction parameters generalizing index seen initial result with
  | nil =>
    simp only [bindLambdaParameters, Except.ok.injEq] at accepted
    cases accepted
    exact List.Subset.refl _
  | cons parameter rest ih =>
    cases form : parameter.value with
    | error => simp [bindLambdaParameters, form, bind, Except.bind] at accepted
    | inferred name =>
      simp only [bindLambdaParameters, form, bind, Except.bind] at accepted
      repeat' first | split at accepted
      all_goals try simp_all
      all_goals
        subst result
        subst_vars
        exact (List.subset_cons_self _ _).trans (ih _ _ _ (by assumption))
    | typed marker name sourceType =>
      simp only [bindLambdaParameters, form] at accepted
      cases resolved : resolveSourceType context sourceType with
      | error error => simp [resolved, bind, Except.bind] at accepted
      | ok type =>
        simp only [resolved, bind, Except.bind] at accepted
        repeat' first | split at accepted
        all_goals try simp_all
        all_goals
          subst result
          subst_vars
          exact (List.subset_cons_self _ _).trans (ih _ _ _ (by assumption))

private theorem prefix_binders
    {context : SourceInference.Context} {expected : Option Ty}
    {annotation : Option Syntax.TypeExpr} {types : List Ty}
    {initial final : State} {resultType : Ty}
    (facts : LambdaPrefixFacts context expected annotation types initial resultType final) :
    final.localBinders = initial.localBinders := by
  cases facts with
  | noExpectedPartsAnnotated => rfl
  | noExpectedPartsFresh _ _ fresh =>
    rw [← show initial.fresh.2 = final from congrArg Prod.snd fresh]
    rfl
  | expectedPartsAnnotated _ unified | expectedPartsInferred _ unified =>
    exact congrArg LexicalScope.binders (unify_preserves_lexicalScope unified)

theorem GeneralizationLifetime.finishLambda
    {whole : TypedSource} {finalSubstitution : Substitution}
    {binder : TypedBinder} {initializer : ExpressionId}
    {event : RetainedGeneralization whole finalSubstitution binder initializer}
    {childFuel : Nat}
    {context : SourceInference.Context} {expression : Syntax.Expr}
    {parameters : Syntax.DelimitedList Syntax.LambdaParameter} {annotation : Option Syntax.TypeExpr}
    {body : Syntax.Block} {expected : Option Ty} {initial : State}
    {boundParameters : List TypedBinder} {parameterTypes : List Ty} {parameterState : State}
    {resultType : Ty} {prefixState : State} {bodyResult : BlockResult}
    {unifiedState restoredState : State} {final : InferredExpression × State}
    (lifetime : GeneralizationLifetime event prefixState.inference.next bodyResult.state [bodyResult.type])
    (ready : initial.InferenceReady)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes))
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow initial.inference.next)
    (parametersRun : bindLambdaParameters context parameters.elements 0 []
      initial.allocateExpressionId.2 = .ok (boundParameters, parameterTypes, parameterState))
    (prefixFacts : LambdaPrefixFacts context expected annotation parameterTypes parameterState resultType prefixState)
    (bodyRun : inferStatementsFuel childFuel {context with loopDepth := 0}
      body.value resultType prefixState = .ok bodyResult)
    (unified : Detail.unify bodyResult.state bodyResult.type resultType = .ok unifiedState)
    (restoredEq : restoredState = unifiedState.restoreLexicalScope initial.allocateExpressionId.2.lexicalScope)
    (recorded : recordExpressionWithExpected context expression initial.allocateExpressionId.1
      (.function (restoredState.resolve (Ty.productMany parameterTypes)) (restoredState.resolve resultType))
      (.lambda boundParameters (restoredState.resolve resultType) bodyResult.statements)
      [] expected restoredState = .ok final) :
    GeneralizationLifetime event initial.inference.next final.2 [final.1.type] := by
  let protectedVars := binder.scheme.quantified
  let allocated := initial.allocateExpressionId.2
  have allocation : initial.InferenceProgress allocated := .allocateExpressionId _ ready.solved
  have parametersProperties := bindLambdaParameters_inferenceProperties ready.allocateExpressionId parametersRun
  have parameterBelow := Ty.variablesBelow_productMany parametersProperties.2.2
  have initialToParameter := allocation.trans parametersProperties.1
  have prefixProperties := lambdaPrefixFacts_inferenceProperties prefixFacts parametersProperties.2.1
    parameterBelow (fun type member => (expectedBelow type member).weaken initialToParameter.next_le)
  have bodyProperties := inferStatementsFuel_inferenceProperties
    (context := {context with loopDepth := 0}) prefixProperties.2.1 formation canonical
    prefixProperties.2.2 bodyRun
  have unifiedProgress := unify_inferenceProgress bodyProperties.2.1.solved bodyProperties.2.2
    (prefixProperties.2.2.weaken bodyProperties.1.next_le) unified
  have unifiedReady := unify_preserves_inferenceReady bodyProperties.2.1 bodyProperties.2.2
    (prefixProperties.2.2.weaken bodyProperties.1.next_le) unified
  have unifiedPrivacy : SafeTransport protectedVars bodyResult.state unifiedState :=
    ProtectedVariables.unify (lifetime.values _ (List.mem_singleton_self _)) (lifetime.older resultType prefixProperties.2.2) unified
  have parametersToUnified := prefixProperties.1.trans (bodyProperties.1.trans unifiedProgress)
  have allocatedToUnified := parametersProperties.1.trans parametersToUnified
  have restoredProperties := State.restoreLexicalScope_inferenceProperties ready.allocateExpressionId allocatedToUnified
  subst restoredState
  let restored := unifiedState.restoreLexicalScope allocated.lexicalScope
  have restoredReady : restored.InferenceReady := restoredProperties.2
  have restorePrivacy : SafeTransport protectedVars unifiedState restored := .of_substitution_eq rfl
  have restoreProgress : unifiedState.InferenceProgress restored := .restoreLexicalScope _ _ unifiedReady.solved
  have bodyToRestored := unifiedPrivacy.trans restorePrivacy
  have parametersAtBody := lifetime.older (Ty.productMany parameterTypes)
    (parameterBelow.weaken prefixProperties.1.next_le)
  have initialToPrefix := initialToParameter.trans prefixProperties.1
  have expectedAtBody : ∀ type ∈ expected, Safe protectedVars bodyResult.state type := by
    intro type member
    exact lifetime.older type ((expectedBelow type member).weaken initialToPrefix.next_le)
  have savedSubset : allocated.localBinders ⊆ bodyResult.state.localBinders := by
    apply (parameter_binders_subset parametersRun).trans
    apply List.Subset.trans (l₂ := prefixState.localBinders)
    · rw [prefix_binders prefixFacts]
      exact List.Subset.refl _
    · exact inferStatementsFuel_binders_subset bodyRun
  have restoredLive : LiveBindersSafe protectedVars restored := by
    intro binder member
    have before := lifetime.live binder (savedSubset member)
    exact before.transport bodyToRestored
  have resultToRestored := bodyProperties.1.trans (unifiedProgress.trans restoreProgress)
  have parametersToRestored := parametersToUnified.trans restoreProgress
  have initialToRestored := allocation.trans restoredProperties.1
  have recordPrivacy := recordExpressionWithExpected_private catalog restoredReady
    ((Ty.variablesBelow_function_iff _ _ _).mpr
      ⟨parametersToRestored.resolve_variablesBelow parameterBelow,
        resultToRestored.resolve_variablesBelow prefixProperties.2.2⟩)
    (fun type member => (expectedBelow type member).weaken initialToRestored.next_le)
    ((safe_function_iff _ _ _ _).mpr
      ⟨safe_resolved restoredReady (bodyToRestored _ parametersAtBody),
        safe_resolved restoredReady (bodyToRestored _ (lifetime.older resultType prefixProperties.2.2))⟩)
    (fun type member => bodyToRestored type (expectedAtBody type member)) restoredLive recorded
  have recordProperties := recordExpressionWithExpected_inferenceProperties restoredReady
    ((Ty.variablesBelow_function_iff _ _ _).mpr
      ⟨parametersToRestored.resolve_variablesBelow parameterBelow,
        resultToRestored.resolve_variablesBelow prefixProperties.2.2⟩)
    (fun type member => (expectedBelow type member).weaken initialToRestored.next_le) recorded
  have bodyToFinal := bodyToRestored.trans recordPrivacy.1
  have bodyRows : ∀ requirement ∈ restored.requirements,
      requirement ∉ event.readyState.requirements →
        PredicateSafe protectedVars restored requirement.predicate := by
    intro requirement member fresh type typeMember
    apply bodyToRestored
    apply lifetime.newRows requirement _ fresh type typeMember
    change requirement ∈ unifiedState.requirements at member
    simpa only [unify_requirements_eq unified] using member
  exact {
    createdAfter := Nat.le_trans initialToPrefix.next_le lifetime.createdAfter
    allocated := lifetime.allocated
    bound := fun q member => Nat.lt_of_lt_of_le (lifetime.bound q member)
      (Nat.le_trans unifiedProgress.next_le (Nat.le_trans restoreProgress.next_le recordProperties.1.next_le))
    transport := lifetime.transport.trans bodyToFinal
    live := recordPrivacy.2.2.1
    values := fun type member => (List.mem_singleton.mp member) ▸ recordPrivacy.2.1
    older := fun type below => bodyToFinal type (lifetime.older type (below.weaken initialToPrefix.next_le))
    newRows := new_requirements_trans bodyRows recordPrivacy.2.2.2 recordPrivacy.1 }

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceGeneralizedForState
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend SourceInference TypeSystem ProtectedVariables

theorem GeneralizedActualStateInvariant.ofForItemPreservingBinders
    {fuel : Nat} {context : SourceInference.Context} {item : Syntax.ForItem}
    {initial final : State} {inferred : ForItemForm} {source : TypedSource}
    (invariant : GeneralizedActualStateInvariant initial source)
    (ready : initial.InferenceReady)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (accepted : Detail.inferForItemFuel fuel context item initial = .ok (inferred, final))
    (binders : final.localBinders = initial.localBinders) :
    GeneralizedActualStateInvariant final source := by
  obtain ⟨pending, ledger⟩ := invariant.ledger
  have properties := Detail.inferForItemFuel_inferenceProperties ready formation canonical accepted
  refine ⟨⟨pending ++ inferred.localSchemeTemplateIds, (actualLedgerFamily fuel).statements.forItem accepted ledger⟩,
    invariant.origins.congr_localBinders binders,
    activeQuantifiersBelowNext_transport invariant.quantifiersBelow binders properties.1.next_le,
    ?_, invariant.backed.transport (fun _ member => binders ▸ member)
      (Detail.inferForItemFuel_requirements_subset accepted) properties.1.substitution_extends⟩
  intro binder member
  have old := binders ▸ member
  exact (inferForItemFuel_private binder.scheme.quantified fuel context item initial
    ready ledger.requirements (invariant.quantifiersBelow binder old) (invariant.privacy binder old)
    catalog formation canonical _ accepted).2.1

end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceGeneralizedPlaceState
/-! Actual place inference preserves the generalized operational state and
keeps the resulting writable type private from active scheme quantifiers. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend SourceInference TypeSystem ProtectedVariables

theorem GeneralizedActualStateInvariant.ofPlace
    {fuel : Nat} {context : SourceInference.Context} {expression : Syntax.Expr}
    {initial final : State} {place : PlaceResolution} {source : TypedSource}
    (invariant : GeneralizedActualStateInvariant initial source)
    (ready : initial.InferenceReady)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (accepted : Detail.inferPlaceFuel fuel context expression initial = .ok (place, final)) :
    GeneralizedActualStateInvariant final source := by
  obtain ⟨pending, ledger⟩ := invariant.ledger
  have properties := Detail.inferPlaceFuel_inferenceProperties ready formation canonical accepted
  have binders : final.localBinders = initial.localBinders :=
    congrArg LexicalScope.binders (Detail.inferPlaceFuel_success_lexicalScope_eq accepted)
  refine ⟨⟨pending, (actualLedgerFamily fuel).place accepted ledger⟩,
    invariant.origins.congr_localBinders binders,
    activeQuantifiersBelowNext_transport invariant.quantifiersBelow binders properties.1.next_le,
    ?_, invariant.backed.transport (fun _ member => binders ▸ member)
      (Detail.inferPlaceFuel_requirements_subset accepted) properties.1.substitution_extends⟩
  intro binder member
  have old := binders ▸ member
  exact (inferPlaceFuel_private binder.scheme.quantified fuel context expression initial
    ready ledger.requirements (invariant.quantifiersBelow binder old) (invariant.privacy binder old)
    catalog formation canonical _ accepted).2.2.1

theorem GeneralizedActualStateInvariant.place_type_private
    {fuel : Nat} {context : SourceInference.Context} {expression : Syntax.Expr}
    {initial final : State} {place : PlaceResolution} {source : TypedSource}
    (invariant : GeneralizedActualStateInvariant initial source)
    (ready : initial.InferenceReady)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (accepted : Detail.inferPlaceFuel fuel context expression initial = .ok (place, final)) :
    ∀ binder ∈ final.localBinders, Safe binder.scheme.quantified final place.type := by
  intro binder member
  have binders : final.localBinders = initial.localBinders :=
    congrArg LexicalScope.binders (Detail.inferPlaceFuel_success_lexicalScope_eq accepted)
  have old := binders ▸ member
  exact (inferPlaceFuel_private binder.scheme.quantified fuel context expression initial
    ready invariant.requirements (invariant.quantifiersBelow binder old) (invariant.privacy binder old)
    catalog formation canonical _ accepted).2.1

theorem GeneralizedActualStateInvariant.placeIndexPrefix
    {fuel : Nat} {context : SourceInference.Context} {expression : Syntax.Expr}
    {initial baseState keyInitial : State} {place : PlaceResolution} {source : TypedSource}
    (invariant : GeneralizedActualStateInvariant initial source)
    (ready : initial.InferenceReady)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (accepted : Detail.inferPlaceFuel fuel context expression initial = .ok (place, baseState))
    (unified : Detail.unify baseState.fresh.2.fresh.2 place.type
      (.mapping baseState.fresh.1 baseState.fresh.2.fresh.1) = .ok keyInitial) :
    GeneralizedActualStateInvariant keyInitial source ∧
    ∀ binder ∈ keyInitial.localBinders,
      Safe binder.scheme.quantified keyInitial (keyInitial.resolve baseState.fresh.1) := by
  have properties := Detail.inferPlaceFuel_inferenceProperties ready formation canonical accepted
  have baseOperational := invariant.ofPlace ready catalog formation canonical accepted
  have keyProperties := Detail.fresh_eq_inferenceProperties properties.2.1
    (initial := baseState) (type := baseState.fresh.1) (next := baseState.fresh.2) rfl
  have valueProperties := Detail.fresh_eq_inferenceProperties keyProperties.2.1
    (initial := baseState.fresh.2) (type := baseState.fresh.2.fresh.1)
    (next := baseState.fresh.2.fresh.2) rfl
  have baseBelow := properties.2.2.weaken (keyProperties.1.trans valueProperties.1).next_le
  have mappingBelow : (Ty.mapping baseState.fresh.1 baseState.fresh.2.fresh.1).VariablesBelow
      baseState.fresh.2.fresh.2.inference.next :=
    (Ty.variablesBelow_mapping_iff _ _ _).2
      ⟨keyProperties.2.2.weaken valueProperties.1.next_le, valueProperties.2.2⟩
  have baseSafe : ∀ binder ∈ baseState.localBinders, Safe binder.scheme.quantified baseState place.type :=
    invariant.place_type_private ready catalog formation canonical accepted
  have freshSafety : ∀ binder ∈ baseState.fresh.2.fresh.2.localBinders,
      Safe binder.scheme.quantified baseState.fresh.2.fresh.2 place.type ∧
      Safe binder.scheme.quantified baseState.fresh.2.fresh.2
        (.mapping baseState.fresh.1 baseState.fresh.2.fresh.1) ∧
      Safe binder.scheme.quantified baseState.fresh.2.fresh.2 baseState.fresh.1 := by
    intro binder member
    have baseMember : binder ∈ baseState.localBinders := member
    have keySafe := ProtectedVariables.fresh_type properties.2.1
      (baseOperational.quantifiersBelow binder baseMember)
    have valueSafe := ProtectedVariables.fresh_type keyProperties.2.1
      (baseOperational.fresh.quantifiersBelow binder member)
    have keyAtValue := ProtectedVariables.fresh _ keySafe
    exact ⟨ProtectedVariables.fresh _ (ProtectedVariables.fresh _ (baseSafe binder baseMember)),
      (safe_mapping_iff _ _ _ _).mpr ⟨keyAtValue, valueSafe⟩, keyAtValue⟩
  have operational := baseOperational.fresh.fresh.unify valueProperties.2.1 baseBelow mappingBelow
    (fun binder member => (freshSafety binder member).1)
    (fun binder member => (freshSafety binder member).2.1) unified
  refine ⟨operational, ?_⟩
  intro binder member
  have binders : keyInitial.localBinders = baseState.fresh.2.fresh.2.localBinders :=
    congrArg LexicalScope.binders (Detail.unify_preserves_lexicalScope unified)
  have safety := freshSafety binder (binders ▸ member)
  exact safe_resolved
    (Detail.unify_preserves_inferenceReady valueProperties.2.1 baseBelow mappingBelow unified)
    (ProtectedVariables.unify safety.1 safety.2.1 unified _ safety.2.2)

end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceGeneralizedStatementState
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend SourceInference TypeSystem ProtectedVariables

theorem GeneralizedActualStateInvariant.ofStatementPreservingBinders
    {fuel : Nat} {context : SourceInference.Context} {statement : Syntax.Statement}
    {expectedReturn : Ty} {initial : State} {result : Detail.StatementResult}
    {source : TypedSource}
    (invariant : GeneralizedActualStateInvariant initial source)
    (ready : initial.InferenceReady)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (returnBelow : expectedReturn.VariablesBelow initial.inference.next)
    (returnSafe : ∀ binder ∈ initial.localBinders,
      Safe binder.scheme.quantified initial expectedReturn)
    (accepted : Detail.inferStatementFuel fuel context statement expectedReturn initial = .ok result)
    (binders : result.state.localBinders = initial.localBinders) :
    GeneralizedActualStateInvariant result.state source := by
  obtain ⟨pending, ledger⟩ := invariant.ledger
  have properties := Detail.inferStatementFuel_inferenceProperties ready formation canonical returnBelow accepted
  refine ⟨⟨pending, (actualLedgerFamily fuel).statements.statement accepted ledger⟩,
    invariant.origins.congr_localBinders binders,
    activeQuantifiersBelowNext_transport invariant.quantifiersBelow binders properties.1.next_le,
    ?_, invariant.backed.transport (fun _ member => binders ▸ member)
      (Detail.inferStatementFuel_requirements_subset accepted) properties.1.substitution_extends⟩
  intro binder member
  have old := binders ▸ member
  exact (inferStatementFuel_private binder.scheme.quantified fuel context statement expectedReturn initial
    ready ledger.requirements (invariant.quantifiersBelow binder old) (invariant.privacy binder old)
    catalog formation canonical returnBelow (returnSafe binder old) _ accepted).2.2.1

end Solcore.SourceSemantics.SourceInferenceSoundness
end
