import Solcore.SourceSemantics.SourceInferenceNormalizedPatternPrefixes

/-! Normalized formation follows all actual nested pattern calls. The final
substitution is threaded backwards through their accepted continuations. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
open Frontend SourceInference TypeSystem Detail SourceInferenceSoundness

private def PatternCallFormation (semantic : SourceSemantics.Context) (outer : Substitution)
    (fuel : Nat) (context : SourceInference.Context) (pattern : Syntax.Pattern) (expected : Ty)
    (seen : List String) (state : State) : Prop :=
  ∀ result, state.InferenceReady → expected.VariablesBelow state.inference.next →
    InferenceFormationContext semantic context outer →
    NormalizedStateFormation semantic outer state →
    TypeAdmissible semantic (outer.apply expected) →
    inferMatchPatternFlatFuel fuel context pattern expected seen state = .ok result →
    outer.SemanticallyExtends result.state.inference.substitution →
    NormalizedStateFormation semantic outer result.state

private def PatternsCallFormation (semantic : SourceSemantics.Context) (outer : Substitution)
    (fuel : Nat) (context : SourceInference.Context) (patterns : List Syntax.Pattern) (expected : List Ty)
    (seen : List String) (state : State) : Prop :=
  ∀ result, state.InferenceReady →
    (∀ type ∈ expected, type.VariablesBelow state.inference.next) →
    InferenceFormationContext semantic context outer →
    NormalizedStateFormation semantic outer state →
    (∀ type ∈ expected, TypeAdmissible semantic (outer.apply type)) →
    inferMatchPatternsFlatFuel fuel context patterns expected seen state = .ok result →
    outer.SemanticallyExtends result.state.inference.substitution →
    NormalizedStateFormation semantic outer result.state

set_option maxHeartbeats 2000000 in
private theorem pattern_call_formation (semantic : SourceSemantics.Context) (outer : Substitution)
    (fuel : Nat) (context : SourceInference.Context) (pattern : Syntax.Pattern) (expected : Ty)
    (seen : List String) (state : State) :
    PatternCallFormation semantic outer fuel context pattern expected seen state := by
  apply inferMatchPatternFlatFuel.induct context
    (motive1 := fun fuel pattern expected seen state =>
      PatternCallFormation semantic outer fuel context pattern expected seen state)
    (motive2 := fun fuel patterns expected seen state =>
      PatternsCallFormation semantic outer fuel context patterns expected seen state)
  case case3 =>
    intros
    unfold PatternCallFormation at *
    intro result ready expectedBelow formation formed expectedFormed success continuation
    unfold inferMatchPatternFlatFuel at success
    simp_all [bind,Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals simp_all [pure,Pure.pure,Except.pure]
    all_goals
      rename_i unified
      exact integer_pattern_prefix_formation formation formed unified rfl rfl
  case case5 =>
    intros
    unfold PatternCallFormation at *
    intro result ready expectedBelow formation formed expectedFormed success continuation
    unfold inferMatchPatternFlatFuel at success
    simp_all [bind,Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals simp_all [pure,Pure.pure,Except.pure]
    all_goals
      rename_i unified
      exact integer_pattern_prefix_formation formation formed unified rfl rfl
  case case10 =>
    intros sourcePattern sourceExpected sourceSeen inputState sourceFuel
      leadingDot qualifiers constructorName sourceArguments patternEq branchEq
      flatArguments contextualBranch childrenIH
    unfold PatternCallFormation at *
    intro result ready expectedBelow formation formed expectedFormed success continuation
    unfold inferMatchPatternFlatFuel at success
    simp_all [bind,Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals simp_all [pure,Pure.pure,Except.pure]
    all_goals try subst_vars
    all_goals first
      | have beforeChildren := contextual_pattern_prefix_formation ready expectedBelow formation formed expectedFormed
          (by assumption) (by assumption)
        have childProperties := inferMatchPatternsFlatFuel_inferenceProperties beforeChildren.ready beforeChildren.below
          formation.validated (by assumption)
        have prefixFormed := beforeChildren.formed (continuation.trans childProperties.1.substitution_extends)
        exact childrenIH _ _ _ beforeChildren.ready beforeChildren.below formation prefixFormed.1 prefixFormed.2
          (by assumption) continuation
      | have beforeChildren := explicit_pattern_prefix_formation ready expectedBelow formation formed expectedFormed
          (by assumption) rfl (by assumption)
        have childProperties := inferMatchPatternsFlatFuel_inferenceProperties beforeChildren.ready beforeChildren.below
          formation.validated (by assumption)
        have prefixFormed := beforeChildren.formed (continuation.trans childProperties.1.substitution_extends)
        exact childrenIH _ _ _ beforeChildren.ready beforeChildren.below formation prefixFormed.1 prefixFormed.2
          (by assumption) continuation
  case case11 =>
    intros sourcePattern sourceExpected sourceSeen inputState sourceFuel
      leadingDot qualifiers constructorName sourceArguments patternEq branchEq
      flatArguments explicitBranch childrenIH
    unfold PatternCallFormation at *
    intro result ready expectedBelow formation formed expectedFormed success continuation
    unfold inferMatchPatternFlatFuel at success
    simp_all [bind,Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals simp_all [pure,Pure.pure,Except.pure]
    all_goals try subst_vars
    all_goals first
      | have beforeChildren := contextual_pattern_prefix_formation ready expectedBelow formation formed expectedFormed
          (by assumption) (by assumption)
        have childProperties := inferMatchPatternsFlatFuel_inferenceProperties beforeChildren.ready beforeChildren.below
          formation.validated (by assumption)
        have prefixFormed := beforeChildren.formed (continuation.trans childProperties.1.substitution_extends)
        exact childrenIH _ _ _ beforeChildren.ready beforeChildren.below formation prefixFormed.1 prefixFormed.2
          (by assumption) continuation
      | have beforeChildren := explicit_pattern_prefix_formation ready expectedBelow formation formed expectedFormed
          (by assumption) rfl (by assumption)
        have childProperties := inferMatchPatternsFlatFuel_inferenceProperties beforeChildren.ready beforeChildren.below
          formation.validated (by assumption)
        have prefixFormed := beforeChildren.formed (continuation.trans childProperties.1.substitution_extends)
        exact childrenIH _ _ _ beforeChildren.ready beforeChildren.below formation prefixFormed.1 prefixFormed.2
          (by assumption) continuation
  case case13 =>
    intros sourcePattern sourceExpected sourceSeen inputState sourceFuel
      elements patternEq sources argumentTypes allocatedState freshEq childrenIH
    unfold PatternCallFormation at *
    intro result ready expectedBelow formation formed expectedFormed success continuation
    unfold inferMatchPatternFlatFuel at success
    simp_all [bind,Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals simp_all
    have argumentTypesEq : (freshTypes sources.length inputState).1 = argumentTypes := congrArg Prod.fst freshEq
    have allocatedStateEq : (freshTypes sources.length inputState).2 = allocatedState := congrArg Prod.snd freshEq
    have beforeChildren := tuple_pattern_prefix_formation (count := sources.length) (types := argumentTypes)
      (allocated := allocatedState) ready expectedBelow formation formed freshEq (by
        rw [← allocatedStateEq,← argumentTypesEq]
        simpa only [sources] using (by assumption))
    rename_i rawChildren
    have childRun := rawChildren
    change inferMatchPatternsFlatFuel sourceFuel context sources
      (freshTypes sources.length inputState).1 sourceSeen _ = _ at childRun
    rw [argumentTypesEq] at childRun
    have childProperties := inferMatchPatternsFlatFuel_inferenceProperties beforeChildren.ready beforeChildren.below
      formation.validated childRun
    have prefixFormed := beforeChildren.formed (continuation.trans childProperties.1.substitution_extends)
    exact childrenIH _ _ beforeChildren.ready beforeChildren.below formation prefixFormed.1 prefixFormed.2
      childRun continuation
  case case17 =>
    intros fuel head rest expectedHead expectedTail seen state ihHead ihTail
    unfold PatternsCallFormation
    unfold PatternCallFormation at ihHead
    unfold PatternsCallFormation at ihTail
    intro result ready expectedBelow formation formed expectedFormed success continuation
    simp only [inferMatchPatternsFlatFuel] at success
    cases headRun : inferMatchPatternFlatFuel fuel context head expectedHead seen state with
    | error error => simp [headRun,bind,Except.bind] at success
    | ok inferredHead =>
      simp only [headRun,bind,Except.bind] at success
      cases tailRun : inferMatchPatternsFlatFuel fuel context rest expectedTail inferredHead.names inferredHead.state with
      | error error => simp [tailRun] at success
      | ok inferredTail =>
        simp only [tailRun] at success
        injection success with resultEq
        subst result
        have headProperties := inferMatchPatternFlatFuel_inferenceProperties ready
          (expectedBelow _ List.mem_cons_self) formation.validated headRun
        have tailBelow : ∀ type ∈ expectedTail, type.VariablesBelow inferredHead.state.inference.next :=
          fun type member => (expectedBelow type (List.mem_cons_of_mem _ member)).weaken headProperties.1.next_le
        have tailProperties := inferMatchPatternsFlatFuel_inferenceProperties headProperties.2 tailBelow formation.validated tailRun
        have headFormation := ihHead inferredHead ready (expectedBelow _ List.mem_cons_self) formation formed
          (expectedFormed _ List.mem_cons_self) headRun (continuation.trans tailProperties.1.substitution_extends)
        exact ihTail inferredHead inferredTail headProperties.2 tailBelow formation headFormation
          (fun type member => expectedFormed type (List.mem_cons_of_mem _ member)) tailRun continuation
  all_goals
    intros
    first | unfold PatternCallFormation at * | unfold PatternsCallFormation at *
    intro result ready expectedBelow formation formed expectedFormed success continuation
    first | unfold inferMatchPatternFlatFuel at success | unfold inferMatchPatternsFlatFuel at success
    simp_all [bind,Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals try simp_all
    all_goals try exact formed
    all_goals try exact (by simpa only using ih1 _ ready expectedBelow formation formed expectedFormed (by assumption) continuation)
    all_goals
      apply NormalizedStateFormation.allocate formed
      apply NormalizedBinderFormation.mono
      exact (continuation _).symm ▸ expectedFormed

/-- All actual nested pattern constructors preserve normalized formation. -/
theorem inferMatchPatternFlatFuel_normalized_formation
    {semantic : SourceSemantics.Context} {outer : Substitution} {fuel : Nat}
    {context : SourceInference.Context} {pattern : Syntax.Pattern} {expected : Ty}
    {seen : List String} {state : State} {result : InferredPattern}
    (ready : state.InferenceReady) (expectedBelow : expected.VariablesBelow state.inference.next)
    (formation : InferenceFormationContext semantic context outer)
    (formed : NormalizedStateFormation semantic outer state)
    (expectedFormed : TypeAdmissible semantic (outer.apply expected))
    (accepted : inferMatchPatternFlatFuel fuel context pattern expected seen state = .ok result)
    (continuation : outer.SemanticallyExtends result.state.inference.substitution) :
    NormalizedStateFormation semantic outer result.state :=
  pattern_call_formation semantic outer fuel context pattern expected seen state result ready expectedBelow formation
    formed expectedFormed accepted continuation

/-- The public pattern wrapper retains the actual recursive pattern state. -/
theorem inferMatchPatternFuel_normalized_formation
    {semantic : SourceSemantics.Context} {outer : Substitution} {fuel : Nat}
    {context : SourceInference.Context} {pattern : Syntax.Pattern} {expected : Ty}
    {state : State} {result : TypedMatchPattern × State}
    (ready : state.InferenceReady) (expectedBelow : expected.VariablesBelow state.inference.next)
    (formation : InferenceFormationContext semantic context outer)
    (formed : NormalizedStateFormation semantic outer state)
    (expectedFormed : TypeAdmissible semantic (outer.apply expected))
    (accepted : inferMatchPatternFuel fuel context pattern expected state = .ok result)
    (continuation : outer.SemanticallyExtends result.2.inference.substitution) :
    NormalizedStateFormation semantic outer result.2 := by
  unfold inferMatchPatternFuel at accepted
  cases actual : inferMatchPatternFlatFuel fuel context pattern expected [] state with
  | error error => simp [actual,bind,Except.bind] at accepted
  | ok inferred =>
    simp only [actual,bind,Except.bind,pure,Pure.pure,Except.pure,Except.ok.injEq] at accepted
    cases accepted
    exact inferMatchPatternFlatFuel_normalized_formation ready expectedBelow formation formed expectedFormed actual continuation

end Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
