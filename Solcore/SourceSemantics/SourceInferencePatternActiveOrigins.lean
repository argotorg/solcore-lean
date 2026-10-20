import Solcore.SourceSemantics.SourceInferencePatternRawIsolation

/-! Pattern traversal retains old binders and introduces only monomorphic
binders with empty scheme requirements. This is an actual scope fact, without
an incoming monomorphism or raw-isolation assumption. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem

structure PatternScope (initial current : State) : Prop where
  quantified : activeSchemeQuantifiers current = activeSchemeQuantifiers initial
  retained : initial.localBinders ⊆ current.localBinders
  origin : ∀ binder ∈ current.localBinders, binder ∈ initial.localBinders ∨
    (binder.scheme.quantified = [] ∧ binder.schemeRequirements = [])

theorem PatternScope.refl (state : State) : PatternScope state state :=
  ⟨rfl,List.Subset.refl _,fun _ member => .inl member⟩

private theorem PatternScope.of_scope {start before after : State}
    (tracked : PatternScope start before) (scope : after.lexicalScope = before.lexicalScope) :
    PatternScope start after := by
  have same : after.localBinders = before.localBinders := congrArg LexicalScope.binders scope
  exact ⟨by simpa [activeSchemeQuantifiers,same] using tracked.quantified,
    same.symm ▸ tracked.retained,fun binder member => tracked.origin binder (same ▸ member)⟩

private theorem PatternScope.fresh {start state : State} (tracked : PatternScope start state) :
    PatternScope start state.fresh.2 := tracked.of_scope rfl

private theorem PatternScope.addRequirementWithId {start state : State}
    (tracked : PatternScope start state) (predicate : ProgramPredicate) :
    PatternScope start (state.addRequirementWithId predicate).2 := tracked.of_scope rfl

private theorem PatternScope.unify {start before after : State} {left right : Ty}
    (tracked : PatternScope start before) (accepted : Detail.unify before left right = .ok after) :
    PatternScope start after := tracked.of_scope (Detail.unify_preserves_lexicalScope accepted)

private theorem PatternScope.freshDataConstructorInstantiation {start state : State}
    (tracked : PatternScope start state) (dataType : ProgramDataSignature)
    (constructor : ProgramDataConstructorSignature) :
    PatternScope start (Detail.freshDataConstructorInstantiation dataType constructor state).2 :=
  tracked.of_scope (Detail.freshDataConstructorInstantiation_preserves_lexicalScope dataType constructor state)

private theorem PatternScope.allocateMonoBinder {start state : State}
    (tracked : PatternScope start state) (name : String) (type : Ty)
    (span : Option Syntax.SourceSpan) (comptime : Bool) :
    PatternScope start (state.allocateBinder name (.mono type) span comptime []).2 := by
  refine ⟨?_,tracked.retained.trans (List.subset_cons_self _ _),?_⟩
  · simpa only [activeSchemeQuantifiers,State.allocateBinder,List.flatMap_cons,Scheme.mono,List.nil_append]
      using tracked.quantified
  · intro binder member
    simp only [State.allocateBinder,List.mem_cons] at member
    rcases member with rfl | old
    · exact .inr ⟨rfl,rfl⟩
    · exact tracked.origin binder old

private theorem freshTypesTracking {start state : State}
    (tracked : PatternScope start state) (count : Nat) :
    PatternScope start (Detail.freshTypes count state).2 := by
  induction count generalizing state with
  | zero => exact tracked
  | succ count ih => exact ih tracked.fresh

private theorem integerPatternsTracking {start state : State}
    (tracked : PatternScope start state) (patterns : List IntegerPatternOrigin) :
    PatternScope start {state with integerPatterns := patterns} := tracked.of_scope rfl

private def PatternProperty {alpha : Type} (stateOf : alpha → State)
    (start state : State) (computation : Except Error alpha) : Prop :=
  ∀ result, computation = .ok result → PatternScope start state → PatternScope start (stateOf result)

private theorem flatPatternTracking (start : State) (fuel : Nat) (context : Frontend.SourceInference.Context)
    (pattern : Syntax.Pattern) (expected : Ty) (seen : List String) (state : State) :
    PatternProperty Detail.InferredPattern.state start state
      (Detail.inferMatchPatternFlatFuel fuel context pattern expected seen state) := by
  apply Detail.inferMatchPatternFlatFuel.induct context
    (motive1 := fun fuel pattern expected seen state =>
      PatternProperty Detail.InferredPattern.state start state
        (Detail.inferMatchPatternFlatFuel fuel context pattern expected seen state))
    (motive2 := fun fuel patterns expected seen state =>
      PatternProperty Detail.InferredPatterns.state start state
        (Detail.inferMatchPatternsFlatFuel fuel context patterns expected seen state))
  case case3 =>
    intros
    unfold PatternProperty at *
    intro result success tracked
    unfold Detail.inferMatchPatternFlatFuel at success
    simp_all [bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals simp_all [pure, Pure.pure, Except.pure]
    all_goals exact (integerPatternsTracking (tracked.fresh.addRequirementWithId _) _).unify (by assumption)
  case case5 =>
    intros
    unfold PatternProperty at *
    intro result success tracked
    unfold Detail.inferMatchPatternFlatFuel at success
    simp_all [bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals simp_all [pure, Pure.pure, Except.pure]
    all_goals exact (integerPatternsTracking (tracked.fresh.addRequirementWithId _) _).unify (by assumption)
  case case10 =>
    intros sourcePattern sourceExpected sourceSeen inputState sourceFuel leadingDot qualifiers constructorName sourceArguments
      patternEq branchEq flatArguments branch childrenIH
    unfold PatternProperty at *
    intro result success tracked
    unfold Detail.inferMatchPatternFlatFuel at success
    simp_all [bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals simp_all [pure, Pure.pure, Except.pure]
    all_goals try subst_vars
    all_goals first
      | exact childrenIH _ _ _ (by assumption) (tracked.unify (by assumption))
      | exact childrenIH _ _ _ (by assumption)
          ((tracked.freshDataConstructorInstantiation _ _).unify (by assumption))
  case case11 =>
    intros sourcePattern sourceExpected sourceSeen inputState sourceFuel leadingDot qualifiers constructorName sourceArguments
      patternEq branchEq flatArguments branch childrenIH
    unfold PatternProperty at *
    intro result success tracked
    unfold Detail.inferMatchPatternFlatFuel at success
    simp_all [bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals simp_all [pure, Pure.pure, Except.pure]
    all_goals try subst_vars
    all_goals first
      | exact childrenIH _ _ _ (by assumption) (tracked.unify (by assumption))
      | exact childrenIH _ _ _ (by assumption)
          ((tracked.freshDataConstructorInstantiation _ _).unify (by assumption))
  case case13 =>
    intros sourcePattern sourceExpected sourceSeen inputState sourceFuel elements patternEq sources argumentTypes allocatedState freshEq childrenIH
    unfold PatternProperty at *
    intro result success tracked
    unfold Detail.inferMatchPatternFlatFuel at success
    simp_all [bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals simp_all
    rename_i unifyAction next unifyAccepted childAction inferred childAccepted
    simp only [sources] at freshEq
    rw [freshEq] at unifyAccepted childAccepted
    have freshTracked := freshTypesTracking tracked sources.length
    rw [freshEq] at freshTracked
    exact childrenIH _ _ childAccepted (freshTracked.unify unifyAccepted)
  case case17 =>
    intros fuel head rest expectedHead expectedTail seen state headIH tailIH
    unfold PatternProperty at *
    intro result success tracked
    simp only [Detail.inferMatchPatternsFlatFuel] at success
    cases headResult : Detail.inferMatchPatternFlatFuel fuel context head expectedHead seen state with
    | error error => simp [headResult, bind, Except.bind] at success
    | ok inferredHead =>
      simp only [headResult, bind, Except.bind] at success
      cases tailResult : Detail.inferMatchPatternsFlatFuel fuel context rest expectedTail inferredHead.names inferredHead.state with
      | error error => simp [tailResult] at success
      | ok inferredTail =>
        simp only [tailResult, pure, Pure.pure, Except.pure] at success
        cases success
        exact tailIH inferredHead inferredTail tailResult (headIH inferredHead headResult tracked)
  all_goals
    intros
    unfold PatternProperty at *
    intro result success tracked
    first | unfold Detail.inferMatchPatternFlatFuel at success | unfold Detail.inferMatchPatternsFlatFuel at success
    simp_all [bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals try simp_all
    all_goals try exact tracked
    all_goals try exact tracked.allocateMonoBinder _ _ _ _
    all_goals try exact ih1 _ (by assumption) tracked


/-- The exact flat pattern computation retains the actual active scheme list
and identifies every added binder as monomorphic with no template rows. -/
theorem inferMatchPatternFlatFuel_scope
    {fuel : Nat} {context : SourceInference.Context} {pattern : Syntax.Pattern}
    {expected : Ty} {seen : List String} {initial : State} {result : Detail.InferredPattern}
    (accepted : Detail.inferMatchPatternFlatFuel fuel context pattern expected seen initial = .ok result) :
    PatternScope initial result.state :=
  flatPatternTracking initial fuel context pattern expected seen initial result accepted (.refl _)

/-- Public pattern inference returns the scope from the same flat computation. -/
theorem inferMatchPatternFuel_scope
    {fuel : Nat} {context : SourceInference.Context} {pattern : Syntax.Pattern}
    {expected : Ty} {initial : State} {result : TypedMatchPattern × State}
    (accepted : Detail.inferMatchPatternFuel fuel context pattern expected initial = .ok result) :
    PatternScope initial result.2 := by
  unfold Detail.inferMatchPatternFuel at accepted
  cases flatAccepted : Detail.inferMatchPatternFlatFuel fuel context pattern expected [] initial with
  | error error => simp [flatAccepted,bind,Except.bind] at accepted
  | ok inferred =>
    simp only [flatAccepted,bind,Except.bind,pure,Pure.pure,Except.pure,Except.ok.injEq] at accepted
    cases accepted
    exact inferMatchPatternFlatFuel_scope flatAccepted

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
