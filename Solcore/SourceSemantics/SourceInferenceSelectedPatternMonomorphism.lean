import Solcore.Frontend.SourceInference.ExpressionProperties

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

namespace PatternMonomorphism

def Monomorphic (state : State) : Prop :=
  ∀ binder ∈ state.localBinders, binder.scheme.quantified = []

theorem Monomorphic.of_scope {before after : State}
    (mono : Monomorphic before) (scope : after.lexicalScope = before.lexicalScope) :
    Monomorphic after := by
  intro binder member
  have same : after.localBinders = before.localBinders := congrArg LexicalScope.binders scope
  exact mono binder (same ▸ member)

theorem Monomorphic.fresh {state : State} (mono : Monomorphic state) :
    Monomorphic state.fresh.2 := mono

theorem Monomorphic.addRequirementWithId {state : State} (mono : Monomorphic state)
    (predicate : ProgramPredicate) : Monomorphic (state.addRequirementWithId predicate).2 := mono

theorem Monomorphic.unify {before after : State} {left right : Ty}
    (mono : Monomorphic before) (accepted : Detail.unify before left right = .ok after) :
    Monomorphic after := mono.of_scope (Detail.unify_preserves_lexicalScope accepted)

theorem Monomorphic.freshDataConstructorInstantiation {state : State}
    (mono : Monomorphic state) (dataType : ProgramDataSignature)
    (constructor : ProgramDataConstructorSignature) :
    Monomorphic (Detail.freshDataConstructorInstantiation dataType constructor state).2 :=
  mono.of_scope (Detail.freshDataConstructorInstantiation_preserves_lexicalScope dataType constructor state)

theorem Monomorphic.allocateMonoBinder {state : State} (mono : Monomorphic state)
    (name : String) (type : Ty) (span : Option Syntax.SourceSpan) (comptime : Bool) :
    Monomorphic (state.allocateBinder name (.mono type) span comptime []).2 := by
  intro binder member
  simp only [State.allocateBinder, List.mem_cons] at member
  rcases member with same | old
  · cases same
    rfl
  · exact mono binder old

private theorem freshTypesMonomorphic {state : State}
    (tracked : Monomorphic state) (count : Nat) :
    Monomorphic (Detail.freshTypes count state).2 := by
  induction count generalizing state with
  | zero => exact tracked
  | succ count ih => exact ih tracked.fresh

private theorem integerPatternsMonomorphic {state : State}
    (tracked : Monomorphic state) (patterns : List IntegerPatternOrigin) :
    Monomorphic {state with integerPatterns := patterns} := tracked

private def PatternProperty {alpha : Type} (stateOf : alpha → State)
    (state : State) (computation : Except Error alpha) : Prop :=
  ∀ result, computation = .ok result → Monomorphic state → Monomorphic (stateOf result)

private theorem flatPatternMonomorphic (fuel : Nat) (context : Frontend.SourceInference.Context)
    (pattern : Syntax.Pattern) (expected : Ty) (seen : List String) (state : State) :
    PatternProperty Detail.InferredPattern.state state
      (Detail.inferMatchPatternFlatFuel fuel context pattern expected seen state) := by
  apply Detail.inferMatchPatternFlatFuel.induct context
    (motive1 := fun fuel pattern expected seen state =>
      PatternProperty Detail.InferredPattern.state state
        (Detail.inferMatchPatternFlatFuel fuel context pattern expected seen state))
    (motive2 := fun fuel patterns expected seen state =>
      PatternProperty Detail.InferredPatterns.state state
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
    all_goals exact (integerPatternsMonomorphic (tracked.fresh.addRequirementWithId _) _).unify (by assumption)
  case case5 =>
    intros
    unfold PatternProperty at *
    intro result success tracked
    unfold Detail.inferMatchPatternFlatFuel at success
    simp_all [bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals simp_all [pure, Pure.pure, Except.pure]
    all_goals exact (integerPatternsMonomorphic (tracked.fresh.addRequirementWithId _) _).unify (by assumption)
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
    have freshTracked := freshTypesMonomorphic tracked sources.length
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


theorem inferMatchPatternFlatFuel_preserves_monomorphicBinders
    {fuel : Nat} {context : Frontend.SourceInference.Context} {pattern : Syntax.Pattern}
    {expected : Ty} {seen : List String} {initial : State} {result : Detail.InferredPattern}
    (accepted : Detail.inferMatchPatternFlatFuel fuel context pattern expected seen initial = .ok result)
    (monomorphic : Monomorphic initial) : Monomorphic result.state :=
  flatPatternMonomorphic fuel context pattern expected seen initial result accepted monomorphic

theorem inferMatchPatternFuel_preserves_monomorphicBinders
    {fuel : Nat} {context : Frontend.SourceInference.Context} {pattern : Syntax.Pattern}
    {expected : Ty} {initial final : State} {inferred : TypedMatchPattern}
    (accepted : Detail.inferMatchPatternFuel fuel context pattern expected initial = .ok (inferred, final))
    (monomorphic : Monomorphic initial) : Monomorphic final := by
  unfold Detail.inferMatchPatternFuel at accepted
  cases flatAccepted : Detail.inferMatchPatternFlatFuel fuel context pattern expected [] initial with
  | error error => simp [flatAccepted, bind, Except.bind] at accepted
  | ok result =>
    simp only [flatAccepted, bind, Except.bind, pure, Pure.pure, Except.pure] at accepted
    cases accepted
    exact inferMatchPatternFlatFuel_preserves_monomorphicBinders flatAccepted monomorphic

end PatternMonomorphism
end Solcore.SourceSemantics.SourceInferenceSoundness
