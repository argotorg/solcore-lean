import Solcore.SourceSemantics.SourceInferenceExpressionLedgerInvariant

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

private theorem freshTypesLedger {state : State} {pending : List RequirementId}
    (tracked : RecursiveLedgerInvariant state pending) (count : Nat) :
    RecursiveLedgerInvariant (Detail.freshTypes count state).2 pending := by
  induction count generalizing state with
  | zero => exact tracked
  | succ count ih => exact ih tracked.fresh

private theorem integerPatternsLedger {state : State} {pending : List RequirementId}
    (tracked : RecursiveLedgerInvariant state pending)
    (patterns : List IntegerPatternOrigin) :
    RecursiveLedgerInvariant {state with integerPatterns := patterns} pending := by
  exact ⟨tracked.requirements, tracked.templates.classified, tracked.templates.unique, tracked.templates.covered⟩

private def PatternLedger {alpha : Type} (stateOf : alpha → State)
    (state : State) (computation : Except Error alpha) : Prop :=
  ∀ pending result, computation = .ok result →
    RecursiveLedgerInvariant state pending → RecursiveLedgerInvariant (stateOf result) pending

private theorem flatPatternLedger (fuel : Nat) (context : Frontend.SourceInference.Context)
    (pattern : Syntax.Pattern) (expected : Ty) (seen : List String) (state : State) :
    PatternLedger Detail.InferredPattern.state state
      (Detail.inferMatchPatternFlatFuel fuel context pattern expected seen state) := by
  apply Detail.inferMatchPatternFlatFuel.induct context
    (motive1 := fun fuel pattern expected seen state =>
      PatternLedger Detail.InferredPattern.state state
        (Detail.inferMatchPatternFlatFuel fuel context pattern expected seen state))
    (motive2 := fun fuel patterns expected seen state =>
      PatternLedger Detail.InferredPatterns.state state
        (Detail.inferMatchPatternsFlatFuel fuel context patterns expected seen state))
  case case3 =>
    intros
    unfold PatternLedger at *
    intro pending result success tracked
    unfold Detail.inferMatchPatternFlatFuel at success
    simp_all [bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals simp_all [pure, Pure.pure, Except.pure]
    all_goals exact (integerPatternsLedger (tracked.fresh.addRequirementWithId _) _).unify (by assumption)
  case case5 =>
    intros
    unfold PatternLedger at *
    intro pending result success tracked
    unfold Detail.inferMatchPatternFlatFuel at success
    simp_all [bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals simp_all [pure, Pure.pure, Except.pure]
    all_goals exact (integerPatternsLedger (tracked.fresh.addRequirementWithId _) _).unify (by assumption)
  case case10 =>
    intros sourcePattern sourceExpected sourceSeen inputState sourceFuel leadingDot qualifiers constructorName sourceArguments
      patternEq branchEq flatArguments branch childrenIH
    unfold PatternLedger at *
    intro pending result success tracked
    unfold Detail.inferMatchPatternFlatFuel at success
    simp_all [bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals simp_all [pure, Pure.pure, Except.pure]
    all_goals try subst_vars
    all_goals first
      | exact childrenIH _ _ pending _ (by assumption) (tracked.unify (by assumption))
      | exact childrenIH _ _ pending _ (by assumption)
          ((tracked.freshDataConstructorInstantiation _ _).unify (by assumption))
  case case11 =>
    intros sourcePattern sourceExpected sourceSeen inputState sourceFuel leadingDot qualifiers constructorName sourceArguments
      patternEq branchEq flatArguments branch childrenIH
    unfold PatternLedger at *
    intro pending result success tracked
    unfold Detail.inferMatchPatternFlatFuel at success
    simp_all [bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals simp_all [pure, Pure.pure, Except.pure]
    all_goals try subst_vars
    all_goals first
      | exact childrenIH _ _ pending _ (by assumption) (tracked.unify (by assumption))
      | exact childrenIH _ _ pending _ (by assumption)
          ((tracked.freshDataConstructorInstantiation _ _).unify (by assumption))
  case case13 =>
    intros sourcePattern sourceExpected sourceSeen inputState sourceFuel elements patternEq sources argumentTypes allocatedState freshEq childrenIH
    unfold PatternLedger at *
    intro pending result success tracked
    unfold Detail.inferMatchPatternFlatFuel at success
    simp_all [bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals simp_all
    rename_i unifyAction next unifyAccepted childAction inferred childAccepted
    simp only [sources] at freshEq
    rw [freshEq] at unifyAccepted childAccepted
    have freshTracked := freshTypesLedger tracked sources.length
    rw [freshEq] at freshTracked
    exact childrenIH _ pending _ childAccepted (freshTracked.unify unifyAccepted)
  case case17 =>
    intros fuel head rest expectedHead expectedTail seen state headIH tailIH
    unfold PatternLedger at *
    intro pending result success tracked
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
        exact tailIH inferredHead pending inferredTail tailResult (headIH pending inferredHead headResult tracked)
  all_goals
    intros
    unfold PatternLedger at *
    intro pending result success tracked
    first | unfold Detail.inferMatchPatternFlatFuel at success | unfold Detail.inferMatchPatternsFlatFuel at success
    simp_all [bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals try simp_all
    all_goals try exact tracked
    all_goals try exact tracked.allocateBinderWithoutRequirements _ _ _ _
    all_goals try exact ih1 pending _ (by assumption) tracked

/-- Successful nested pattern inference preserves both operational ledgers. -/
theorem inferMatchPatternFlatFuel_ledgerPreservation
    {fuel : Nat} {context : Frontend.SourceInference.Context} {pattern : Syntax.Pattern}
    {expected : Ty} {seen : List String} {initial : State} {result : Detail.InferredPattern}
    {pending : List RequirementId}
    (accepted : Detail.inferMatchPatternFlatFuel fuel context pattern expected seen initial = .ok result)
    (tracked : RecursiveLedgerInvariant initial pending) :
    RecursiveLedgerInvariant result.state pending :=
  flatPatternLedger fuel context pattern expected seen initial pending result accepted tracked

theorem inferMatchPatternFuel_ledgerPreservation
    {fuel : Nat} {context : Frontend.SourceInference.Context} {pattern : Syntax.Pattern}
    {expected : Ty} {initial final : State} {inferred : TypedMatchPattern}
    {pending : List RequirementId}
    (accepted : Detail.inferMatchPatternFuel fuel context pattern expected initial = .ok (inferred, final))
    (tracked : RecursiveLedgerInvariant initial pending) :
    RecursiveLedgerInvariant final pending := by
  unfold Detail.inferMatchPatternFuel at accepted
  cases flatAccepted : Detail.inferMatchPatternFlatFuel fuel context pattern expected [] initial with
  | error error => simp [flatAccepted, bind, Except.bind] at accepted
  | ok result =>
    simp only [flatAccepted, bind, Except.bind, pure, Pure.pure, Except.pure] at accepted
    cases accepted
    exact inferMatchPatternFlatFuel_ledgerPreservation flatAccepted tracked

end Solcore.SourceSemantics.SourceInferenceSoundness
