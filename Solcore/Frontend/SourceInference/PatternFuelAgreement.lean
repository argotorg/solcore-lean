import Solcore.Frontend.SourceInference.Expression

/-! Increasing the structural inference budget preserves each successful
pattern result, including its complete state and ordered instructions. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.Frontend.SourceInference.Detail
open TypeSystem

private def Stable {α : Type} (action : Nat → Except Error α) (fuel : Nat) : Prop :=
  ∀ extra result, action fuel = .ok result → action (fuel + extra) = .ok result

private theorem pattern_stable (context : Context) :
    (∀ fuel pattern expected seen state,
      Stable (fun budget => inferMatchPatternFlatFuel budget context pattern expected seen state) fuel) ∧
    (∀ fuel patterns expected seen state,
      Stable (fun budget => inferMatchPatternsFlatFuel budget context patterns expected seen state) fuel) := by
  apply inferMatchPatternFlatFuel.mutual_induct context
    (motive1 := fun fuel pattern expected seen state =>
      Stable (fun fuel => inferMatchPatternFlatFuel fuel context pattern expected seen state) fuel)
    (motive2 := fun fuel patterns expected seen state =>
      Stable (fun fuel => inferMatchPatternsFlatFuel fuel context patterns expected seen state) fuel)
  all_goals
    intros
    unfold Stable at *
    intro extra result accepted
    simp_all only [Nat.succ_add, inferMatchPatternFlatFuel, inferMatchPatternsFlatFuel,
      bind, Except.bind]
    repeat' first | split at accepted
    all_goals try cases accepted
    all_goals try simp_all [pure, Except.pure]
    all_goals grind

theorem inferMatchPatternFlatFuel_success_mono {fuel : Nat} {context : Context}
    {pattern : Syntax.Pattern} {expected : Ty} {seen : List String} {state : State} {result : InferredPattern}
    (accepted : inferMatchPatternFlatFuel fuel context pattern expected seen state = .ok result)
    (extra : Nat) : inferMatchPatternFlatFuel (fuel + extra) context pattern expected seen state = .ok result :=
  (pattern_stable context).1 fuel pattern expected seen state extra result accepted

theorem inferMatchPatternsFlatFuel_success_mono {fuel : Nat} {context : Context}
    {patterns : List Syntax.Pattern} {expected : List Ty} {seen : List String} {state : State} {result : InferredPatterns}
    (accepted : inferMatchPatternsFlatFuel fuel context patterns expected seen state = .ok result)
    (extra : Nat) : inferMatchPatternsFlatFuel (fuel + extra) context patterns expected seen state = .ok result :=
  (pattern_stable context).2 fuel patterns expected seen state extra result accepted

theorem inferMatchPatternFuel_success_mono {fuel : Nat} {context : Context}
    {pattern : Syntax.Pattern} {expected : Ty} {state : State} {result : TypedMatchPattern × State}
    (accepted : inferMatchPatternFuel fuel context pattern expected state = .ok result)
    (extra : Nat) : inferMatchPatternFuel (fuel + extra) context pattern expected state = .ok result := by
  unfold inferMatchPatternFuel at accepted ⊢
  cases selected : inferMatchPatternFlatFuel fuel context pattern expected [] state with
  | error error => simp [selected, bind, Except.bind] at accepted
  | ok output =>
    have same := inferMatchPatternFlatFuel_success_mono selected extra
    simpa only [selected, same, bind, Except.bind] using accepted

end Solcore.Frontend.SourceInference.Detail
