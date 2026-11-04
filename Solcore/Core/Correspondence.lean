import Solcore.Core.Internal.Simulation
import Solcore.Core.Internal.MachineLaws

/-!
# The evaluator and the machine agree

Main theorems. `runStateful_evaluation_sound` and `run_evaluation_sound`: a machine run that ends
is an evaluation. `evaluation_runStateful_complete`, `evaluation_run_complete` and their
`_with_sufficient_fuel` forms: an evaluation is reached by a machine run with enough fuel. The two
directions are proved in `Internal/Simulation`.
-/

set_option autoImplicit false

namespace Solcore.Core

theorem runStateful_evaluation_sound
    {fuel : Nat} {environment : Environment}
    {initialStore finalStore : Store} {expr : Expr} {value : Value}
    (result :
      runStateful fuel (State.initial expr environment initialStore) =
        .done value finalStore) :
    Evaluates environment initialStore expr value finalStore := by
  obtain ⟨steps, _, path⟩ := runStateful_sound result
  exact steps_from_initial_sound path

theorem run_stateful_evaluation_sound
    {fuel : Nat} {environment : Environment}
    {initialStore finalStore : Store} {expr : Expr} {value : Value}
    (result :
      runStateful fuel (State.initial expr environment initialStore) =
        .done value finalStore) :
    Evaluates environment initialStore expr value finalStore :=
  runStateful_evaluation_sound result

theorem evaluation_runStateful_complete
    {environment : Environment} {initialStore finalStore : Store}
    {expr : Expr} {value : Value}
    (evaluation : Evaluates environment initialStore expr value finalStore) :
    ∃ fuel,
      runStateful fuel (State.initial expr environment initialStore) =
        .done value finalStore := by
  obtain ⟨steps, path⟩ := evaluation.toSteps
  exact ⟨steps, runStateful_complete_with_fuel path (Nat.le_refl steps)⟩

theorem evaluation_run_stateful_complete
    {environment : Environment} {initialStore finalStore : Store}
    {expr : Expr} {value : Value}
    (evaluation : Evaluates environment initialStore expr value finalStore) :
    ∃ fuel,
      runStateful fuel (State.initial expr environment initialStore) =
        .done value finalStore :=
  evaluation_runStateful_complete evaluation

theorem evaluation_runStateful_complete_with_sufficient_fuel
    {environment : Environment} {initialStore finalStore : Store}
    {expr : Expr} {value : Value}
    (evaluation : Evaluates environment initialStore expr value finalStore) :
    ∃ required,
      ∀ fuel,
        required ≤ fuel →
        runStateful fuel (State.initial expr environment initialStore) =
          .done value finalStore := by
  obtain ⟨steps, path⟩ := evaluation.toSteps
  exact ⟨steps, fun fuel enough =>
    runStateful_complete_with_fuel path enough⟩

theorem evaluation_run_stateful_complete_with_sufficient_fuel
    {environment : Environment} {initialStore finalStore : Store}
    {expr : Expr} {value : Value}
    (evaluation : Evaluates environment initialStore expr value finalStore) :
    ∃ required,
      ∀ fuel,
        required ≤ fuel →
        runStateful fuel (State.initial expr environment initialStore) =
          .done value finalStore :=
  evaluation_runStateful_complete_with_sufficient_fuel evaluation

theorem run_evaluation_sound
    {fuel : Nat} {environment : Environment} {initialStore : Store}
    {expr : Expr} {value : Value}
    (result : run fuel (State.initial expr environment initialStore) = .done value) :
    ∃ finalStore,
      Evaluates environment initialStore expr value finalStore := by
  obtain ⟨finalStore, steps, _, path⟩ := run_sound result
  exact ⟨finalStore, steps_from_initial_sound path⟩

theorem evaluation_run_complete
    {environment : Environment} {initialStore finalStore : Store}
    {expr : Expr} {value : Value}
    (evaluation : Evaluates environment initialStore expr value finalStore) :
    ∃ fuel,
      run fuel (State.initial expr environment initialStore) = .done value := by
  obtain ⟨steps, path⟩ := evaluation.toSteps
  exact ⟨steps, run_complete_with_fuel path (Nat.le_refl steps)⟩

theorem evaluation_run_complete_with_sufficient_fuel
    {environment : Environment} {initialStore finalStore : Store}
    {expr : Expr} {value : Value}
    (evaluation : Evaluates environment initialStore expr value finalStore) :
    ∃ required,
      ∀ fuel,
        required ≤ fuel →
        run fuel (State.initial expr environment initialStore) = .done value := by
  obtain ⟨steps, path⟩ := evaluation.toSteps
  exact ⟨steps, fun fuel enough => run_complete_with_fuel path enough⟩

end Solcore.Core
