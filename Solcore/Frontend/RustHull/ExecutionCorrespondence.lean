import Solcore.Frontend.RustHull.ScalarExecutionSafety
import Solcore.Frontend.RustHull.ScalarInputCorrespondence
import Solcore.Core.FuelResumptionProperties

/-! Exact execution at the public scalar boundary. A semantic lowering proof
supplies a Core evaluation with its final value and store. These results connect
that evaluation to the actual public runner and any finite sequence of genuine
checkpoints, without identifying Hull meaning with a lowered Core program. -/
set_option autoImplicit false

namespace Solcore.Frontend.RustHull.ScalarExecution

/-- Successful preparation supplies the actual compiler and argument-parser
results, so downstream correspondence does not assume a second initialization. -/
theorem prepare_components {program : Program} {entry : String} {inputs : List String}
    {compilationFuel : Nat} {prepared : Prepared}
    (accepted : prepare program entry inputs compilationFuel = .ok prepared) :
    ∃ compiled argument,
      compile program entry compilationFuel = .ok compiled ∧
      parseArguments compiled.parameters inputs = .ok argument ∧
      prepared = ⟨compiled, argument⟩ := by
  cases compiled : compile program entry compilationFuel with
  | error error => simp [prepare, compiled, Except.mapError, Bind.bind, Except.bind] at accepted
  | ok function =>
      cases parsed : parseArguments function.parameters inputs with
      | error error => simp [prepare, compiled, parsed, Except.mapError, Bind.bind, Except.bind] at accepted
      | ok argument =>
          simp [prepare, compiled, parsed, Except.mapError, Bind.bind, Except.bind] at accepted
          cases accepted
          exact ⟨function, argument, rfl, parsed, rfl⟩

/-- The actual public preparation supplies its compiler result, independent
source arguments, their Core representation and unchanged initial heap. -/
theorem prepare_argument_correspondence {program : Program} {entry : String} {inputs : List String}
    {compilationFuel : Nat} {prepared : Prepared}
    (accepted : prepare program entry inputs compilationFuel = .ok prepared) :
    ∃ sources targets,
      compile program entry compilationFuel = .ok prepared.compiled ∧
      InputsRel prepared.compiled.parameters inputs sources ∧
      ValuesRel prepared.compiled.parameters sources targets ∧
      ∀ environment store, Core.Evaluates environment store prepared.argument (bundleValues targets) store := by
  obtain ⟨compiled, argument, checked, parsed, rfl⟩ := prepare_components accepted
  obtain ⟨sources, targets, inputsRelated, valuesRelated, evaluated⟩ := parseArguments_correspondence parsed
  exact ⟨sources, targets, checked, inputsRelated, valuesRelated, evaluated⟩

/-- A terminating semantic evaluation has one exact transition cost. Resuming
does not reset the heap or environment: every public chain completes with the
same value and store precisely when its combined fuel reaches that cost. -/
theorem evaluation_resumes_exact {prepared : Prepared} {value : Core.Value} {store : Core.Store}
    (evaluation : Core.Evaluates [] [] prepared.expression value store) :
    ∃ required, ∀ fuel additional last,
      Resumes (run prepared fuel) additional last →
        (last = .done value store ↔ required ≤ fuel + additional) ∧
        ((∃ checkpoint, last = .outOfFuel checkpoint) ↔ fuel + additional < required) := by
  obtain ⟨required, path⟩ := evaluation.toSteps
  refine ⟨required, ?_⟩
  intro fuel additional last resumed
  rw [resumed.eq_combined_run prepared fuel rfl]
  exact ⟨path.runStateful_done_iff, path.runStateful_outOfFuel_iff⟩

/-- The public runner returns the exact semantic value and final heap at every
sufficient budget, rather than merely returning some value of the right type. -/
theorem evaluation_run_complete {prepared : Prepared} {value : Core.Value} {store : Core.Store}
    (evaluation : Core.Evaluates [] [] prepared.expression value store) :
    ∃ required, ∀ fuel, required ≤ fuel → run prepared fuel = .done value store := by
  exact Core.evaluation_runStateful_complete_with_sufficient_fuel evaluation

/-- A genuine checkpoint after any finite chain retains enough information to
finish the semantic execution. The residual threshold uses all fuel consumed. -/
theorem evaluation_resumes_complete {prepared : Prepared} {value : Core.Value} {store : Core.Store}
    (evaluation : Core.Evaluates [] [] prepared.expression value store) :
    ∃ required, ∀ fuel additional last,
      Resumes (run prepared fuel) additional last →
      ∀ checkpoint, last = .outOfFuel checkpoint →
      ∀ more, required - (fuel + additional) ≤ more →
        resume checkpoint more = .done value store := by
  obtain ⟨required, exactCost⟩ := evaluation_resumes_exact evaluation
  refine ⟨required, ?_⟩
  intro fuel additional last resumed checkpoint exhausted more enough
  have cost := exactCost fuel (additional + more) (resume checkpoint more)
    (.step resumed exhausted more)
  exact cost.1.mpr (by omega)

/-- A completed public run has a semantic Core derivation for those exact
bytes/values and that exact heap; no replacement execution is introduced. -/
theorem run_done_evaluates {prepared : Prepared} {fuel : Nat}
    {value : Core.Value} {store : Core.Store}
    (completed : run prepared fuel = .done value store) :
    Core.Evaluates [] [] prepared.expression value store :=
  Core.runStateful_evaluation_sound completed

theorem resumes_done_evaluates {prepared : Prepared} {fuel additional : Nat}
    {last : Core.StatefulRunResult} {value : Core.Value} {store : Core.Store}
    (resumed : Resumes (run prepared fuel) additional last)
    (completed : last = .done value store) :
    Core.Evaluates [] [] prepared.expression value store :=
  run_done_evaluates ((resumed.eq_combined_run prepared fuel rfl).symm.trans completed)

end Solcore.Frontend.RustHull.ScalarExecution
