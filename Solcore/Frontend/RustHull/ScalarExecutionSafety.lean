import Solcore.Frontend.RustHull.ScalarExecution
import Solcore.Frontend.RustHull.LoweringSafety

/-! Safety from actual scalar input preparation. The public preparation result
supplies both the compiler evidence and the typed argument; callers need no
separate argument, environment or heap typing assumption. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ScalarExecution

theorem parseInput_hasType {type : Core.Ty} {input : String} {expression : Core.Expr}
    (parsed : parseInput type input = .ok expression) : Core.HasType [] expression type := by
  cases type <;> try simp [parseInput, fail] at parsed
  case word =>
    obtain ⟨value, _, returned⟩ := lower_bind_eq_ok.mp parsed
    cases returned
    exact .word
  case unit =>
    split at parsed
    · cases parsed; exact .unit
    · contradiction
  case bool =>
    split at parsed
    · cases parsed; exact .bool
    · split at parsed
      · cases parsed; exact .bool
      · contradiction
  case sum left right =>
    cases left <;> cases right <;> simp only at parsed <;> try contradiction
    split at parsed
    · cases parsed; exact .inRight .unit .unit
    · split at parsed
      · cases parsed; exact .inLeft .unit .unit
      · contradiction

theorem parseArguments_hasType {parameters : List Core.Ty} {inputs : List String} {argument : Core.Expr}
    (parsed : parseArguments parameters inputs = .ok argument) :
    Core.HasType [] argument (bundleType parameters) := by
  induction parameters generalizing inputs argument with
  | nil =>
      cases inputs with
      | nil =>
          simp [parseArguments] at parsed
          cases parsed
          exact .unit
      | cons input inputs => simp [parseArguments, fail, Bind.bind, Except.bind] at parsed
  | cons type types ih =>
      cases inputs with
      | nil => simp [parseArguments, fail, Bind.bind, Except.bind] at parsed
      | cons input inputs =>
          by_cases length : inputs.length = types.length
          · cases types with
            | nil =>
                have empty : inputs = [] := List.eq_nil_of_length_eq_zero length
                subst inputs
                simp only [parseArguments, List.length_cons, List.length_nil, ↓reduceIte] at parsed
                exact parseInput_hasType parsed
            | cons next rest =>
                have lengths : (input :: inputs).length = (type :: next :: rest).length :=
                  congrArg Nat.succ length
                simp only [parseArguments, lengths, ↓reduceIte] at parsed
                obtain ⟨head, headParsed, tail⟩ := lower_bind_eq_ok.mp parsed
                obtain ⟨tail, tailParsed, returned⟩ := lower_bind_eq_ok.mp tail
                cases returned
                exact .pair (parseInput_hasType headParsed) (ih tailParsed)
          · rw [parseArguments.eq_def] at parsed
            simp [length, fail, Bind.bind, Except.bind] at parsed

theorem prepare_hasType {program : Program} {entry : String} {inputs : List String}
    {compilationFuel : Nat} {prepared : Prepared}
    (accepted : prepare program entry inputs compilationFuel = .ok prepared) :
    Core.HasType [] prepared.expression prepared.resultType := by
  cases compiled : compile program entry compilationFuel with
  | error error => simp [prepare, compiled, Except.mapError, Bind.bind, Except.bind] at accepted
  | ok function =>
      cases parsed : parseArguments function.parameters inputs with
      | error error => simp [prepare, compiled, parsed, Except.mapError, Bind.bind, Except.bind] at accepted
      | ok argument =>
          simp [prepare, compiled, parsed, Except.mapError, Bind.bind, Except.bind] at accepted
          cases accepted
          exact compile_application_hasType compiled (parseArguments_hasType parsed)

/-- Actual preparation initializes a closed expression, empty environment and
empty heap with the invariant required by every Core transition. -/
theorem prepare_initial_hasType {program : Program} {entry : String} {inputs : List String}
    {compilationFuel : Nat} {prepared : Prepared}
    (accepted : prepare program entry inputs compilationFuel = .ok prepared) :
    Core.StateHasType (.initial prepared.expression) prepared.resultType :=
  Core.initial_state_has_type (prepare_hasType accepted)

theorem prepare_run_hasType {program : Program} {entry : String} {inputs : List String}
    {compilationFuel : Nat} {prepared : Prepared}
    (accepted : prepare program entry inputs compilationFuel = .ok prepared) (fuel : Nat) :
    (run prepared fuel).HasType prepared.resultType :=
  Core.well_typed_runStateful_has_type (prepare_initial_hasType accepted) fuel

theorem prepare_run_never_faults {program : Program} {entry : String} {inputs : List String}
    {compilationFuel fuel : Nat} {prepared : Prepared} {error : Core.MachineFault} {faultState : Core.State}
    (accepted : prepare program entry inputs compilationFuel = .ok prepared) :
    run prepared fuel ≠ .fault error faultState :=
  Core.well_typed_runStateful_never_faults (prepare_initial_hasType accepted)

theorem prepare_resume_hasType {program : Program} {entry : String} {inputs : List String}
    {compilationFuel spent : Nat} {prepared : Prepared} {checkpoint : Core.State}
    (accepted : prepare program entry inputs compilationFuel = .ok prepared)
    (exhausted : run prepared spent = .outOfFuel checkpoint) (additional : Nat) :
    (resume checkpoint additional).HasType prepared.resultType ∧
      resume checkpoint additional = run prepared (spent + additional) :=
  Core.well_typed_runStateful_resume_has_type (prepare_initial_hasType accepted) exhausted additional

theorem prepare_resume_never_faults {program : Program} {entry : String} {inputs : List String}
    {compilationFuel spent additional : Nat} {prepared : Prepared}
    {checkpoint faultState : Core.State} {error : Core.MachineFault}
    (accepted : prepare program entry inputs compilationFuel = .ok prepared)
    (exhausted : run prepared spent = .outOfFuel checkpoint) :
    resume checkpoint additional ≠ .fault error faultState :=
  Core.well_typed_runStateful_never_faults
    (Core.well_typed_runStateful_preserves_checkpoint_type (prepare_initial_hasType accepted) exhausted)

/-- A finite sequence of actual public resumptions. The middle index counts
additional fuel supplied after the first result; zero-fuel resumes are allowed.
Each step retains the checkpoint returned by the previous execution. -/
inductive Resumes : Core.StatefulRunResult → Nat → Core.StatefulRunResult → Prop where
  | refl (result : Core.StatefulRunResult) : Resumes result 0 result
  | step {first previous : Core.StatefulRunResult} {spent : Nat} {checkpoint : Core.State}
      (path : Resumes first spent previous)
      (exhausted : previous = .outOfFuel checkpoint)
      (additional : Nat) :
      Resumes first (spent + additional) (resume checkpoint additional)

/-- Repeated public resumes have exactly the same result, final store and
checkpoint as one public run with the combined fuel allowance. -/
theorem Resumes.eq_combined_run {first last : Core.StatefulRunResult} {additional : Nat}
    (path : Resumes first additional last) (prepared : Prepared) (fuel : Nat)
    (initial : first = run prepared fuel) : last = run prepared (fuel + additional) := by
  induction path with
  | refl => simpa only [Nat.add_zero] using initial
  | @step previous spent checkpoint path exhausted more ih =>
      have stopped : run prepared (fuel + spent) = .outOfFuel checkpoint := ih.symm.trans exhausted
      simpa only [resume, run, Nat.add_assoc] using Core.runStateful_resume stopped more

theorem Resumes.hasType {first last : Core.StatefulRunResult} {additional : Nat}
    {type : Core.Ty} {definitions : Core.DataEnvironment}
    (path : Resumes first additional last) (initial : first.HasType type definitions) :
    last.HasType type definitions := by
  induction path with
  | refl => exact initial
  | step _ exhausted more ih =>
      have checkpointTyped := ih
      rw [exhausted] at checkpointTyped
      exact Core.well_typed_runStateful_has_type checkpointTyped more

/-- Actual scalar preparation proves safety for every finite sequence of
public checkpoints, together with exact combined-fuel execution equality. -/
theorem prepare_resumes_hasType {program : Program} {entry : String} {inputs : List String}
    {compilationFuel : Nat} {prepared : Prepared}
    (accepted : prepare program entry inputs compilationFuel = .ok prepared)
    (fuel : Nat) {additional : Nat} {last : Core.StatefulRunResult}
    (resumed : Resumes (run prepared fuel) additional last) :
    last.HasType prepared.resultType ∧ last = run prepared (fuel + additional) :=
  ⟨resumed.hasType (prepare_run_hasType accepted fuel), resumed.eq_combined_run prepared fuel rfl⟩

theorem prepare_resumes_never_faults {program : Program} {entry : String} {inputs : List String}
    {compilationFuel : Nat} {prepared : Prepared}
    (accepted : prepare program entry inputs compilationFuel = .ok prepared)
    (fuel : Nat) {additional : Nat} {last : Core.StatefulRunResult}
    (resumed : Resumes (run prepared fuel) additional last)
    (error : Core.MachineFault) (faultState : Core.State) : last ≠ .fault error faultState := by
  have typed := (prepare_resumes_hasType accepted fuel resumed).1
  intro faulted
  simp only [faulted, Core.StatefulRunResult.HasType] at typed

theorem prepare_resumes_checkpoint_hasType {program : Program} {entry : String} {inputs : List String}
    {compilationFuel : Nat} {prepared : Prepared}
    (accepted : prepare program entry inputs compilationFuel = .ok prepared)
    (fuel : Nat) {additional : Nat} {last : Core.StatefulRunResult} {checkpoint : Core.State}
    (resumed : Resumes (run prepared fuel) additional last)
    (exhausted : last = .outOfFuel checkpoint) : Core.StateHasType checkpoint prepared.resultType := by
  have typed := (prepare_resumes_hasType accepted fuel resumed).1
  simpa only [exhausted, Core.StatefulRunResult.HasType] using typed

end Solcore.Frontend.RustHull.ScalarExecution
