import Solcore.Frontend.SourceCoreUnifiedRuntime

/-! Request-indexed certificates for the actual public Core-only adapter.
These retain the original source boundary checks and prepared deep certificate;
they do not assert a whole-source execution derivation or equal numeric fuel. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreUnifiedRuntime

open SourceInference

theorem Prepared.root?_facts {checked : Checked} {program : Program checked}
    {prepared : Prepared program} {key : Key} {root : Root program}
    (found : prepared.root? key = some root) :
    root ∈ prepared.roots ∧ root.entry.key = key := by
  change prepared.roots.find? (fun root => decide (root.entry.key = key)) = some root at found
  exact ⟨List.mem_of_find?_eq_some found, of_decide_eq_true (List.find?_some (p := fun candidate : Root program => decide (candidate.entry.key = key)) found)⟩

/-- Every native execution retained by `run` belongs to the exact request. -/
theorem run_execution_request {checked : Checked} {program : Program checked}
    {prepared : Prepared program} {key : Key} {arguments : List SourceValue}
    {validationFuel executionFuel : Nat} {initial : SourceState} {result : Result prepared}
    (ran : run prepared key arguments validationFuel executionFuel initial = .ok result)
    {execution : Execution prepared} (produced : result.execution = some execution) :
    execution.root.entry.key = key ∧ execution.arguments = arguments ∧
      execution.validationFuel = validationFuel ∧ execution.initial = initial := by
  unfold run at ran
  split at ran
  · simp only [pure, Except.pure, Except.ok.injEq] at ran
    cases ran
    contradiction
  · simp only [bind, Except.bind] at ran
    split at ran
    · next root found =>
      simp only [pure, Except.pure] at ran
      split at ran
      · simp only [Except.ok.injEq] at ran
        cases ran
        contradiction
      · simp only [Except.mapError] at ran
        split at ran
        · contradiction
        · split at ran
          · split at ran
            · split at ran
              · contradiction
              · simp only [Except.ok.injEq] at ran
                cases ran
                simp only [Option.some.injEq] at produced
                cases produced
                exact ⟨(Prepared.root?_facts found).2, rfl, rfl, rfl⟩
            · contradiction
          · contradiction
    · contradiction

/-- The accepted request retains the old shallow and deep validation decisions
and the authoritative specialization input/result metadata. -/
theorem run_execution_boundary {checked : Checked} {program : Program checked}
    {prepared : Prepared program} {key : Key} {arguments : List SourceValue}
    {validationFuel executionFuel : Nat} {initial : SourceState} {result : Result prepared}
    (ran : run prepared key arguments validationFuel executionFuel initial = .ok result)
    {execution : Execution prepared} (produced : result.execution = some execution) :
    SourceCompilationPlan.exactSpecialization program.base.validationPlan key = .ok execution.root.specialized ∧
    execution.root.entry.inputs.map (·.scheme.body) = execution.root.argumentTypes ∧
    execution.root.entry.sourceResultType = execution.root.expected ∧
    SourceTypedRuntime.validateInputs program.base.sourceProgram.signatures program.base.validationPlan
      validationFuel execution.root.argumentTypes arguments = none ∧
    initial.isDeeplySafe validationFuel program.base.sourceProgram.signatures program.base.plan = true ∧
    SourceTypedRuntime.valuesDeeplySafe validationFuel program.base.sourceProgram.signatures program.base.plan
      initial arguments execution.root.argumentTypes = true := by
  rcases run_execution_request ran produced with ⟨keyExact, argumentsExact, fuelExact, initialExact⟩
  have selected := execution.root.selected
  rw [keyExact] at selected
  have boundary := boundaryFailure_none execution.boundaryAccepted
  rw [argumentsExact, fuelExact, initialExact] at boundary
  exact ⟨selected, execution.root.inputExact, execution.root.resultExact, boundary⟩

/-- The request agreement is reusable across any number of native resumptions. -/
def Result.Requests {checked : Checked} {program : Program checked} {prepared : Prepared program}
    (result : Result prepared) (key : Key) (arguments : List SourceValue)
    (validationFuel : Nat) (initial : SourceState) : Prop :=
  ∀ execution, result.execution = some execution →
    execution.root.entry.key = key ∧ execution.arguments = arguments ∧
      execution.validationFuel = validationFuel ∧ execution.initial = initial

theorem run_requests {checked : Checked} {program : Program checked} {prepared : Prepared program}
    {key : Key} {arguments : List SourceValue} {validationFuel executionFuel : Nat}
    {initial : SourceState} {result : Result prepared}
    (ran : run prepared key arguments validationFuel executionFuel initial = .ok result) :
    result.Requests key arguments validationFuel initial := fun _ produced => run_execution_request ran produced

theorem Result.resume_requests {checked : Checked} {program : Program checked} {prepared : Prepared program}
    {key : Key} {arguments : List SourceValue} {validationFuel fuel : Nat} {initial : SourceState}
    {result resumed : Result prepared} (requested : result.Requests key arguments validationFuel initial)
    (continued : result.resume fuel = .ok resumed) :
    resumed.Requests key arguments validationFuel initial := by
  unfold Result.resume at continued
  split at continued
  · simp only [pure, Except.pure, Except.ok.injEq] at continued
    cases continued
    exact requested
  · next previous previousEq =>
    dsimp only at continued
    split at continued
    · contradiction
    · simp only [pure, Except.pure, Except.ok.injEq] at continued
      cases continued
      intro execution produced
      simp only [Option.some.injEq] at produced
      cases produced
      exact requested previous previousEq

/-- Success uses the source input/result metadata of the specialization selected
by the actual request, with the original arguments and initial heap. -/
theorem Result.requested_done_specialization {checked : Checked} {program : Program checked}
    {prepared : Prepared program} {key : Key} {arguments : List SourceValue}
    {validationFuel : Nat} {initial : SourceState} {result : Result prepared}
    {value : SourceValue} {final : SourceState}
    (requested : result.Requests key arguments validationFuel initial)
    (done : result.observation = .done value final) :
    ∃ specialized, SourceCompilationPlan.exactSpecialization program.base.validationPlan key = .ok specialized ∧
      SourceTypedRuntime.PreparedDeepExecution program.base.sourceProgram program.base.validationPlan
        (specialized.function.typedBody.inputs.map (·.scheme.body)) specialized.function.inferredBodyType
        arguments initial value final := by
  rcases result.done_certificate done with ⟨execution, produced, certificate⟩
  rcases requested execution produced with ⟨keyExact, argumentsExact, _, initialExact⟩
  have selected := execution.root.selected
  rw [keyExact] at selected
  refine ⟨execution.root.specialized, selected, ?_⟩
  simpa only [Root.argumentTypes, Root.expected, argumentsExact, initialExact] using certificate

theorem run_done_specialization {checked : Checked} {program : Program checked}
    {prepared : Prepared program} {key : Key} {arguments : List SourceValue}
    {validationFuel executionFuel : Nat} {initial : SourceState} {result : Result prepared}
    {value : SourceValue} {final : SourceState}
    (ran : run prepared key arguments validationFuel executionFuel initial = .ok result)
    (done : result.observation = .done value final) :
    ∃ specialized, SourceCompilationPlan.exactSpecialization program.base.validationPlan key = .ok specialized ∧
      SourceTypedRuntime.PreparedDeepExecution program.base.sourceProgram program.base.validationPlan
        (specialized.function.typedBody.inputs.map (·.scheme.body)) specialized.function.inferredBodyType
        arguments initial value final :=
  Result.requested_done_specialization (run_requests ran) done

theorem Result.requested_done_certificate {checked : Checked} {program : Program checked}
    {prepared : Prepared program} {key : Key} {arguments : List SourceValue}
    {validationFuel : Nat} {initial : SourceState} {result : Result prepared}
    {value : SourceValue} {final : SourceState} {specialized : SourceSpecialization.SpecializedFunction}
    (requested : result.Requests key arguments validationFuel initial)
    (selected : SourceCompilationPlan.exactSpecialization program.base.validationPlan key = .ok specialized)
    (done : result.observation = .done value final) :
    SourceTypedRuntime.PreparedDeepExecution program.base.sourceProgram program.base.validationPlan
      (specialized.function.typedBody.inputs.map (·.scheme.body)) specialized.function.inferredBodyType
      arguments initial value final := by
  rcases Result.requested_done_specialization requested done with ⟨actual, actualSelected, certificate⟩
  have exactSpecialization : actual = specialized := Except.ok.inj (actualSelected.symm.trans selected)
  cases exactSpecialization
  exact certificate

theorem run_done_certificate {checked : Checked} {program : Program checked}
    {prepared : Prepared program} {key : Key} {arguments : List SourceValue}
    {validationFuel executionFuel : Nat} {initial : SourceState} {result : Result prepared}
    {value : SourceValue} {final : SourceState} {specialized : SourceSpecialization.SpecializedFunction}
    (ran : run prepared key arguments validationFuel executionFuel initial = .ok result)
    (selected : SourceCompilationPlan.exactSpecialization program.base.validationPlan key = .ok specialized)
    (done : result.observation = .done value final) :
    SourceTypedRuntime.PreparedDeepExecution program.base.sourceProgram program.base.validationPlan
      (specialized.function.typedBody.inputs.map (·.scheme.body)) specialized.function.inferredBodyType
      arguments initial value final :=
  Result.requested_done_certificate (run_requests ran) selected done

theorem run_resume_done_certificate {checked : Checked} {program : Program checked}
    {prepared : Prepared program} {key : Key} {arguments : List SourceValue}
    {validationFuel executionFuel resumeFuel : Nat} {initial : SourceState}
    {result resumed : Result prepared} {value : SourceValue} {final : SourceState}
    {specialized : SourceSpecialization.SpecializedFunction}
    (ran : run prepared key arguments validationFuel executionFuel initial = .ok result)
    (continued : result.resume resumeFuel = .ok resumed)
    (selected : SourceCompilationPlan.exactSpecialization program.base.validationPlan key = .ok specialized)
    (done : resumed.observation = .done value final) :
    SourceTypedRuntime.PreparedDeepExecution program.base.sourceProgram program.base.validationPlan
      (specialized.function.typedBody.inputs.map (·.scheme.body)) specialized.function.inferredBodyType
      arguments initial value final :=
  Result.requested_done_certificate (Result.resume_requests (run_requests ran) continued) selected done

end Solcore.Frontend.SourceCoreUnifiedRuntime
