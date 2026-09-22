import Solcore.Frontend.SourceCompiler
import Solcore.Frontend.SourceSpecializationWorklistProperties

/-! Small interface laws for the restricted public source compiler. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCompiler

@[simp] theorem Invocation.coreFresh_kind (arguments : List Core.Value) :
    (Invocation.coreFresh arguments).kind = .coreValues := by
  rfl

@[simp] theorem Invocation.typedFresh_kind
    (arguments : List SourceTypedRuntime.Value) :
    (Invocation.typedFresh arguments).kind = .typedValues := by
  rfl

theorem CompiledEntry.runCore_eq_run (compiled : CompiledEntry)
    (arguments : List Core.Value) (options : RunOptions) (store : Core.Store) :
    compiled.runCore arguments options store =
      compiled.run (.coreValues arguments store) options := by
  rfl

theorem CompiledEntry.runTyped_eq_run (compiled : CompiledEntry)
    (arguments : List SourceTypedRuntime.Value) (options : RunOptions)
    (state : SourceTypedRuntime.RuntimeState) :
    compiled.runTyped arguments options state =
      compiled.run (.typedValues arguments state) options := by
  rfl

/-- A typed-source artifact rejects Core-domain inputs before either runtime
starts.  In particular, execution fuel cannot turn this boundary failure into
a runtime result. -/
theorem CompiledEntry.runCore_of_typedSource (compiled : CompiledEntry)
    (arguments : List Core.Value) (options : RunOptions) (store : Core.Store)
    (hbackend : compiled.backend = .typedSource) :
    compiled.runCore arguments options store =
      .error (.invocationKindMismatch .typedSource .coreValues) := by
  cases compiled
  rename_i program plan root executable
  cases executable <;> simp_all [CompiledEntry.backend, CompiledEntry.runCore,
    CompiledEntry.run, Invocation.kind]

/-- A direct-Core artifact rejects source-typed inputs before execution. -/
theorem CompiledEntry.runTyped_of_core (compiled : CompiledEntry)
    (arguments : List SourceTypedRuntime.Value) (options : RunOptions)
    (state : SourceTypedRuntime.RuntimeState)
    (hbackend : compiled.backend = .core) :
    compiled.runTyped arguments options state =
      .error (.invocationKindMismatch .core .typedValues) := by
  cases compiled
  rename_i program plan root executable
  cases executable <;> simp_all [CompiledEntry.backend, CompiledEntry.runTyped,
    CompiledEntry.run, Invocation.kind]

/-- A structural-call-graph artifact rejects source-typed inputs before
execution. -/
theorem CompiledEntry.runTyped_of_callGraph (compiled : CompiledEntry)
    (arguments : List SourceTypedRuntime.Value) (options : RunOptions)
    (state : SourceTypedRuntime.RuntimeState)
    (hbackend : compiled.backend = .callGraph) :
    compiled.runTyped arguments options state =
      .error (.invocationKindMismatch .callGraph .typedValues) := by
  cases compiled
  rename_i program plan root executable
  cases executable <;> simp_all [CompiledEntry.backend, CompiledEntry.runTyped,
    CompiledEntry.run, Invocation.kind]

/-- Once a typed-source artifact receives typed inputs, validation failures,
runtime faults, and either fuel exhaustion are retained inside its native
result carrier rather than being relabeled as facade errors. -/
theorem CompiledEntry.runTyped_ok_of_typedSource (compiled : CompiledEntry)
    (arguments : List SourceTypedRuntime.Value) (options : RunOptions)
    (state : SourceTypedRuntime.RuntimeState)
    (hbackend : compiled.backend = .typedSource) :
    ∃ result, compiled.runTyped arguments options state =
      .ok (.typedSource result) := by
  cases compiled
  rename_i program plan root executable
  cases executable <;> simp_all [CompiledEntry.backend, CompiledEntry.runTyped,
    CompiledEntry.run]

/-- A structural call-graph runtime likewise retains faults and exhaustion in
its native result carrier after the invocation domain has matched. -/
theorem CompiledEntry.runCore_ok_of_callGraph (compiled : CompiledEntry)
    (arguments : List Core.Value) (options : RunOptions) (store : Core.Store)
    (hbackend : compiled.backend = .callGraph) :
    ∃ result, compiled.runCore arguments options store =
      .ok (.callGraph result) := by
  cases compiled
  rename_i program plan root executable
  cases executable <;> simp_all [CompiledEntry.backend, CompiledEntry.runCore,
    CompiledEntry.run]

/-- After a Core-domain invocation reaches the direct backend, the only
facade-level rejection is the explicit input-type mismatch.  Every runtime
outcome remains in one of the exact backend result carriers. -/
theorem CompiledEntry.runCore_outcome_of_core (compiled : CompiledEntry)
    (arguments : List Core.Value) (options : RunOptions) (store : Core.Store)
    (hbackend : compiled.backend = .core) :
    (∃ result, compiled.runCore arguments options store =
        .ok (.core result)) ∨
      (∃ result, compiled.runCore arguments options store =
        .ok (.callGraph result)) ∨
      (∃ expected actual, compiled.runCore arguments options store =
        .error (.coreInputTypesMismatch expected actual)) := by
  cases compiled
  rename_i program plan root executable
  cases executable <;> simp_all [CompiledEntry.backend]
  rename_i entry
  simp only [CompiledEntry.runCore, CompiledEntry.run]
  cases hresult : entry.runExact? arguments options.executionFuel store with
  | none =>
      exact Or.inr (Or.inr ⟨entry.elaborated.inputs.values,
        arguments.map Core.Value.type, by simp⟩)
  | some result =>
      cases result with
      | core result => exact Or.inl ⟨result, by simp⟩
      | runtime result => exact Or.inr (Or.inl ⟨result, by simp⟩)

theorem run_of_compiled (raw : Workspace.RawWorkspace) (seed : Seed)
    (invocation : Invocation) (limits : Limits) (compiled : CompiledEntry)
    (compiledOk : compile raw seed limits.toCheckingOptions = .ok compiled) :
    run raw seed invocation limits =
      (compiled.run invocation limits.toRunOptions).mapError Error.execution := by
  unfold run
  rw [compiledOk]
  change (do
    let compiled ← Except.ok compiled
    (compiled.run invocation limits.toRunOptions).mapError Error.execution) = _
  rfl

/-- Whole-program checking failures retain their phase and exact payload; no
seed resolution or specialization step can relabel them. -/
theorem compile_of_checking_error (raw : Workspace.RawWorkspace) (seed : Seed)
    (options : CheckingOptions) (errors : List ProgramCheckError)
    (failed : checkProgram raw options.checkingFuel = .error errors) :
    compile raw seed options = .error (.checking errors) := by
  unfold compile
  rw [failed]
  rfl

/-- Seed-resolution failures are reported before the worklist is entered. -/
theorem compileChecked_of_seed_error (program : CheckedProgram) (seed : Seed)
    (options : CompileOptions) (error : SourceProgramExecution.SeedError)
    (failed : SourceProgramExecution.resolveSeed program seed = .error error) :
    compileChecked program seed options = .error (.seed error) := by
  unfold compileChecked
  rw [failed]
  rfl

/-- Zero distinct-specialization budget exposes the first canonical root and
its one-element pending frontier.  Staging fuel is independent and is never
consulted on this path. -/
theorem compileChecked_zero_specializationBudget
    (program : CheckedProgram) (seed : Seed)
    (request : SourceSpecializationWorklist.Request)
    (specialized : SourceSpecialization.SpecializedFunction)
    (stagingFuel : Nat)
    (seedOk : SourceProgramExecution.resolveSeed program seed = .ok request)
    (resolved : SourceSpecializationWorklist.resolveRequest program request =
      .ok specialized) :
    compileChecked program seed {
      specializationBudget := 0
      stagingFuel
    } = .error (.specializationBudgetExhausted specialized.key 1) := by
  unfold compileChecked
  rw [seedOk]
  simp only [Except.mapError, bind, Except.bind]
  rw [SourceSpecializationWorklist.run_zero_single program request specialized
    resolved]
  rfl

/-- Raw-workspace compilation preserves the root identity fixed after checking
and exact seed resolution. -/
theorem compile_key_of_resolved (raw : Workspace.RawWorkspace) (seed : Seed)
    (options : CheckingOptions) (program : CheckedProgram)
    (request : SourceSpecializationWorklist.Request)
    (specialized : SourceSpecialization.SpecializedFunction)
    (compiled : CompiledEntry)
    (checked : checkProgram raw options.checkingFuel = .ok program)
    (seedOk : SourceProgramExecution.resolveSeed program seed = .ok request)
    (resolved : SourceSpecializationWorklist.resolveRequest program request =
      .ok specialized)
    (compiledOk : compile raw seed options = .ok compiled) :
    compiled.key = specialized.key := by
  unfold compile at compiledOk
  rw [checked] at compiledOk
  simp only [Except.mapError, bind, Except.bind] at compiledOk
  exact compileChecked_key_of_resolved program seed options.toCompileOptions
    request specialized compiled seedOk resolved compiledOk

/-- One-shot execution preserves an exact compilation failure and never
reclassifies it as a runtime-domain failure. -/
theorem run_of_compile_error (raw : Workspace.RawWorkspace) (seed : Seed)
    (invocation : Invocation) (limits : Limits) (error : CompileError)
    (failed : compile raw seed limits.toCheckingOptions = .error error) :
    run raw seed invocation limits = .error (.compilation error) := by
  unfold run
  rw [failed]
  rfl

end Solcore.Frontend.SourceCompiler
