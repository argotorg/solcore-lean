import Solcore.Frontend.SourceCompiler
import Solcore.Frontend.SourceCoreDirectLinkingProperties
import Solcore.Frontend.SourceSpecializationWorklistProperties
import Solcore.Frontend.SourceTypedRuntimeProperties

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

/-- A successful direct-Core facade result inherits the checked Core body's
deep result/store preservation theorem. -/
theorem CompiledEntry.run_core_done_preserves_type
    (compiled : CompiledEntry) (arguments : List Core.Value)
    (store : Core.Store) (options : RunOptions)
    {value : Core.Value} {finalStore : Core.Store}
    (precondition : compiled.PreservationPrecondition
      (.coreValues arguments store))
    (ran : compiled.run (.coreValues arguments store) options =
      .ok (.core (.done value finalStore))) :
    compiled.SuccessfulResultHasNativeType (.core (.done value finalStore)) := by
  cases compiled
  rename_i program plan root executable
  cases executable with
  | core entry =>
      simp only [CompiledEntry.PreservationPrecondition] at precondition
      obtain ⟨world, environmentTyped, storeTyped⟩ := precondition
      simp only [CompiledEntry.run] at ran
      cases exactRun : entry.runExact? arguments options.executionFuel store with
      | none =>
          rw [exactRun] at ran
          cases ran
      | some result =>
          rw [exactRun] at ran
          cases result with
          | core result =>
              cases ran
              simp only [CompiledEntry.SuccessfulResultHasNativeType]
              exact entry.runExact?_core_done_preserves_type arguments
                options.executionFuel store environmentTyped storeTyped exactRun
          | runtime result =>
              cases ran
  | callGraph entry =>
      simp only [CompiledEntry.run] at ran
      cases ran
  | typedSource =>
      simp only [CompiledEntry.PreservationPrecondition] at precondition

/-- Under the same deep invocation premise, the facade's direct-Core route
cannot expose a machine fault at any finite execution budget. -/
theorem CompiledEntry.run_core_never_faults
    (compiled : CompiledEntry) (arguments : List Core.Value)
    (store : Core.Store) (options : RunOptions)
    (precondition : compiled.PreservationPrecondition
      (.coreValues arguments store))
    (error : Core.MachineFault) (faultState : Core.State) :
    compiled.run (.coreValues arguments store) options ≠
      .ok (.core (.fault error faultState)) := by
  cases compiled
  rename_i program plan root executable
  cases executable with
  | core entry =>
      simp only [CompiledEntry.PreservationPrecondition] at precondition
      obtain ⟨world, environmentTyped, storeTyped⟩ := precondition
      intro ran
      simp only [CompiledEntry.run] at ran
      cases exactRun : entry.runExact? arguments options.executionFuel store with
      | none =>
          rw [exactRun] at ran
          cases ran
      | some result =>
          rw [exactRun] at ran
          cases result with
          | core result =>
              cases ran
              exact entry.runExact?_core_never_faults arguments
                options.executionFuel store environmentTyped storeTyped
                error faultState exactRun
          | runtime result =>
              cases ran
  | callGraph entry =>
      simp [CompiledEntry.run]
  | typedSource =>
      simp only [CompiledEntry.PreservationPrecondition] at precondition

/-- Either facade route which reaches the finite call-graph runtime preserves
the result type declared by the exact selected runtime signature. -/
theorem CompiledEntry.run_callGraph_done_preserves_type
    (compiled : CompiledEntry) (invocation : Invocation)
    (options : RunOptions) {value : SourceRuntime.Value}
    {finalStore : Core.Store}
    (ran : compiled.run invocation options =
      .ok (.callGraph (.done value finalStore))) :
    compiled.SuccessfulResultHasNativeType
      (.callGraph (.done value finalStore)) := by
  cases compiled
  rename_i program plan root executable
  cases executable with
  | core entry =>
      cases invocation with
      | coreValues arguments store =>
          simp only [CompiledEntry.run] at ran
          cases exactRun : entry.runExact? arguments options.executionFuel store with
          | none =>
              rw [exactRun] at ran
              cases ran
          | some result =>
              rw [exactRun] at ran
              cases result with
              | core result =>
                  cases ran
              | runtime result =>
                  cases ran
                  cases runtime : entry.runtime with
                  | none =>
                      simp [SourceCoreDirectLinking.LinkedEntry.runExact?,
                        runtime] at exactRun
                  | some checked =>
                      have completed : checked.run options.executionFuel
                          entry.key arguments store =
                            .done value finalStore := by
                        have dispatched :
                            arguments.map Core.Value.type =
                                entry.elaborated.inputs.values ∧
                              checked.run options.executionFuel entry.key
                                  arguments store = .done value finalStore := by
                          simpa [SourceCoreDirectLinking.LinkedEntry.runExact?,
                            runtime] using exactRun
                        exact dispatched.2
                      obtain ⟨definition, _, signature, valueTyped⟩ :=
                        checked.run_done_hasType options.executionFuel entry.key
                          arguments store finalStore value completed
                      simp only [CompiledEntry.SuccessfulResultHasNativeType, runtime,
                        CompiledEntry.GraphResultHasType]
                      exact ⟨definition.signature, signature, valueTyped⟩
      | typedValues arguments state =>
          simp [CompiledEntry.run, Invocation.kind] at ran
  | callGraph entry =>
      cases invocation with
      | coreValues arguments store =>
          have completed : entry.program.run options.executionFuel entry.key
              arguments store = .done value finalStore := by
            simpa [CompiledEntry.run] using ran
          obtain ⟨definition, _, signature, valueTyped⟩ :=
            entry.program.run_done_hasType options.executionFuel entry.key
              arguments store finalStore value completed
          simp only [CompiledEntry.SuccessfulResultHasNativeType,
            CompiledEntry.GraphResultHasType]
          exact ⟨definition.signature, signature, valueTyped⟩
      | typedValues arguments state =>
          simp [CompiledEntry.run, Invocation.kind] at ran
  | typedSource =>
      cases invocation <;> simp [CompiledEntry.run, Invocation.kind] at ran

/-- A successful source-typed facade result has the inferred result type of
the unique retained root specialization. -/
theorem CompiledEntry.run_typedSource_done_preserves_type
    (compiled : CompiledEntry)
    (arguments : List SourceTypedRuntime.Value)
    (initial : SourceTypedRuntime.RuntimeState) (options : RunOptions)
    {value : SourceTypedRuntime.Value}
    {finalState : SourceTypedRuntime.RuntimeState}
    (precondition : compiled.PreservationPrecondition
      (.typedValues arguments initial))
    (ran : compiled.run (.typedValues arguments initial) options =
      .ok (.typedSource (.done value finalState))) :
    compiled.SuccessfulResultHasNativeType
      (.typedSource (.done value finalState)) := by
  cases compiled
  rename_i program plan root executable
  cases executable with
  | core entry =>
      simp only [CompiledEntry.PreservationPrecondition] at precondition
  | callGraph entry =>
      simp only [CompiledEntry.PreservationPrecondition] at precondition
  | typedSource =>
      simp only [CompiledEntry.PreservationPrecondition] at precondition
      have completed : SourceTypedRuntime.runWithValidationFuel
          program.signatures plan root.key arguments
            options.inputValidationFuel options.executionFuel initial =
          .done value finalState := by
        simpa [CompiledEntry.run] using ran
      simp only [CompiledEntry.SuccessfulResultHasNativeType]
      exact SourceTypedRuntime.runWithValidationFuel_done_has_inferredBodyType
        program.signatures plan root.key arguments options.inputValidationFuel
        options.executionFuel initial finalState value root precondition completed

/-- On the typed backend, the common native-type conclusion is exactly the
artifact's public source result type, not a separate runtime declaration. -/
theorem CompiledEntry.runTyped_done_has_public_resultType
    (compiled : CompiledEntry)
    (arguments : List SourceTypedRuntime.Value)
    (initial : SourceTypedRuntime.RuntimeState) (options : RunOptions)
    {value : SourceTypedRuntime.Value}
    {finalState : SourceTypedRuntime.RuntimeState}
    (precondition : compiled.PreservationPrecondition
      (.typedValues arguments initial))
    (ran : compiled.runTyped arguments options initial =
      .ok (.typedSource (.done value finalState))) :
    compiled.TypedValueHasResultType value := by
  have native := compiled.run_typedSource_done_preserves_type arguments
    initial options precondition ran
  cases compiled
  rename_i program plan root executable
  cases executable with
  | core entry =>
      simp [CompiledEntry.PreservationPrecondition] at precondition
  | callGraph entry =>
      simp [CompiledEntry.PreservationPrecondition] at precondition
  | typedSource =>
      simpa [CompiledEntry.TypedValueHasResultType,
        CompiledEntry.SuccessfulResultHasNativeType,
        CompiledEntry.resultType] using native

/-- Whole-compiler successful-result preservation.  One theorem now covers
all three selected runtimes without erasing their native value/store domains.
The precondition is substantial only for direct Core (deep values/store) and
for the typed backend's sealed canonical-root provenance. -/
theorem CompiledEntry.run_preserves_successful_result_native_type
    (compiled : CompiledEntry) (invocation : Invocation)
    (options : RunOptions) (result : ExecutionResult)
    (precondition : compiled.PreservationPrecondition invocation)
    (ran : compiled.run invocation options = .ok result) :
    compiled.SuccessfulResultHasNativeType result := by
  cases result with
  | core result =>
      cases result with
      | done value finalStore =>
          cases invocation with
          | coreValues arguments store =>
              exact compiled.run_core_done_preserves_type arguments store
                options precondition ran
          | typedValues arguments state =>
              cases compiled
              rename_i program plan root executable
              cases executable <;>
                simp [CompiledEntry.run, Invocation.kind] at ran
      | outOfFuel state =>
          simp [CompiledEntry.SuccessfulResultHasNativeType]
      | fault error state =>
          simp [CompiledEntry.SuccessfulResultHasNativeType]
  | callGraph result =>
      cases result with
      | done value finalStore =>
          exact compiled.run_callGraph_done_preserves_type invocation options ran
      | outOfFuel store =>
          simp [CompiledEntry.SuccessfulResultHasNativeType]
      | fault error store =>
          simp [CompiledEntry.SuccessfulResultHasNativeType]
  | typedSource result =>
      cases result with
      | done value finalState =>
          cases invocation with
          | coreValues arguments store =>
              cases compiled
              rename_i program plan root executable
              cases executable with
              | core entry =>
                  simp only [CompiledEntry.run] at ran
                  split at ran <;> cases ran
              | callGraph entry =>
                  simp [CompiledEntry.run] at ran
              | typedSource =>
                  simp [CompiledEntry.run, Invocation.kind] at ran
          | typedValues arguments initial =>
              exact compiled.run_typedSource_done_preserves_type arguments
                initial options precondition ran
      | outOfFuel state =>
          simp [CompiledEntry.SuccessfulResultHasNativeType]
      | fault error state =>
          simp [CompiledEntry.SuccessfulResultHasNativeType]

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

/-- Raw-workspace compilation exposes the same canonical-root certificate as
the already-checked compile-once path. -/
theorem compile_hasCanonicalRoot
    (raw : Workspace.RawWorkspace) (seed : Seed) (options : CheckingOptions)
    (compiled : CompiledEntry)
    (compiledOk : compile raw seed options = .ok compiled) :
    compiled.HasCanonicalRoot := by
  unfold compile at compiledOk
  cases checked : checkProgram raw options.checkingFuel with
  | error errors =>
      rw [checked] at compiledOk
      cases compiledOk
  | ok program =>
      rw [checked] at compiledOk
      simp only [Except.mapError, bind, Except.bind] at compiledOk
      exact compileChecked_hasCanonicalRoot program seed
        options.toCompileOptions compiled compiledOk

/-- For a compiler-produced typed backend, the root provenance required by
the backend-native preservation theorem is automatic. -/
theorem compileChecked_typed_preservation_precondition
    (program : CheckedProgram) (seed : Seed) (options : CompileOptions)
    (compiled : CompiledEntry)
    (compiledOk : compileChecked program seed options = .ok compiled)
    (typedBackend : compiled.backend = .typedSource)
    (arguments : List SourceTypedRuntime.Value)
    (state : SourceTypedRuntime.RuntimeState) :
    compiled.PreservationPrecondition (.typedValues arguments state) := by
  have canonical := compileChecked_hasCanonicalRoot program seed options
    compiled compiledOk
  cases compiled
  rename_i checked plan root executable
  cases executable <;>
    simp_all [CompiledEntry.backend, CompiledEntry.PreservationPrecondition]

/-- The same provenance is available after one-shot raw-workspace
compilation, independently of the chosen validation and execution fuels. -/
theorem compile_typed_preservation_precondition
    (raw : Workspace.RawWorkspace) (seed : Seed)
    (options : CheckingOptions) (compiled : CompiledEntry)
    (compiledOk : compile raw seed options = .ok compiled)
    (typedBackend : compiled.backend = .typedSource)
    (arguments : List SourceTypedRuntime.Value)
    (state : SourceTypedRuntime.RuntimeState) :
    compiled.PreservationPrecondition (.typedValues arguments state) := by
  have canonical := compile_hasCanonicalRoot raw seed options compiled compiledOk
  cases compiled
  rename_i checked plan root executable
  cases executable <;>
    simp_all [CompiledEntry.backend, CompiledEntry.PreservationPrecondition]

/-- A compiler-produced typed entry needs no caller-supplied root certificate:
normal completion has the artifact's public source result type. -/
theorem compileChecked_runTyped_done_has_public_resultType
    (program : CheckedProgram) (seed : Seed) (compileOptions : CompileOptions)
    (compiled : CompiledEntry)
    (compiledOk : compileChecked program seed compileOptions = .ok compiled)
    (typedBackend : compiled.backend = .typedSource)
    (arguments : List SourceTypedRuntime.Value)
    (initial : SourceTypedRuntime.RuntimeState) (runOptions : RunOptions)
    {value : SourceTypedRuntime.Value}
    {finalState : SourceTypedRuntime.RuntimeState}
    (ran : compiled.runTyped arguments runOptions initial =
      .ok (.typedSource (.done value finalState))) :
    compiled.TypedValueHasResultType value := by
  exact compiled.runTyped_done_has_public_resultType arguments initial
    runOptions
    (compileChecked_typed_preservation_precondition program seed
      compileOptions compiled compiledOk typedBackend arguments initial)
    ran

/-- End-to-end one-shot execution inherits the three-backend successful-result
preservation theorem from the exact artifact produced in its compile phase. -/
theorem run_of_compiled_preserves_successful_result_native_type
    (raw : Workspace.RawWorkspace) (seed : Seed) (invocation : Invocation)
    (limits : Limits) (compiled : CompiledEntry) (result : ExecutionResult)
    (compiledOk : compile raw seed limits.toCheckingOptions = .ok compiled)
    (precondition : compiled.PreservationPrecondition invocation)
    (ran : SourceCompiler.run raw seed invocation limits = .ok result) :
    compiled.SuccessfulResultHasNativeType result := by
  rw [run_of_compiled raw seed invocation limits compiled compiledOk] at ran
  cases executed : compiled.run invocation limits.toRunOptions with
  | error error =>
      rw [executed] at ran
      cases ran
  | ok actual =>
      rw [executed] at ran
      cases ran
      exact compiled.run_preserves_successful_result_native_type invocation
        limits.toRunOptions result precondition executed

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
