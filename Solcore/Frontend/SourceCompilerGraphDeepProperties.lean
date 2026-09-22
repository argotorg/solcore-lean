import Solcore.Frontend.SourceCompilerProperties
import Solcore.Frontend.SourceRuntimeEntryDeepProperties

/-! Conditional deep preservation through the public graph-backend facade. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCompiler

namespace CompiledEntry

/-- The public deep graph result refines the existing native result-tag
certificate when the artifact's public result projection is known. -/
theorem GraphDeepResult.native
    (compiled : CompiledEntry) (initialWorld : Core.StoreTyping)
    (value : SourceRuntime.Value) (finalStore : Core.Store)
    (projection : compiled.HasPublicResultProjection)
    (deep : compiled.GraphDeepResult initialWorld value finalStore) :
    compiled.SuccessfulResultHasNativeType
      (.callGraph (.done value finalStore)) := by
  cases compiled
  rename_i program plan root executable
  cases executable with
  | core entry => simp only [GraphDeepResult] at deep
  | typedSource => simp only [GraphDeepResult] at deep
  | callGraph entry =>
      obtain ⟨publicType, finalWorld, lowered, _, _, valueTyping⟩ := deep
      obtain ⟨signature, found, resultType⟩ :=
        entry.signatureResultType
      change root.function.inferredBodyType = entry.sourceBodyType at projection
      have publicEqualsEntry : publicType = entry.resultType := by
        have loweredEntry :
            SourceRuntimeLinking.lowerType entry.sourceBodyType =
              .ok publicType := by
          simpa [CompiledEntry.resultType, projection] using lowered
        rw [entry.resultType_eq_source] at loweredEntry
        exact (Except.ok.inj loweredEntry).symm
      simp only [SuccessfulResultHasNativeType, GraphResultHasType]
      exact ⟨signature, found, by
        simpa [publicEqualsEntry, resultType] using valueTyping.hasType⟩

/-- The actual public `CompiledEntry.run` graph branch preserves deep source
value and final-store typing after checker-certified compilation, deep caller
input typing, and a public-result projection certificate. -/
theorem run_callGraph_done_deep
    (compiled : CompiledEntry) (arguments : List Core.Value)
    (initialStore : Core.Store) (options : RunOptions)
    (value : SourceRuntime.Value) (finalStore : Core.Store)
    (input : compiled.GraphDeepInput arguments initialStore)
    (projection : compiled.HasPublicResultProjection)
    (ran : compiled.run (.coreValues arguments initialStore) options =
      .ok (.callGraph (.done value finalStore))) :
    ∃ initialWorld,
      compiled.GraphDeepResult initialWorld value finalStore := by
  cases compiled
  rename_i program plan root executable
  cases executable with
  | core entry => simp only [GraphDeepInput] at input
  | typedSource => simp only [GraphDeepInput] at input
  | callGraph entry =>
      obtain ⟨world, argumentsTyping, storeTyping⟩ := input
      have completed : entry.program.run options.executionFuel entry.key
          arguments initialStore = .done value finalStore := by
        simpa [CompiledEntry.run] using ran
      obtain ⟨finalWorld, extension, finalStoreTyping, valueTyping⟩ :=
        entry.run_done_deep argumentsTyping storeTyping completed
      change root.function.inferredBodyType = entry.sourceBodyType at projection
      have lowered : SourceRuntimeLinking.lowerType
          root.function.inferredBodyType = .ok entry.resultType := by
        simpa [projection] using entry.resultType_eq_source
      refine ⟨world, ?_⟩
      simp only [GraphDeepResult]
      exact ⟨entry.resultType, finalWorld, lowered, extension,
        finalStoreTyping, valueTyping⟩

end CompiledEntry

/-- Successful checked-program compilation supplies the public-result
projection certificate required by the graph deep-preservation facade. -/
theorem compileChecked_runGraph_done_deep
    (program : CheckedProgram) (seed : Seed)
    (compileOptions : CompileOptions) (compiled : CompiledEntry)
    (compiledOk : compileChecked program seed compileOptions = .ok compiled)
    (arguments : List Core.Value) (initialStore : Core.Store)
    (runOptions : RunOptions) (value : SourceRuntime.Value)
    (finalStore : Core.Store)
    (input : compiled.GraphDeepInput arguments initialStore)
    (ran : compiled.run (.coreValues arguments initialStore) runOptions =
      .ok (.callGraph (.done value finalStore))) :
    ∃ initialWorld,
      compiled.GraphDeepResult initialWorld value finalStore := by
  exact compiled.run_callGraph_done_deep arguments initialStore runOptions
    value finalStore input
    (compileChecked_hasPublicResultProjection program seed compileOptions
      compiled compiledOk) ran

/-- The one-shot raw-workspace compiler likewise supplies the public-result
projection certificate; the caller still provides genuinely deep arguments
and an initial store in one Core world. -/
theorem compile_runGraph_done_deep
    (raw : Workspace.RawWorkspace) (seed : Seed)
    (checkingOptions : CheckingOptions) (compiled : CompiledEntry)
    (compiledOk : compile raw seed checkingOptions = .ok compiled)
    (arguments : List Core.Value) (initialStore : Core.Store)
    (runOptions : RunOptions) (value : SourceRuntime.Value)
    (finalStore : Core.Store)
    (input : compiled.GraphDeepInput arguments initialStore)
    (ran : compiled.run (.coreValues arguments initialStore) runOptions =
      .ok (.callGraph (.done value finalStore))) :
    ∃ initialWorld,
      compiled.GraphDeepResult initialWorld value finalStore := by
  exact compiled.run_callGraph_done_deep arguments initialStore runOptions
    value finalStore input
    (compile_hasPublicResultProjection raw seed checkingOptions compiled
      compiledOk) ran

end Solcore.Frontend.SourceCompiler
