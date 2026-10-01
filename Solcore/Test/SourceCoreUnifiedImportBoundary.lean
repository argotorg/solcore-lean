import Solcore.Frontend.Current

/-! The current public frontend exposes one Core execution API and pure source
boundary certificates. The conventional compiler namespace re-exports the same
definitions; backend selection and the historical source evaluator are absent. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceTypedRuntime.runTrusted
#check_failure Solcore.Frontend.SourceTypedRuntime.runWithValidationFuel
#check_failure Solcore.Frontend.SourceTypedRuntime.runDeepCertifiedWithValidationFuel
#check_failure Solcore.Frontend.SourceTypedRuntime.run?
#check_failure Solcore.Frontend.SourceTypedRuntime.ExpressionResult
#check_failure Solcore.Frontend.SourceTypedRuntime.FlowOutcome
#check_failure Solcore.Frontend.SourceTypedRuntime.ResolvedPlace
#check_failure Solcore.Frontend.SourceTypedRuntime.updateResolvedValue
#check_failure Solcore.Frontend.SourceTypedRuntime.writeResolvedPlace

#check Solcore.Frontend.SourceCoreUnifiedCompilation.prepare
#check Solcore.Frontend.SourceCoreUnifiedCompilation.Compiled.run
#check Solcore.Frontend.SourceCompiler.compileChecked
#check Solcore.Frontend.SourceCompiler.compileEntry
#check Solcore.Frontend.SourceCompiler.compileStaticWord
#check Solcore.Frontend.SourceCompiler.Compiled.open
#check Solcore.Frontend.SourceCompiler.Session.run
#check Solcore.Frontend.SourceCompiler.Session.invokePacked
#check Solcore.Frontend.SourceCompiler.Session.authenticate
#check Solcore.Frontend.SourceCompiler.Checkpoint.resume
#check Solcore.Frontend.SourceCompiler.Options.compilationFuel
#check Solcore.Frontend.SourceCompiler.RunOptions.executionFuel
#check Solcore.Frontend.SourceCompiler.Authentication.typed
#check_failure Solcore.Frontend.SourceCompiler.Backend
#check_failure Solcore.Frontend.SourceCompiler.BackendPreference
#check_failure Solcore.Frontend.SourceCompiler.BackendRejection
#check_failure Solcore.Frontend.SourceCompiler.Invocation
#check_failure Solcore.Frontend.SourceCompiler.InvocationKind
#check_failure Solcore.Frontend.SourceCompiler.ExecutionResult
#check_failure Solcore.Frontend.SourceCompiler.CompileOptions
#check_failure Solcore.Frontend.SourceCompiler.Options.backendPreference
#check_failure Solcore.Frontend.SourceCompiler.CompiledEntry
#check_failure Solcore.Frontend.SourceCompiler.CompiledEntry.runTypedWithCheckpoint
#check_failure Solcore.Frontend.SourceCompiler.CompiledEntry.TypedCheckpoint.resume
#check_failure Solcore.Frontend.SourceCompiler.TypedCheckpoint
#check_failure Solcore.Frontend.SourceCompiler.Value.cellRef
#check_failure Solcore.Frontend.SourceCompiler.Value.closure
#check_failure Solcore.Frontend.SourceCompiler.Value.global
#check_failure Solcore.Frontend.SourceCompiler.Value.builtin
#check_failure Solcore.Frontend.SourceCompiler.Session.payload
#check_failure Solcore.Frontend.SourceCompiler.Checkpoint.payload
#check_failure Solcore.Frontend.SourceCompilerSession.Compiled
#check Solcore.Frontend.SourceTypedRuntime.Value.HasPreparedType
#check Solcore.Frontend.SourceTypedRuntime.PreparedDeepExecution
#check Solcore.Frontend.SourceTypedRuntime.checkedLambdaNode_provenance
#check Solcore.Frontend.SourceTypedRuntime.closure_hasPlanCode_checkedLambdaNode
#check Solcore.Frontend.SourceTypedRuntime.exactSpecialization
#check Solcore.Frontend.SourceTypedRuntime.validateExecutablePlan
#check Solcore.Frontend.SourceTypedRuntime.prepareExecutablePlanEvidence

namespace Tests.SourceCoreUnifiedImportBoundary
open Solcore Solcore.Frontend

example : SourceCompiler.Compiled = SourceCoreExecution.Compiled := rfl
example : SourceCompiler.Value = SourceCoreExecution.Value := rfl
example : SourceCompiler.Handle = SourceCoreExecution.Handle := rfl
example : SourceCompiler.Artifact = SourceCoreExecution.Artifact := rfl
example (artifact : SourceCompiler.Artifact) :
    SourceCompiler.Session artifact = SourceCoreExecution.Session artifact := rfl
example (artifact : SourceCompiler.Artifact) :
    SourceCompiler.Checkpoint artifact = SourceCoreExecution.Checkpoint artifact := rfl
example : @SourceCompiler.prepare = @SourceCoreExecution.prepare := rfl
example : @SourceCompiler.compileChecked = @SourceCoreExecution.compileChecked := rfl
example : @SourceCompiler.compileEntry = @SourceCoreExecution.compileEntry := rfl
example : @SourceCompiler.compileStaticWord = @SourceCoreExecution.compileStaticWord := rfl
example : @SourceCompiler.Session.run = @SourceCoreExecution.Session.run := rfl
example : @SourceCompiler.Session.invokePacked = @SourceCoreExecution.Session.invokePacked := rfl
example : @SourceCompiler.Checkpoint.resume = @SourceCoreExecution.Checkpoint.resume := rfl
example : @SourceCompiler.Seed.declaration = @SourceCoreCompiler.Seed.declaration := rfl
example : @SourceCompiler.Seed.named = @SourceCoreCompiler.Seed.named := rfl
example (word : Core.Word) : SourceCompiler.Value.word word = SourceCorePublicValues.Value.word word := rfl
example {artifact : SourceCompiler.Artifact} (completion : SourceCompiler.Completion artifact) :
    completion.session.Authenticates completion.boundaryFuel completion.sourceType completion.value :=
  SourceCompiler.Completion.typed completion

end Tests.SourceCoreUnifiedImportBoundary
