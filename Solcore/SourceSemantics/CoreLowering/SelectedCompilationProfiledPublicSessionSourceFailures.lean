import Solcore.SourceSemantics.CoreLowering.SelectedCompilationProfiledPublicSessionFailures
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicSourceCallOutcomes

/-! Actual public completions reflect to independent Dynamic applications at
the same issued session state. Failure keeps its semantic or staging origin
and the exact public diagnostic relation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationCertifiedPublicSession
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedFunctionValues (Header)
open SelectedCompilationPublicSessionState (StartedCall FunctionCall Call SourceCall PlainValue FailureProjection)
open RecursiveNamedPublicScalarResults (ScalarOutput)

variable {recipe : SourceCoreIndexedSession.Recipe} {issued : Profiled recipe}
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
  {options : SourceCoreExecution.RunOptions}

/-- The semantic branch has a Dynamic fault; the stage branch retains the
actual rejected guard. Both retain the exact completed public state. -/
theorem Profiled.reflect_initial_failure_plain
    {call : StartedCall session key publicArguments options} (initial : Initial issued.toIssued call)
    (returned : SourceCoreExecution.Session artifact) (reason : Word)
    (failedCall : session.RunAt key publicArguments options (.ok (.failed reason returned)))
    (simple : ∀ value ∈ publicArguments, SourceCoreIndexedSession.SimplePublic value)
    (inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      initial.header.function.context publicArguments initial.header.types)
    {arguments : List Dynamic.Value}
    (inputMeanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments)
    (invocation : Staging.Recursive.Scope) :
    ∃ failure, ∃ after : issued.toIssued.State initial.header returned [],
      SourceCall initial.header initial.header invocation ⟨[]⟩ arguments (.fault failure) after.heap ∧
      FailureProjection initial.header initial.header invocation ⟨[]⟩ arguments failure after.heap ∧
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults after.receiving.result.diagnostics failure reason := by
  obtain ⟨failure, after, trace, diagnostic⟩ :=
    Profiled.reflect_initial_failure initial returned reason failedCall simple inputTypes inputMeanings invocation
  exact ⟨failure, after, trace, trace.failure_plain, diagnostic⟩

variable (issued : Profiled recipe)
  {anchor : Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
  {entries : List RecursiveNamedPublicFunctionHistory.Entry}
  (state : issued.toIssued.State anchor session entries)

theorem Profiled.reflect_failure_plain
    (call : StartedCall session key publicArguments options)
    (returned : SourceCoreExecution.Session artifact) (reason : Word)
    (failedCall : session.RunAt key publicArguments options (.ok (.failed reason returned)))
    (request : RecursiveNamedPublicHistoryFrontdoor.Started (headers issued.catalog.rows) issued.prepared
      call.checkpoint state.session key publicArguments options.inputValidationFuel state.world state.store)
    {arguments : List Dynamic.Value}
    (inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments)
    (invocation : Staging.Recursive.Scope) :
    ∃ failure, ∃ after : issued.toIssued.State anchor returned entries,
      SourceCall anchor request.header invocation state.heap arguments (.fault failure) after.heap ∧
      FailureProjection anchor request.header invocation state.heap arguments failure after.heap ∧
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults after.receiving.result.diagnostics failure reason := by
  obtain ⟨failure, after, trace, diagnostic⟩ :=
    issued.reflect_failure state call returned reason failedCall request inputs invocation
  exact ⟨failure, after, trace, trace.failure_plain, diagnostic⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationCertifiedPublicSession
