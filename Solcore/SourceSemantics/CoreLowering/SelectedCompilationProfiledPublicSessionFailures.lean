import Solcore.SourceSemantics.CoreLowering.SelectedCompilationProfiledPublicSession
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCertifiedPublicSessionSteps
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionInitialScalarForward
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionInitialScalarStep
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionInitialFailureForward
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionInitialFailureStep
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionRegistryFailureForward
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionRegistryFailureStep

/-! Certified sessions can begin with scalar success or a Source fault. Later
failures retain the same physical history and use the actual input registry. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationCertifiedPublicSession
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedFunctionValues (Header)
open SelectedCompilationPublicSessionState (StartedCall Call SourceCall)
open RecursiveNamedPublicScalarResults (ScalarOutput)

variable {recipe : SourceCoreIndexedSession.Recipe} {issued : Profiled recipe}
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
  {options : SourceCoreExecution.RunOptions}

theorem Profiled.forward_initial_failure
    {call : StartedCall session key publicArguments options} (initial : Initial issued.toIssued call)
    (simple : ∀ value ∈ publicArguments, SourceCoreIndexedSession.SimplePublic value)
    (inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      initial.header.function.context publicArguments initial.header.types)
    {arguments : List Dynamic.Value}
    (inputMeanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap} {failure : Staging.Recursive.Failure}
    (trace : SourceCall initial.header initial.header invocation ⟨[]⟩ arguments (.fault failure) after) :
    SelectedCompilationPublicSessionFailureForward.FailureForwardAt (entries := []) issued.catalog.rows
      initial.header issued.initial issued.support.profile recipe failure call after :=
  SelectedCompilationPublicSessionInitialFailureForward.first_failure issued.catalog.rows issued.prepared
    initial.header initial.header issued.support issued.registryBodies issued.catalog.distinct call initial.start simple
    inputTypes inputMeanings trace

theorem Profiled.reflect_initial_failure
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
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults after.receiving.result.diagnostics failure reason := by
  obtain ⟨descriptor⟩ := header_descriptor initial.header
  exact SelectedCompilationPublicSessionInitialFailureStep.first_failure issued.catalog.rows issued.prepared
    initial.header initial.header issued.support issued.registryBodies issued.catalog.distinct call returned reason failedCall initial.start simple
    inputTypes inputMeanings descriptor invocation

variable (issued : Profiled recipe)
  {anchor : Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
  {entries : List RecursiveNamedPublicFunctionHistory.Entry}
  (state : issued.toIssued.State anchor session entries)

theorem Profiled.forward_failure
    (call : StartedCall session key publicArguments options)
    (request : RecursiveNamedPublicHistoryFrontdoor.Started (headers issued.catalog.rows) issued.prepared
      call.checkpoint state.session key publicArguments options.inputValidationFuel state.world state.store)
    {arguments : List Dynamic.Value}
    (inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments)
    (ready : session.ExportsReady)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap} {failure : Staging.Recursive.Failure}
    (trace : SourceCall anchor request.header invocation state.heap arguments (.fault failure) after) :
    SelectedCompilationPublicSessionFailureForward.FailureForwardAt (entries := entries)
      issued.catalog.rows anchor issued.initial issued.support.profile recipe failure call after :=
  SelectedCompilationPublicSessionFailureForward.forward_call_at_input_registry issued.support issued.registryBodies
    issued.prepared state call request inputs ready trace

theorem Profiled.reflect_failure
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
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults after.receiving.result.diagnostics failure reason := by
  obtain ⟨descriptor⟩ := header_descriptor request.header
  exact SelectedCompilationPublicSessionFailureStep.State.failed_call_at_input_registry issued.support issued.registryBodies
    issued.prepared state call returned reason failedCall request inputs descriptor invocation

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationCertifiedPublicSession
