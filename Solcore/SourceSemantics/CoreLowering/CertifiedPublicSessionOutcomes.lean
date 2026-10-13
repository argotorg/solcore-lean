import Solcore.SourceSemantics.CoreLowering.CertifiedPublicSessionSteps
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalSessionInitialScalarForward
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalSessionInitialScalarStep
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalSessionInitialFailureForward
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalSessionInitialFailureStep
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalSessionRegistryFailureForward
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalSessionRegistryFailureStep

/-! Certified sessions can begin with scalar success or a Source fault. Later
failures retain the same physical history and use the actual input registry. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CertifiedPublicSession
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedFunctionValues (Header)
open RecursiveNamedPublicPhysicalSessionState (StartedCall Call SourceCall)
open RecursiveNamedPublicScalarResults (ScalarOutput)

variable {recipe : SourceCoreIndexedSession.Recipe} {issued : Issued recipe}
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
  {options : SourceCoreExecution.RunOptions}

theorem Initial.forward_scalar
    {call : StartedCall session key publicArguments options} (initial : Initial issued call)
    (scalar : ScalarOutput)
    (simple : ∀ value ∈ publicArguments, SourceCoreIndexedSession.SimplePublic value)
    (inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      initial.header.function.context publicArguments initial.header.types)
    {arguments : List Dynamic.Value}
    (inputMeanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments)
    (rawType : initial.header.function.resultType = scalar.sourceType)
    (nativeType : initial.header.output = scalar.nativeType)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap}
    (trace : SourceCall initial.header initial.header invocation ⟨[]⟩ arguments (.value scalar.source) after) :
    RecursiveNamedPublicPhysicalSessionScalarForward.ForwardAt (entries := []) issued.catalog.rows
      initial.header issued.initial issued.support.profile recipe scalar call after :=
  RecursiveNamedPublicPhysicalSessionInitialScalarForward.first_scalar issued.catalog.rows issued.prepared
    initial.header initial.header issued.support issued.catalog.distinct scalar call initial.start simple
    inputTypes inputMeanings rawType nativeType trace

theorem Initial.reflect_scalar
    {call : Call session key publicArguments options} (initial : Initial issued call.toStartedCall)
    (scalar : ScalarOutput) (returned : call.completion.value = scalar.publicValue)
    (simple : ∀ value ∈ publicArguments, SourceCoreIndexedSession.SimplePublic value)
    (inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      initial.header.function.context publicArguments initial.header.types)
    {arguments : List Dynamic.Value}
    (inputMeanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments)
    (rawType : initial.header.function.resultType = scalar.sourceType)
    (nativeType : initial.header.output = scalar.nativeType)
    (invocation : Staging.Recursive.Scope) :
    ∃ after : issued.State initial.header call.completion.session [],
      SourceCall initial.header initial.header invocation ⟨[]⟩ arguments (.value scalar.source) after.heap := by
  obtain ⟨descriptor⟩ := header_descriptor initial.header
  exact RecursiveNamedPublicPhysicalSessionInitialScalarStep.first_scalar issued.catalog.rows issued.prepared
    initial.header initial.header issued.support issued.catalog.distinct scalar call returned initial.start simple
    inputTypes inputMeanings rawType nativeType descriptor invocation

theorem Initial.forward_failure
    {call : StartedCall session key publicArguments options} (initial : Initial issued call)
    (simple : ∀ value ∈ publicArguments, SourceCoreIndexedSession.SimplePublic value)
    (inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      initial.header.function.context publicArguments initial.header.types)
    {arguments : List Dynamic.Value}
    (inputMeanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap} {failure : Staging.Recursive.Failure}
    (trace : SourceCall initial.header initial.header invocation ⟨[]⟩ arguments (.fault failure) after) :
    RecursiveNamedPublicPhysicalSessionFailureForward.FailureForwardAt (entries := []) issued.catalog.rows
      initial.header issued.initial issued.support.profile recipe failure call after :=
  RecursiveNamedPublicPhysicalSessionInitialFailureForward.first_failure issued.catalog.rows issued.prepared
    initial.header initial.header issued.support issued.catalog.distinct call initial.start simple
    inputTypes inputMeanings trace

theorem Initial.reflect_failure
    {call : StartedCall session key publicArguments options} (initial : Initial issued call)
    (returned : SourceCoreExecution.Session artifact) (reason : Word)
    (failedCall : session.RunAt key publicArguments options (.ok (.failed reason returned)))
    (simple : ∀ value ∈ publicArguments, SourceCoreIndexedSession.SimplePublic value)
    (inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      initial.header.function.context publicArguments initial.header.types)
    {arguments : List Dynamic.Value}
    (inputMeanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments)
    (invocation : Staging.Recursive.Scope) :
    ∃ failure, ∃ after : issued.State initial.header returned [],
      SourceCall initial.header initial.header invocation ⟨[]⟩ arguments (.fault failure) after.heap ∧
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults after.receiving.result.diagnostics failure reason := by
  obtain ⟨descriptor⟩ := header_descriptor initial.header
  exact RecursiveNamedPublicPhysicalSessionInitialFailureStep.first_failure issued.catalog.rows issued.prepared
    initial.header initial.header issued.support issued.catalog.distinct call returned reason failedCall initial.start simple
    inputTypes inputMeanings descriptor invocation

variable (issued : Issued recipe)
  {anchor : Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
  {entries : List RecursiveNamedPublicFunctionHistory.Entry}
  (state : issued.State anchor session entries)

theorem Issued.forward_failure
    (call : StartedCall session key publicArguments options)
    (request : RecursiveNamedPublicHistoryFrontdoor.Started (headers issued.catalog.rows) issued.prepared
      call.checkpoint state.session key publicArguments options.inputValidationFuel state.world state.store)
    {arguments : List Dynamic.Value}
    (inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments)
    (ready : session.ExportsReady)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap} {failure : Staging.Recursive.Failure}
    (trace : SourceCall anchor request.header invocation state.heap arguments (.fault failure) after) :
    RecursiveNamedPublicPhysicalSessionFailureForward.FailureForwardAt (entries := entries)
      issued.catalog.rows anchor issued.initial issued.support.profile recipe failure call after :=
  RecursiveNamedPublicPhysicalSessionFailureForward.forward_call_at_input_registry issued.support
    issued.prepared state call request inputs ready trace

theorem Issued.reflect_failure
    (call : StartedCall session key publicArguments options)
    (returned : SourceCoreExecution.Session artifact) (reason : Word)
    (failedCall : session.RunAt key publicArguments options (.ok (.failed reason returned)))
    (request : RecursiveNamedPublicHistoryFrontdoor.Started (headers issued.catalog.rows) issued.prepared
      call.checkpoint state.session key publicArguments options.inputValidationFuel state.world state.store)
    {arguments : List Dynamic.Value}
    (inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments)
    (invocation : Staging.Recursive.Scope) :
    ∃ failure, ∃ after : issued.State anchor returned entries,
      SourceCall anchor request.header invocation state.heap arguments (.fault failure) after.heap ∧
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults after.receiving.result.diagnostics failure reason := by
  obtain ⟨descriptor⟩ := header_descriptor request.header
  exact RecursiveNamedPublicPhysicalSessionFailureStep.State.failed_call_at_input_registry issued.support
    issued.prepared state call returned reason failedCall request inputs descriptor invocation

end Solcore.SourceSemantics.CoreLowering.CertifiedPublicSession
