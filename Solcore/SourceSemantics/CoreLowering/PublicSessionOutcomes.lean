import Solcore.SourceSemantics.CoreLowering.PublicSessions
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.PublicSessionSteps
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.MethodRoots
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.PublicDirectSessions
import Solcore.SourceSemantics.Staging.RecursiveCallableErasure

/-!
# Public session outcomes

One call of an issued session, in both directions.

Main declarations:
- `SelectedCompilationCertifiedPublicSession.Issued.forward_scalar`,
  `SelectedCompilationCertifiedPublicSession.Issued.forward_function` and
  `SelectedCompilationCertifiedPublicSession.Profiled.forward_failure`, from Source to the
  public result;
- `SelectedCompilationCertifiedPublicSession.Issued.reflect_scalar_plain`,
  `SelectedCompilationCertifiedPublicSession.Issued.reflect_function_plain` and
  `SelectedCompilationCertifiedPublicSession.Profiled.reflect_failure_plain`, back to
  independent Dynamic applications at the same session state;
- `SelectedCompilationCertifiedPublicSession.Initial.reflect_scalar_plain` and
  `SelectedCompilationCertifiedPublicSession.Profiled.reflect_initial_failure_plain`, the
  first call;
- `SelectedCompilationCertifiedPublicSession.Issued.reflect_direct_scalar_plain` and
  `SelectedCompilationCertifiedPublicSession.Profiled.reflect_direct_failure_plain`,
  direct calls through a handle.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationCertifiedPublicSessionSteps
/-! Session steps use the automatically issued body families and the actual
input registry. Source traces and typed public inputs remain independent. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationCertifiedPublicSession
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedFunctionValues (Header)
open SelectedCompilationPublicSessionState (StartedCall FunctionCall Call SourceCall)
open RecursiveNamedPublicScalarResults (ScalarOutput)

variable {recipe : SourceCoreIndexedSession.Recipe} (issued : Issued recipe)
  {anchor : Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {entries : List RecursiveNamedPublicFunctionHistory.Entry}
  (state : issued.State anchor session entries)
  {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
  {options : SourceCoreExecution.RunOptions}

theorem Issued.forward_function
    (call : StartedCall session key publicArguments options)
    (request : RecursiveNamedPublicHistoryFrontdoor.Started (headers issued.catalog.rows) issued.prepared
      call.checkpoint state.session key publicArguments options.inputValidationFuel state.world state.store)
    {arguments : List Dynamic.Value}
    (inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments)
    {parameterType resultType : TypeSystem.Ty}
    (rawType : request.header.function.resultType = .function parameterType resultType)
    (ready : session.ExportsReady)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap} {source : Dynamic.Value}
    (trace : SourceCall anchor request.header invocation state.heap arguments (.value source) after) :
    SelectedCompilationPublicSessionFunctionForward.FunctionForwardAt (entries := entries)
      issued.catalog.rows anchor issued.initial issued.support.profile recipe call parameterType resultType source after :=
  SelectedCompilationPublicSessionFunctionForward.forward_function_at_input_registry issued.support
    issued.prepared state call request inputs rawType ready trace

theorem Issued.forward_scalar
    (scalar : ScalarOutput) (call : StartedCall session key publicArguments options)
    (request : RecursiveNamedPublicHistoryFrontdoor.Started (headers issued.catalog.rows) issued.prepared
      call.checkpoint state.session key publicArguments options.inputValidationFuel state.world state.store)
    {arguments : List Dynamic.Value}
    (inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments)
    (rawType : request.header.function.resultType = scalar.sourceType)
    (nativeType : request.header.output = scalar.nativeType)
    (ready : session.ExportsReady)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap}
    (trace : SourceCall anchor request.header invocation state.heap arguments (.value scalar.source) after) :
    SelectedCompilationPublicSessionScalarForward.ForwardAt (entries := entries)
      issued.catalog.rows anchor issued.initial issued.support.profile recipe scalar call after :=
  SelectedCompilationPublicSessionScalarForward.forward_call_at_input_registry issued.support
    issued.prepared state scalar call request inputs rawType nativeType ready trace

theorem Issued.reflect_function
    (call : FunctionCall session key publicArguments options)
    (request : RecursiveNamedPublicHistoryFrontdoor.Started (headers issued.catalog.rows) issued.prepared
      call.checkpoint state.session key publicArguments options.inputValidationFuel state.world state.store)
    {arguments : List Dynamic.Value}
    (inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments)
    (invocation : Staging.Recursive.Scope) :
    ∃ retained : RecursiveNamedPublicFunctionHistory.Entry,
      retained.sourceType = request.header.function.resultType ∧ retained.handle = call.handle ∧
      call.handle.sourceType = request.header.function.resultType ∧
      ∃ after : issued.State anchor call.completion.session (entries ++ [retained]),
        SourceCall anchor request.header invocation state.heap arguments (.value retained.source) after.heap := by
  obtain ⟨descriptor⟩ := header_descriptor request.header
  exact SelectedCompilationPublicSessionFunctionStep.State.make_typed_handle_at_input_registry issued.support
    issued.prepared state call request inputs descriptor invocation

theorem Issued.reflect_scalar
    (scalar : ScalarOutput) (call : Call session key publicArguments options)
    (returned : call.completion.value = scalar.publicValue)
    (request : RecursiveNamedPublicHistoryFrontdoor.Started (headers issued.catalog.rows) issued.prepared
      call.checkpoint state.session key publicArguments options.inputValidationFuel state.world state.store)
    {arguments : List Dynamic.Value}
    (inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments)
    (rawType : request.header.function.resultType = scalar.sourceType)
    (nativeType : request.header.output = scalar.nativeType)
    (invocation : Staging.Recursive.Scope) :
    ∃ after : issued.State anchor call.completion.session entries,
      SourceCall anchor request.header invocation state.heap arguments (.value scalar.source) after.heap := by
  obtain ⟨descriptor⟩ := header_descriptor request.header
  exact SelectedCompilationPublicSessionScalarStep.State.finished_call_at_input_registry issued.support
    issued.prepared state scalar call returned request inputs rawType nativeType descriptor invocation

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationCertifiedPublicSession
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationCertifiedPublicSessionOutcomes
/-! Successful scalar calls retain their actual session and input registry. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationCertifiedPublicSession
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedFunctionValues (Header)
open SelectedCompilationPublicSessionState (StartedCall Call SourceCall)
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
    SelectedCompilationPublicSessionScalarForward.ForwardAt (entries := []) issued.catalog.rows
      initial.header issued.initial issued.support.profile recipe scalar call after :=
  SelectedCompilationPublicSessionInitialScalarForward.first_scalar issued.catalog.rows issued.prepared
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
  exact SelectedCompilationPublicSessionInitialScalarStep.first_scalar issued.catalog.rows issued.prepared
    initial.header initial.header issued.support issued.catalog.distinct scalar call returned initial.start simple
    inputTypes inputMeanings rawType nativeType descriptor invocation

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationCertifiedPublicSession
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationCertifiedPublicSessionSourceOutcomes
/-! Successful public completions reflect to independent Dynamic applications
at the same issued session state, callable and reached Source heap. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationCertifiedPublicSession
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedFunctionValues (Header)
open SelectedCompilationPublicSessionState (StartedCall FunctionCall Call SourceCall PlainValue)
open RecursiveNamedPublicScalarResults (ScalarOutput)

variable {recipe : SourceCoreIndexedSession.Recipe} {issued : Issued recipe}
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
  {options : SourceCoreExecution.RunOptions}

theorem Initial.reflect_function_plain
    {call : FunctionCall session key publicArguments options}
    (initial : Initial issued call.toCall.toStartedCall)
    (simple : ∀ value ∈ publicArguments, SourceCoreIndexedSession.SimplePublic value)
    (inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      initial.header.function.context publicArguments initial.header.types)
    {arguments : List Dynamic.Value}
    (inputMeanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments)
    (invocation : Staging.Recursive.Scope) :
    ∃ retained : RecursiveNamedPublicFunctionHistory.Entry,
      retained.sourceType = initial.header.function.resultType ∧ retained.handle = call.handle ∧
      ∃ state : issued.State initial.header call.completion.session [retained],
        PlainValue initial.header initial.header invocation ⟨[]⟩ arguments retained.source state.heap := by
  obtain ⟨retained, sourceType, handle, state, trace⟩ :=
    initial.reflect_function simple inputTypes inputMeanings invocation
  exact ⟨retained, sourceType, handle, state, trace.value_plain⟩

theorem Initial.reflect_scalar_plain
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
      PlainValue initial.header initial.header invocation ⟨[]⟩ arguments scalar.source after.heap := by
  obtain ⟨after, trace⟩ := initial.reflect_scalar scalar returned simple inputTypes inputMeanings rawType nativeType invocation
  exact ⟨after, trace.value_plain⟩

variable (issued : Issued recipe)
  {anchor : Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
  {entries : List RecursiveNamedPublicFunctionHistory.Entry}
  (state : issued.State anchor session entries)

theorem Issued.reflect_function_plain
    (call : FunctionCall session key publicArguments options)
    (request : RecursiveNamedPublicHistoryFrontdoor.Started (headers issued.catalog.rows) issued.prepared
      call.checkpoint state.session key publicArguments options.inputValidationFuel state.world state.store)
    {arguments : List Dynamic.Value}
    (inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments)
    (invocation : Staging.Recursive.Scope) :
    ∃ retained : RecursiveNamedPublicFunctionHistory.Entry,
      retained.sourceType = request.header.function.resultType ∧ retained.handle = call.handle ∧
      call.handle.sourceType = request.header.function.resultType ∧
      ∃ after : issued.State anchor call.completion.session (entries ++ [retained]),
        PlainValue anchor request.header invocation state.heap arguments retained.source after.heap := by
  obtain ⟨retained, sourceType, handle, handleType, after, trace⟩ :=
    issued.reflect_function state call request inputs invocation
  exact ⟨retained, sourceType, handle, handleType, after, trace.value_plain⟩

theorem Issued.reflect_scalar_plain
    (scalar : ScalarOutput) (call : Call session key publicArguments options)
    (returned : call.completion.value = scalar.publicValue)
    (request : RecursiveNamedPublicHistoryFrontdoor.Started (headers issued.catalog.rows) issued.prepared
      call.checkpoint state.session key publicArguments options.inputValidationFuel state.world state.store)
    {arguments : List Dynamic.Value}
    (inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments)
    (rawType : request.header.function.resultType = scalar.sourceType)
    (nativeType : request.header.output = scalar.nativeType)
    (invocation : Staging.Recursive.Scope) :
    ∃ after : issued.State anchor call.completion.session entries,
      PlainValue anchor request.header invocation state.heap arguments scalar.source after.heap := by
  obtain ⟨after, trace⟩ := issued.reflect_scalar state scalar call returned request inputs rawType nativeType invocation
  exact ⟨after, trace.value_plain⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationCertifiedPublicSession
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationCertifiedPublicSessionDirectSourceOutcomes
/-! Actual calls through retained handles expose the original independent
Source callable and its exact application at the same returned session. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationCertifiedPublicSession
open Core Frontend SourceInference
open CallableIndexedOwnedFunctionValues (Header)
open RecursiveNamedPublicFunctionHistory (Entry)
open RecursiveNamedPublicScalarResults (ScalarOutput)

variable {recipe : SourceCoreIndexedSession.Recipe} (issued : Issued recipe)
  {anchor : Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {entries : List Entry}

/-- Packed public input, the retained callable and the actual completion
determine the ordered Source arguments and both Source outcome witnesses. -/
theorem Issued.reflect_direct_scalar_plain
    (before : issued.State anchor session entries)
    (entry : Entry) (member : entry ∈ entries) (scalar : ScalarOutput)
    {parameter hostParameter : TypeSystem.Ty}
    (entryType : entry.sourceType = .function parameter scalar.sourceType)
    (handleType : entry.handle.sourceType = .function hostParameter scalar.sourceType)
    {argument : SourceCorePublicValues.Value} {packedSource : Dynamic.Value}
    (input : RecursiveNamedPublicFunctionHistoryInputs.Input entries anchor.function.context
      parameter argument packedSource)
    {options : SourceCoreExecution.RunOptions}
    {completion : SourceCoreExecution.Completion artifact}
    (invoked : session.InvokeAt entry.handle argument options (.ok (.succeeded completion)))
    (output : completion.value = scalar.publicValue)
    (invocation : Staging.Recursive.Scope) :
    ∃ sources, Dynamic.ValuesPack sources packedSource ∧
      RecursivePublicCallableArity.Arity (Program.ofChecked recipe.compiled.sourceProgram)
        entry.source sources.length ∧
      ∃ next : issued.State anchor completion.session entries,
      ∃ size, Staging.Recursive.Size.Applies (Program.ofChecked recipe.compiled.sourceProgram)
        (SelectedCompilationPhysicalProgramSupport.stages recipe.compiled) size
        invocation anchor.function.context before.heap entry.source sources (.value scalar.source) next.heap ∧
      Dynamic.CallableApplies (Program.ofChecked recipe.compiled.sourceProgram)
        anchor.function.context invocation.evidence (Staging.Recursive.callableEvidence entry.source)
        before.heap entry.source sources scalar.source next.heap := by
  obtain ⟨sources, packing, arity, next, size, trace⟩ :=
    SelectedCompilationPublicSessionDirectScalarStep.State.invoke_scalar issued.support issued.prepared
      before entry member scalar entryType handleType input invoked output invocation
  exact ⟨sources, packing, arity, next, size, trace, trace.sound.value_plain⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationCertifiedPublicSession
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationProfiledPublicSessionFailures
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationProfiledPublicSessionSourceFailures
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationProfiledPublicSessionDirectFailures
/-! Actual failed calls through retained handles preserve their original
callable, full dictionary, exact heap and complete prior history. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationCertifiedPublicSession
open Core Frontend SourceInference
open CallableIndexedOwnedFunctionValues (Header)
open RecursiveNamedPublicFunctionHistory (Entry)

variable {recipe : SourceCoreIndexedSession.Recipe} (issued : Profiled recipe)
  {anchor : Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {entries : List Entry}

/-- The original constructor determines whether the fault is an ordinary
Dynamic fault or a rejected stage guard. -/
def DirectFailureProjection (program : Program) (context : Context)
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap)
    (callable : Dynamic.Value) (arguments : List Dynamic.Value)
    (failure : Staging.Recursive.Failure) (after : Dynamic.Heap) : Prop :=
  match failure with
  | .semantic reason => Dynamic.CallableFaults program context invocation.evidence
      (Staging.Recursive.callableEvidence callable) before callable arguments reason after
  | .stage origin call reason => Staging.Recursive.Generated origin call reason

theorem Profiled.reflect_direct_failure
    (before : issued.toIssued.State anchor session entries)
    (entry : Entry) (member : entry ∈ entries)
    {parameter result : TypeSystem.Ty}
    (entryType : entry.sourceType = .function parameter result)
    {argument : SourceCorePublicValues.Value} {packedSource : Dynamic.Value}
    (input : RecursiveNamedPublicFunctionHistoryInputs.Input entries anchor.function.context
      parameter argument packedSource)
    {options : SourceCoreExecution.RunOptions}
    {returned : SourceCoreExecution.Session artifact} {reason : Word}
    (invoked : session.InvokeAt entry.handle argument options (.ok (.failed reason returned)))
    (invocation : Staging.Recursive.Scope) :
    ∃ sources, Dynamic.ValuesPack sources packedSource ∧
      RecursivePublicCallableArity.Arity (Program.ofChecked recipe.compiled.sourceProgram) entry.source sources.length ∧
      ∃ failure, ∃ next : issued.toIssued.State anchor returned entries,
      ∃ size, Staging.Recursive.Size.Applies (Program.ofChecked recipe.compiled.sourceProgram)
        (SelectedCompilationPhysicalProgramSupport.stages recipe.compiled) size
        invocation anchor.function.context before.heap entry.source sources (.fault failure) next.heap ∧
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
        next.receiving.result.diagnostics failure reason :=
  SelectedCompilationPublicSessionDirectFailureStep.State.invoke_failure
    issued.support issued.registryBodies issued.prepared before entry member entryType input invoked invocation

theorem Profiled.reflect_direct_failure_plain
    (before : issued.toIssued.State anchor session entries)
    (entry : Entry) (member : entry ∈ entries)
    {parameter result : TypeSystem.Ty}
    (entryType : entry.sourceType = .function parameter result)
    {argument : SourceCorePublicValues.Value} {packedSource : Dynamic.Value}
    (input : RecursiveNamedPublicFunctionHistoryInputs.Input entries anchor.function.context
      parameter argument packedSource)
    {options : SourceCoreExecution.RunOptions}
    {returned : SourceCoreExecution.Session artifact} {reason : Word}
    (invoked : session.InvokeAt entry.handle argument options (.ok (.failed reason returned)))
    (invocation : Staging.Recursive.Scope) :
    ∃ sources, Dynamic.ValuesPack sources packedSource ∧
      RecursivePublicCallableArity.Arity (Program.ofChecked recipe.compiled.sourceProgram) entry.source sources.length ∧
      ∃ failure, ∃ next : issued.toIssued.State anchor returned entries,
      ∃ size, Staging.Recursive.Size.Applies (Program.ofChecked recipe.compiled.sourceProgram)
        (SelectedCompilationPhysicalProgramSupport.stages recipe.compiled) size
        invocation anchor.function.context before.heap entry.source sources (.fault failure) next.heap ∧
      DirectFailureProjection (Program.ofChecked recipe.compiled.sourceProgram) anchor.function.context
        invocation before.heap entry.source sources failure next.heap ∧
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
        next.receiving.result.diagnostics failure reason := by
  obtain ⟨sources, packing, arity, failure, next, size, trace, diagnostic⟩ :=
    issued.reflect_direct_failure before entry member entryType input invoked invocation
  refine ⟨sources, packing, arity, failure, next, size, trace, ?_, diagnostic⟩
  cases failure with
  | semantic reason => exact trace.sound.semanticFault_plain
  | stage origin call reason => exact trace.sound.stage_origin rfl

theorem Profiled.forward_direct_failure
    (before : issued.toIssued.State anchor session entries)
    (entry : Entry) (member : entry ∈ entries)
    {parameter result : TypeSystem.Ty}
    (entryType : entry.sourceType = .function parameter result)
    {argument : SourceCorePublicValues.Value} {packedSource : Dynamic.Value}
    (input : RecursiveNamedPublicFunctionHistoryInputs.Input entries anchor.function.context
      parameter argument packedSource)
    {inputFuel : Nat} {checkpoint : SourceCoreExecution.Checkpoint artifact}
    (accepted : session.startHandlePacked entry.handle argument inputFuel = .ok checkpoint)
    (ready : session.ExportsReady)
    {invocation : Staging.Recursive.Scope} {sources : List Dynamic.Value}
    (packing : Dynamic.ValuesPack sources packedSource)
    (arity : RecursivePublicCallableArity.Arity (Program.ofChecked recipe.compiled.sourceProgram) entry.source sources.length)
    {sourceSize : Nat} {after : Dynamic.Heap} {failure : Staging.Recursive.Failure}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked recipe.compiled.sourceProgram)
      (SelectedCompilationPhysicalProgramSupport.stages recipe.compiled) sourceSize
      invocation anchor.function.context before.heap entry.source sources (.fault failure) after) :
    SelectedCompilationPublicSessionDirectFailureForward.FailureForwardAt
      issued.catalog.rows anchor issued.initial issued.support.profile recipe entries failure checkpoint after :=
  SelectedCompilationPublicSessionDirectFailureForward.forward_call
    issued.support issued.registryBodies issued.prepared before entry member entryType input accepted ready packing arity trace

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationCertifiedPublicSession
end
