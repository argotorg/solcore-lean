import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCertifiedPublicSessionInitial
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionRegistryFunctionForward
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionRegistryScalarForward
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionRegistryFunctionStep
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionRegistryScalarStep

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
