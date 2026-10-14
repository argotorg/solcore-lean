import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCertifiedPublicSessionOutcomes
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicSourceCallOutcomes

/-! Successful public completions reflect to independent Dynamic applications
at the same issued session state, callable and reached Source heap. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationCertifiedPublicSession
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedFunctionValues (Header)
open RecursiveNamedPublicPhysicalSessionState (StartedCall FunctionCall Call SourceCall PlainValue)
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
