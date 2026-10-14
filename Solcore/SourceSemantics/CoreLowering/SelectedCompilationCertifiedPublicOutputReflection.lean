import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicDirectOutputReflection
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicNamedOutputReflection
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicInitialOutputReflection
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationProfiledPublicSession

/-! Closed reflection entry points retain the complete public result and the
ordinary Source outcome using the actual checker-derived selected support. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationCertifiedPublicSession
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedFunctionValues (Header)
open RecursiveNamedPublicPhysicalSessionState (Call SourceCall PlainValue)
open RecursiveNamedPublicFunctionHistory (Entry)
open SelectedCompilationStageClosedDirectForward.Output (ReturnedValue)

variable {recipe : SourceCoreIndexedSession.Recipe} {issued : Profiled recipe}
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
  {options : SourceCoreExecution.RunOptions}

/-- Actual initial success reflects to the whole Source value and exact heap. -/
theorem Initial.reflect_output_plain
    {call : Call session key publicArguments options}
    (initial : Initial issued.toIssued call.toStartedCall)
    (simple : ∀ value ∈ publicArguments, SourceCoreIndexedSession.SimplePublic value)
    (inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      initial.header.function.context publicArguments initial.header.types)
    {arguments : List Dynamic.Value}
    (inputMeanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments)
    (invocation : Staging.Recursive.Scope) :
    ∃ source, ∃ after : issued.toIssued.State initial.header call.completion.session [],
      SourceCall initial.header initial.header invocation ⟨[]⟩ arguments (.value source) after.heap ∧
      PlainValue initial.header initial.header invocation ⟨[]⟩ arguments source after.heap ∧
      ReturnedValue call.completion after initial.header.function.resultType source options.outputValidationFuel := by
  obtain ⟨descriptor⟩ := header_descriptor initial.header
  exact SelectedCompilationPublicInitialOutputReflection.first_output issued.catalog.rows issued.prepared
    initial.header initial.header issued.support issued.catalog.distinct call initial.start simple
    inputTypes inputMeanings descriptor invocation

variable (issued : Profiled recipe)
  {anchor : Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
  {entries : List Entry}

/-- Named completion keeps the receiving registry and all prior callable captures. -/
theorem Profiled.reflect_output_plain
    (state : issued.toIssued.State anchor session entries)
    (call : Call session key publicArguments options)
    (request : RecursiveNamedPublicHistoryFrontdoor.Started (headers issued.catalog.rows) issued.prepared
      call.checkpoint state.session key publicArguments options.inputValidationFuel state.world state.store)
    {arguments : List Dynamic.Value}
    (inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments)
    (invocation : Staging.Recursive.Scope) :
    ∃ source, ∃ after : issued.toIssued.State anchor call.completion.session entries,
      SourceCall anchor request.header invocation state.heap arguments (.value source) after.heap ∧
      PlainValue anchor request.header invocation state.heap arguments source after.heap ∧
      ReturnedValue call.completion after request.header.function.resultType source options.outputValidationFuel := by
  obtain ⟨descriptor⟩ := header_descriptor request.header
  exact SelectedCompilationPublicNamedOutputReflection.State.reflect_output_at_input_registry
    issued.support issued.prepared state call request inputs descriptor invocation

/-- Packed direct completion recovers the true arity and complete Source value;
host and Source raw result types retain their actual compatibility equality. -/
theorem Profiled.reflect_direct_output_plain
    (state : issued.toIssued.State anchor session entries)
    (entry : Entry) (member : entry ∈ entries)
    {parameter result : TypeSystem.Ty}
    (entryType : entry.sourceType = .function parameter result)
    {argument : SourceCorePublicValues.Value} {packedSource : Dynamic.Value}
    (input : RecursiveNamedPublicFunctionHistoryInputs.Input entries anchor.function.context
      parameter argument packedSource)
    {completion : SourceCoreExecution.Completion artifact}
    (invoked : session.InvokeAt entry.handle argument options (.ok (.succeeded completion)))
    (invocation : Staging.Recursive.Scope) :
    ∃ sources, Dynamic.ValuesPack sources packedSource ∧
      RecursivePublicCallableArity.Arity (Program.ofChecked recipe.compiled.sourceProgram) entry.source sources.length ∧
      ∃ source, ∃ after : issued.toIssued.State anchor completion.session entries,
      ∃ size, Staging.Recursive.Size.Applies (Program.ofChecked recipe.compiled.sourceProgram)
        (SelectedCompilationPhysicalProgramSupport.stages recipe.compiled) size
        invocation anchor.function.context state.heap entry.source sources (.value source) after.heap ∧
      Dynamic.CallableApplies (Program.ofChecked recipe.compiled.sourceProgram) anchor.function.context
        invocation.evidence (Staging.Recursive.callableEvidence entry.source)
        state.heap entry.source sources source after.heap ∧
      ReturnedValue completion after result source options.outputValidationFuel :=
  SelectedCompilationPublicDirectOutputReflection.State.reflect_output issued.support issued.prepared
    state entry member entryType input invoked invocation

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationCertifiedPublicSession
