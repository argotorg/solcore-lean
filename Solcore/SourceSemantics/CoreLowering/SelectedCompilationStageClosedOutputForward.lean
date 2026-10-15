import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageNamedOutputForward
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageInitialOutputForward
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosedInitialForward
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosedPublicForward

/-! Ordinary Source success determines the complete public value, including
its original metadata and any selected callable leaves retained for later use. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosedOutputForward
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedFunctionValues (Header)
open SelectedCompilationPublicSessionState
open SelectedCompilationCertifiedPublicSession (Profiled Initial)
open SelectedCompilationStagePublicInputLifting
open SelectedCompilationStageClosedDirectForward.Output (ForwardAt)

variable {recipe : SourceCoreIndexedSession.Recipe} (issued : Profiled recipe)
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
  {options : SourceCoreExecution.RunOptions}

/-- Initial data inputs and an ordinary Source result suffice for full output
reimport and ordered retention of nested callables, or genuine stage failure. -/
theorem initial (call : StartedCall session key publicArguments options)
    (start : Initial issued.toIssued call)
    (simple : ∀ value ∈ publicArguments, SourceCoreIndexedSession.SimplePublic value)
    (inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      start.header.function.context publicArguments start.header.types)
    {arguments : List Dynamic.Value}
    (inputMeanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap} {value : Dynamic.Value}
    (trace : PlainValue start.header start.header invocation ⟨[]⟩ arguments value after) :
    (SourceCall start.header start.header invocation ⟨[]⟩ arguments (.value value) after ∧
      ForwardAt issued.catalog.rows start.header issued.initial issued.support.profile recipe []
        start.header.function.resultType call.checkpoint value after) ∨
    SelectedCompilationStageClosedInitialForward.StageStopped issued call start invocation arguments := by
  obtain ⟨staged, reached, lifted, adapted⟩ :=
    SelectedCompilationStageClosedInitialForward.lift_call issued call start simple inputTypes
      inputMeanings (plain_value trace)
  cases adapted with
  | completed =>
    exact .inl ⟨lifted, SelectedCompilationStageInitialOutputForward.first_output
      issued.catalog.rows issued.prepared start.header start.header issued.support
      issued.catalog.distinct call start.start simple inputTypes inputMeanings lifted⟩
  | rejected origin occurrence reason reached =>
    exact .inr ⟨origin, occurrence, reason, reached, lifted.failure_plain, lifted,
      Profiled.forward_initial_failure start simple inputTypes inputMeanings lifted⟩

/-- A later named call preserves the whole result and earlier handle history;
selected nested handles can join that same returned physical state. -/
theorem later
    {anchor : Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (state : issued.toIssued.State anchor session entries)
    (call : StartedCall session key publicArguments options)
    (request : RecursiveNamedPublicHistoryFrontdoor.Started (headers issued.catalog.rows) issued.prepared
      call.checkpoint state.session key publicArguments options.inputValidationFuel state.world state.store)
    {arguments : List Dynamic.Value}
    (inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments)
    (ready : session.ExportsReady)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap} {value : Dynamic.Value}
    (trace : PlainValue anchor request.header invocation state.heap arguments value after) :
    (SourceCall anchor request.header invocation state.heap arguments (.value value) after ∧
      ForwardAt issued.catalog.rows anchor issued.initial issued.support.profile recipe entries
        request.header.function.resultType call.checkpoint value after) ∨
    SelectedCompilationStagePublicForward.StageStopped issued state call request.header invocation arguments := by
  obtain ⟨staged, reached, lifted, adapted⟩ := lift_call_at_input_registry issued.support
    (SelectedCompilationStagePublicProgramLifting.named_bodies issued.support)
    issued.prepared state call request inputs (plain_value trace)
  cases adapted with
  | completed =>
    exact .inl ⟨lifted, SelectedCompilationStageNamedOutputForward.forward_at_input_registry
      issued.support issued.prepared state call request inputs ready lifted⟩
  | rejected origin occurrence reason reached =>
    exact .inr ⟨origin, occurrence, reason, reached, lifted.failure_plain, lifted,
      SelectedCompilationPublicSessionFailureForward.forward_call_at_input_registry
        issued.support issued.registryBodies issued.prepared state call request inputs ready lifted⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosedOutputForward
