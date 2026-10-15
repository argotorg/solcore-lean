import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStagePublicProgramLifting
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStagePublicForward
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationProfiledPublicSession
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionRegistryFailureForward
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionExportForward

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosedPublicForward
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedFunctionValues (Header)
open SelectedCompilationPublicSessionState
open SelectedCompilationCertifiedPublicSession (Profiled)
open SelectedCompilationStagePublicInputLifting
open RecursiveNamedPublicScalarResults (ScalarOutput)

variable {recipe : SourceCoreIndexedSession.Recipe} (issued : Profiled recipe)
  {anchor : Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {entries : List RecursiveNamedPublicFunctionHistory.Entry}
  {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
  {options : SourceCoreExecution.RunOptions}

open SelectedCompilationStagePublicForward (StageStopped)

variable (state : issued.toIssued.State anchor session entries)
  (call : StartedCall session key publicArguments options)
  (request : RecursiveNamedPublicHistoryFrontdoor.Started (headers issued.catalog.rows) issued.prepared
    call.checkpoint state.session key publicArguments options.inputValidationFuel state.world state.store)
  {arguments : List Dynamic.Value}
  (inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
    (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments)
  (ready : session.ExportsReady)
  {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap}

include inputs ready in
/-- An ordinary scalar application completes publicly with the same value
and heap, unless an authentic earlier stage check rejects the call. -/
theorem scalar (scalar : ScalarOutput)
    (rawType : request.header.function.resultType = scalar.sourceType)
    (nativeType : request.header.output = scalar.nativeType)
    (trace : PlainValue anchor request.header invocation state.heap arguments scalar.source after) :
    (SourceCall anchor request.header invocation state.heap arguments (.value scalar.source) after ∧
      SelectedCompilationPublicSessionScalarForward.ForwardAt (entries := entries)
        issued.catalog.rows anchor issued.initial issued.support.profile recipe scalar call after) ∨
    StageStopped issued state call request.header invocation arguments := by
  obtain ⟨staged, reached, lifted, adapted⟩ := lift_call_at_input_registry issued.support
    (SelectedCompilationStagePublicProgramLifting.named_bodies issued.support)
    issued.prepared state call request inputs (plain_value trace)
  cases adapted with
  | completed =>
    exact .inl ⟨lifted, SelectedCompilationPublicSessionScalarForward.forward_call_at_input_registry
      issued.support issued.prepared state scalar call request inputs rawType nativeType ready lifted⟩
  | rejected origin occurrence reason reached =>
    exact .inr ⟨origin, occurrence, reason, reached, lifted.failure_plain, lifted,
      SelectedCompilationPublicSessionFailureForward.forward_call_at_input_registry
        issued.support issued.registryBodies issued.prepared state call request inputs ready lifted⟩

include inputs ready in
/-- Ordinary semantic failure preserves its reason and reached heap, with
an explicit alternative for a genuine earlier stage rejection. -/
theorem fault (reason : Dynamic.SemanticFault)
    (trace : PlainFault anchor request.header invocation state.heap arguments reason after) :
    (SourceCall anchor request.header invocation state.heap arguments (.fault (.semantic reason)) after ∧
      SelectedCompilationPublicSessionFailureForward.FailureForwardAt (entries := entries)
        issued.catalog.rows anchor issued.initial issued.support.profile recipe (.semantic reason) call after) ∨
    StageStopped issued state call request.header invocation arguments := by
  obtain ⟨staged, reached, lifted, adapted⟩ := lift_call_at_input_registry issued.support
    (SelectedCompilationStagePublicProgramLifting.named_bodies issued.support)
    issued.prepared state call request inputs (plain_fault trace)
  cases adapted with
  | completed =>
    exact .inl ⟨lifted, SelectedCompilationPublicSessionFailureForward.forward_call_at_input_registry
      issued.support issued.registryBodies issued.prepared state call request inputs ready lifted⟩
  | rejected origin occurrence reason reached =>
    exact .inr ⟨origin, occurrence, reason, reached, lifted.failure_plain, lifted,
      SelectedCompilationPublicSessionFailureForward.forward_call_at_input_registry
        issued.support issued.registryBodies issued.prepared state call request inputs ready lifted⟩

include inputs ready in
/-- The actual returned function can be exported and imported again at the
same output budget while preserving every earlier retained handle. -/
theorem function {parameterType resultType : TypeSystem.Ty} {value : Dynamic.Value}
    (rawType : request.header.function.resultType = .function parameterType resultType)
    (trace : PlainValue anchor request.header invocation state.heap arguments value after) :
    (SourceCall anchor request.header invocation state.heap arguments (.value value) after ∧
      SelectedCompilationPublicSessionExportForward.ForwardAt
        issued.catalog.rows anchor issued.initial issued.support.profile recipe entries call.checkpoint
        (.function parameterType resultType) value after) ∨
    StageStopped issued state call request.header invocation arguments := by
  obtain ⟨staged, reached, lifted, adapted⟩ := lift_call_at_input_registry issued.support
    (SelectedCompilationStagePublicProgramLifting.named_bodies issued.support)
    issued.prepared state call request inputs (plain_value trace)
  cases adapted with
  | completed =>
    exact .inl ⟨lifted, SelectedCompilationPublicSessionExportForward.forward_function_at_input_registry
      issued.support issued.prepared state call request inputs rawType ready lifted⟩
  | rejected origin occurrence reason reached =>
    exact .inr ⟨origin, occurrence, reason, reached, lifted.failure_plain, lifted,
      SelectedCompilationPublicSessionFailureForward.forward_call_at_input_registry
        issued.support issued.registryBodies issued.prepared state call request inputs ready lifted⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosedPublicForward
