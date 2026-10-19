import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageInitialDataInputLifting
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionInitialDataForward
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionInitialDataScalarForward
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionInitialDataFailureForward
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageInitialDataOutputForward
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionInitialDataScalarStep
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionInitialDataFailureStep
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicInitialDataOutputReflection
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosedInitialForward

/-! Initial calls accept the complete structurally typed data input family.
Actual bootstrap and public encoding construct the heap and receiving registry;
ordinary Source traces supply execution outcomes. The raw input certificate
retains constructor, mapping and proxy metadata before runtime erasure. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationCertifiedPublicSession
open Core Frontend SourceInference
open SelectedCompilationPublicSessionState
open SelectedCompilationStagePublicInputLifting
open RecursiveNamedPublicScalarResults (ScalarOutput)
open SelectedCompilationStageClosedDirectForward.Output (ReturnedValue)

variable {recipe : SourceCoreIndexedSession.Recipe} {issued : Profiled recipe}
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
  {options : SourceCoreExecution.RunOptions}

theorem Initial.lift_data_call
    {call : StartedCall session key publicArguments options} (initial : Initial issued.toIssued call)
    (inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      initial.header.function.context publicArguments initial.header.types)
    {arguments : List Dynamic.Value}
    (inputMeanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments)
    {invocation : Staging.Recursive.Scope} {plain : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : PlainCall initial.header initial.header invocation ⟨[]⟩ arguments plain after) :
    ∃ staged reached,
      SourceCall initial.header initial.header invocation ⟨[]⟩ arguments staged reached ∧
      Staging.Recursive.Lifting.Adapted plain after staged reached :=
  SelectedCompilationStageInitialDataInputLifting.lift_call
    issued.catalog.rows issued.prepared initial.header initial.header issued.support
    (SelectedCompilationStagePublicProgramLifting.named_bodies issued.support)
    issued.catalog.distinct call initial.start inputTypes inputMeanings trace

theorem Initial.forward_data_failure
    {call : StartedCall session key publicArguments options} (initial : Initial issued.toIssued call)
    (inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      initial.header.function.context publicArguments initial.header.types)
    {arguments : List Dynamic.Value}
    (inputMeanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap} {failure : Staging.Recursive.Failure}
    (trace : SourceCall initial.header initial.header invocation ⟨[]⟩ arguments (.fault failure) after) :
    SelectedCompilationPublicSessionFailureForward.FailureForwardAt (entries := []) issued.catalog.rows
      initial.header issued.initial issued.support.profile recipe failure call after :=
  SelectedCompilationPublicSessionInitialDataFailureForward.first_failure issued.catalog.rows issued.prepared
    initial.header initial.header issued.support issued.registryBodies issued.catalog.distinct call initial.start
    inputTypes inputMeanings trace

theorem Initial.forward_data_scalar_plain
    {call : StartedCall session key publicArguments options} (initial : Initial issued.toIssued call)
    (inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      initial.header.function.context publicArguments initial.header.types)
    {arguments : List Dynamic.Value}
    (inputMeanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments)
    (scalar : ScalarOutput)
    (rawType : initial.header.function.resultType = scalar.sourceType)
    (nativeType : initial.header.output = scalar.nativeType)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap}
    (trace : PlainValue initial.header initial.header invocation ⟨[]⟩ arguments scalar.source after) :
    (SourceCall initial.header initial.header invocation ⟨[]⟩ arguments (.value scalar.source) after ∧
      SelectedCompilationPublicSessionScalarForward.ForwardAt (entries := []) issued.catalog.rows
        initial.header issued.initial issued.support.profile recipe scalar call after) ∨
    SelectedCompilationStageClosedInitialForward.StageStopped issued call initial invocation arguments := by
  obtain ⟨staged, reached, lifted, adapted⟩ := initial.lift_data_call inputTypes inputMeanings (plain_value trace)
  cases adapted with
  | completed =>
    exact .inl ⟨lifted, SelectedCompilationPublicSessionInitialDataScalarForward.first_scalar
      issued.catalog.rows issued.prepared initial.header initial.header issued.support issued.catalog.distinct
      scalar call initial.start inputTypes inputMeanings rawType nativeType lifted⟩
  | rejected origin occurrence reason reached =>
    exact .inr ⟨origin, occurrence, reason, reached, lifted.failure_plain, lifted,
      initial.forward_data_failure inputTypes inputMeanings lifted⟩

theorem Initial.forward_data_fault_plain
    {call : StartedCall session key publicArguments options} (initial : Initial issued.toIssued call)
    (inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      initial.header.function.context publicArguments initial.header.types)
    {arguments : List Dynamic.Value}
    (inputMeanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap} {reason : Dynamic.SemanticFault}
    (trace : PlainFault initial.header initial.header invocation ⟨[]⟩ arguments reason after) :
    (SourceCall initial.header initial.header invocation ⟨[]⟩ arguments (.fault (.semantic reason)) after ∧
      SelectedCompilationPublicSessionFailureForward.FailureForwardAt (entries := []) issued.catalog.rows
        initial.header issued.initial issued.support.profile recipe (.semantic reason) call after) ∨
    SelectedCompilationStageClosedInitialForward.StageStopped issued call initial invocation arguments := by
  obtain ⟨staged, reached, lifted, adapted⟩ := initial.lift_data_call inputTypes inputMeanings (plain_fault trace)
  cases adapted with
  | completed => exact .inl ⟨lifted, initial.forward_data_failure inputTypes inputMeanings lifted⟩
  | rejected origin occurrence reason reached =>
    exact .inr ⟨origin, occurrence, reason, reached, lifted.failure_plain, lifted,
      initial.forward_data_failure inputTypes inputMeanings lifted⟩

theorem Initial.forward_data_output_plain
    {call : StartedCall session key publicArguments options} (initial : Initial issued.toIssued call)
    (inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      initial.header.function.context publicArguments initial.header.types)
    {arguments : List Dynamic.Value}
    (inputMeanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap} {value : Dynamic.Value}
    (trace : PlainValue initial.header initial.header invocation ⟨[]⟩ arguments value after) :
    (SourceCall initial.header initial.header invocation ⟨[]⟩ arguments (.value value) after ∧
      SelectedCompilationStageClosedDirectForward.Output.ForwardAt issued.catalog.rows initial.header issued.initial
        issued.support.profile recipe [] initial.header.function.resultType call.checkpoint value after) ∨
    SelectedCompilationStageClosedInitialForward.StageStopped issued call initial invocation arguments := by
  obtain ⟨staged, reached, lifted, adapted⟩ := initial.lift_data_call inputTypes inputMeanings (plain_value trace)
  cases adapted with
  | completed =>
    exact .inl ⟨lifted, SelectedCompilationStageInitialDataOutputForward.first_output
      issued.catalog.rows issued.prepared initial.header initial.header issued.support issued.catalog.distinct
      call initial.start inputTypes inputMeanings lifted⟩
  | rejected origin occurrence reason reached =>
    exact .inr ⟨origin, occurrence, reason, reached, lifted.failure_plain, lifted,
      initial.forward_data_failure inputTypes inputMeanings lifted⟩

theorem Initial.forward_data_function_plain
    {call : StartedCall session key publicArguments options} (initial : Initial issued.toIssued call)
    (inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      initial.header.function.context publicArguments initial.header.types)
    {arguments : List Dynamic.Value}
    (inputMeanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments)
    {parameter resultType : TypeSystem.Ty} {value : Dynamic.Value}
    (functionResult : SourceCoreRawMetadata.runtimeType initial.header.function.resultType =
      .function parameter resultType)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap}
    (trace : PlainValue initial.header initial.header invocation ⟨[]⟩ arguments value after) :
    (SourceCall initial.header initial.header invocation ⟨[]⟩ arguments (.value value) after ∧
      SelectedCompilationPublicSessionInitialForward.ForwardAt issued.catalog.rows initial.header
        initial.header issued.support call value after) ∨
    SelectedCompilationStageClosedInitialForward.StageStopped issued call initial invocation arguments := by
  obtain ⟨staged, reached, lifted, adapted⟩ := initial.lift_data_call inputTypes inputMeanings (plain_value trace)
  cases adapted with
  | completed =>
    exact .inl ⟨lifted, SelectedCompilationPublicSessionInitialDataForward.first_function
      issued.catalog.rows issued.prepared initial.header initial.header issued.support issued.catalog.distinct
      call initial.start inputTypes inputMeanings functionResult lifted⟩
  | rejected origin occurrence reason reached =>
    exact .inr ⟨origin, occurrence, reason, reached, lifted.failure_plain, lifted,
      initial.forward_data_failure inputTypes inputMeanings lifted⟩

theorem Initial.reflect_data_scalar_plain
    {call : Call session key publicArguments options} (initial : Initial issued.toIssued call.toStartedCall)
    (inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      initial.header.function.context publicArguments initial.header.types)
    {arguments : List Dynamic.Value}
    (inputMeanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments)
    (scalar : ScalarOutput) (returned : call.completion.value = scalar.publicValue)
    (rawType : initial.header.function.resultType = scalar.sourceType)
    (nativeType : initial.header.output = scalar.nativeType)
    (invocation : Staging.Recursive.Scope) :
    ∃ after : issued.toIssued.State initial.header call.completion.session [],
      PlainValue initial.header initial.header invocation ⟨[]⟩ arguments scalar.source after.heap := by
  obtain ⟨descriptor⟩ := header_descriptor initial.header
  obtain ⟨after, trace⟩ := SelectedCompilationPublicSessionInitialDataScalarStep.first_scalar
    issued.catalog.rows issued.prepared initial.header initial.header issued.support issued.catalog.distinct
    scalar call returned initial.start inputTypes inputMeanings rawType nativeType descriptor invocation
  exact ⟨after, trace.value_plain⟩

theorem Initial.reflect_data_failure_plain
    {call : StartedCall session key publicArguments options} (initial : Initial issued.toIssued call)
    (returned : SourceCoreExecution.Session artifact) (reason : Word)
    (failedCall : session.RunAt key publicArguments options (.ok (.failed reason returned)))
    (inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      initial.header.function.context publicArguments initial.header.types)
    {arguments : List Dynamic.Value}
    (inputMeanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments)
    (invocation : Staging.Recursive.Scope) :
    ∃ failure, ∃ after : issued.toIssued.State initial.header returned [],
      SourceCall initial.header initial.header invocation ⟨[]⟩ arguments (.fault failure) after.heap ∧
      FailureProjection initial.header initial.header invocation ⟨[]⟩ arguments failure after.heap ∧
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults after.receiving.result.diagnostics failure reason := by
  obtain ⟨descriptor⟩ := header_descriptor initial.header
  obtain ⟨failure, after, trace, diagnostic⟩ := SelectedCompilationPublicSessionInitialDataFailureStep.first_failure
    issued.catalog.rows issued.prepared initial.header initial.header issued.support issued.registryBodies
    issued.catalog.distinct call returned reason failedCall initial.start inputTypes inputMeanings descriptor invocation
  exact ⟨failure, after, trace, trace.failure_plain, diagnostic⟩

theorem Initial.reflect_data_output_plain
    {call : Call session key publicArguments options} (initial : Initial issued.toIssued call.toStartedCall)
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
  exact SelectedCompilationPublicInitialDataOutputReflection.first_output issued.catalog.rows issued.prepared
    initial.header initial.header issued.support issued.catalog.distinct call initial.start
    inputTypes inputMeanings descriptor invocation

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationCertifiedPublicSession
