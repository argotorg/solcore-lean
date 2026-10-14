import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageInitialInputLifting
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStagePublicProgramLifting
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationProfiledPublicSessionFailures

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosedInitialForward
open Core Frontend SourceInference
open RecursiveNamedPublicPhysicalSessionState
open SelectedCompilationCertifiedPublicSession (Profiled Initial)
open SelectedCompilationStagePublicInputLifting
open RecursiveNamedPublicScalarResults (ScalarOutput)

variable {recipe : SourceCoreIndexedSession.Recipe} (issued : Profiled recipe)
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
  {options : SourceCoreExecution.RunOptions}

/-- An authentic early stage rejection keeps its reached heap and the public
failure continuation from the actual initial bootstrap. -/
def StageStopped (call : StartedCall session key publicArguments options)
    (initial : Initial issued.toIssued call)
    (invocation : Staging.Recursive.Scope) (arguments : List Dynamic.Value) : Prop :=
  ∃ origin occurrence reason reached,
    Staging.Recursive.Generated origin occurrence reason ∧
    SourceCall initial.header initial.header invocation ⟨[]⟩ arguments
      (.fault (.stage origin occurrence reason)) reached ∧
    SelectedCompilationPublicSessionFailureForward.FailureForwardAt (entries := [])
      issued.catalog.rows initial.header issued.initial issued.support.profile recipe
      (.stage origin occurrence reason) call reached

variable (call : StartedCall session key publicArguments options)
  (initial : Initial issued.toIssued call)
  (simple : ∀ value ∈ publicArguments, SourceCoreIndexedSession.SimplePublic value)
  (inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
    initial.header.function.context publicArguments initial.header.types)
  {arguments : List Dynamic.Value}
  (inputMeanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments)
  {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap}

include simple inputTypes inputMeanings in
/-- The selected physical support supplies every internal body lifting proof. -/
theorem lift_call {plain : Dynamic.ExpressionOutcome}
    (trace : PlainCall initial.header initial.header invocation ⟨[]⟩ arguments plain after) :
    ∃ staged reached,
      SourceCall initial.header initial.header invocation ⟨[]⟩ arguments staged reached ∧
      Staging.Recursive.Lifting.Adapted plain after staged reached :=
  SelectedCompilationStageInitialInputLifting.lift_call
    issued.catalog.rows issued.prepared initial.header initial.header issued.support
    (SelectedCompilationStagePublicProgramLifting.named_bodies issued.support)
    issued.catalog.distinct call initial.start simple inputTypes inputMeanings trace

include simple inputTypes inputMeanings in
/-- An ordinary initial scalar result gives the same public result and heap,
with a separate alternative for a genuine earlier stage rejection. -/
theorem scalar (scalar : ScalarOutput)
    (rawType : initial.header.function.resultType = scalar.sourceType)
    (nativeType : initial.header.output = scalar.nativeType)
    (trace : PlainValue initial.header initial.header invocation ⟨[]⟩ arguments scalar.source after) :
    (SourceCall initial.header initial.header invocation ⟨[]⟩ arguments (.value scalar.source) after ∧
      SelectedCompilationPublicSessionScalarForward.ForwardAt (entries := [])
        issued.catalog.rows initial.header issued.initial issued.support.profile recipe scalar call after) ∨
    StageStopped issued call initial invocation arguments := by
  obtain ⟨staged, reached, lifted, adapted⟩ :=
    lift_call issued call initial simple inputTypes inputMeanings (plain_value trace)
  cases adapted with
  | completed =>
    exact .inl ⟨lifted, SelectedCompilationPublicSessionInitialScalarForward.first_scalar
      issued.catalog.rows issued.prepared initial.header initial.header issued.support
      issued.catalog.distinct scalar call initial.start simple inputTypes inputMeanings rawType nativeType lifted⟩
  | rejected origin occurrence reason reached =>
    exact .inr ⟨origin, occurrence, reason, reached, lifted.failure_plain, lifted,
      Profiled.forward_initial_failure initial simple inputTypes inputMeanings lifted⟩

include simple inputTypes inputMeanings in
/-- An ordinary initial semantic fault retains its diagnostic and heap, unless
an actual stage check rejects before that fault is reached. -/
theorem fault (reason : Dynamic.SemanticFault)
    (trace : PlainFault initial.header initial.header invocation ⟨[]⟩ arguments reason after) :
    (SourceCall initial.header initial.header invocation ⟨[]⟩ arguments (.fault (.semantic reason)) after ∧
      SelectedCompilationPublicSessionFailureForward.FailureForwardAt (entries := [])
        issued.catalog.rows initial.header issued.initial issued.support.profile recipe (.semantic reason) call after) ∨
    StageStopped issued call initial invocation arguments := by
  obtain ⟨staged, reached, lifted, adapted⟩ :=
    lift_call issued call initial simple inputTypes inputMeanings (plain_fault trace)
  cases adapted with
  | completed =>
    exact .inl ⟨lifted, Profiled.forward_initial_failure initial simple inputTypes inputMeanings lifted⟩
  | rejected origin occurrence reason reached =>
    exact .inr ⟨origin, occurrence, reason, reached, lifted.failure_plain, lifted,
      Profiled.forward_initial_failure initial simple inputTypes inputMeanings lifted⟩

include simple inputTypes inputMeanings in
/-- An ordinary initial function result can be exported as a retained handle
with the same Source value and heap, or stop at a genuine earlier stage check. -/
theorem function {parameter resultType : TypeSystem.Ty} {value : Dynamic.Value}
    (functionResult : SourceCoreRawMetadata.runtimeType initial.header.function.resultType =
      .function parameter resultType)
    (trace : PlainValue initial.header initial.header invocation ⟨[]⟩ arguments value after) :
    (SourceCall initial.header initial.header invocation ⟨[]⟩ arguments (.value value) after ∧
      SelectedCompilationPublicSessionInitialForward.ForwardAt issued.catalog.rows
        initial.header initial.header issued.support call value after) ∨
    StageStopped issued call initial invocation arguments := by
  obtain ⟨staged, reached, lifted, adapted⟩ :=
    lift_call issued call initial simple inputTypes inputMeanings (plain_value trace)
  cases adapted with
  | completed =>
    exact .inl ⟨lifted, initial.forward_function simple inputTypes inputMeanings functionResult lifted⟩
  | rejected origin occurrence reason reached =>
    exact .inr ⟨origin, occurrence, reason, reached, lifted.failure_plain, lifted,
      Profiled.forward_initial_failure initial simple inputTypes inputMeanings lifted⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosedInitialForward
