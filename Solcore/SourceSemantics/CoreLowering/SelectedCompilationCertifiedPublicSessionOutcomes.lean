import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCertifiedPublicSessionSteps
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionInitialScalarForward
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionInitialScalarStep

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
