import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageInitialDataInputLifting
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStagePublicInputLifting
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionInitialScalarForward

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageInitialInputLifting
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open SelectedCompilationPublicSessionState (StartedCall SourceCall)
open SelectedCompilationPublicSessionInitial (Started)
open SelectedCompilationPhysicalProgramSupport (Support stagePrepared stages)
open SelectedCompilationStagePublicInputLifting (PlainCall NamedBodies)

variable {recipe : SourceCoreIndexedSession.Recipe}
  {inputs : List (Input recipe.compiled)} (rows : Inventory inputs)
  (prepared : SourceCoreIndexedSession.Recipe.prepare recipe.compiled = .ok recipe)
  (anchor header : Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))
  {initial : CallableIndexedOwnedPublicFaultReceivers.Receiver recipe.compiled.indexed}
  (support : Support recipe.compiled (headers rows) (keys recipe.compiled) initial)
  {publicArtifact : SourceCoreExecution.Artifact}
  {session : SourceCoreExecution.Session publicArtifact}
  {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
  {options : SourceCoreExecution.RunOptions}

theorem lift_call
    (bodies : NamedBodies support)
    (distinct : (inputs.map (fun input => input.prepared.index)).Nodup)
    (call : StartedCall session key publicArguments options)
    (start : Started rows prepared header call)
    (simple : ∀ value ∈ publicArguments, SourceCoreIndexedSession.SimplePublic value)
    (inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      header.function.context publicArguments header.types)
    {arguments : List Dynamic.Value}
    (inputMeanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments)
    {invocation : Staging.Recursive.Scope} {plain : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : PlainCall anchor header invocation ⟨[]⟩ arguments plain after) :
    ∃ staged reached, SourceCall anchor header invocation ⟨[]⟩ arguments staged reached ∧
      Staging.Recursive.Lifting.Adapted plain after staged reached := by
  have _ := simple
  exact SelectedCompilationStageInitialDataInputLifting.lift_call
    rows prepared anchor header support bodies distinct call start inputTypes inputMeanings trace

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageInitialInputLifting
