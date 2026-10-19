import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageInitialDataOutputForward
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosedDirectForward
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicInitialArguments
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicReturnedValues
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicClosureHistory
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionInitial
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionExportForward
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryNamedOutputPreservation

/-! Initial Source success preserves the whole exported value and any selected
nested callable leaves at the exact reached heap. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageInitialOutputForward
open Core Frontend SourceInference
open SelectedCompilationStageClosedDirectForward.Output (ForwardAt)
open RecursiveNamedPublicNestedOutputSelections (Selection)
open RecursiveNamedPublicFunctionHistory (Entry)
open SelectedCompilationPublicSessionDirectOutputCollection (selected_of_cast)
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open SelectedCompilationPublicSessionState (StartedCall State SourceCall)
open SelectedCompilationPublicSessionInitial (Started)
open SelectedCompilationPhysicalProgramSupport (Support stagePrepared)

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

theorem first_output
    (distinct : (inputs.map (fun input => input.prepared.index)).Nodup)
    (call : StartedCall session key publicArguments options)
    (start : Started rows prepared header call)
    (simple : ∀ value ∈ publicArguments, SourceCoreIndexedSession.SimplePublic value)
    (inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      header.function.context publicArguments header.types)
    {arguments : List Dynamic.Value}
    (inputMeanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap} {source : Dynamic.Value}
    (trace : SourceCall anchor header invocation ⟨[]⟩ arguments (.value source) after) :
    ForwardAt rows anchor initial support.profile
      recipe [] header.function.resultType call.checkpoint source after := by
  have _ := simple
  exact SelectedCompilationStageInitialDataOutputForward.first_output
    rows prepared anchor header support distinct call start inputTypes inputMeanings trace

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageInitialOutputForward
