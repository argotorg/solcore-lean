import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicInitialDataOutputReflection
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicSourceCallOutcomes
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosedDirectForward
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicInitialArguments
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicReturnedValues
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicClosureHistory
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionInitial
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionScalarStep

/-! Initial public success reflects to a complete Source value and heap. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicInitialOutputReflection
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedFunctionValues (Header)
open SelectedCompilationStageClosedDirectForward.Output (ReturnedValue)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open SelectedCompilationPublicSessionState (StartedCall Call State SourceCall PlainValue)
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
    (call : Call session key publicArguments options)
    (start : Started rows prepared header call.toStartedCall)
    (simple : ∀ value ∈ publicArguments, SourceCoreIndexedSession.SimplePublic value)
    (inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      header.function.context publicArguments header.types)
    {arguments : List Dynamic.Value}
    (inputMeanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments)
    (descriptor : SourceCoreCallableContracts.Descriptor recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named header.named.signature.key))
    (invocation : Staging.Recursive.Scope) :
    ∃ source, ∃ after : State rows anchor initial support.profile recipe call.completion.session [],
      SourceCall anchor header invocation ⟨[]⟩ arguments (.value source) after.heap ∧
      PlainValue anchor header invocation ⟨[]⟩ arguments source after.heap ∧
      ReturnedValue call.completion after header.function.resultType source options.outputValidationFuel := by
  have _ := simple
  exact SelectedCompilationPublicInitialDataOutputReflection.first_output
    rows prepared anchor header support distinct call start inputTypes inputMeanings descriptor invocation

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicInitialOutputReflection
