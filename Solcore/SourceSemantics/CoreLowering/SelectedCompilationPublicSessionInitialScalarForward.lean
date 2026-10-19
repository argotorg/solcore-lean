import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionInitialDataScalarForward
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicInitialArguments
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicReturnedValues
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicClosureHistory
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionInitial
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionScalarForward

/-! An initial scalar call retains the real bootstrapped state with an empty
handle history. Independent Source success supplies both required budgets. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionInitialScalarForward
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedFunctionValues (Header)
open RecursiveNamedPublicScalarResults (ScalarOutput)
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

theorem first_scalar
    (distinct : (inputs.map (fun input => input.prepared.index)).Nodup)
    (scalar : ScalarOutput) (call : StartedCall session key publicArguments options)
    (start : Started rows prepared header call)
    (simple : ∀ value ∈ publicArguments, SourceCoreIndexedSession.SimplePublic value)
    (inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      header.function.context publicArguments header.types)
    {arguments : List Dynamic.Value}
    (inputMeanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments)
    (rawType : header.function.resultType = scalar.sourceType)
    (nativeType : header.output = scalar.nativeType)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap}
    (trace : SourceCall anchor header invocation ⟨[]⟩ arguments (.value scalar.source) after) :
    SelectedCompilationPublicSessionScalarForward.ForwardAt (entries := [])
      rows anchor initial support.profile recipe scalar call after := by
  have _ := simple
  exact SelectedCompilationPublicSessionInitialDataScalarForward.first_scalar
    rows prepared anchor header support distinct scalar call start inputTypes inputMeanings rawType nativeType trace

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionInitialScalarForward
